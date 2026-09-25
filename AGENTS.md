# AGENTS.md — seLe4n project guidance

> This file mirrors `CLAUDE.md` so that non-Claude coding agents (and any
> tool that follows the AGENTS.md convention) get the same project rules.
> If you edit one, edit the other in the same PR — the two files must
> stay byte-identical apart from this header.

## What this project is

seLe4n is a production-oriented microkernel written in Lean 4 with machine-checked
proofs, improving on seL4 architecture. Every kernel transition is an executable
pure function with zero `sorry`/`axiom`. First hardware target: Raspberry Pi 5.
Lean 4.28.0 toolchain, Lake build system, version 0.36.2.

> The version line above is one of the version sites that
> `scripts/check_version_sync.sh` (a Tier 0 gate, also run by the
> pre-commit hook) holds equal to `lakefile.toml`. When you bump
> `lakefile.toml` you must bump every site in the same PR — see the
> **Versioning policy** section below. Keep this sentence on a single
> line with the canonical trigger phrase (`Lake build system, version
> <x.y.z>`) intact: the verifier greps for the literal phrase on one
> line, so do not reword it or split it across a wrap.

## Versioning policy (every PR bumps the patch version)

**Every PR bumps the patch version and updates all version locations.**
There is no "release cut" accumulation under an `Unreleased` heading —
each merged PR ships its own `vX.Y.Z` and the docs always reflect the
live version.

- **Canonical source:** the `version` field in `lakefile.toml`. Every
  other site must equal it.
- **Bump in one step:** run `./scripts/bump_version.sh <new-version>`
  (e.g. `./scripts/bump_version.sh 0.31.11`). It rewrites every site
  listed in `scripts/version_locations.sh`, then self-verifies. Add a
  matching `## v<new-version> — <summary>` entry at the top of
  `CHANGELOG.md` by hand (the bumper reminds you).
- **Enforcement (sync gate):** `scripts/check_version_sync.sh` verifies
  that all sites equal `lakefile.toml`. It runs as a Tier 0 hygiene gate
  (CI, on every PR and push) and from the pre-commit hook (whenever a
  version-bearing file is staged), so a bump that forgets a location is
  a hard failure, never a silent drift. There is deliberately **no**
  force-bump (increment-vs-`main`) gate, so automated contributors
  (e.g. dependabot) are never blocked.
- **The version sites** (authoritative list in
  `scripts/version_locations.sh`): `lakefile.toml`; the four `sele4n-*`
  crates in `rust/Cargo.toml` / `rust/Cargo.lock`; `KERNEL_VERSION` in
  `rust/sele4n-hal/src/boot.rs`; `docs/spec/SELE4N_SPEC.md`; `CLAUDE.md`
  + `AGENTS.md`; the root `README.md` badge + `Version` row; the eleven
  `docs/i18n/*/README.md` badges and `Version` rows (all 11 locales); the
  GitBook `README.md`, `navigation_manifest.json`, and
  `05-specification-and-roadmap.md`; and `docs/codebase_map.json`.
- **Adding a site:** register it once in
  `scripts/version_locations.sh` — both the verifier and the bumper pick
  it up automatically.
- **Not version sites (never auto-bumped):** historical prose such as
  `CHANGELOG.md` headers, "LANDED at vX.Y.Z" / "Version bumped A → B"
  notes, the Lean toolchain version (`4.28.0`), and audit-document
  filenames (`AUDIT_v0.30.6_*`).

## Build and run

```bash
# Environment setup (runs automatically via SessionStart hook — no build)
./scripts/setup_lean_env.sh --skip-test-deps

# Full setup including test dependencies (shellcheck, ripgrep)
./scripts/setup_lean_env.sh

# Manual build (run separately after setup)
source ~/.elan/env && lake build

# Run executable trace harness
lake exe sele4n
```

## Validation commands (tiered)

```bash
./scripts/test_fast.sh      # Tier 0+1: hygiene + build
./scripts/test_smoke.sh     # Tier 0-2: + trace + negative-state
./scripts/test_full.sh      # Tier 0-3: + invariant surface anchors
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # Tier 0-4

./scripts/test_rust.sh                 # host Rust: build, tests, fmt, clippy
./scripts/test_aarch64_cross_build.sh  # the kernel's real target
```

Run at least `test_smoke.sh` before any PR. Run `test_full.sh` when changing
theorems, invariants, or documentation anchors.

**A tier stops at its first failing check.**  `run_check` calls
`finalize_report` unless `--continue` is passed, so one run names *one* broken
gate and a green run after a fix says nothing about the checks that never ran.
Pass `--continue` to any tier script to collect every failure in one pass:

```bash
./scripts/test_tier3_invariant_surface.sh --continue   # every broken anchor, once
```

That matters most after a **refactor**: moving a definition silently breaks every
Tier 3 anchor scoped to it, and Tier 3 runs last.  Before running it, sweep the
anchors over every file the cut touched —
`rg -n '^run_(check|negative_check|prose_check|prose_negative_check) ' scripts/test_tier3_invariant_surface.sh`
filtered to those paths — and execute each one directly; that is seconds against
tens of minutes per iteration.  This is the *sweep what was pinning the thing you
deleted* rule with a mechanism: `v0.35.116` moved a table parse between two
functions and three anchors over the old home went silent, of which the run
reported one.

**Run `test_aarch64_cross_build.sh` after any change under `rust/`.** The
tier scripts and `test_rust.sh` both compile the *host* target, where every
`#[cfg(target_arch = "aarch64")]` block is removed before rustc or clippy
sees it — so the hardware half of the HAL, which is most of it, is invisible
to them.  The cross gate builds `sele4n-hal` for `aarch64-unknown-none` in
both profiles, verifies `boot.S` / `vectors.S` / `trap.S` actually assembled,
and lints the cross target with `-D warnings`.  It runs in CI as the
`aarch64 Cross Build` job.  A `cargo check` is **not** a substitute: it stops
before code generation, so it never hands an `asm!` template to an assembler
— the four `TLBI *OS` encoding defects WS-RR RR1 found were all `check`-clean.

## Module build verification (mandatory)

**Before committing any `.lean` file**, you MUST verify that the specific
module compiles:

```bash
source ~/.elan/env && lake build <Module.Path>
```

For example, after editing `SeLe4n/Kernel/RobinHood/Bridge.lean`:

```bash
lake build SeLe4n.Kernel.RobinHood.Bridge
```

**`lake build` (default target) is NOT sufficient.** The default target only
builds modules reachable from `Main.lean` and the test executables. Modules
not yet imported by the main kernel will silently pass `lake build` even
with broken proofs.

A pre-commit hook enforces this automatically. Install with
`./scripts/install_git_hooks.sh` (invoked automatically by
`setup_lean_env.sh` and by the Lean Action CI workflow, so fresh clones
and CI checkouts are guarded without manual action). For CI contexts:

```bash
./scripts/install_git_hooks.sh          # install (idempotent no-op if present)
./scripts/install_git_hooks.sh --check  # verify installation (non-zero if absent)
./scripts/install_git_hooks.sh --force  # overwrite; backs up any diverging hook
```

The hook detects staged `.lean` files, builds each modified module, checks
for `sorry` in staged content, and **blocks the commit** if any build fails
or sorry is found. Do NOT bypass it with `--no-verify`.  It also runs the
identifier-naming gate (`scripts/check_identifier_naming.py`) whenever a
non-documentation file is staged (PR #887 review round 3): that gate reads
the **git index**, so a Tier 0 run on unstaged edits checks the *previous*
content and passes while the commit fails in CI — which is how one review
round shipped a workstream token in a Tier 3 anchor.  Stage first, then run
`test_tier0_hygiene.sh`; the hook is the backstop.

## Source layout

Top-level subsystems (the filesystem is the authoritative file list — it
changes more often than this map can track):

```
SeLe4n/PackedString.lean         Packed strings: one Nat per inventory string, kernel-cheap distinctness
SeLe4n/Prelude.lean              Typed identifiers, monad foundations
SeLe4n/Machine.lean              Machine state primitives
SeLe4n/Model/                    Object types, kernel/system state, builder, freeze
SeLe4n/Kernel/Scheduler/         Scheduler transitions, run queues, EDF, PIP, liveness
SeLe4n/Kernel/Capability/        CSpace/capability ops + invariants
SeLe4n/Kernel/IPC/               Endpoint/notification IPC, dual-queue, capability transfer
SeLe4n/Kernel/Lifecycle/         Thread suspend/resume, retype, cleanup
SeLe4n/Kernel/Service/           Service orchestration + policy
SeLe4n/Kernel/Architecture/      ARM64 page tables, exceptions, interrupts, TLB/cache,
                                 register/syscall decode, IPC buffer validation
SeLe4n/Kernel/InformationFlow/   Security labels, projection, non-interference
SeLe4n/Kernel/RobinHood/         Verified Robin Hood hash table
SeLe4n/Kernel/RadixTree/         Verified flat-array CNode radix tree
SeLe4n/Kernel/SchedContext/      CBS budgets, replenishment queue, MCP authority
SeLe4n/Kernel/FrozenOps/         Frozen-state kernel operations, refined against the live API
SeLe4n/Kernel/Concurrency/       SMP-latent assumption inventory
SeLe4n/Kernel/CrossSubsystem.lean  Cross-subsystem invariants, discharge index marker
SeLe4n/Kernel/API.lean           Public kernel interface + syscall wrappers
SeLe4n/Platform/Contract.lean    PlatformBinding typeclass
SeLe4n/Platform/DeviceTree.lean  FDT parsing
SeLe4n/Platform/FFI.lean         Lean ↔ Rust HAL bridge (`@[extern]` / `@[export]`)
SeLe4n/Platform/Boot.lean        Boot sequence (PlatformConfig → IntermediateState)
SeLe4n/Platform/Sim/             Simulation platform contracts
SeLe4n/Platform/RPi5/            Raspberry Pi 5 (BCM2712) bindings, boot VSpace
SeLe4n/Platform/Staged.lean      Build anchor pulling staged platform modules into CI
SeLe4n/Testing/                  Test harness, state builder, fixtures
Main.lean                        Executable entry point
tests/                           Executable test suites + fixtures
rust/                            ARM64 boot assembly + HAL crates
```

Each subsystem follows the **Operations / Invariant split**: `Operations.lean`
holds the transitions, `Invariant.lean` holds the proofs. Both may be
re-export hubs over per-concern submodules in a sibling directory of the
same name. Re-export hubs are import-only files that preserve backward
compatibility — existing `import` statements keep working unchanged.

## Reading large files

Several files in this repo exceed 500 lines (invariant suites, audit plans,
specs). When reading any file, always use `offset` and `limit` parameters
to read in chunks rather than attempting the whole file at once:

```
Read(file_path, offset=1,   limit=500)   # lines 1-500
Read(file_path, offset=501, limit=500)   # lines 501-1000
```

To find files that need pagination today, run:

```bash
./scripts/find_large_lean_files.sh
```

**Known large files** (read in ≤500-line chunks, threshold ~800 lines):
- `CHANGELOG.md` (~82427 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/DualQueueMembership.lean` (~23845 lines)
- `tests/SmpInformationFlowSuite.lean` (~12507 lines)
- `SeLe4n/Kernel/Concurrency/Locks/RwLock.lean` (~9581 lines)
- `SeLe4n/Kernel/API.lean` (~9221 lines)
- `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` (~8709 lines)
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean` (~8235 lines)
- `docs/spec/SELE4N_SPEC.md` (~7873 lines)
- `SeLe4n/Platform/Boot.lean` (~7278 lines)
- `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean` (~6360 lines)
- `SeLe4n/Model/State.lean` (~6153 lines)
- `SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean` (~5753 lines)
- `tests/SmpIpcSuite.lean` (~5560 lines)
- `SeLe4n/Kernel/IPC/Invariant/DispatchArmPreservation.lean` (~5439 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean` (~5413 lines)
- `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean` (~5402 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~5389 lines)
- `SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuite.lean` (~4850 lines)
- `tests/NegativeStateSuite.lean` (~4770 lines)
- `docs/dev_history/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md` (~4721 lines)
- `SeLe4n/Kernel/CrossSubsystem.lean` (~4450 lines)
- `SeLe4n/Kernel/Concurrency/Locks/QueuedRwLockRefinement.lean` (~4263 lines)
- `SeLe4n/Kernel/InformationFlow/FineLockFlow.lean` (~4226 lines)
- `docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md` (~4130 lines)
- `SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean` (~4117 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` (~3843 lines)
- `SeLe4n/Kernel/IPC/Invariant/QueueSplicePreservation.lean` (~3811 lines)
- `SeLe4n/Kernel/InformationFlow/AuditRead.lean` (~3789 lines)
- `SeLe4n/Platform/FFI.lean` (~3667 lines)
- `SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean` (~3517 lines)
- `SeLe4n/Testing/MainTraceHarness.lean` (~3477 lines)
- `docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md` (~3389 lines)
- `tests/SmpTlbShootdownSuite.lean` (~3354 lines)
- `SeLe4n/Kernel/Lifecycle/Invariant/CancellationReplyShape.lean` (~3328 lines)
- `tests/OperationChainSuite.lean` (~3320 lines)
- `SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean` (~3281 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean` (~3275 lines)
- `SeLe4n/Model/Object/Structures.lean` (~3260 lines)
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` (~3249 lines)
- `SeLe4n/Kernel/IPC/Invariant/DispatchPayoff.lean` (~3188 lines)
- `tests/FrozenOpsSuite.lean` (~3180 lines)
- `docs/dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md` (~3140 lines)
- `docs/dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md` (~3134 lines)
- `SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean` (~3087 lines)
- `SeLe4n/Model/Object/Types.lean` (~3021 lines)
- `tests/SmpCancellationSuite.lean` (~2988 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointCallInvariant.lean` (~2934 lines)
- `SeLe4n/Kernel/Capability/Operations.lean` (~2909 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/StoreObjectFrame.lean` (~2833 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Core.lean` (~2820 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/PerOperation.lean` (~2778 lines)
- `SeLe4n/Kernel/SyscallSchedFootprint.lean` (~2749 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointCall.lean` (~2714 lines)
- `SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean` (~2639 lines)
- `SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean` (~2637 lines)
- `docs/planning/HIERARCHICAL_CBS_PLAN.md` (~2606 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreChooseThread.lean` (~2604 lines)
- `SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean` (~2602 lines)
- `SeLe4n/Kernel/Architecture/TlbShootdown.lean` (~2562 lines)
- `SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean` (~2512 lines)
- `SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean` (~2505 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/QueueNextTransport.lean` (~2504 lines)
- `SeLe4n/Kernel/InformationFlow/TaintPropagation.lean` (~2484 lines)
- `docs/dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md` (~2476 lines)
- `docs/dev_history/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md` (~2472 lines)
- `tests/ModelIntegritySuite.lean` (~2456 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` (~2360 lines)
- `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` (~2356 lines)
- `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean` (~2352 lines)
- `docs/dev_history/audits/AUDIT_v0.25.14_WORKSTREAM_PLAN.md` (~2340 lines)
- `docs/dev_history/audits/AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md` (~2339 lines)
- `docs/audits/AUDIT_v0.30.11_DEEP_VERIFICATION.md` (~2325 lines)
- `tests/Ak9PlatformSuite.lean` (~2320 lines)
- `SeLe4n/Kernel/IPC/Invariant/QueueNextBlocking.lean` (~2290 lines)
- `SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean` (~2281 lines)
- `SeLe4n/Kernel/Lifecycle/Invariant/CancellationQueueShape.lean` (~2207 lines)
- `SeLe4n/Prelude.lean` (~2201 lines)
- `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean` (~2176 lines)
- `SeLe4n/Kernel/IPC/Invariant/QueueMembership.lean` (~2115 lines)
- `tests/SyscallDispatchSuite.lean` (~2112 lines)
- `SeLe4n/Kernel/Lifecycle/Suspend.lean` (~2086 lines)
- `SeLe4n/Kernel/InformationFlow/Policy.lean` (~2066 lines)
- `SeLe4n/Kernel/Architecture/Invariant.lean` (~2057 lines)
- `SeLe4n/Platform/DeviceTree.lean` (~2042 lines)
- `SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean` (~2031 lines)
- `SeLe4n/Kernel/Scheduler/PriorityInheritance/PerCore.lean` (~2031 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreWake.lean` (~2023 lines)
- `docs/planning/UNFINISHED_SMP_WORK.md` (~2018 lines)
- `SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean` (~2004 lines)
- `SeLe4n/Kernel/FrozenOps/Operations.lean` (~1996 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyInvariant.lean` (~1979 lines)
- `docs/dev_history/planning/V3_PROOF_CHAIN_HARDENING_E_G6_PLAN.md` (~1966 lines)
- `SeLe4n/Kernel/IPC/DualQueue/Core.lean` (~1962 lines)
- `tests/LockSetSuite.lean` (~1960 lines)
- `docs/dev_history/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md` (~1917 lines)
- `SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean` (~1909 lines)
- `tests/InformationFlowSuite.lean` (~1903 lines)
- `SeLe4n/Kernel/Concurrency/Locks/TicketLock.lean` (~1901 lines)
- `docs/dev_history/planning/V3E_IPC_UNWRAP_CAPS_LOOP_COMPOSITION_PLAN.md` (~1891 lines)
- `docs/dev_history/audits/AUDIT_v0.30.6_COMPREHENSIVE.md` (~1889 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreCbs.lean` (~1884 lines)
- `SeLe4n/Kernel/Concurrency/Locks/Serializability.lean` (~1878 lines)
- `tests/FaultHandlingSuite.lean` (~1839 lines)
- `SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean` (~1834 lines)
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` (~1832 lines)
- `SeLe4n/Model/FreezeProofs.lean` (~1819 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` (~1815 lines)
- `docs/dev_history/audits/AUDIT_v0.27.6_WORKSTREAM_PLAN.md` (~1801 lines)
- `docs/dev_history/audits/AUDIT_v0.25.21_WORKSTREAM_PLAN.md` (~1800 lines)
- `docs/dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md` (~1776 lines)
- `SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean` (~1748 lines)
- `docs/dev_history/audits/AUDIT_v0.25.14_COMPREHENSIVE.md` (~1739 lines)
- `docs/dev_history/audits/WORKSTREAM_PLAN_WS_O_SYSCALL_RUST_WRAPPERS.md` (~1725 lines)
- `SeLe4n/Kernel/Concurrency/Locks/RwLockRefinement.lean` (~1702 lines)
- `SeLe4n/Kernel/Architecture/SyscallReturn.lean` (~1695 lines)
- `docs/dev_history/AUDIT_v0.22.10_WORKSTREAM_PLAN.md` (~1674 lines)
- `SeLe4n/Kernel/FrozenOps/Core.lean` (~1656 lines)
- `tests/SmpCrossCoreCallSuite.lean` (~1632 lines)
- `tests/PriorityManagementSuite.lean` (~1605 lines)
- `tests/SmpSurfaceAnchors.lean` (~1600 lines)
- `SeLe4n/Kernel/IPC/Invariant/LookupCongruence.lean` (~1593 lines)
- `SeLe4n/Testing/KernelTransitionReachabilityCensus.lean` (~1537 lines)
- `docs/planning/SMP_RELEASE_READINESS_PLAN.md` (~1521 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatch.lean` (~1511 lines)
- `docs/dev_history/audits/AUDIT_v0.28.0_WORKSTREAM_PLAN.md` (~1480 lines)
- `docs/dev_history/planning/V3B_LOAD_FACTOR_BOUNDED_MIGRATION_PLAN.md` (~1457 lines)
- `docs/dev_history/audits/AUDIT_v0.25.3_WORKSTREAM_PLAN.md` (~1452 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean` (~1441 lines)
- `tests/SmpFoundationsSuite.lean` (~1419 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreSwitchToThread.lean` (~1417 lines)
- `docs/dev_history/audits/WS_RC_R5_DEFERRED_COMPLETION_PLAN.md` (~1414 lines)
- `docs/dev_history/AUDIT_v0.23.21_WORKSTREAM_PLAN.md` (~1411 lines)
- `SeLe4n/Kernel/Scheduler/Invariant.lean` (~1409 lines)
- `SeLe4n/Kernel/Concurrency/Locks/LockSetForSyscall.lean` (~1396 lines)
- `docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md` (~1392 lines)
- `SeLe4n/Kernel/IPC/Operations/Donation.lean` (~1388 lines)
- `SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean` (~1385 lines)
- `docs/dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md` (~1382 lines)
- `docs/planning/SMP_DECLASSIFICATION_COMPLETION_PLAN.md` (~1370 lines)
- `docs/planning/DONATION_POP_TRIGGER_PLAN.md` (~1366 lines)
- `docs/dev_history/audits/AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md` (~1357 lines)
- `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean` (~1348 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointCallDispatch.lean` (~1345 lines)
- `docs/dev_history/audits/AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md` (~1342 lines)
- `SeLe4n/Kernel/Concurrency/Locks/DynamicChainExtension.lean` (~1313 lines)
- `tests/SmpCbsSuite.lean` (~1307 lines)
- `SeLe4n/Kernel/Concurrency/Locks/WithLockSet.lean` (~1272 lines)
- `SeLe4n/Kernel/InformationFlow/Taint.lean` (~1261 lines)
- `docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md` (~1261 lines)
- `SeLe4n/Kernel/InformationFlow/Projection.lean` (~1255 lines)
- `docs/dev_history/audits/AUDIT_v0.22.17_WORKSTREAM_PLAN.md` (~1252 lines)
- `SeLe4n/Kernel/RobinHood/Bridge.lean` (~1251 lines)
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean` (~1242 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreDomain.lean` (~1241 lines)
- `SeLe4n/Testing/ReplyStackWriteCensus.lean` (~1240 lines)
- `SeLe4n/Kernel/SchedContext/Operations.lean` (~1210 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatchInvariant.lean` (~1207 lines)
- `SeLe4n/Kernel/Scheduler/Invariant/PerCorePreservation.lean` (~1200 lines)
- `tests/SyscallReturnAbiSuite.lean` (~1185 lines)
- `tests/SmpCacheMaintenanceSuite.lean` (~1184 lines)
- `docs/dev_history/audits/AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md` (~1178 lines)
- `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean` (~1168 lines)
- `SeLe4n/Kernel/Scheduler/RunQueue.lean` (~1168 lines)
- `SeLe4n/Kernel/IPC/CrossCore/NotificationSignal.lean` (~1165 lines)
- `SeLe4n/Kernel/Lifecycle/Invariant/RetypeReservation.lean` (~1161 lines)
- `SeLe4n/Platform/RPi5/MmioAdapter.lean` (~1154 lines)
- `tests/KernelErrorMatrixSuite.lean` (~1154 lines)
- `SeLe4n/Machine.lean` (~1144 lines)
- `SeLe4n/Kernel/Architecture/VSpace.lean` (~1142 lines)
- `SeLe4n/Kernel/IPC/CrossCore/Fault.lean` (~1132 lines)
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean` (~1126 lines)
- `SeLe4n/Model/FrozenState.lean` (~1121 lines)
- `SeLe4n/Kernel/IPC/Invariant/BlockedSenderPreservation.lean` (~1120 lines)
- `tests/SmpIdleSuite.lean` (~1118 lines)
- `tests/PerObjectLockSuite.lean` (~1104 lines)
- `SeLe4n/Kernel/IPC/CrossCore/CancellationNI.lean` (~1099 lines)
- `SeLe4n/Kernel/Concurrency/Locks/LockSet.lean` (~1084 lines)
- `docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md` (~1071 lines)
- `SeLe4n/Kernel/IPC/Invariant/CancellationBundle.lean` (~1068 lines)
- `SeLe4n/Kernel/Concurrency/Locks/LockSetHeld.lean` (~1063 lines)
- `SeLe4n/Kernel/IPC/Operations/CapTransfer.lean` (~1044 lines)
- `SeLe4n/Kernel/Lifecycle/Invariant/CancellationNotificationShape.lean` (~1043 lines)
- `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean` (~1043 lines)
- `SeLe4n/Kernel/Lifecycle/Operations/Cleanup.lean` (~1041 lines)
- `SeLe4n/Kernel/SyscallDispatchEntry.lean` (~1022 lines)
- `tests/DeadlockFreedomSuite.lean` (~1008 lines)
- `SeLe4n/Kernel/Concurrency/Runtime.lean` (~1000 lines)
- `docs/dev_history/audits/AUDIT_v0.19.6_WORKSTREAM_PLAN.md` (~984 lines)
- `SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean` (~973 lines)
- `docs/planning/SMP_PER_CORE_STATE_PLAN.md` (~968 lines)
- `SeLe4n/Kernel/IPC/Operations/Donation/Primitives.lean` (~964 lines)
- `SeLe4n/Kernel/IPC/Operations/SchedulerLemmas.lean` (~960 lines)
- `docs/dev_history/planning/WS_X_LEAN_ETHEREUM_FORMALIZATION_PLAN.md` (~958 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreTickCbsPreservation.lean` (~947 lines)
- `tests/SmpCrossCoreNotificationSuite.lean` (~937 lines)
- `SeLe4n/Kernel/Concurrency/MemoryModel.lean` (~935 lines)
- `SeLe4n/Kernel/InformationFlow/Declassification.lean` (~935 lines)
- `docs/planning/SMP_TLB_SHOOTDOWN_PLAN.md` (~934 lines)
- `tests/SmpTimerSuite.lean` (~934 lines)
- `docs/DEVELOPMENT.md` (~931 lines)
- `docs/dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md` (~930 lines)
- `SeLe4n/Kernel/IPC/Operations/Fault.lean` (~923 lines)
- `docs/dev_history/audits/AUDIT_v0.28.0_COMPREHENSIVE.md` (~921 lines)
- `docs/dev_history/audits/AUDIT_H3_HARDWARE_BINDING_v0.25.27.md` (~911 lines)
- `tests/SuspendResumeSuite.lean` (~910 lines)
- `docs/dev_history/audits/AUDIT_v0.25.10_WORKSTREAM_PLAN.md` (~909 lines)
- `docs/planning/SMP_RELEASE_CLOSURE_PLAN.md` (~908 lines)
- `tests/TwoPhaseArchSuite.lean` (~901 lines)
- `SeLe4n/Kernel/Concurrency/Locks/LockSet2PL.lean` (~897 lines)
- `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/Signal.lean` (~891 lines)
- `docs/dev_history/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md` (~884 lines)
- `docs/planning/SYSCALL_RETURN_ABI_PLAN.md` (~880 lines)
- `SeLe4n/Testing/InvariantChecks.lean` (~879 lines)
- `SeLe4n/Kernel/SchedContext/BindingAffinity.lean` (~868 lines)
- `docs/planning/SMP_RUST_HAL_PLAN.md` (~868 lines)
- `tests/An10CascadeSuite.lean` (~866 lines)
- `SeLe4n/Kernel/Capability/Invariant/Authority.lean` (~861 lines)
- `docs/REGISTERED_DEBT.md` (~861 lines)
- `docs/dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md` (~859 lines)
- `docs/planning/SMP_FINE_LOCK_MIGRATION_PLAN.md` (~841 lines)
- `docs/gitbook/12-proof-and-invariant-map.md` (~840 lines)
- `tests/DecodingSuite.lean` (~835 lines)
- `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` (~825 lines)
- `SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean` (~824 lines)
- `tests/WithLockSetSuite.lean` (~820 lines)
- `docs/dev_history/audits/WS_RC_R4_CLOSEOUT_PLAN.md` (~818 lines)
- `SeLe4n/Kernel/IPC/Invariant/QueueNoDup.lean` (~812 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreWcrt.lean` (~812 lines)
- `SeLe4n/Kernel/InformationFlow/AuditRecord.lean` (~811 lines)
- `docs/dev_history/AUDIT_v0.21.7_WORKSTREAM_PLAN.md` (~808 lines)
- `docs/dev_history/audits/AUDIT_CODEBASE_v0.11.6.md` (~806 lines)
This bullet block is a **curated snapshot**, not a static enumeration.
`scripts/find_large_lean_files.sh --check` (called from
`scripts/sync_documentation_metrics.sh`) compares it against the live
tree and emits a warning when drift is detected. To refresh after a
substantial source-tree change, run
`./scripts/find_large_lean_files.sh --format bullets` and replace the
bullets above. The literal `**Known large files**` header anchors the
script's awk-based extraction — do not rename or rewrap it.

When editing large files, read the specific region around the target
lines first (e.g. `offset=380, limit=40`) rather than the whole file.
This avoids context-window pressure and "file too large" errors.
## Writing and editing large files

The Write tool replaces an entire file in one call. For files over ~100
lines this is error-prone: the call **times out**, content gets silently
truncated, sections are accidentally dropped, and the context window
fills up. **Prefer the Edit tool for all changes to existing files**,
regardless of size.

**Hard rules:**

- **Never pass more than 100 lines of content in a single Write call.**
  Files at or above this threshold must be built incrementally
  (skeleton + Edit appends) or written via Bash `cat <<'EOF'` heredoc.
- **For existing files, never use Write at all.** Always use Edit with
  targeted `old_string`/`new_string` pairs. Edit calls do not carry the
  full file content and therefore do not time out.
- **One logical change per Edit call.** Three function changes → three
  Edit calls, not one whole-file replacement.
- **Read before you edit.** Always Read the specific region first
  (e.g. `offset=350, limit=50`) so the `old_string` matches exactly,
  including indentation and whitespace.
- **Adding large new sections.** Break inserts >80 lines into multiple
  sequential Edit calls, each anchored to context already present in
  the file.
- **Creating new large files.** Either build incrementally (small Write
  skeleton → successive Edit appends ≤80 lines each, ending with
  `wc -l` verification) or use Bash heredoc
  (`cat <<'EOF' > path/file.lean ... EOF`) to write the file in one
  shot — Bash has no content-size timeout.
- **Post-write verification.** After any large write or series of edits,
  spot-check by reading the modified region (and the file's last few
  lines) to confirm nothing was truncated or duplicated.

**Example — appending a theorem block to an invariant file:**

```
# Step 1: Read the anchor region at the end of the file
Read("SeLe4n/Kernel/Capability/Invariant.lean", offset=880, limit=20)

# Step 2: Edit using the last lines as old_string, appending new content
Edit(file_path="SeLe4n/Kernel/Capability/Invariant.lean",
     old_string="<last 2-3 lines of file>",
     new_string="<those same lines>\n<new theorem block>")

# Step 3: Verify
Bash("wc -l SeLe4n/Kernel/Capability/Invariant.lean")
```

### Build-fragile pattern: deep `do`-chain nesting in test suites

Lean test suites with hundreds of sequential `expectErr` / `expectOkSt`
calls inside a single `do`-block compile to deeply nested C `if`-trees
that can exceed clang's default `-fbracket-depth=256`. Symptom:
`lake build <suite>:exe` fails with `fatal error: bracket nesting level
exceeded maximum of 256`, even though `lake env lean --run <suite>.lean`
(the interpretation path) works fine.

**Mitigation**: keep test helper functions ≤ ~150 Lean lines and use the
thin-dispatcher pattern. `tests/NegativeStateSuite.lean`'s
`runNegativeChecks` is the canonical example: a 13-line dispatcher
calling 8 per-area sub-helpers. C-scope nesting depth resets at each
function boundary in the codegen, so each sub-helper stays well below
the limit. Factor large `do`-blocks into per-area `private def`s up
front rather than waiting for the build to break.

## Handling large search and command output

Search and command output can saturate context if unbounded. Constrain
upfront:

- **Grep**: Use `head_limit` (e.g. `head_limit=30`); paginate with
  `offset`. Prefer `output_mode: "files_with_matches"` first to identify
  relevant files, then switch to `output_mode: "content"` on specific
  files.
- **Glob**: Narrow with `path` instead of searching the whole repo.
- **Bash**: Pipe through `head` or `tail`
  (e.g. `lake build 2>&1 | tail -80`). For very large output, redirect
  to a temp file: `lake build 2>&1 > /tmp/build.log` then
  `Read("/tmp/build.log", offset=1, limit=500)`.

**Rule of thumb**: if a command or search might return more than ~100
lines, limit it upfront. Paginate rather than requesting everything at
once.

## Background agent file-change protection

Background agents (launched via the Agent tool with
`run_in_background: true`) run concurrently and may finish after the
foreground agent has already modified the same files. Their stale writes
will silently overwrite the foreground agent's progress. **You must
prevent this.**

**Rules:**

1. **Never delegate file writes to a background agent for files you may
   also edit.** If there is any chance the foreground agent will touch
   the same file, run the agent in the foreground or restructure the
   work so there is no file overlap.
2. **Partition files strictly** when parallel work is genuinely needed.
   Spell the partition out in the agent's prompt (e.g. "You own
   `Foo.lean` and `Bar.lean` only — do not modify any other file"), and
   do not touch those files yourself until the agent completes.
3. **Use background agents only for read-only or independent-file
   tasks**: running builds/tests, searching the codebase, or writing
   files the foreground will never touch. Unsafe uses include editing
   shared source files or modifying configuration.
4. **Check background results before acting on shared state.** If the
   agent wrote to a file you have since modified, discard its version
   and redo that work on top of your current file state.
5. **When in doubt, run in foreground.** The performance benefit is
   never worth silently lost work.

**Safe pattern:**

```
# Background agent runs tests (read-only, no file writes)
Agent(subagent_type="general-purpose", run_in_background=true,
      prompt="Run ./scripts/test_smoke.sh and report results")

# Meanwhile, foreground edits Operations.lean — no conflict
Edit("SeLe4n/Kernel/Scheduler/Operations.lean", ...)
```

**Unsafe pattern to avoid:**

```
# WRONG: background agent will edit Invariant.lean
Agent(subagent_type="general-purpose", run_in_background=true,
      prompt="Add theorem X to Invariant.lean")

# Foreground also edits Invariant.lean — background will overwrite!
Edit("SeLe4n/Kernel/Scheduler/Invariant.lean", ...)
```

## Key conventions

- **Gates read code, prose reads prose.** No comment or docstring may
  decide whether a check passes. Every source-scanning gate matches
  against the *code view* — `scripts/lean_code_view.py --overlay`, a
  whole-repo overlay whose `.lean` files are comment-free and
  byte-aligned with the originals — so a docstring can neither satisfy
  an anchor (a symbol that survives only in a comment after its
  definition is deleted) nor trip one (a negative anchor firing on the
  sentence that explains what it forbids), and the AK7 counters measure
  code rather than the text discussing it. This is wired at the helper,
  not at the call site: `run_check` / `run_negative_check` route through
  the view automatically, because requiring an opt-in would mean the
  obvious way to write a new anchor is the wrong one. When a check's
  subject genuinely *is* the text — a module docstring must exist, a
  contract sentence must be present, a retracted figure must not come
  back — declare it with **`run_prose_check`** / **`run_prose_negative_check`**,
  which read the real tree. Both mechanisms are pinned by witnesses in
  Tier 0 (`lean_code_view.py --self-test` for the stripper,
  `test_code_view_wiring.sh` for the routing), since a stripper that
  stops stripping and a helper that stops routing both fail silently.
  Never contort prose to satisfy a scanner — if a comment cannot say
  something plainly, the scanner is reading the wrong text.
  *Known duplication, tracked*: `generate_codebase_map.py` and
  `check_identifier_naming.py` each carry their own Lean comment
  stripper and were already doing the right thing — which is why the
  anchors and AK7 counters reading raw text was an oversight rather
  than a design choice. Three strippers is two too many; consolidating
  them onto `lean_code_view.strip` is a follow-up, deliberately not
  done in the same cut as the mechanism they would depend on.
  **The view is per-language, and a language absent from it is read
  raw** (WS-RR RR7.17). `test_lib.sh`'s classifier routes *every*
  `rg`/`grep` anchor through the overlay, not only the Lean ones, but
  the overlay linked `.rs` files whole — so 215 Tier-3 anchors over
  Rust matched comments, and "gates read code, prose reads prose" held
  for Lean only. It surfaced the way this class always does: the first
  negative written against a Rust construct was satisfied by the
  comment explaining what it forbids, and the project's own rule
  forbids the obvious escape (*never contort prose to satisfy a
  scanner*). The overlay's `_STRIPPERS` table now maps `.lean` to
  `lean_code_view.strip` and `.rs` to `rust_code_view.code` — the same
  view the Python gates read, so the tree has one Rust view rather than
  two that can disagree — and a suffix absent from the table is linked
  whole, which is a *decision* rather than a default: adding a language
  whose files gates scan means adding its stripper. The witness suite
  `test_code_view_wiring.sh` covers both languages on all three
  directions (a comment cannot satisfy a code anchor; a prose check
  still reads the real text; code anchors still match code), in both
  Rust comment forms, because a Lean-only witness is exactly what let
  the Rust hole stay open while the script reported PASS.
- **A presence check is not a relation check.**  Nearly every gate here
  is a text scanner, and the recurring way one fails is that it asserts a
  *token is present* when the property it means is a *relation*: that the
  flag reaches **this command**, that the guard precedes **this
  instruction**, that the artefact came from **this run**, that the
  reference is **this occurrence**.  Presence is necessary and almost
  never sufficient, and the gap is invisible because the token really is
  there.  **Seventeen instances** shipped across three review rounds of one
  cut (WS-RR RR1, `v0.34.41`), and the count is the point: each
  round fixed the instances it was shown and the next round found more, in
  the code written to fix the last.  Round 1 (`v0.34.41`): a workflow step
  *name* satisfying a check for an installed target; a two-profile script
  satisfying a `cargo build` check after one profile became a `check`;
  `CROSS_TARGET=`/`CROSS_FEATURES=` assignments satisfying flag checks
  while the builds passed something else; a stale archive satisfying "the
  sources assembled"; `body.contains(guard)` passing with the guard moved
  *below* the instruction it protects; a call-syntax regex missing
  `use … as alias`; a whole-file exemption set from a docstring — that one
  in the gate written to enforce *gates read code, prose reads prose*; and
  two self-inflicted, inside the fixes for the others (a shell expander
  taking the *first* assignment, so a re-assigned setting read at a value
  the command never receives; a divergence check testing for `fatal_halt()`
  **file-wide**).  Round 3 found eight more, six of them
  reported and two found while fixing those: a host `--release` build
  satisfying "the *cross* build is done in both profiles"; `cargo test
  --doc … --features host_tools` satisfying "the host lane tests with
  `host_tools`" while running none of the tests the feature gates; `run:
  echo ./script.sh` satisfying "a job runs the gate"; a nested
  `if has_feat_tlbios() { fatal_halt(); }` satisfying the
  *branch*-scoped divergence check written in round 2; a module-scope
  `static` inheriting the allowlist entry of the function textually above
  it; a `//` inside an `asm!` template deleting the emitted instruction
  from the view; a string literal `"require_feat_tlbios()"` standing in for
  the call that keeps an UNDEFINED instruction off a Cortex-A76; and a
  file-wide directive count read from a view that had blanked the templates
  holding them.

  What the third round changed is the response.  Patching instances was not
  converging, because every one of them substituted an *ad-hoc slice of
  text* for a question about a *program*, and the ways text can diverge
  from structure are unbounded.  So the slices were replaced by shared
  structural views: `scripts/rust_code_view.py` (comments blanked, with
  string contents kept or blanked as the question requires, brace-matched
  `fn` bodies, byte-aligned) for the Python-side gates, its counterpart
  `rust_code_views` in `rust/sele4n-hal/build.rs`, and a `shell_commands` /
  `argv_of` / `option_values` layer so a flag is read on a **command**
  rather than on a line — and, since PR #889 review round 2, a Lean view in
  `build.rs` (`lean_code_view`) so the export inventory that drives the
  readiness gate is derived from code rather than from the docstrings that
  cite retired seams, and a recursive shell view in
  `check_identifier_naming.py` so a `$( … )` body is lexed rather than copied — and, since the RR7 audit round, a here-document body is lexed as a document of its own, so an apostrophe in a fixture line cannot carry quote state past its terminator.  The rule is unchanged and now has a mechanism:
  **resolve the text into the structure it stands for before asserting** —
  expand the script's variables and check the command, take byte offsets
  and check the order, parse the array and check the element, lex the
  source and check the scope.  Where a scanner genuinely cannot
  (reachability, aliasing through a value), say so in its docstring and
  make it over-approximate, so it fails **closed**.
- **Test a gate by breaking the relation, not by deleting the token.**
  The corollary, and the reason every instance above passed its own
  self-test: the fixtures mutated by *removal*, which any presence check
  survives.  The mutation that finds this class **keeps the token and
  breaks the relation** — leave `hw_target` in the file but build another
  target; keep `--release` but put it on a *host* build; keep the guard but
  move it after the `asm!`; keep `fatal_halt()` but nest it under the
  negation of its own branch condition; keep the reference but move it out
  of the function whose allowlist entry covers it.

  **And having built the resolver, sweep every site that asks the same
  question.**  Round 4 of the same review failed differently from the first
  three: the resolvers were right, and each was wired into exactly the call
  site the review had named.  `job_runs_gate` required a command position
  while its neighbour `cargo_invocations` still scanned tokens anywhere, so
  `echo cargo build --target …` passed; `rust_code_view.enclosing_fn` got
  real brace-matched bodies while `enclosing_lean_decl`, four lines below,
  stayed last-declaration-wins, so an `initialize` block inherited the
  preceding `def`'s allowlist entry; the Rust view became quote-aware while
  the `.S` view kept a `//`-only stripper resting on an asserted claim about
  the tree's *content* ("the `.S` sources use `//` exclusively") rather than
  the preprocessor's grammar.  A fix applied at one site and not its
  siblings leaves the class open and reads as closed.

  A related shape, and the one worth looking for unprompted: **an
  enumeration standing in for a derivation**.  A hand-written list of the
  things a gate protects — local TLBI wrappers, `*OS` wrappers, `.S`
  sources, FFI bindings — cannot see the one that does not exist yet, so the
  gate is silent exactly when something new is added.  Derive the set from
  what the code actually does and keep the list as a pin that fails when the
  two diverge.  Three of the four such lists in these gates were found by
  sweeping for the shape after the fourth was reported.

  **And a cardinality is not a set** (WS-OD OD3.5, prompted).  The same
  substitution one dimension down, and the one this file had not written
  because the gate wearing it *reported numbers*, which reads as measurement.
  `scripts/check_store_reader_hygiene_monotonic.sh` held the residual raw
  `match st.objects[…]?` reads at a whole-tree floor per variant — nine
  endpoint reads, fifty-three TCB reads — and its own docstring says what the
  floor means: "a previously hygienized site re-introduced the raw pattern".
  That is a statement about **which** sites, and a total cannot make it: a
  change that hygienizes one raw read in file A and introduces a fresh one in
  file B leaves every number identical, so the gate passed on exactly the
  movement it exists to catch.  Demonstrated on the real tree, not on a
  fixture — `RAW_MATCH_ENDPOINT` and `RAW_MATCH_TOTAL` both unmoved, a raw
  endpoint discriminator newly resident in `Scheduler/RunQueue.lean`.

  The floor is now the per-(file, variant) inventory, which is the shape
  `scripts/identifier_naming_baseline.json` had already reached for the same
  reason and which nothing had swept onto its sibling: **a set of keys alone
  cannot see a second occurrence inside a file that already contains one, and
  a count alone cannot see the first occurrence in a file that did not**, so
  the floor has to be both.  Two corollaries fell out of the same reading.
  The should-*grow* direction had the plain form of the defect — adoption was
  `grep -c "getEndpoint?"`, so `getEndpoint?_eq_some_iff` and every theorem
  named `*_ok_getEndpoint?` counted as a read of the object store (29 of 210),
  and writing a lemma *about* a helper raised the floor for *using* it; it
  counts whole symbols now — and since `v0.35.202` it also excludes a line whose
  leading token is a tactic that **unfolds** the accessor, because
  `unfold SystemState.getCNode? at hStep` takes the accessor *out* of the goal to
  reach the raw store, which is the opposite of the migration the metric is named
  for.  That one was found by the metric *scoring an improvement as a regression*:
  collapsing eight inline re-derivations onto one shared decomposition lowered
  `GETCNODE_ADOPTION` from 147 to 129 and failed a should-grow floor, and 45 of
  its 172 lines turned out to be tactic references to the definition.  **The
  measurement is what makes the scope honest**: it is a floor over *recognised*
  uses, since whether an occurrence reads *through* an accessor is a question
  about elaboration; an unrecognised tactic spelling leaves the figure a little
  high rather than inverting its direction.  And the per-variant scan carried awk state across
  the file list with no `FNR == 1` reset, so a trailing `match … .objects[` at
  the end of one file could pair with a `some (.tcb …)` at the start of the
  next and report a site existing in neither.

  The mutation for this class keeps every total and moves the site — and the
  self-test's harness *asserts* that each rejecting case leaves every scalar
  metric byte-identical, because that assertion is precisely the statement
  that the superseded gate admitted the case.  A live floor also does not
  live in `docs/dev_history/`: this one did, in a directory the project
  reserves for material contributors are told not to read.

  Every check in a self-tested gate needs at least one such case, and
  **that requirement is now enforced rather than asserted**: each case in
  `check_aarch64_cross_target.py` and `check_tlbi_broadcast_discipline.py`
  declares the check it exercises and whether its mutation is `preserving`
  or `deleting`, and the harness fails when any check has no preserving
  case.  Writing the rule in this file did not stop the next round from
  shipping eight more instances; a harness that refuses to pass does.  The
  harness must also reject a mutation that leaves the fixture unchanged,
  since an inert mutation reads as coverage while asserting nothing.  A
  fixture must also be **no thinner than the file it stands for**: a
  `mod`-less, gate-less toy passes checks the real file would fail, which
  is how a missing `re.MULTILINE` and an unanchored `.file()` search both
  survived.

  **And a count over two populations measures neither** (`v0.35.7`, prompted).
  The same substitution again, and the one this file had not written because the
  gate wearing it was *already* an inventory: `RAW_LOOKUP_TID` held raw
  `st.objects[…]` reads at a whole-tree ceiling, and 96.9% of what it counted was
  **specification vocabulary** — 1490 of 1711 lines in `theorem`s, 168 more in
  `Prop`-valued `def`s, `structure` fields and `inductive` arguments — against 53
  lines of executable code.  A proposition about the store has no helper form
  (`getTcb? k = none` holds for an absent key and a wrong-kinded object alike, so
  a frame statement quantified over every key cannot be phrased through a variant
  accessor without weakening it), so the enforced number rose whenever anyone
  wrote an invariant, and it was re-anchored **upward four times in three days**
  (1609 → 1600 → 1678 → 1711).  A ceiling that every cut raises is a ratchet
  running backwards; it reads as measurement because it prints a number.
  Three further defects rode along, each a rule already in this file applied
  everywhere but here: the metric was named `_TID` while **four** types carry
  `.toObjId` (*a name is not the thing*); it was `grep -c`, so two reads on one
  line counted once and a reflow lowered it (*a cardinality is not a set*, one
  level down); and `RAW_LOOKUP_SITE` was keyed by `(file)` while its sibling
  `RAW_SITE` had been refined to `(file, declaration, variant)` for the stated
  reason that a per-file key cannot see a read moving between declarations —
  *when a fix names a relation, grep for every other place that asks it*, unrun.

  **Split the populations, enforce the one that can reach zero, and report the
  other.**  `scripts/lean_store_read_census.py` classifies each read by whether it
  sits in the *body* of a declaration whose result is not a `Prop` — a binder or a
  result type is a proposition whatever the declaration's kind — and emits
  `STORE_READ_CODE` beside `STORE_READ_SPEC` (diagnostic, the treatment
  `RAW_MATCH_UNCLASSIFIED` already had).  The mutation for this class **moves a
  read between the populations while holding their sum fixed**, which is all the
  superseded figure could see: the gate's self-test has that case in both
  directions, the spec→code one rejecting and the code→spec one passing, because
  the second is the migration working.

  **And a floor that reaches zero stops being a floor** (`v0.35.8`).  The split
  was shipped with `STORE_READ_CODE` held to a **ceiling** and a per-key
  inventory — which is the superseded metric's own shape, one population
  narrower, and it carried the superseded metric's own escape: a cut that
  exceeds a ceiling may re-anchor it, which is what happened four times in three
  days.  So the residue was finished rather than registered.  The whole
  executable population is **zero**: `SeLe4n/Kernel` and `SeLe4n/Platform` were
  already there at `v0.35.7`, and the 76 that remained — 65 trace-harness
  bodies, 10 runtime invariant helpers, and one proof case split whose enclosing
  `def` returns a record of proofs — went in this cut, with the golden fixture
  **byte-identical**, which is the measurement that retired the deferral's own
  stated reason (*migrating it risks a fixture churn*).  The last of them came
  out by restating two theorems' hypotheses in the accessor vocabulary rather
  than bridging at the call site, so no `def` body mentions the store at all.
  `STORE_READ_CODE` is now a `ZERO_METRICS` entry beside `SORRY_COUNT` and
  `AXIOM_COUNT`: **regenerating the baseline does not clear it**, only fixing
  the tree does, and the gate says so in its failure epilogue.  Since `v0.35.76`
  `STORE_WRITE_CODE` sits beside it: the same classifier run over the raw
  *write* spellings, with the bodies that write raw by design registered in
  `WRITE_PRIMITIVE_BODIES` and reconciled in both directions — and it was a
  zero floor from its first measurement, the raw-write migration having
  reached the primitives before the census existed.

  **Both zeros are over the DIRECT spellings, and `v0.35.117` is where that stops
  being implied and starts being printed.**  Until then this paragraph said the
  only raw reads left anywhere were the accessor bodies and propositions, and the
  §7's raw-write ledger said the only raw writes were the five primitives and one
  planted witness.  Both were **false**, and the reason is the rule this file
  states one item down (*a helper the scanner cannot see is a spelling that evades
  the metric*) read in the other direction: every pattern here keys on the
  receiver text `.objects`, so a declaration that holds the table through an
  **indirection** is invisible to all of them.  There are two spellings of that
  indirection and they are one question — a binding (`let objs := st.objects`,
  then `objs.insert k v`) and a parameter (`(objs : RHTable ObjId KernelObject)`)
  — and three executable declarations use them: `endpointQueueRemove` (four
  writes, two reads), `spliceOutMidQueueNode` (two and two) and
  `queueNeighbourPatch` (one and one).  Twelve keyed accesses, outside two
  enforced zeros, which is why the raw-write migration
  (`v0.35.64`..`v0.35.78`) passed over all three: *the population a census
  measures is the population its receiver can name.*

  `STORE_INDIRECT_CODE` is the number, `STORE_INDIRECT_SCOPE` the claim, and both
  zeros now print their own `_SCOPE` line saying *recognised spellings only; a
  floor, not a proof of absence*.  Four things new code must respect.  (1) **One
  classifier, both spellings**: `table_receivers` derives the identifiers that
  denote the table — from three binder positions, a signature binder, a lambda
  binder and an unbracketed ascription, all read over the *whole* declaration
  rather than its signature alone, and from a binding of the projection, closed
  **transitively**, so one extra `let` is not a hole — and the access alternation
  is `_TABLE_OPS`', the same one `READ` and `WRITE` are built from, so a newly
  classified operation reaches the direct and indirect censuses by construction.
  The table type itself has one definition (`_TABLE_TYPE`), so a binder and an
  ascription cannot disagree about what a table is.  Flooring one spelling and
  describing the other in prose would have been *a fix applied at one site and not
  its sibling*.  (2) **It is driven through
  `classify`**, via a `collect` hook, because the property is a relation between a
  declaration's signature and its body that no line pattern can express — so the
  declaration boundary, the `Prop` verdict and the region split stay ONE answer
  and a mutation of any of them fails both censuses.  (3) **The unit is the
  access, not the binding**: a binding count cannot see a second `objs.insert`
  added to a declaration that already aliases, which is *a cardinality is not a
  set* one level down and is exactly what the two zeros count.  (4) **It is a
  floor, not a zero, and that is the honest shape**: a `ZERO_METRICS` entry this
  project may not re-anchor would have had to be false on the day it landed.  The
  table's own operations are exempt, **derived** from `_TABLE_SOURCES` — a
  declaration named `RHTable.insert` in the table's own source *is* the primitive,
  so counting it would report the definition of the thing being measured — and
  reconciled both ways so a stale exemption cannot read as coverage.

  **Driving it to zero is registered, with its architecture named rather than
  left to be rediscovered** (`docs/REGISTERED_DEBT.md` table C).  The target is
  not a new primitive: `queueNeighbourPatch` becomes state-level, which is
  `Option.elim` over the `updateTcb` this tree has had since `v0.35.65`, and the
  two aliasing removals then compose it and `rewriteObject` with no table in
  scope.  What that costs is measured rather than estimated — nine theorems stated
  over the *table* in `CleanupPreservation.lean`, twenty-five over
  `spliceOutMidQueueNode` across fifteen files, and the two `_eq_patches` pins
  whose right-hand sides compose at the table level — which is why it is a cut of
  its own and not a rider on the census that found it.

  **And a spelling is not a write either — nor is a regex a classification**
  (PR #897 review, `v0.35.97`).  That zero was true of `objects.insert` and
  `objects.erase` and blind to `objects.set`, which the WRITE pattern named in
  its *qualified* branch and not in its *method* one — so `st.objects.set k v`,
  the frozen surface's ordinary store, walked around an **enforced zero**, and
  thirty-one executable raw writes sat behind it.  That is `v0.35.12`'s finding
  on the other census, one branch down, and patching the branch would have been
  the fourth telling of a rule this file already carries twice.

  So the *question* has one answer: `_TABLE_OPS` classifies every operation of
  either object table `read` / `write` / `sweep` / `other`, and `READ`, `WRITE`
  and `SWEEP` are built from **one alternation** over it, so a widening reaches
  both spellings by construction.  Two reconciliations run in every mode:
  `table_op_violations` derives the operation set from `RHTable`'s and
  `FrozenMap`'s own sources and fails in both directions — *an operation nobody
  classified is one neither pattern ever looks for*, which is precisely how
  `set` escaped — and `branch_symmetry_violations` asserts each kind is
  recognised in the method spelling *and* the qualified one.  The decisive
  self-test case keeps the write and changes only how it is written.

  Two things that widening measured, and both generalise.  **A helper the
  scanner cannot see is a spelling that evades the metric**: the frozen writes
  went onto `frozenWithObjectStored`, a *state*-level primitive, because a
  map-level one would carry its raw `set` on a bare `FrozenMap` parameter, which
  a census keyed on `.objects` is blind to — so a new store primitive takes the
  state, never the table.  And **a transition can wear a primitive's
  exemption**: `frozenUpdatePipBoost` was in `WRITE_PRIMITIVE_BODIES` because it
  spelled its write `st.objects.insert`, the one form the `set`-only branch
  could not see; it writes through `frozenRewriteObject` — the total mirror of
  the live `rewriteObject`, sound because `FrozenMap.insert` *is* `set` with an
  append fallback — and the registry names the primitive alone.  Whole-table
  traversals are now **reported** (`STORE_SWEEP_*`) rather than silently outside
  the population, because a fold is not a keyed access and a number beside the
  two zeros is what stops their silence reading as absence.

  **And the collapse surfaced twelve answers to one question.**  Moving the
  writes behind a primitive broke eleven proofs that each `unfold`ed a composite
  down to `FrozenMap.set` and case-split on it — plus a twelfth,
  `frozenStoreObject_extracts_state`, which said exactly that, `private`, in a
  module **downstream of every asker**: *when a question has one owner and an
  asker that cannot see it, the owner is in the wrong layer.*  The owner is now
  beside the write (`frozenWithObjectStored_ok`, `_only_modifies_objects`,
  `frozenRewriteObject_only_modifies_objects`, `frozenOnlyObjects_rfl` /
  `_trans`) and the duplicate is deleted with a tombstone.  The re-derivations
  were coupled to the wrong thing besides — each closed its leaves by
  `injection` on a literal `{ st with objects := _ }`, so it depended on how many
  branches a body had *and* on every write being spelled inline, which is why
  the migration broke them rather than leaving them redundant.
  `frozen_objects_frame` **searches** the branch for whatever store chain the
  split left in context, so a store added to a frozen operation costs its frame
  proof nothing.

  One mechanical note, because it corrected the author rather than the tree: a
  mutation run first read as showing the registry reconciliation passing a stale
  entry.  It was not stale — `frozenUpdatePipBoost` genuinely still held a raw
  write, in the `insert` spelling the fixing sweep had grepped past.  **The gate
  was right and the sweep was one spelling wide**, which is this cut's own
  finding arriving inside the work to fix it.

  **And the sweep's subject is the SET a cut retires, not the artefact the last
  red gate named.**  Four artefacts watched this one change and each reported
  separately: the de-threading gate (a `macro` is declaration-minting
  machinery), the reply-stack write census (a helper one hop past the frontier),
  and **two** Tier 3 anchors — one on the retired `WRITE` alternation, one on
  the retired `WRITE_PRIMITIVE_BODIES` key.  The fourth is the finding: after
  the third, this file's own *sweep what was pinning the thing you deleted* rule
  was run — and run against the retired **pattern**, which is what the red gate
  had pointed at, so the anchor naming a retired **registry key** stayed
  invisible until Tier 3 reached it.  A cut that deletes a pattern, a helper and
  a registry key has three sweeps to run.  Deriving that set is a mechanism
  `scripts/check_anchor_symbol_liveness.py` already has for Python *symbols* and
  does not have for the string-literal *keys* these registries are indexed by;
  extending it is registered in `docs/REGISTERED_DEBT.md` table C rather than
  restated here, because a rule this file has now stated three times is owed a
  check.

  **And a spelling is not a read** (PR #895 review, `v0.35.12`).  The zero above
  was true of `s.objects[k]?` and blind to `s.objects.get? k`, which is *the same
  read*: the `GetElem?` instance **is** `RHTable.get?`, and this tree proves it
  outright (`objects_getElem?_eq_get?`, by `rfl`).  So the census measured a
  spelling, and an enforced zero a rename walks around is worse than no zero,
  because the number reads like a measurement.  Not theoretical either: forty
  executable reads were hiding in the method form, and one of them —
  `Concurrency.updateObjectAt` — **said so in its own docstring**, *"so the
  AK7-cascade raw-match floor stays at its v0.31.2 baseline"*, which is choosing
  a spelling to evade a metric and is the mirror image of this file's own rule
  against contorting prose to satisfy a scanner.  Its second claim, that no typed
  accessor applied, was false besides: `getObject?` is the kind-agnostic one.
  `READ` reads both spellings now, and the self-test's decisive case keeps the
  read and changes only how it is written.

  Three things new code must respect.  (1) **The frozen surface is in scope, and
  always was.**  `FrozenKernelObject.reply` carries the live
  `SeLe4n.Kernel.Reply` and `Model.freeze` copies a live state's records
  verbatim, so a frozen transition discriminating a variant at the call site is
  the defect this census is named for — it had twenty-nine such reads, now zero,
  routed through a frozen accessor family (`Model/FrozenState.lean`) that mirrors
  the live one and which `FrozenOps.frozenLookup*` is stated over rather than
  beside.  (2) **Where a site distinguishes "wrong kind" from "absent" the typed
  accessor is the wrong tool**: it answers `none` to both, so collapsing the two
  would change an error code.  Those sites read `getObject?` and keep their arms
  — no raw table read, and the distinction that *is* the semantics survives.  (3)
  **The exemption is per declaration, not per file.**  `Model/State.lean` was
  skipped whole, which is a 4800-line module that is not only accessors, so a raw
  read added anywhere in it was invisible; `ACCESSOR_BODIES` names the twenty-one
  bodies that *are* the accessors and the store primitives, and is reconciled in
  both directions in **every** mode — `--rows` included, since that is the mode
  Tier 0 calls — so a stale exemption fails rather than reading like coverage.

  Two mechanical notes, both the *one question, two answers* rule at the point
  where the fix could have introduced it.  The per-key inventory for this metric
  was **deleted**, not kept beside the zero: at zero a cardinality and a set say
  the same thing, and carrying both would be this file's own duplication hazard
  inside the gate written to close it.  What replaced it is the *relation* — the
  gate asserts `STORE_READ_CODE` equals the sum of its own `STORE_READ_CODE_SITE`
  rows, in the baseline and in the current capture, so a hand-edited or truncated
  file claiming "none" beside a live site row is refused as a gate defect rather
  than passed on the strength of the total; the rows are still emitted, because
  when the zero breaks they are what names the offending declaration.  And the
  self-test grew a second case shape, because the two claims are token-preserving
  with respect to different things: the inventory cases hold every scalar fixed
  and the harness asserts it, while the census cases move the scalars and the
  harness asserts the fixture is internally consistent.  Its decisive case keeps
  the baseline and the current value **equal at one** — everything a ceiling
  asks, and exactly what a zero floor must still reject.

  **A region-scoped presence check is still a presence check** (PR #887
  review round 4).  Resolving the guard's block, the tail after a branch, or
  the body after a binding and then asking whether a token occurs inside it
  moves the haystack without changing the question: a divergence nested under
  `if retry { … }`, a halt nested under `if frame.x0() == 0 { … }`, and a
  routing `match` nested under a condition beside a second `match` all keep
  the token and break the relation, and `if lean_ready(c) == false { … }` is
  a condition without `||` that entails the *opposite* of readiness.  Ask the
  question of **statements** — `rust/sele4n-hal/build.rs`'s
  `top_level_statements` is the view: what a block does unconditionally is
  what its top-level statements say, a divergence is the block's *last*
  top-level statement, a routing construct is a top-level statement of the
  body, and a predicate entails readiness only in a structural form
  (`ready_condition_argument`: a conjunct that *is* the call).  The mutation
  for this class nests the token under a condition, or inverts the predicate
  around it.

  **Provenance, sole consumption and location are relations too** (PR #887
  review rounds 6 and 7).  A statement-level view answers "is this
  unconditional"; it does not answer *whose* value a guard reads, whether a
  bound name has a *second* consumer, or *which* of two matching arms is the
  live one — and a scanner that resolves the statement and then takes the
  token's first occurrence, or accepts any argument, is back to presence.
  `lean_ready(0)` on core 1, `let invoke = lean_x;`, a no-op `match`
  followed by an `if` on the same class, a `#[cfg(test)]` decode of tag 2
  beside the live one, and a decoy `Faulted` arm ahead of the real one all
  kept every token round 4 checked.  So: read the guard's **argument** back
  to the executing core through the statements that dominate it, with the
  last binding winning (`ready_argument_is_executing_core`); **count** a
  name's whole-word occurrences when the claim is "nothing else consumes
  it" (`word_occurrences`); and **locate** an arm by walking from the
  function's terminal statement through parsed arms
  (`terminal_routing_match`, `match_arm_spans`) rather than by its first
  textual match.  Round 4 applied the statement view to the three checks the
  review named and left their siblings on text slices; rounds 6 and 7 swept
  the siblings — the sweep rule above, failing in the way it says.  The
  mutation for this class keeps the token and changes its provenance, adds
  a second consumer, or puts a decoy ahead of the live occurrence.

  **A name is not a definition** (PR #889 review round 12).  The last
  relation in this family is the one a scanner performs implicitly every
  time it matches an identifier: that the spelling *denotes* the
  declaration it stands for.  It does not.  `let bootAndInitialiseRPi5 :=
  fun _ => pure (.ok default)` above the call satisfies every
  executed-call and branch-and-halt check written against the callee's
  name; `Fake.ffiFatalHalt` and a local `let ffiFatalHalt : BaseIO Unit
  := pure ()` both satisfy a halt pattern that allows an arbitrary
  qualifier; `@[inline, export lean_kernel_main]` is invisible to a
  `@\[export\s+…\]` regex, so the declaration carrying it is not
  recognised as the boot entry *at all* and its contract passes
  vacuously; and `#[link_name = "actual"] fn local();` names a symbol the
  Rust identifier never mentions.  So **resolve the reference before
  asserting about it**: `resolves_to` applied Lean's own suffix rule
  against fully-qualified names (`lean_qualified_declarations`) — that
  Lean-side machinery was retired at round 17, where the elaborator
  resolves references with no suffix rule to get wrong; the Rust and
  attribute halves below are live — the
  candidate set must contain nothing unapproved, a bare name is refused
  where the declaration binds it locally, the attribute list is parsed
  rather than matched (`lean_code_view.attribute_arguments`, shared with
  `build.rs`'s parser so the two inventories cannot disagree), and an
  `extern` declaration's symbol is its *effective linker name*.  Where
  resolution is beyond a scanner — an alias for a Lean upcall, which no
  gate can attribute to a readiness guard — refuse the alias
  (`lean_link_name_aliases`) rather than read past it.  The mutation for
  this class keeps the name and changes what it denotes: rebind it, put
  it in another namespace, spell the attribute a second legal way.

  **A nested construct is not a sibling** (PR #889 review round 13).  The
  same substitution one level down: a scanner that splits a multi-line
  construct into lines and treats them as peers has thrown away the
  nesting, and nesting is what says which construct a line belongs to.
  Stripping each continuation's indentation let a `match` *inside* an arm
  donate its `| .error _ => halt` to the arm list of the match that
  contains it, so a boot-result match with only a wildcard arm read as
  having a named, halting error handler; and "the arm's last non-empty
  line" is the arm's outcome only until the conditional is written across
  lines, where the halt in an `else` branch is the last line and runs
  only when the condition is false.  **Keep the depth and ask the
  question of the level you mean**: continuations retain their column
  relative to the block, arms are the `|`s at the match's own column, and
  a body's terminal statement is the last line at the body's *minimum*
  column.  The mutation for this class keeps the token at an accepted
  position and moves it one level in or out.

  Round 14 of the same review is that sweep rule failing four times at
  once, and is the clearest evidence for it: `let` was not every binder
  (`have` shadowed the value the boot-result match reads), an exit is not
  always the whole statement (`if skip then return ()` passed a check
  that asked whether the statement *begins* with `return`, while
  `build.rs`'s `statement_may_exit` had asked the right question since
  PR #887), the halt-alias closure resolved by suffix while
  `reference_failure` in the same file required a *unique* candidate
  (both retired at round 17 with the rest of the Lean scan), and
  the recursive shell view lexed `$( … )` while the legacy backtick
  spelling beside it was still copied verbatim.  The RR7 audit round found the third sibling: a here-document body was lexed as the enclosing script's text, so one apostrophe in a Lean fixture inside `check_physical_address_width.sh` inverted the quote state for the rest of the file and every double-quoted diagnostic below it counted as code.  None was a new class;
  each was a rule already written down, applied at one site and not at
  its sibling.  **When a fix names a relation, grep for every other place
  that asks it** — the same file, the other language, the other
  spelling.  Its fifth finding adds the one genuinely new point:
  **the view you read depends on the question, and one walk can need
  both** — a string literal supplied a `{` that a nesting walk read as an
  enclosing block *and* a `#[cfg]` that the verdict read as that block's
  header, because both were taken from the strings-kept view.  Structure
  (braces, attributes, statements) comes from the string-free view; only
  the text a predicate is *about* comes from the aligned kept one.

  **When the enumeration cannot be finished, state a contract instead**
  (PR #889 review round 16).  The four preceding rules all say *resolve
  the text into the structure it stands for* — and rounds 12, 14, 15 and
  16 showed the limit of doing that with regexes over a language you are
  not parsing: each round taught the binder scan one more Lean form
  (`have`, `for`, `let ⟨a, _⟩ :=`, the same pattern across lines) and
  the head-matching call scan one more way to discard what the head
  named (`f x |> fun _ => …`).  The fixes were right and the class
  stayed open, because the set of valid spellings that defeat a regex is
  unbounded while the set a gate has seen is finite.  Where the subject
  is code **this project writes** — and especially where it does not
  exist yet — the exit is to require a canonical spelling and refuse the
  rest: the boot entry names the checked boot and the halt by their
  *fully-qualified* names (Lean's local binders bind single-component
  identifiers, so nothing local can shadow one) and the accepted
  expression is the call *and its arguments*, never a prefix of a larger
  expression; the readiness guard is written `crate::lean_ready::lean_ready(..)`
  and the bare spelling never counts.  A contract on unwritten code
  costs nothing and makes the question decidable; keep parsing only
  where the subject is code you do not control.

  **A Lean question goes to the Lean elaborator, never to a regular
  expression** (PR #889 review round 17, and a standing instruction).  The
  rule above is the last patch this class accepts; the class itself ends
  here.  From PR #889 review round 3 to round 16 the boot-entry check in
  `scripts/check_kernel_entry_exports.py` grew into a Lean parser made of
  regexes, and eleven rounds of findings against it were one defect in
  eleven costumes — a name is not a definition, a nested construct is not
  a sibling, a prefix is not the expression, a constructor's head is not
  its coverage, a `renaming` binds a name no declaration mentions.  Each
  fix was correct and the next round found more, because the set of Lean
  spellings that defeat a regex is unbounded.

  So: **if the property is about elaboration — which declaration a name
  denotes, what an expression evaluates, which values a pattern matches,
  what a body transitively calls — ask the environment.**  A `run_cmd`
  over `Environment` that throws is a gate: `getExportNameFor?` finds an
  `@[export]` whatever its attribute list looks like,
  `Expr.getUsedConstants` returns *constants*, and a constant has one
  definition, so aliasing, shadowing, `renaming`, qualification and
  notation are not questions any more.  Building the module is the check
  (`scripts/test_tier1_build.sh`), and it carries witnesses so it is
  decisive before the code it governs exists.  The tree has three such
  gates: `SeLe4n/Testing/BootEntryContract.lean` (the hardware boot
  entry's contract), `SeLe4n/Testing/IpcDethreadingEnvironmentCensus.lean`,
  and the probe-driven `check_live_arm_per_core_routing.py` /
  `check_content_flow_coverage.py`.

  **And occurrence is not execution** (PR #889 review round 18).  Asking the
  environment answers *which declaration*, not *whether it runs*:
  `Expr.getUsedConstants` reports that a constant occurs in the elaborated
  term, so `if cond then bootAndInitialiseRPi5OrHalt config else pure ()`
  satisfies a used-constants test and boots nothing on the path a real
  configuration takes.  That is this file's oldest rule — a presence check is
  not a relation check — one level below text, and the resolution is the same
  in kind: **walk the structure that cannot branch** and ask the question of
  what it reaches.  `unconditionalActions` follows binders, `let`s, metadata
  and both action arguments of a monadic bind; a conditional or a `match`
  appears there as one action whose head is `ite` / `dite` / a matcher, which
  is not the call being required, so it satisfies nothing.  The mutation for
  this class keeps the call and nests it in a branch.  **And the walk's own
  assumptions are relations too** (PR #889 review round 19): a `Bind.bind`
  application sequences only under a lawful *instance*, which is an argument —
  a `Bind` on a type definitionally equal to `BaseIO Unit` may discard both of
  them, so the instance is compared against the one synthesis finds
  (`isCanonicalBaseIOBind`); and `ConstantInfo.value?` hides an `opaque` body
  by default, so a walk that does not pass `allowOpaque := true` reads
  `opaque overwrite := initialiseKernelState` as a harmless leaf.  Where the
  environment still cannot answer — an `@[extern]` body is foreign — say so in
  the docstring and state why the property survives, rather than assuming it
  away.  The same round's third finding is the *enumeration* rule again, and
  the second instance of it in the same place: `PlatformConfig.wellFormed`'s
  conjuncts and the `else if` chain reporting them were two lists that had to
  agree, and twice a conjunct was added to one and not the other, so a config
  was refused in the words of a fault it did not have.  **A diagnostic belongs
  with the predicate it reports**: `wellFormedConjuncts` pairs each conjunct
  with its message, `wellFormedDiagnostic` reads that list, and
  `wellFormed_eq_all_conjuncts` fails to elaborate if the two ever diverge.  A second relation the
  environment does not volunteer is the **type**: an `@[export]`ed declaration
  links under its C name whatever its Lean type, so a seam's contract states
  the type its `extern` declaration is called at
  (`expectedBootEntryType`, `UInt64 → BaseIO Unit`).  And the environment a
  contract reads is itself a relation — `SeLe4n/Testing/BootEntryContract.lean`
  imports the production root as well as `Platform.Staged`, and pins that with
  `env.header.moduleNames`, because a declaration outside the imported closure
  is indistinguishable from one that does not exist.

  Two corollaries.  **Prefer making the property structural over checking
  it at all**: `Platform.FFI.bootAndInitialiseRPi5OrHalt` is the checked
  boot with its failure handled, so "the entry's `.error` arm ends in a
  halt" — eight review rounds of parsing — became "the entry calls this
  constant", which `getUsedConstants` answers.  And **a lexical scan is
  still right where the question is lexical**: the `@[export]` inventory
  the archive reconciliation reads is deliberately taken from Lean
  *source*, because a module outside the import closure exports nothing
  into the environment and that drift is precisely what it must catch.
  The test is what the property is *about*, not which language the file
  is written in.  Where a Lean scan survives for that reason, say so in
  its docstring; `rust/sele4n-hal/build.rs` keeps one because it cannot
  depend on a Lean build, and it is pinned against the elaborated
  inventory rather than trusted.
  **And a hand-written analysis over `Expr` is not the elaborator** (PR #889
  review round 21, and the correction to round 17).  Round 17's instruction —
  *a Lean question goes to the Lean elaborator, never to a regular expression*
  — was applied to **names** and ended that sub-class outright, because
  `getExportNameFor?` and `getUsedConstants` return constants and a constant
  has one definition.  It was **not** applied to *behaviour*, and nothing in
  the environment answers "what does this program do": rounds 18, 19, 20 and 21
  are four consecutive findings against `unconditionalActions`, a hand-rolled
  abstract interpreter written in round 17 to decide whether an arbitrary
  `BaseIO` term boots.  A conditional (18), a lawless `Bind` instance (19), a
  hidden `opaque` body (19), a non-returning action (20), a `let`-bound head
  (21) — each fix correct, each round finding another form, for the reason
  round 16 had already written down about regexes: *the set of inputs that
  defeats a partial analysis is unbounded while the set it has seen is finite.*
  Substituting `Expr` for text moved the class down a level; it did not close
  it.

  The exit is the one round 16 named, applied to the **program** rather than to
  its names: **where the subject is code this project writes and does not exist
  yet, require a canonical spelling and refuse the rest.**
  `SeLe4n/Testing/BootEntryContract.lean` no longer analyses the boot entry —
  it requires the entry to *be* `Platform.FFI.bootAndInitialiseRPi5OrHalt`
  applied to a configuration, decided by reducing the entry's body **towards
  the approved call** (`Meta.whnfUntil`: beta, zeta, delta through aliases,
  until that constant is the head) and one reducible `isDefEq` against a
  metavariable on what remains (PR #892 review round 2 — round 21 used one
  unbounded `Meta.isDefEq`, which opens *both* sides: on a deviating entry the
  unifier unfolded the approved call through the whole checked boot and hit
  the recursion limit once the configuration binding reached the RPi5
  RAM-variant selection, and it would have accepted an inlined copy of the
  wrapper's body, which is exactly what naming the wrapper exists to refuse).
  Every question the walk approximated is then answered exactly
  or has no subject: the entry *is* the boot, so nothing precedes it, there is
  no bind whose instance could be lawless, the reduction zeta- and beta-reduces so
  a `let`-bound head is not a form to know about, and nothing else runs at all
  — which makes the contract **stronger** than the walk, not weaker, since that
  one admitted any extra action which happened not to write kernel state.  The
  argument carries the rest type-theoretically: `PlatformConfig` is *data*, so
  no term of that type can install state, diverge or sequence.  Thirteen
  witnesses pin it, and three of them are **acceptances** — the required
  program spelled with a `let`, through an alias, and directly — because a
  contract that refuses everything reads exactly like one that decides.  What
  it deliberately refuses is an entry needing *effects* to build its
  configuration; if SM10.1 needs one, the kernel supplies that wrapper as a
  definition and this contract names it, which is a reviewed one-line change
  rather than a return to analysing arbitrary programs.  Eleven analysis
  definitions and 253 lines went with the walk.

  The corollary for scanners that have no elaborator to ask — a shell lexer, a
  Rust foreign block — is unchanged and is the same rule: **fail closed on what
  you cannot decide.**  A macro invocation inside an `extern` block expands to
  declarations no `fn`-shaped search can see, so the gate refuses the input
  rather than reading past it.

  **And one question answered in two places will diverge** (PR #889 review
  round 22).  The sweep rule above is reactive — *when a fix names a relation,
  grep for every other place that asks it* — and round 22 is three findings
  where it had not been run, which is the signal that the reactive form is not
  enough.  All three were a question with two implementations and only one of
  them right: "which cores does this boot install idle threads on?" answered by
  `bootAndInitialisePlatform` from the binding and by
  `bootAndInitialiseFromPlatform` as a hardcoded `allCores`, so a narrow
  configuration booted a TCB pinned to a PE the machine it installed does not
  have; "how does a boot-fatal condition fail closed?" answered by
  `gic::halt_all()` at three sites and by the per-PE `cpu::fatal_halt()` at the
  handoff refusal, which parks the boot core while the secondaries that *did*
  start keep servicing interrupts; and "is this a function provider?" answered
  by `executable_definitions` (global **text** symbols, since round 8) for the
  archive and by an unqualified `.global` + label conjunction for the source
  fallback, so a `.section .data` object satisfied an `extern "C" fn`.

  **Derive both answers from one, or make the second impossible.**  The core
  list is now `declaredCoresOfConfig`, read off the configuration the machine
  will carry; the refusal calls the barrier the rest of the tree calls; the two
  provider paths both ask the section question (`executable_label_names`).
  Where a second implementation must exist — a source fallback for when the
  object code is not built — it answers the *same* question and
  under-approximates, so the divergence direction is a false missing symbol
  rather than a false provider.

  **And a proxy is not the fact** (PR #889 review round 23).  The corollary of
  the rule above, for the case where the second "implementation" is a
  *stand-in*: `bring_up_secondaries` returns how many PSCI `CPU_ON` calls were
  accepted, and the round-21 handoff compared that against the declared PE
  count — but the number is incremented before the secondary has executed any
  of its own init, so a PE that halts in MMU, GIC or timer setup, or an
  `AlreadyOn` PE that never reaches `secondary_entry`, still counts.  The fact
  is `smp::CORE_IRQ_READY[c]`, which core `c` publishes *itself* after
  `enable_irq` and which the shootdown protocol already reads as the
  IRQ-serviceable set.  `irq_ready_core_count_within` waits for it, **bounded**,
  so a PE that never publishes makes the boot *fail* rather than hang.  When a
  cheap number is available beside the expensive fact, check which one the
  property is about.

  **And a bound has two sides.**  Round 22's `declaredCoresOfConfig` clamped
  `declaredCoreCount` from above and said nothing about zero, where the
  derivation yields the *empty* core list: no idle thread on any core,
  `bootAffinitiesDeclared []` satisfied by any unpinned config, and a boot that
  returns `.ok` with nowhere to run.  `declaredCoreCountInRange` is
  `wellFormed`'s sixth conjunct.  Two mechanical notes from adding it, both
  earned twice now: projection paths into the `wellFormed` conjunction shift
  whenever a conjunct is added, so the accessors are `simp_all only [...]` and
  depend on no nesting; and a Tier 3 anchor written as `X config$` breaks the
  moment a conjunct follows `X`, so anchors name the conjunct-list pairing
  round 19 made canonical instead.

  **And a name is not a contract — read the docstring of what you reach for**
  (PR #889 review round 24).  Round 23's fix for *a proxy is not the fact* was
  paced with `cpu::wfe_bounded`, and its `max_ticks` is **informational**: the
  docstring says in terms that it "does not bound the actual `wfe`", and the
  body opens `let _ = max_ticks;`.  A bare `wfe` returns on an event and a
  secondary that dies in init sends none, so the first iteration could sleep
  forever, the elapsed count never advanced, and the caller's topology refusal
  was unreachable — *a wait that cannot time out cannot fail closed*.  The name
  was the only thing that said "bounded", and the name is not the contract.

  Worse, and this is the point: **`shootdown::wait_all_acked_bounded_in` had
  already reached that conclusion and written it down** — same hazard, same
  word ("asleep FOREVER"), same remedy ("a counted spin is strictly more
  robust"), with an injected clock so the bound is testable.  Writing a third
  bounded-wait instead of using it is the round-22 rule (*one question, two
  answers*) at the point where the tree had already answered.  **Before writing
  a wait, a barrier, a retry or a timeout, find the one this tree already has
  and read why it is shaped that way.**  The readiness wait is now that
  pattern, clocked by `crate::timer::read_counter`, with four host tests that
  the bound actually terminates — a timeout with a straggler, an immediate
  return costing no clock reads, a clamp above the flag array, and a zero
  budget.

  **And a scanner's default branch is a decision — refuse what you cannot
  read** (PR #889 review round 25).  Every rule above is about a scanner that
  asked the wrong question of input it *did* recognise.  This one is about the
  other branch: three separate scanners, asked something they could not parse,
  silently did nothing — and doing nothing is the fail-open answer in all
  three.  An `extern` item that was not a `fn` declared no link requirement, so
  `fn r#lean_real();` — a raw identifier, which names the very same symbol —
  asked the archive for nothing and Tier 1 passed with no provider.  A
  `.section` whose operand the code view had blanked (the quotes make it a
  string literal) matched no section-directive pattern at all, so the scanner
  stayed in whatever section preceded it.  An `@[export]` argument spelled with
  guillemets — `@[export «suspend_generated»]`, which Lean accepts and emits —
  left the export inventory, and with it the readiness-gate seam set, one entry
  short.  In each case the artefact is real and *present*: the symbol links,
  the label is emitted, the export compiles.  Only the gate is silent.

  This is the presence-check family's dual, and it is why they keep appearing
  together: a presence check asserts too little about a token it *found*; a
  silent skip asserts nothing at all about input it did not recognise.  Round
  21 had already established the right shape — an item macro inside an `extern`
  block is refused, not read past, because "where a scanner cannot decide, it
  fails closed" — and applied it to that one case, which is the sweep rule
  failing exactly as it says.  **So make the default branch explicit: enumerate
  the inputs that legitimately produce nothing, and stop the build on anything
  else.**  A spelling the language accepts and the gate does not is a gate
  defect; it should say so, on the day it is introduced, rather than quietly
  checking less.

  **And which direction is closed depends on what the scanner produces.**  A
  scanner that builds a set of **requirements** fails closed by *refusing*
  unreadable input — a requirement it drops is a check nobody runs.  A scanner
  that builds a set of **providers** fails closed by *dropping* it — a provider
  it invents satisfies a requirement that was never met.  So the same
  unreadable `.section` operand makes `executable_label_names` treat the
  section as unknown and therefore **not** executable (a symbol reported
  missing, the gate failing), while it makes `extern_declarations_in` and both
  `@[export]` inventories stop outright.  Choosing the wrong direction is
  indistinguishable from not choosing.  A new mechanism brings its own edge, so
  check it: reading assembler *statements* rather than lines (AArch64 GAS
  separates them with `;`) would have split a `#define ENTRY(x) .text;
  .global x; x:` — a cpp **template**, whose directives and label exist where it
  is invoked — setting the section from a body that never executes there and
  registering the parameter as a provider.  That is round 16's `.macro` hazard
  arriving through the fix for a different one; a preprocessor line is not split
  and contributes nothing.

  **And a FAILED derivation is not an EMPTY one — the same rule at the point
  where a gate learns its own domain** (PR #897 review, `v0.35.147`).  The rule
  above is about *input* a scanner cannot read.  This is about the *question it
  asks the outside world*: four Tier 0 gates derive their whole domain by running
  git, and every one of them answered a failed run with an **empty** one —
  `except (CalledProcessError, FileNotFoundError): return []` and its `{}` twin.
  `[]` is also what a clean scan of a tree with nothing in it returns, so the
  caller iterates over nothing, finds nothing, and the gate prints PASS.

  **The review reported one site; the sweep found seven**, and the sweep is the
  point.  Its first form keyed on `subprocess.` and so missed the *reported*
  one, which runs git through a helper — *a helper the scanner cannot see is a
  spelling that evades the metric*, inside the measurement written to size the
  class — so the domain is closed **transitively** over intra-module calls.  The
  test that separates a defect from a deliberate sentinel is sharp and needs no
  registry: **a failure branch is a defect when its value is one the SUCCESS path
  can also return.**  `-> list[str]` returning `[]` is indistinguishable;
  `-> str | None` returning `None` is a sentinel the caller reads.  Measured over
  every tracked `scripts/*.py`: 10 failure branches in the git-derivation domain,
  **8 indistinguishable and 2 sentinels, with nothing undecidable**.

  Three things this cut records.  **The consequence is measured per site, not
  asserted**: only `check_deferral_registration.tracked_files` was run to ground,
  and what it produced was not a silent pass but a **misdiagnosis** — 35 false
  "row cites a path the index does not track" findings, naming the register
  instead of git, which is *answering in the words of a fault it does not have*;
  the rest are the same wrong shape at lower or unmeasured reachability, and the
  fix is the shape.  Claiming seven silent passes would have been the overstatement
  the measurement exists to prevent.  **The shared answer is
  `scripts/indexed_source.py`**, because `check_deferral_registration.indexed_contents`
  and `generate_smp_theorem_manifest.indexed_text` were the same `cat-file --batch`
  parser — same loop, same header split, same `i += size + 1`, same trailing
  comment — under two names; collapsing them found a **third** instance inside
  the body itself, since both `break` on an unreadable header and return the
  **prefix** they had parsed, which is a truncated domain indistinguishable from
  a complete one.  And **not everything that runs git should raise**:
  `select_changed_anchors._git` stays status-returning because three of its
  callers ask git a question whose answer IS the exit status (`rev-parse
  --verify`; `diff --no-index`, where 1 means "they differ"), so only the two for
  which a nonzero status is a *failure* raise.  A raise cannot be mistaken for an
  answer, which is why the shared module raises and that helper must not be folded
  into it.

  The fifth instance is the same rule one artefact over, and it is the one that
  says where to look next: `check_anchor_consistency`'s `filtered` bucket means
  *composed*, and its **membership** was a fall-through from every other arm — so
  `LC_ALL=C rg PATTERN FILE` inside a `bash -lc`, which heads no option table and
  is not a `SEARCH_TOOLS` head either, landed in the EXCLUDED bucket on a stated
  ground that is false of it, while the bare-argv sibling answered `unparsed`.
  `_is_composed` decides that bucket positively now and everything else that
  searches and does not reduce is `unparsed`, whatever its head.  **When a
  category has a stated reason, its membership test must BE that relation** — and
  a bucket reached by falling through is not one.  The widening admits nothing on
  the live tree (5211 / 827 / 38, byte-identical), so every witness is planted,
  and the two new fixtures are decided by *different* conditions: restoring the
  fall-through flips both, while opening the assignment set flips only one — which
  is what keeps either from being inert.

  **And the shell has the same defect with a second failure mode: the fallback
  APPENDS** (WS-RR RR8.15, `v0.35.186`).  The rule above is about Python calling
  git; every shell gate in this tree counts with `grep -c`, which *prints its
  count on the failing path too* — so `n=$(grep -c PAT F || echo 0)` does not
  substitute a default, it **adds a second line**.  On a clean run `grep -c`
  prints `0` and exits 1 (no matches), so `n` holds `0\n0`, every later
  `[ "$n" -gt … ]` dies with `integer expression expected`, and the `if` takes
  the else arm.  `test_tier5_cross_language.sh` did exactly that: **the one
  comparison the whole gate exists for did not decide**, and agreed with the
  truth by accident of which arm a failing `[` takes, while an *unreadable*
  mismatch log — `grep -c` exits 1 for "no matches" and above 1 for an I/O
  failure — produced the same verdict as a clean one.  Read the status
  (`n=$(grep -c …) || rc=$?`), make `rc > 1` a named gate failure, and refuse an
  unreadable input rather than defaulting it.  The sweep off that one found
  **three** more, all latent — `store_reader_hygiene_baseline.sh` twice and the commit
  hook once — and a Tier 3 negative refuses a fifth.
  **And a FOURTH sat two lines above the helper that sweep wrote** (`v0.35.204`,
  found while re-anchoring the metric it produces): the baseline script's
  `SENTINEL_CHECK_DISPATCH` kept the idiom with its `grep -c` on one line and the
  fallback on the next, behind a backslash continuation, and the tree-wide
  negative was single-line — so *a line is not the command*, and a sweep that
  reads lines misses exactly the instance a contributor wrapped.  The anchor
  reads the continued command now, and its mutation set has the two-line shape
  beside the one-line one.  Two things this cut
  measured about its own method.  `shellcheck` passes every one of them, and the
  shell's error line sat *above* the gate's `PASS`, so only **running** the gate
  found it; this is the second consecutive cut where running an artefact found
  what auditing it did not.  And the mutation harness written to judge the fix's
  anchors re-implemented `test_lib.sh`'s own view routing, always using the
  overlay — where `rg` skips the symlinks the overlay is made of on a *recursive*
  scan, and where a `bash -lc … scripts/…` anchor does not run at all — so a
  decisive anchor read as MISSED.  **A harness that re-implements the gate's
  routing answers a different question from the gate**; it sources
  `_run_with_view` now, with `set +e` after the source, because under `set -e`
  the failing command a negative anchor *expects* kills the harness at the first
  one and truncates the run.

  **And a default branch over a closed inductive is a decision five artefacts got
  wrong** (PR #897 review, `v0.35.114` and `v0.35.115`).  The rule above is about
  input a scanner cannot *read*; this is the same rule where the scanner reads the
  input perfectly and answers a wildcard.  `ConstantInfo` has exactly eight
  constructors, and "which declarations carry a body" is the first question every
  environment-derived **domain** in this tree has to settle.  It had **six
  answers** — this paragraph said five for one cut, because `v0.35.114`'s
  enumeration was of the *censuses* and two embedded Lean probes ask the same
  question; the sixth was found by sweeping the tree for the eight constructor
  names, which is the measurement that produced the check below.
  `ReplyStackWriteCensus` was the one that was right (`.defnInfo` *or*
  `.opaqueInfo`), and five sites across three censuses and two probes matched
  `.defnInfo` alone, or read `value?` without `allowOpaque := true`, and
  wildcarded the rest — so an `opaque`, which is executable, which this tree's FFI
  surface has seventy-odd of, and whose body
  `ConstantInfo.value? (allowOpaque := true)` hands back, was silently outside
  **five** derived domains at once.  What each one then stopped asking: an
  unreachable `opaque` transition owed no wire-or-record judgement
  (`KernelTransitionReachabilityCensus`), an `opaque` lock-set footprint owed no
  `_size_le` bound — so `boundedWait_under_2pl` and the whole WCRT surface would
  be **silent** about it — an `opaque` invariant conjunct dropped out of
  `measuredConjuncts`, making the de-threading census demand less, an `opaque`
  writer of `SystemState.declassificationTaint` passed a check whose claim is "one
  live writer", and an `opaque` helper in a syscall arm's chain stopped the
  per-core routing reach there, so the arm beyond it reached no slot at all.  The
  review reported one of the five.

  Three things follow, and the first is why this was not four patches.  **A domain
  miss is silent by construction** — the constant is never examined, the pin never
  moves, and each census goes on reporting that its whole domain is accounted for
  — so the class cannot be found by reading a failure; it is found by sweeping
  every asker of the question.  **The right answer was already in the tree and
  unreachable from two of the askers**, which is `v0.35.59`'s rule verbatim: the
  owner was in the wrong layer.  It is
  `SeLe4n/Testing/DeclarationKind.lean`'s `bodyBearing` now, upstream of every
  census, matching all eight constructors with **no `_` case at all**, so a ninth
  in a future toolchain is a *build error* naming the function rather than a silent
  exclusion.  And **two of the six exclusions are necessary rather than
  incidental**, which is precisely why folding them back under a wildcard reads as
  harmless: a `.thmInfo` carries a value, and a result-type test still matches one
  — `theorem f : step st = st'` elaborates to `@Eq SystemState (step st) st'`,
  whose implicit type argument *is* the constant a `SystemState` domain looks for —
  and `.ctorInfo` covers `SystemState.mk`, whose result type is `SystemState`
  itself.  `scripts/check_module_axioms.py` had enumerated all eight, case for
  case, since it was written; that was the precedent, unswept onto the censuses.

  **The widening is not vacuous, and the witnesses are the measurement.**  On the
  real tree it admitted exactly one constant: `Platform.FFI.kernelStateRef`, an
  `opaque IO.Ref SystemState` — the state cell the reachability census is
  *defined over*, since "commits state" means "reaches a write to it", and which
  was outside its own census's domain.  It is reachable from every committing
  seam, so it needs no pin entry; carving it out by name would be the enumeration
  the census exists to retire.  Beyond that the arms needed planting, since a
  check that cannot fire and carries no witness is indistinguishable from one that
  is wrong: the owner carries a `def`, an `opaque` and a `theorem` control, and
  the reachability census carries an `opaque` transformer that must be in its pin
  and a control that only *takes* a `SystemState` and must not be.  Both census
  witnesses were decided by **building**: deleting the pin entry makes the
  reconciliation report the transformer as unrecorded, and reading the whole type
  instead of the telescoped result makes it report the control as unrecorded — so
  the pair pins the domain in both directions, and the first draft's claim that
  the control witnesses "any declaration" was corrected by the mutation that
  refused to produce it.


  **And the question a resemblance stands in for may have THREE answers, not
  one** (PR #897 review, `v0.35.148`).  `check_content_flow_coverage.py` decided
  *"is this constant a compiler auxiliary"* by a **substring** over the qualified
  name, so `SeLe4n.Kernel.congruentTaintWriter` matched `.congr` and left a gate
  whose whole claim is *one live taint writer*.  The obvious remedy — repoint it
  at the environment-based answer this tree already has — is wrong, and the
  measurement says so: asked of this tree, the substring test and
  `KernelTransitionReachabilityCensus.isCompilerGenerated` disagree in **both**
  directions, **1156** constants one way and **2814** the other.  They are not
  two answers to one question.  *Before collapsing two predicates onto one owner,
  measure whether they agree; two that disagree in both directions are two
  questions, and naming one of them the owner silently changes what the other
  asker asks.*

  What licensed deleting it instead was a different measurement: the filter
  discarded **nothing** (disabling it left the gate byte-identical), and
  everything it *could* discard is a name a human wrote — the probe reports every
  writer through its owner-resolution, so the names reaching the filter have
  already been mapped to a human-written definition.  **A filter positioned where
  it can only ever be wrong is not a filter**; the two answers upstream of it
  (the owner resolution, and "a theorem is not a program") were already doing the
  work.

  And writing the witness found the real cause one layer down, which is the part
  worth keeping: the owner resolution itself stripped any component with a
  reserved prefix, so a contributor's `eq_foo` was attributed to its **parent
  namespace**.  Same class, better unit — the final component rather than a
  substring — and still a resemblance.  `v0.35.130`'s rule closes it: *the name
  narrows and the environment decides*, a declaration the compiler minted
  carrying no source range (`Lean.declRangeExt`, pure).  Two things that fix had
  to get right.  The range is asked of the constant **as the environment holds
  it**, never of its un-mangled user name — `privateToUserName?` maps
  `_private.M.0.foo` to `M.foo`, which is not a registered constant, so asking
  there answers "no range" for every private declaration and strips them all,
  re-creating the private-blindness the gate was fixed for two cuts earlier.  And
  the un-mangling was **folded into** the owner resolution rather than left as a
  helper beside it, because the two are one step and splitting them is precisely
  how the wrong name gets asked.

  The witness is the measurement here, as it is in every cut whose widening
  admits nothing: every existing plant in that gate is named `cfPlanted…`, so not
  one of them could show either defect.  The plant that decides is named the way
  a contributor would name a real definition (`eq_cfPlantedUserNamedTaintWriter`),
  and it is asserted on **both** sweeps.  *A witness drawn from the naming
  convention the fixtures already use cannot see a defect about naming.*

  **And the answer to "who else asks this" is a SWEEP, and once the sweep has run
  twice the third response is a check** (PR #897 review, `v0.35.115`).  `v0.35.114`
  gave the question one owner, repointed four askers and wrote the paragraph above.
  It named a fifth asker rather than omitting it — `check_content_flow_coverage.py`'s
  embedded Lean probe, whose `cfExecutableValue` both matched on the kind *and*
  called `value?` with no flag, with four sweeps beside it that bypassed even that.
  Then the *sweep* — every tracked file, for each of the eight constructor names —
  found a **sixth**: `check_live_arm_per_core_routing.py`'s `routeExecutableValue`,
  byte-for-byte the function `cfExecutableValue` had been, feeding a **reachability**
  question, so an `opaque` helper anywhere in a syscall arm's chain made the walk
  stop there and the arm beyond it was reported as touching no per-core slot.  The
  enumeration that opened this cut said *five*; the count was six, and nothing but
  running the search over the whole tree would have said so.

  So the response is not a seventh paragraph.
  `scripts/check_declaration_kind_askers.py` (Tier 0) refuses any subject that
  matches a `ConstantInfo` constructor and is not a recorded asker, keyed
  `(subject, constructor)` with a **count** and reconciled in both directions — the
  floor shape `identifier_naming_baseline.json` already has, because a set of keys
  alone cannot see a second occurrence inside a subject that already has one and a
  count alone cannot see the first in a subject that had none.  **Its domain is
  derived over both places this tree writes Lean**: `.lean` files, and a probe
  string a Python gate hands to `lake env lean`, located by `ast` — so the three
  such gates are found without any of them being named, and a fourth is found the
  day it is written.  A file whose import markers the located constants do not
  account for is **refused** rather than skipped, since "could not read" must not
  answer the same as "read and clean".  Both views are the ones this tree already
  owns, because several subjects document in their docstrings exactly which
  constructors they retired and a check that counted those would force them to stop
  explaining themselves.

  Three things that cut measured.  **The widening admits nothing on the live tree**
  — both gates' whole inventories and both production verdicts are byte-identical
  before and after — which is the opposite of `v0.35.114`, where one real constant
  (`kernelStateRef`) came in; so here the *plants* are the entire measurement, and
  each is its neighbour with one keyword changed: `cfPlantedOpaqueTaintWriter` is
  the first plant's body spelled `opaque`, and `routeSelfTestOpaque` is
  `routeSelfTestAlias` spelled `opaque`.  **Neither could have been an older
  witness**: all four existing plants and all three older routing witnesses are
  definitions, so every one of them passes both halves of the defect, which is
  exactly why four review rounds and a sweep were needed to see it.  And **the new
  check earned its keep on its first run**, twice: its own reconciliation reported
  two guessed probe-variable names that do not exist, and the mutation set confirms
  it reports each pre-fix probe, a census re-deciding the question, a stale entry, a
  moved count in either direction and an unlocatable probe.

  **And the answer to "who else asks this" had a THIRD dimension: the census's own
  domain and closure** (PR #897 review, `v0.35.125`).  `v0.35.115` derived which
  *files* hold a Lean probe and gave the question one owner; it left
  `KernelTransitionReachabilityCensus`'s own three questions to resemblances, and a
  review found all three at once.  A **name prefix** stood for "generated"
  (`startsWith "initFn"`, which an ordinary `initFnCleanup` trips — this file's own
  retired `eq_` prefix, one census over); a **constant occurrence** stood for
  "reachable", so a transformer mentioned only inside a proof was marked live and
  escaped the wire-or-record pin; and a **mention** of `SystemState` stood for
  "returns state", so `TlbCacheJointState.pageTableUpdate` — which rewrites that
  record's `sysState` field — was on neither side of the reconciliation while the
  projection `TlbCacheJointState.sysState` was.

  Each remedy is the environment answering, and each was **measured before it was
  chosen**.  The prefix is *deleted* rather than narrowed: of the 4 `initFn`
  constants here, **0** are outside `isAuxiliary`, a module's init being
  macro-scoped, so the clause excluded nothing while admitting a user name.  The
  closure skips an **erased** constant, decided on the telescoped result through
  the sibling census's `isPredicate`, since `Expr.isProp` is true of a proof and
  false of `SystemState → Prop` and a proposition reaches the walk as an implicit
  argument at a call site: the permissive closure is 4231 constants and the
  erasure-respecting one 3477, and **zero** of the 754 are transformers, so the
  tightening is free today and closes the path one proof-carrying body would open.
  And the domain asks whether a result **carries** state — `SystemState`, or a
  non-propositional project inductive holding one in a constructor field,
  transitively — which is 10 carrier types and 39 more pinned definitions, the boot
  path among them.

  Two rules the carrier derivation cost, both about the measurement rather than the
  code.  **A constructor's telescope opens the inductive's own parameters**, so
  without dropping `numParams` a `Prop` structure over a state reads as holding
  one — 64 carriers, almost all propositions, which is a measurement that would
  have licensed a much larger claim than the tree supports.  And **a field carries
  state when its own telescoped result does**, the same question the domain asks of
  a definition: judging by a mention anywhere admits `PlatformBinding` and both
  boundary contracts, and with them every configuration record in the tree.  *A
  measurement that licenses a conclusion gets checked as hard as the conclusion* —
  twice here, and the third reading is the one that shipped.

  One thing the erasure witness had to get right, and it generalises: **`Expr`
  traversal walks binder TYPES**, so a helper whose argument is typed with the
  proposition reaches the subject through its own signature rather than through the
  proof — a type-level mention, which is not execution either but is not the route
  the witness is about.  The consumer is generic in the proposition, and the check
  asserts that the theorem's own proof term mentions the transformer, because a
  proof term that does not makes the whole witness **inert**.

  **And a REDUCIBLE ALIAS is not a different type, nor is an exhausted fixpoint a
  smaller answer** (PR #897 review, `v0.35.128`).  Two more misses in that same
  derivation one cut later, and both are the *domain* half of this family rather than
  the predicate half — so both fail in the one direction this census structurally
  cannot report: a constant it never examines moves no pin, and the reconciliation goes
  on stating that every non-executed transformer is recorded.

  `forallTelescopeReducing` reduces only far enough to expose a `∀`, so a result spelled
  through `abbrev StateResult := Option SystemState` arrives as the alias **constant** —
  which the carrier set never contains, that set being built from inductives — and the
  transformer is then in neither the reachable nor the unreachable set.  One `whnf` at
  **reducible** transparency is the exact boundary, and *exact* is measured rather than
  argued: `abbrev` is what Lean makes reducible, so it unfolds, while **default**
  transparency opens a dependent projection like `id.evidenceProp` and files **four**
  records of proofs (`covertChannelEvidence`, `fineLockClaimEvidence`,
  `declassificationRuleEvidence`, `crossCoreLiveArmEvidence`) as state transformers.
  The negative anchor on the unrestricted spelling is what keeps that boundary.

  Two things the fix records.  **The widening needed the environment's own answer to
  "did you generate this"**: reducing a `T.noConfusion`'s result mentions the
  constructor fields' types, so `Lean.isAuxRecursor`, `Lean.isNoConfusion` and
  `Meta.isMatcherCore` join the filter — and they are **complementary** to the
  hand-written component list rather than a replacement, measured both ways (the list
  catches `_flat_ctor` / `_sizeOf_inst` / `_unsafe_rec` members the predicates do not;
  the predicates catch every `*.noConfusion` the list does not).  *Derive what the
  environment can answer and keep the list as a pin for what it cannot* — claiming
  redundancy in either direction would have shrunk the filter.  And **the real tree
  gains zero declarations**, so the plants are the entire measurement: an `abbrev`
  naming a state-carrying type (which must be in the pin) beside the control naming one
  that carries nothing (which must not), so the pair decides *the alias names a carrier*
  rather than *the result is an alias*.

  The second miss is *a rule stated is not a rule enforced*, and the rule was stated in
  the very docstring that failed to enforce it: `carrierFixpointBound`'s own text said
  exhaustion "would under-approximate the carriers, which makes the domain SMALLER, so
  a new bound must be checked rather than assumed" — and the loop then **returned the
  partial set as though it were complete**.  It throws now.  The bound is an *argument*
  so the refusal has a witness, because on this tree the fixpoint converges in **two**
  rounds against a bound of twelve and nothing in production can reach the throw:
  `carrierFixpointRefusalViolations` runs the derivation at a bound of **1** and reports
  a violation when it *succeeds*, which is the only direction that can be silent.  (The
  two-round figure also corrects the previous cut's docstring, which said three — it had
  counted the convergence-detecting pass that does not run.)

  **And the sort the alias DECLARES is normalised too** (PR #897 review,
  `v0.35.135`).  The same miss four lines above, in the same derivation, unswept by
  the cut that wrote the paragraph above: the alias test read `ci.type` **raw**, so a
  declared sort that is itself reducibly aliased — `abbrev CarrierSort : Type 1 :=
  Type`, then `abbrev StateAlias : CarrierSort := SystemState` — is a `.const`,
  neither `isSort` nor `isForall`, and the alias never entered the candidate array at
  all.  A transformer over it is then in neither reconciliation set, which is the same
  silent direction one level further out.  *When a fix names a relation, grep for every
  other place that asks it* — here the other place was the **next test in the same
  function**, and asking it is what shows that the whole type and a telescoped body
  were two spellings of one question: `declaresNonPropSort` is the one owner and the
  branch on the raw shape is deleted, since `forallTelescopeReducing` over a non-`∀`
  type calls its continuation on that type.  Both boundaries above carry over
  unchanged — reducible unfolds an `abbrev` while default files the four evidence
  records, and `Prop` is a sort — so the plants are again the entire measurement (585
  over 19 before and after the fix; 586 over 20 with the pair), and the **control** is
  what makes them decide *the aliased sort is normalised* rather than *anything
  declared through this sort is a carrier*.

  **And a domain written as a NODE KIND is the same defect one grammar down**
  (PR #897 review, `v0.35.124`).  `v0.35.115` derived *which files* hold a Lean
  probe and left *which expressions* to one `ast` node kind: `embedded_lean` read
  the value of an `Assign`/`AnnAssign` and nothing else, with an explicit `else:
  continue`.  So a probe handed straight to its runner —
  `run_probe(<a literal>)` — was located by no shape at all, and the fail-closed
  refusal beside it asked whether **anything** had been found, which one assigned
  probe in the same file answers for every marker in it.  Measured on the fixture:
  the capture read the assigned probe alone and refused nothing, so an inline probe
  could re-decide the body-bearing question with the inventory unchanged and Tier 0
  green — *invisible in both directions at once*, which is what makes a domain miss
  unfindable by reading a failure.

  Four things follow, and each is a rule this file already carries arriving at a
  smaller unit.  **The domain is every string constant**, plus every expression that
  *assembles* one (`A + B`, an f-string, a `.join`/`.format`), because an assembled
  probe's import marker and its `ConstantInfo` match sit in different fragments and
  neither is a probe on its own evidence — measured at **zero** admitted on the
  tracked tree, against **1060** for the statement-level grouping first tried, so
  the widening costs nothing and every witness is planted.  **The refusal is a
  count** (`markers_located < markers_in_text`), since *a cardinality is what sees
  the second occurrence*; its witness is therefore an unlocatable marker **beside** a
  located probe, because a fixture whose only marker is the unlocatable one is
  refused by the superseded reading too and would pass with the count reverted.  It
  counts markers in located TEXT and not in the rows reported, because one constant
  bound to two names is reported twice and that surplus would pay for a marker nobody
  read — found by re-reading this cut's own diff, not by a review.  **A
  subject key must identify a subject**: an assembled probe takes its assignment's
  name rather than its scope, or two of them in one module collapse into one key
  where the counts add — and two probes that bind *no* name in one scope are
  **refused**, not bucketed, since an ordinal key churns when an earlier probe is
  deleted and *refuse, name the scope, state the remedy* is what this project does
  wherever a scanner cannot decide.  And **the reassembly is in SOURCE order**:
  `ast.walk` is breadth-first, so `A + B + C` yields `C, A, B`, and a join in that
  order destroys a constructor name straddling the last boundary — two fragments
  cannot witness it, which is why the fixture the defect arrived with could not have
  caught it.

  One mechanical note, and it is the *fail-fast harness* hazard rather than a new
  class: a `UnreadableProbe` raised inside a self-test case escaped as a traceback,
  which is not the gate's voice and which skips every case after it — so one
  mutation could mask another, and two of this cut's eleven mutations were
  mis-attributed until the direct reads went through a helper that reports a refusal
  the way `violations` already did.  **A harness that crashes where it should report
  hides the second defect**, and a mutation run is the only thing that shows it.

  **And the located subject's TEXT and its IDENTITY are each something the program
  computes** (PR #897 review, `v0.35.127`).  Two fail-open defects in that same
  locator, one cut later, and they are one class: it asked *what shape is this* where
  the question was *what value does this have*, and *what is this called* where the
  question was *which subject is this*.

  The text half is `a spelling is not the text` at the one place the text is
  assembled rather than written.  `_is_concatenation` asked whether an expression
  builds a string from parts, and the callers then **joined its literals in source
  order** — which is the string `"a" + "b"` builds and is *not* the one
  `"… .{}Info …".format("opaque")` builds: joining yields `… .{}Info … opaque`, so the
  constructor pattern matches nothing while the template's own import marker **is**
  accounted for, so the fail-closed marker count passes too and the asker is invisible
  in both directions at once.  `_reconstruct` returns the string or `None`, and four
  forms are determined by literals — a literal, `+` over two determined operands, an
  f-string with no interpolation, and `<literal>.join([<determined>, …])`.  Narrowing
  the reader is **not enough on its own**, and that is the load-bearing part: with
  `.format` no longer forming an assembly its template would fall through to the
  bare-constant branch and be *located*, reopening the hole one branch over — so
  `_unreadable_assemblies` **refuses** a string assembly that carries a marker and
  does not reconstruct, which is *a scanner's default branch is a decision* applied to
  the one branch a narrowing creates.  The shape set excludes a call on a plain
  **name**, because a probe handed straight to a helper is this tree's commonest idiom
  and its literal is the call's *argument* rather than a part of a string the call
  builds; a `.replace` on a named `@SENTINEL@` template — how all four real probes are
  built — is likewise not a subject, its marker living in the template's own
  assignment.  Measured before choosing: **zero** such expressions on the tracked
  tree, so the refusal is entirely planted today.

  The identity half is this file's own rule inside the cut that wrote it.  A named
  probe's key was the bare target name, so two probes assigning `PROBE` in two
  functions shared one subject and their counts **added**: change one from `.defnInfo`
  to `.opaqueInfo` and the other the inverse, and every number in the inventory is
  unchanged while *both* askers have re-decided the question.  `v0.35.124` had already
  refused exactly that for probes binding **no** name, one branch over, under a
  comment stating the reason — *a fix applied at one site and not its sibling*, for the
  third time in this file.  `_qualified` keys a named probe by scope-and-name, the
  scope itself is now a **qualified path** rather than the nearest declaration name (a
  bare name is a resemblance two methods in two classes share), and two probes that
  still land on one key are **refused** — by OCCURRENCE, not by distinct text, because
  two identical rebindings double every constructor in them and a set cannot see the
  second one.  Free on the tree: all 17 located probes are at module scope, so every
  key is byte-identical and the pin does not move.

  Two things the cut records about its own witnesses.  **The axis came from Python's
  grammar, not from the reported spelling**: the review named `.format`, and `%` was
  not even *grouped* by the superseded reader — so its template was read as a bare
  inline probe and the constructor was lost the same way, one branch further over —
  while an interpolating f-string has `FormattedValue` parts that are not literals at
  all.  All three are cases, with **two controls** (a literal f-string, which
  reconstructs and is read; a `@SENTINEL@` template, which is the tree's own idiom),
  because a fix that banned the node type would pass a case list drawn from the
  finding.  And **a mutation must revert the defect, not merely edit the code**: the
  first mutation written against the `.format` refusal widened a branch whose other
  conditions still rejected the input, so the self-test passed and the case read as
  unverified; the mutation that decides restores the *superseded reading* — a
  `.format` branch returning the source-order join — and is caught immediately.

  **And a TRANSFORM of located text is a third thing, beside its shape and its
  value** (PR #897 review, `v0.35.129`).  `v0.35.127` replaced *what shape is this*
  with *what value does this have*, and the case that survived is the one where the
  answer is **almost** the value.  A named template holding a constructor spelling
  with a hole in it is a **located** subject: its import marker is accounted for, the
  fail-closed marker count is satisfied, and its constructor count is **zero**, while
  the probe handed to Lean decides the question.  Invisible in both directions at
  once — the shape that makes a domain miss unfindable by reading a failure — and
  reached by the tree's own commonest probe idiom, a `@SENTINEL@` template consumed
  by `.replace`.

  **So the reconstruction is PARTIAL: determined text with holes.**  Not the
  all-or-nothing string, and not a shape — `_reconstruct_holed` returns the text the
  expression builds with one non-word `_HOLE` wherever text the scanner cannot read
  enters it, and "determined" is that with no holes left.  Four things follow, and
  each is a rule already in this file arriving at a smaller unit.  **A name resolves,
  fail-closed at both ends** — a template is reached *through* its name, so a scanner
  that cannot resolve the name cannot see the text a substitution applies to, and a
  name bound more than once resolves to nothing because two bindings are two texts
  and no occurrence says which is live.  **The refusal asks COMPLETION, not the
  presence of a hole**: `_constructor_completing_holes` is derived from the
  constructor tuple and inherits its `\b` bounds, so a hole is refused exactly where
  the template has written part of a constructor against it — measured at
  **thirteen** substitution sites on the tree, every one undetermined and **zero**
  writing a constructor against its hole, so refusing every hole would refuse the
  tree and the mutation that does fails the control *and* the live gate.  **The
  default branch is taken per CALL SITE rather than per spelling** — an unmodelled
  form is unreadable when applied to determined probe text and an ordinary value
  fragment otherwise, which is what keeps the recognised set from having to be
  complete.  And **the admission test moves with the text**: the marker is asked of
  the assembled text in *both* branches, because a template reached through its name
  puts the marker in no literal fragment of the expression that substitutes into it.

  Two things that cut records about its own witnesses.  **The widening admits nothing
  and refuses nothing on the live tree** — 25 subjects, byte-identical counts, zero
  refusals — so the plants are the entire measurement, as at `v0.35.115`.  And **two
  of the ten mutations were MISSED on the first run**, which is the part worth
  keeping: the word-boundary guards and the named branch's admission test each passed
  every case that existed, because every fixture reached them through the other
  branch.  *An unwitnessed condition is indistinguishable from a wrong one*, so the
  answer is not to reason about it but to plant the case that separates it — a
  fixture with **two** holes, so a mutation dropping one guard is caught by its own
  half; a substitution **assigned** to a name beside the one that is returned; and an
  ambiguous name that is *not* probe text, since the ambiguous-probe refusal fires
  first for every name that is.  **Run the mutations before believing the cases.**


  **And a PREFILTER is not the SIGNAL — and asking one with the other's predicate
  skipped two whole gates** (PR #897 review, `v0.35.132`).  Every rule above is about
  what a scanner asserts of input it examined.  This is the cheapest way not to
  examine any: `embedded_lean` returned early unless `_probe_signal(text)` held, and
  that predicate is written for a probe's OWN text, where the import begins a line.
  Asked of a whole Python file it is a different question, false for one of the
  commonest spellings there is — `PROBE = """import SeLe4n ...` opens the literal on
  the assignment line, so no line of the file begins with the import.

  **Measured, and the measurement is why this is a rule rather than a patch**: that
  skipped `check_ipc_invariant_dethreading.py` (11 markers) and
  `check_tlbi_broadcast_discipline.py` (4) — two real Tier 0 gates, every embedded
  Lean probe outside the inventory, with the gate reporting the tree clean.  Not
  fixtures; the plants in the six preceding cuts admitted nothing, and this widening
  admits exactly those two files.  **A prefilter must be strictly WIDER than the
  predicate it stands in for**, and where a scanner has both, the narrow one is kept
  for the questions that genuinely are about a line start.

  Its sibling finding is the resolution residue reached by an extra HOP: `ALIAS =
  PROBE` resolves to no literal, so a transform through it substitutes into a hole
  whose result carries no marker, and the template is still located carrying the
  constructors its *unsubstituted* text spells.  **The refusal is the remedy, not
  resolution** — a probe has one name, deleting an alias is a one-line change, and
  chasing a chain whose depth nothing bounds is the partial-analysis shape this file
  retires twice over; the probe SET is closed transitively all the same, so `B = A`
  over `A = PROBE` is seen.

  One correction this cut records about its own plan, because the plan was wrong and
  the measurement said so before any code was written.  The first design deleted the
  hole machinery outright, on the ground that no probe in the tree assembles text.
  That is true of the 41 probe **assignments** and false of their **uses**: three
  `@SENTINEL@` `.replace` sites substitute *computed* values, so a canonical
  "substitute with literals or refuse" rule would have refused every real probe in
  the repository.  *Measure the uses, not only the definitions* — and when a
  measurement kills the plan, that is the measurement working.

  **And when TWO conditions guard one question, each needs a witness the other
  cannot rescue** (PR #897 review, `v0.35.130`).  `v0.35.125` deleted the `initFn`
  prefix and kept the component list on the stated ground that its members are
  *whole* components the compiler reserves rather than prefixes of user names.  True,
  and not enough twice over: Lean accepts `_flat_ctor` as an ordinary identifier, so
  a contributor's transformer with that name was excluded before its result type was
  read; and `components.any` excludes every declaration **nested beneath a namespace**
  of such a name, whatever it is called.  So the remedy is the one this section keeps
  arriving at — the name *narrows* and the **environment decides**: a reserved
  spelling is a suffix, so the question is the FINAL component, and a declaration the
  compiler minted carries **no declaration range**, which
  `Lean.findDeclarationRangesCore?` answers.

  What is new is what the mutation run then showed.  With the range test in place,
  **neither** the `any`→`last` narrowing nor the name test itself was observable:
  every user-written plant carries a range, so restoring `components.any` and
  deleting the name test each passed every case.  Two conjuncts, one of them
  witnessed.  *A condition no case can reach is indistinguishable from a wrong one*,
  and the pair rescuing each other is how a two-condition guard hides a dead half —
  so the witness has to be the shape **neither** existing plant can take: a
  transformer **minted** through `Lean.addDecl`, with no declaration range, an
  ordinary final component, under a reserved namespace.  It decides both mutations at
  once, because it is the only input on which the two conjuncts disagree.

  Generalising: when a guard is a conjunction, ask of each conjunct *what input does
  this one alone reject?* — and if every fixture is rejected by its partner too, the
  conjunct is unwitnessed however plausible it reads.  The plant will usually have to
  be constructed rather than written, because the property being witnessed is
  precisely the one the ordinary way of writing code cannot produce.

  **And when a cut fixes an exhaustion, SWEEP every other bounded walk — the
  conservative direction is different for each** (PR #897 review, `v0.35.131`).
  `v0.35.128` made an exhausted carrier fixpoint an error and wrote down why; the
  question was never asked of its siblings.  Asking it found the tree has **four**
  bounded walks and that three of them fail closed for three *different* reasons —
  `reachesAny` answers `true` (does this export reach a state write? `true` demands
  more), `entailedTargets` answers the empty entailment set (fewer entailments
  demand more), `stateCarryingTypes` throws — while `liveClosure` returned its
  partial set.  A bound is not conservative in itself; **which** answer is
  conservative depends on what the predicate means, so every walk needs the question
  asked separately and the answer recorded at the walk.

  Two things that cut records.  **A docstring that compares itself to a sibling is a
  claim about the sibling**: `liveClosure`'s said it was "fuel-bounded like its
  sibling", and the sibling does the opposite — the comparison was false in exactly
  the direction that mattered, and it read as having been checked.  And **a
  precedence you would otherwise have to witness is better removed**: distinguishing
  "finished" from "exhausted" by arm order in one `match a, b` is a property no
  witness on this tree can reach (it bites only when the worklist empties on the last
  unit of fuel), so the arms are *nested* instead and there is nothing left to get
  wrong.  *Prefer making the property structural over checking it at all.*

  The same cut's second finding is the recursion rule one level down: a normalisation
  that reaches only the HEAD is a partial answer too.  `whnf` on `Option StateAlias`
  stops at `Option`, so an alias nested under a constructor never unfolds — and the
  answer is not to recurse the normalisation, which is one more partial analysis, but
  to add the alias to the **set** the search consults, where the existing fixpoint
  closes a chain of them for free.  *When a reduction cannot reach the thing, widen
  what the question is asked about rather than deepening the reduction.*

  Two corollaries about the plants it needed, both earned by a mutation run that
  found three of five conditions unwitnessed.  **A control that mentions the subject
  for an unrelated reason decides nothing**: the parameterised-alias plant first
  passed its argument as an inline `fun _ => 0`, whose own binder type put
  `SystemState` in the result expression outright, so the plant was in the domain
  whatever the code did.  And **`Prop` is a sort** — the one place this cut's first
  draft had to be told twice, because dropping that half admitted 30 spurious domain
  members and the mutation that proves it must target the branch the tree's own
  predicates actually take.

  **And a recognised set is not a derived set — so a count over one is a floor,
  not a measurement** (PR #895 review, rounds 1 and 2, `v0.35.13`).  Every rule
  above polices the **predicate**: what a scanner asserts of an element it
  found.  None of them polices the **domain**: whether it found them all.  That
  asymmetry is why this family keeps reappearing, because the two fail
  differently — a predicate miss can fire on a real element, while a domain miss
  is *silent by construction*: the element is never examined, the count stays
  clean, and the gate reports a number that reads as a measurement of absence.

  Six of the eight findings across two review rounds of one PR were that one
  defect.  `.objects.get?`, then `RHTable.get? st.objects k`, then a `where`
  equation body whose signature never closed — three spellings of one read.
  `pub unsafe extern "C" fn`, skipped entirely rather than judged.  `FrozenOps`,
  outside both library roots, so *every reply-stack write* meant every one in
  the modules the census imported.  A frontier that asked "constructs **and**
  stores" of one body, which a writer defeats by delegating the construction to
  a helper.  Each fix was right and the next round found another, because the
  boundary was being probed rather than the property.

  **Two kinds of gate, and only one of them can be closed.**  Where the domain
  is *derivable* — which constants a term uses, which modules an environment
  imports, what a definition transitively calls — derive it and reconcile both
  directions, and the class really does end there: the reply-stack write census
  now follows construction through helpers (`reachesChainConstructor`, walked
  backwards from the storing definitions and memoised, since nearly everything
  reaches a constructor forwards), and asks the *environment* which constants it
  generated rather than matching name prefixes.  Where the domain is a **coding
  convention over unbounded syntax** — "obtain objects through an accessor",
  "justify every unsafe site" — there is no closed formulation, in text *or* in
  the environment: round 17's instruction sends questions about **elaboration**
  to the elaborator, and "is this occurrence a read rather than a write" is a
  question about an API's meaning, which the environment has no opinion on.
  Measured rather than assumed: 245 hand-written executable definitions mention
  the object-table projection, because writing the store is what a transition
  does — so "never mention it" is not a stateable contract either, and the
  attempt to derive a read-set from result types promptly classified
  `FrozenMap.set`, a *write*, as a read.

  So for the second kind, **fix the claim**: report the number as a floor over
  recognised forms, in the gate's own output and in the prose that cites it
  (`STORE_READ_SCOPE`, and the unsafe gate's `scope:` line).  The enforcement is
  unchanged — a recognised violation still fails Tier 0 outright — but a
  widening of the recogniser becomes an improvement to a diagnostic rather than
  the closing of a hole that was claimed shut, which is the only way the reports
  stop being findings.  And keep the other half of round 25's rule, which is
  what bounds the gap: an input the scanner does not recognise **fails the
  gate**, so the unrecognised set is visible rather than assumed empty.

  One mechanical note, earned twice in this round: a fix for a domain defect can
  introduce one.  `Name.isInternal` looked like the environment's own answer to
  "did Lean generate this" and is true of the `_private.…` mangling, so adding
  it to the auxiliary filter would have excluded **every `private def` in the
  kernel** — the same class, inside its own remedy.  The census's planted
  witness caught it, which is what witnesses are for.

  **And a domain written as an exclusion is the same defect wearing a filter**
  (PR #895 review round 3, `v0.35.15`).  Round 2 named the class and fixed it at
  the four sites the review pointed at; round 3 found four more, and every one
  was the gate's *domain* spelled as a hand-written exclusion rather than
  derived: a glob naming `src` (so integration tests, `build.rs`, examples and
  benches were never scanned), a prefix list naming `eq_` (so a contributor's
  `eq_clearReply` was filtered out as a compiler auxiliary before its constants
  were read), a regex naming `: Prop` that matched a *binder* (so
  `def step (proof : Prop) … : SystemState` filed its raw store reads as
  specification and walked around an enforced zero), and a `usesDirectly` naming
  "direct" (so a writer that hands a built record to a store helper was in
  neither derivation).  None was a new class; each was the round-2 rule applied
  at one site and not swept onto its siblings, which is the failure mode this
  file already documents.

  The remedies are all the same shape — **derive the set, or name the shape
  rather than the resemblance**: every tracked `.rs` file that is not build
  output; the result type is what follows the first depth-zero `:`; and the
  frontier pairs a transitive side with a direct one on each disjunct.  That
  last is the point at which derivation stops being possible: chasing stores
  transitively makes every IPC composite a candidate, measured at 22, so the
  census states its frontier (`chainWriteFrontier`) in its own output instead of
  letting the number read as a proof of absence — the second-kind treatment this
  section already prescribes.  **A predicate over a domain you filtered is a
  measurement of the filter.**

  **And an exclusion's stated reason is a claim about its MEMBERS, re-measured or
  not** (`v0.35.120`).  `check_anchor_consistency.py` leaves an invocation it
  cannot reduce to one `(pattern, target)` out of the satisfiability comparison,
  with the reason written at the category: such an invocation *"pins a property of
  the composition rather than of a pattern, so it has no counterpart to
  contradict"*.  True of a pipeline.  But the *membership* test was not that
  relation — it was *the script inside a `bash -lc` is not one of two recognised
  **wrapper** forms*, a syntactic accident — so a bare `rg PATTERN FILE` that
  happens to be quoted through a shell landed in the bucket, and that is the form
  **every** bounded-gap anchor in this tree must take, the gap carrying a `\n`.
  Measured: **976 of 987** excluded invocations reduced to exactly one
  `(pattern, target)` and 11 were genuinely composed; the compared set was **4579**
  records where it is now **5573**, and the *negative* half **470** of **742**, so
  over a third of the tree's absence pins — the *must not come back* negatives a
  deletion's correctness rests on — were compared against nothing while the gate's
  PASS line read as coverage of the anchor set.  It failed silently by
  construction: an excluded member is never examined, so no count moved.

  Three things follow.  **Make the membership test the relation the reason names**,
  not a shape that usually implies it — the reduction is now the same one a bare
  argv gets, and `_is_composed` decides what a composition is, so the 11 keep an
  exclusion that is true of them.  **Re-measure a category's reason against its
  members when either changes**, because this bucket was correct when it held only
  the two wrapper forms and became wrong as the tree's anchor style moved.  And
  **state what the gate still cannot decide at the gate**: *two positives* over one
  subject are jointly satisfiable in the abstract — a file may hold two matching
  lines — and unsatisfiable only given a fact no scanner has (*this file declares
  that name once*), which is why `v0.35.118`'s defect is the changed-file sweep's
  question and not this one's.  One mechanical note, from this cut's own mutation
  set: the first anchor over the new fail-closed branch pinned its **condition and
  explanatory comment**, so a mutation keeping both and changing `unparsed` to
  `filtered` left it green — *a presence check is not a relation check*, inside an
  anchor written for the cut that closes one.

  **And a narrower resemblance is not a relation** (PR #895 review round 4,
  `v0.35.17`).  The fourth remedy in that list was *a generated component is the
  prefix plus a numeral*, and it is the one that did not hold: `eq_1` is as legal
  a definition name as `eq_clearReply`, so the rule narrowed the set of user
  names a contributor must avoid without making the test a fact about the
  declaration.  Round 4 found six more instances of the round-2/round-3 class, and
  five of the six are the *scanner's own default* rather than its predicate —
  which is this file's `a scanner's default branch is a decision` rule meeting its
  domain rule, since a default that silently answers is a domain written as an
  omission.  A missing metric read as `0`, so **deleting a measurement satisfied
  an enforced zero** (`check_store_reader_hygiene_monotonic.sh`: `SORRY_COUNT`,
  `AXIOM_COUNT` and `STORE_READ_CODE` all rode on it); `structure`/`class` bodies
  were spec whole, so an executable field **default** filed as specification (the
  remedy carried an over-approximation — a default ran to the end of its
  declaration — which that cut called harmless and `v0.35.18` had to retire: it
  filed a later field's *type* as executable, which is fail-strict, not
  harmless); a result-type parser that knew only `→` rejected the ASCII `->`
  that Lean equally accepts; inner rustdoc (`//!`, `/*!`, `#![doc]`) documents the *enclosing*
  module and justified the function below it; and `r#unsafe` — an identifier, not
  the keyword — failed a file outright.

  What closes the name half is not a sixth narrowing but the environment:
  `Meta.isMatcherCore` is pure, every `eq_N`/`proof_N` constant is `Prop`-typed
  and so excluded structurally, and with those two facts the whole name list is
  **redundant** — measured at zero definition-shaped, non-`Prop` writers kept only
  by a name test — so `isGeneratedComponent` was deleted rather than narrowed a
  third time.  **Where a resemblance keeps needing another exception, the
  question belongs to something that knows the answer.**

  **And a parser for a language you are not parsing is a list of the spellings
  you have seen** (PR #895 review round 5, `v0.35.18`).  Round 5 found seven more,
  three of them in code written hours earlier to fix round 4, whose findings were
  in code written to fix round 3.  The through-line is not any one of them: it is
  that `scripts/lean_store_read_census.py` decides two **structural** questions —
  which declaration owns a line, and whether that declaration is executable — by
  reading text.  Over three rounds it was taught seven legal Lean spellings it had
  not seen (a hypothesis binder, a `where` equation body, an ASCII arrow, a
  `structure` field default, a leading indentation, a defaulted binder, a
  per-field reset), which is this file's own regex rule arriving at a gate written
  after it.

  The exit is round 17's — *a Lean question goes to the Lean elaborator* — and the
  obstacle is that the classifier runs in **Tier 0**, before any build, because
  the `ZERO_METRICS` entry it produces is consumed there.  So the exit is taken at
  the tier that can take it: `SeLe4n/Testing/StoreReadClassificationCensus.lean`
  (Tier 1) asks `findDeclarationRanges?` which declaration owns each line and the
  conclusion of its type whether that declaration is specification, and fails the
  build wherever the classifier disagrees.  **And its domain is reconciled
  against the classifier's** (`v0.35.76`): the classifier scans the filesystem
  and the reconciliation reads the environment, and no `SeLe4n/Testing/` module
  was in that environment — invisible while the read census produced no row
  there, and exposed by the write census's first, the reply-stack census's
  planted witness, which the check counted as "outside any declaration" and
  moved on.  A row in a file the environment declares nothing in now fails the
  build naming the module to import (`orphanFiles`), because a declaration
  outside the import closure is indistinguishable from one that does not exist
  and a count of what could not be judged reads as a diagnostic.  Its first run
  named a **kernel** module, not a test one — `ChainFootprint`, outside both
  library roots since RR7.40 — which is how the five-modules finding recorded
  under *a surface outside every derived domain* above was made.  **Where the authoritative answer is
  out of reach at the tier that needs it, derive it at a tier that can and
  reconcile** — the *derive the set, keep the list as a pin* rule, one tier apart.

  Three things that cut records, each found by running the reconciliation rather
  than reading it.  Its first run reported **271** disagreements and every one was
  the *check* being wrong: `Meta.isProp` asks whether a declaration is a **proof**,
  and a predicate (`def p : SystemState → Prop`) is not one — a question
  `ReplyStackWriteCensus` had already answered as `isPredicate`, so asking it a
  second way was the one-question-two-answers shape inside the remedy for it.  Its
  second reported **5**, all hypothesis binders inside executable declarations,
  which a declaration-level verdict structurally *cannot* adjudicate — so the
  classifier reports the region and signature reads are counted, not judged.  And
  the enforced direction **cannot fire while `STORE_READ_CODE` is zero**: there is
  no misfiled executable read to find, so it carries synthetic witnesses, as
  `BootEntryContract` does for the same reason.  **A check that cannot fire on the
  current tree and carries no witness is indistinguishable from one that is
  wrong.**

  **And a reconciliation only closes the direction it judges** (PR #895 review
  round 6, `v0.35.19`).  Round 5 took the structural exit for the Lean
  classifier and wrote the caveat above; round 6 found **seven** more — six
  reported, one self-inflicted — and the useful result is *which* of them the
  round-5 mechanism already covered, because that is the measure of whether the
  exit was the right one.

  It covered one.  `opaque` was missing from the classifier's declaration
  keywords, so an executable `opaque` body following a `theorem` was attributed
  to the theorem and filed `SPEC`, past the enforced zero — and the elaborator
  reconciliation's mismatch message *already named that case* ("a Lean
  declaration form the classifier does not recognise"), because asking
  `findDeclarationRanges?` who owns a line is spelling-independent.  It could
  not fire only because no `opaque` body in the tree holds a read.  **A
  mechanism that would have caught a finding it never saw is the evidence that
  it is the right mechanism**, and the keyword was still added: Tier 0 is where
  the metric is read, and a gate that needs its sibling to notice every miss is
  a worse gate.

  It did **not** cover the other two, and each for a reason worth keeping.  A
  binder's *default value* was emitted in the signature region, which the
  reconciliation skips — correctly, since a declaration-level verdict cannot
  adjudicate a hypothesis binder.  But a default is not a hypothesis: it is
  elaborated and evaluated exactly when its declaration is, so it *is*
  adjudicable, and lumping the two into one region hid an executable read from
  both tiers at once.  **A region is a claim about what a verdict can decide;
  two constructs that differ in that are two regions.**  And a result type that
  is an *alias* of `Prop` was filed `CODE`, which the reconciliation also
  skipped — deliberately, on the reasoning that over-filing `CODE` cannot bypass
  a zero.  True, and it is not the only thing that matters: over-filing makes
  Tier 0 refuse valid specification text, and the tier that knows better was
  staying silent about it.  **Judge both directions: the safe direction is still
  a direction, and a wall with no explanation is a defect too.**

  Two more from the same round, on the Rust side, are the nesting and
  same-line rules one level down — a doc marker nested inside another comment
  publishes nothing, and a preceding *item* on the site's own line does not
  donate its documentation — and the second carries a distinction worth
  stating: the two site kinds ask different questions of that line.  A **block**
  is evaluated inside the statement it sits in, so a binding prefix is not
  something that executed in between; a **declaration** preceded by another item
  is a different item.  Applying one rule to both is wrong in whichever
  direction it is applied, measured: the strict rule over blocks fails 18 live
  sites.

  Finally, the round's own mechanical lesson, earned by nearly shipping a false
  green: **a mutation must revert the defect, not exchange one sound rule for
  another.**  The first mutation written against the same-line fix substituted
  the *block* rule for the *declaration* rule, and the fixture passed under it —
  not because the fixture was weak but because both rules reject that input.
  The mutation that decides is the pre-fix behaviour itself.

  **And a skip is a sink** (PR #895 review round 7, `v0.35.20`).  Round 5 sent
  the classifier's *verdict* to the elaborator and round 6 made that
  reconciliation judge both directions; neither touched the **region boundary**
  — where a declaration's signature ends and its body begins — which stayed a
  two-token regex, and whose failures all landed in `sig`, the one region the
  reconciliation deliberately does not judge.  So the parser's unknown-input
  behaviour drained into the bucket nothing checks.  Measured on the tree:
  Lean's direct equation syntax (`def f : A → B` followed by `| p => rhs`)
  carries neither `:=` nor `where`, so **4778 lines of body across 263
  declarations** were filed as signature — SPEC, unjudged, past an enforced
  zero, in the gate this PR spent four rounds hardening.

  **When a judged direction is split from an unjudged one, every parse failure
  migrates into the unjudged one.**  A skip is never neutral: it attracts
  exactly the defects the judge exists to find, and the size of what it
  attracted is invisible because the rows look ordinary.  Three things follow,
  and all three are now mechanism rather than advice.  Teach the boundary the
  form (a depth-zero clause bar, with `||`, `|||`, `|>.` and `<|>` excluded by
  shape rather than by a list).  **Refuse** what it still cannot close — every
  declaration form has a body except `opaque` and `axiom`, so an unterminated
  signature is a named Tier 0 failure instead of a silent SPEC filing, which is
  this file's *a scanner's default branch is a decision* applied to a region
  boundary.  And **report the residue the skip legitimately leaves**: the Tier 1
  census now counts signature rows sitting inside *executable* declarations —
  five, against the 4778 that were hiding there — so the population no
  declaration-level verdict can reach is a number rather than an implication.

  The round's other two findings are the same meta-shape one level up, and they
  are why this entry is about the class rather than the instances: **a fix
  landed where the review pointed and the question's other askers were left.**
  `CLAUDE.md` recorded *an item macro inside an `extern` block is refused, not
  read past* as implemented — true of `check_kernel_entry_exports.py`, and false
  of `check_unsafe_block_justifications.py`, which parses foreign blocks for the
  same items and scanned them for `fn` alone, so a macro declared an unsafe
  obligation no site, count or baseline could see.  And the reply-stack write
  census named the **frozen** table primitive (`FrozenMap.set`) while omitting
  the **live** one (`RHTable.insert`), so a definition that builds a `Reply` and
  writes `{ st with objects := st.objects.insert … }` — which is how
  `Lifecycle/Suspend.lean` writes a consumed Reply — was in neither derivation.
  That is round 1 of this same PR (*a spelling is not a read*) on the same two
  tables in the opposite direction, with the sweep unrun.

  Stating the sweep rule has now failed often enough to be the finding.  **Give
  it an artefact: derive both answers from one place, or make the second
  implementation impossible.**  The foreign-block walk — ABI-literal resolution,
  brace matching, the item split, and the classification `fn` / `macro` /
  `non-fn` / `unknown` — is `rust_code_view.extern_blocks` /
  `extern_block_items` / `classify_extern_item`, read by both gates, so one
  mutation now fails both self-tests; only what an item *means* stays per gate
  (a linker symbol there, an unsafe obligation here).  The store frontier names
  the two table **primitives** and keeps the wrapper helpers as a *pin* each of
  which must itself reach a primitive — and that pin found two more defects on
  its first run: a fourth entry (`SystemState.storeObject`) that names no
  declaration at all, and a live helper (`storeObjectChecked`) the list had
  never mentioned.  A list nothing reconciles is a list nobody reads.  **And a
  pin's reach is a relation too** (`v0.35.66`): the frontier recognises a store
  one hop from a pinned name, so a helper *over* a pinned helper sits two hops
  out — `refillSchedContext`'s `updateSchedContext` over `rewriteObject` over
  the insert — and the census reported its exemption as stale the moment the
  definition migrated.  The `v0.35.64` cut had met the same report for
  `suspendThread` and deleted the entry, which is the fail-open direction (a
  writer setting `scReply` through the unpinned helper would have been
  invisible); the rewrite family is pinned now and the entry is back.

  The sweep was then **run**, not just written down, and its value is the two
  sites it left alone.  `check_ipc_invariant_dethreading.py` has its own Lean
  `signature_end`, and its fall-through is already a stated decision — with no
  `:=` the signature runs to the next declaration, which over-captures and can
  only make the gate stricter — so it is the sink's opposite and correct as it
  stands.  `build.rs`'s `blank_extern_blocks` is a Rust twin that *blanks* a
  block rather than enumerating its items, so the macro question does not arise
  there, and it already shares the ABI-literal resolution.  A sweep that changes
  nothing at a site is the sweep working; a sweep not run is how all three of
  this round's findings got here.

  **And a conjunct whose antecedent is the property you want enforces nothing**
  (PR #895 review round 8, `v0.35.21`).  This round's sharpest finding is not in
  a scanner at all — it is in the kernel, and it is the invariant-level form of
  *a presence check is not a relation check*.  `passiveServerIdle` reads "an
  unbound thread that is **not queued and not current** is in one of these
  `ipcState`s".  The property the tree wants at a donation pop is *an unbound
  thread is not queued*, and that is precisely the conjunct's own **hypothesis**
  — so a thread left `.unbound` **and still runnable** satisfies it vacuously,
  and every bundle theorem over it stays true while the defect is live.

  The defect it hid: `replyRecvPostReceiveDonation`'s Call arm donates the newly
  dequeued client's context to the **receiver** `tid` and descheduled nobody,
  which is right exactly when `tid` *is* the recorded server — the non-delegated
  steady state — and wrong on a **delegated** reply, where the recorded server
  gave its context back in the pop and receives none.  It then stays on its run
  queue and is selected at its legacy TCB priority charged to no reservation,
  which is WS-OD OD3.6's defect on the path OD3.5 had just made live.  The arm's
  own comment names the distinction two lines above the bug (*"not the (possibly
  delegated) recorded server"*) and its justification sentence ignores it, so:
  **a justification that holds on one side of a distinction the code already
  makes is not a justification — say which side, or make the code not care.**
  `replyRecvServerDeschedule` is the named answer, with the write set, the
  confinement and both bundle proofs carrying it (renamed
  `replyRecvHolderDeschedule` at `v0.35.149`, when its argument stopped being the
  recorded server), and the witness pair in
  `tests/SmpIpcSuite.lean` §3.9b is delegated *and* non-delegated, because a
  deschedule that fires unconditionally passes the first and breaks the second.

  The round's three gate findings are all rules this file already carries, each
  unswept by exactly one step.  `#+\s*Safety` accepts `/// #Safety`, which
  CommonMark renders as a paragraph — the gate whose whole subject is *what a
  caller is told* accepting text that tells the caller nothing.  The upward
  justification walk decided a multi-line `#[cfg(all( … ))]` one physical line at
  a time and stopped at its `))]`, which is *a nested construct is not a sibling*
  applied to Lean and never to Rust attributes; the remedy consumes the closer's
  pending run and requires the balancing line to open an attribute, because a
  multi-line *expression* ending in `]` is code and extending a run across it is
  the fail-open direction.  And `\bextern\b` matches inside `r#extern`, so
  `mod r#extern { … }` parsed as a foreign block — the `r#` exclusion sitting on
  `UNSAFE_KEYWORD` eight lines away in the file this scanner was *moved out of*,
  one round earlier.

  That last one is the measurement worth keeping.  Round 7's remedy was **give
  the sweep an artefact** — two gates consolidated onto one shared view so a
  single mutation fails both.  It worked, and it did not stop the very cut that
  performed the consolidation from writing a fresh regex missing a rule the same
  file states.  **Sharing the answer stops two answers from diverging; it does
  not make a new answer inherit what the old one learned.**  When you move a
  scanner, carry its neighbours' exclusions with it — or, better, reach for the
  existing pattern instead of writing one that looks like it.

  Two mechanical notes.  A census whose headline is one derivation while its
  breakdown is another describes no set: the reply-stack summary counted
  `derived.length` beside disciplines counted over the registry, so the figures
  stopped adding up the moment a site entered through the second frontier, and
  the closure `stating + mirrors + halfSteps = registry` is asserted now.  And a
  registry cannot name a `private def` with a name literal — Lean mangles one to
  `_private.<Module>.0.<name>` and a numeric component is not an identifier — so
  the entry is built with Lean's own `mkPrivateNameCore` rather than with a
  resemblance to it.


  **And a rule stated is not a rule enforced — give it a check, not a third
  telling** (PR #895 review round 9, `v0.35.22`).  Round 8 closed with *sharing
  an answer stops two answers from diverging; it does not make a new answer
  inherit what the old one learned*, and recorded it in this file.  Round 9 found
  **six more** bare keyword spellings in the very file whose one correct pattern
  carries the rule, ten lines below the comment explaining it.  Measured:
  `check_unsafe_block_justifications.py` held **seven** `\bunsafe` regex literals
  and exactly one had the raw-identifier exclusion, so `struct r#unsafe { … }`
  read as an unsafe block and Tier 0 demanded a justification of safe Rust.

  That is this file's own enumeration-versus-derivation rule at the level of a
  **regex fragment**, and the two previous remedies could not reach it: fixing a
  site does not reach the site nobody has written yet, and consolidating a *walk*
  does not constrain a *new pattern* written beside it.  Writing the lesson down
  a third time would have been the move that had already failed twice.

  **So the remedy is a mechanism.**  `rust_code_view.keyword(word)` is the one
  fragment every keyword pattern composes, and `bare_keyword_literals()` reads
  the gate sources and refuses any bare word-boundary keyword spelling written
  outside it, wired into the view's self-test.  The next such pattern fails on
  the day it is written.  Two things make it honest: it reads **code, not
  prose** — `python_code_view` blanks `#` comments and, via `ast`, docstrings,
  because `keyword`'s own docstring quotes the bad spelling in order to explain
  it and a check that counted it would force the file to stop explaining itself
  — and it is mutation-tested in all three directions, since a discipline check
  that cannot fire is indistinguishable from one that is wrong.  **When a rule
  has been restated twice, the third response is not prose.**

  Two corollaries this round paid for.  **An inert witness reads as coverage
  while asserting nothing**: the first case written for the unsafe-attribute
  classification was a *site* case, and a file whose only `unsafe` is an
  attribute produces no sites, so it passed vacuously with the fix reverted —
  the mutation harness caught it by **not** failing, and the witness moved to the
  scan the fix actually lives on.  And **a fix can reopen a closed finding**: the
  new doc-attribute scan was first written `#!?\[`, accepting the *inner*
  `#![doc]` form, which is round 4's *inner rustdoc documents the enclosing
  module* — round 4's own witness failed immediately, which is what witnesses are
  for.

  The round's other three findings are each a question this file already answers,
  asked of the wrong artefact.  Rust 2024's `#[unsafe(no_mangle)]` is the only
  spelling a 2024 crate may use for those attributes and matched no known form,
  so the explicit default branch failed the whole file — classified now, with
  **no** per-site obligation, because it attaches to an item and asserts
  something about the linker namespace that two other gates already enforce.  A
  `///` attaches to the item that *follows*, so the comment after a scope opener
  documents the first item inside it; the run takes the trailing portion after
  the last code character, which is the other side of round 6's rule rather than
  a widening of it, since that one was documentation sitting *before* an
  intervening item.  And `#[doc = r"…\n# Safety"]` is a **raw** literal whose
  `\n` is two characters, so rustdoc publishes no heading: two rounds had
  narrowed that regex and the question itself was wrong, so the value is
  **decoded** by its literal kind and a real line-start question asked of the
  result — *a spelling is not the text*, which is *a spelling is not a read* one
  artefact over.


  **And when two rounds' findings land in each other's fixes, the fix's SHAPE is
  the defect** (PR #895 review round 10, `v0.35.23`).  Round 9 closed with *a
  rule stated is not a rule enforced — give it a check, not a third telling*, and
  built one.  Round 10 then found five more, **two of them inside round 9's own
  fixes**, and the useful reading is not the instances: it is that both were the
  same *kind* of mistake, made at the point where a fix chooses what to trust.

  **A proxy is not the fact, at the scheduler.**  `replyRecvServerDeschedule`
  (`replyRecvHolderDeschedule` since `v0.35.149`)
  accepted the core its caller had already computed — `determineExecutingCore`,
  which finds a core the thread is *current* on and otherwise answers
  `bootCoreId`.  A **queued** server matches nothing there, so the deschedule
  edited the boot core's queue while the server sat on another and the
  temporal-isolation defect the step exists to close survived on the preempted
  path.  `determineTargetCore` is no better and the measurement says why:
  `affinityAdmitsCore` is `true` on *every* core for an unpinned thread, so
  `runQueueAffinityConsistentOnCore` does not pin one to that answer either.
  Both are proxies; the fact is **placement**, and `removeRunnableOnCore` writes
  the run queue *and* the current slot of whatever core it is handed.
  `placedCoreOf?` is the witness, tied to `runnableOnSomeCore ||
  runningOnSomeCore` by theorem so a third answer cannot appear.  The sites
  round 10 named and did not sweep — the cancellation path's `descheduleThread`
  and `cancelIpcBlockingOnCore` — and a third the sweep found, the live
  suspend's own home-then-running-core removal pair, closed at WS-RR RR8.6
  (`v0.35.79`); the standing constraint is recorded below.

  Two things generalise.  **A parameter is a place for a caller to be wrong**:
  the fix is not a better argument at the call site but *no argument* — the step
  resolves its own core, and its footprint reads the same call, so the transition
  and the declaration cannot name different cores.  And **a witness that supplies
  the answer tests the fixture, not the code**: §3.9b passed `serverCore` by hand
  and so asserted nothing about the resolver production actually used, which is
  why a green suite sat over a live defect for a whole cut.  With the parameter
  gone there is nothing left to supply.  Ask of any witness: *could this have
  failed if the production path computed its input differently?*

  **And the view you read depends on the question** — the same rule this file
  states for Lean structure, arriving at a gate that had deliberately chosen raw
  text.  The justification run is raw because what matters is what a reviewer
  reads, and that is right for *reading* a comment and wrong for *deciding
  whether something is one*: an ordinary `// #[doc = "# Safety"]` was decoded as a
  real attribute and a `"// SAFETY: …"` inside `#[allow(reason = …)]` counted as
  a real comment.  Both fail open.  Comment spans are now *derived from the code
  view* rather than re-lexed — a maximal run of blanked bytes holding a byte the
  raw text did not blank **is** a comment — because a second Rust lexer is this
  file's one-question-two-answers hazard.

  Two more corollaries about witnesses, both earned rather than reasoned.  **A
  fix whose revert breaks nothing is indistinguishable from no fix**: the domain
  correction here was first shipped with no witness at all, and the mutation
  harness caught it by reporting `MISSED` — the case lists could not reach it,
  because the function reads the real workspace, so it needed a synthetic tree.
  And **bounding a negative is not automatically safe**: the two Tier 3 anchors
  on the deschedule were mutation-tested in both directions, silent on the clean
  tree and firing on a mutation that keeps every token and moves the pre-fix
  spelling back inside the declaration.

  **And a witness drawn from a finding tests the finding** (PR #895 review round
  11, `v0.35.24`).  Round 10's reading was that a fix's *shape* is the defect
  when two rounds land in each other's fixes; round 11 makes it three, with
  three of its four findings inside round 10's own code, and names where the
  shape comes from.  Every case list in these gates had been grown the same way:
  a round reports a spelling, the fix adds a witness for **that spelling** plus a
  control, and the next round supplies one nobody enumerated — a raw doc
  literal, a `#[unsafe(…)]` attribute, a scope opener, a `*`-decorated block
  comment, attribute-shaped text inside a string.  That is this file's own *a
  recognised set is not a derived set*, applied to a gate's **test cases** rather
  than to its input, and it fails the same way: silently, because the cases that
  exist all pass.

  **So enumerate the space instead of the findings.**  The remedy already existed
  one file over — `per_core_state_matrix` pins the lock by classifying every
  entry point in every per-core state — and it is a *matrix*, not a list: every
  marker FORM crossed with every ENCLOSURE, with the verdict a property of the
  enclosure alone (a real comment justifies; a literal or a commented-out
  spelling never does).  A spelling the gate has not considered is then a missing
  **row** — visible, and addable without waiting for a review round to supply
  it.  Its first run on `check_unsafe_block_justifications.py` found **five**
  defects no round had reported: one fail-closed (an undecorated `/*\nSAFETY: …*/`
  refused), and four fail-open — a `/**` inside a line comment, inside a string,
  or nested in another block comment each publishing a `# Safety` section; a
  `///` heading at the start of a line *inside a string literal* satisfying the
  line-anchored scan; and `UnterminatedLiteral` in no handler, so a file the
  shared lexer cannot finish reached the operator as a traceback rather than as
  the refusal the gate's own "one failure channel" claims.

  Three things fall out of running it.  **Keep the tables symmetric**: the
  declaration side omitted the plain string-literal enclosure the block side had
  carried since round 10, and that asymmetry is what hid the `///` cell — the
  same defect one level up, inside the matrix meant to close it.  **A
  declaration-bounded negative is a statement about that declaration**: round
  10's Tier 3 anchor was scoped to `replyRecvServerDeschedule`
  (`replyRecvHolderDeschedule` since `v0.35.149`) while the relation
  is about *every* deschedule of the thread the pop unbound, so the sibling arm
  twenty-five lines away kept the retired spelling and the anchor's silence read
  as coverage.  And **a harness that re-spells the gate's own decision absorbs
  the defect it is there to find**: the refusal handler was written out three
  times, `UnterminatedLiteral` was missing from two of them, and the self-test's
  private copy caught what the scanner would have crashed on — one `REFUSALS`
  constant now, which is also what makes dropping a member *detectable*.

  **And a matrix enumerates the dimensions you thought of** (PR #895 review
  round 12, `v0.35.25`).  Round 11's remedy was to stop drawing witnesses from
  findings and enumerate the space instead — every marker FORM crossed with
  every ENCLOSURE.  Round 12 then found three more in the same gate, and the
  useful reading is *where* they landed: not in a cell, but **off the grid**.  A
  `# Safety` inside a fenced code block is a markdown enclosure; `#/* c */[doc
  = …]` is a token-separation form; `pub unsafe fn λ()` is a *name* form, a
  dimension of the site scanner the justification matrix does not reach at all.
  The matrix worked exactly as designed — each is now a row — and the lesson is
  that its **axes** were themselves a recognised set.

  **So take the axes from the artefact's grammar, not from the findings.**  The
  question a gate asks has a small number of dimensions, and they are readable
  off the language rather than off a review: for a doc comment they are *which
  marker*, *what encloses it lexically*, *what encloses it in the rendered
  markup*, and *how the item is named*.  Each round-12 finding added an axis and
  then all of its values at once, which is why one cut closed six defects
  including two the review did not report.

  **And when the property is about the whole artefact, build the artefact.**
  That is the sharper half.  A fence is a property of the *rendered document*,
  and three separate line-oriented patterns — a `///` scan, a doc-block scan, a
  decoded-attribute scan — structurally could not see it, however many spellings
  each one learned.  rustdoc concatenates every doc source on an item into one
  markdown input, so `rendered_doc_markdown` now does too and
  `publishes_safety_heading` asks the single question of it.  Three patterns
  became one, a cross-form fence (opened in a `///`, closing after a `#[doc]`)
  became answerable at all, and every rule about which markers attach to the
  item moved to the one place that builds the document.  **Reconstructing what
  the real tool consumes is not a bigger scanner; it is the end of a class of
  scanner defect** — and it is the same payoff shape as round 7's *give the
  sweep an artefact*, one level up.

  Two corollaries this round paid for.  **A field name is not a receiver
  type**: the store census matched `.objects[…]?` by spelling, so an executable
  definition over any other type with an `objects` field was counted as a
  kernel-state read and refused by an enforced zero.  Resolving the receiver is
  an elaborator question and this gate runs before any build, so the *ambiguity*
  is bounded instead — `OBJECTS_FIELD_OWNERS` is derived from the sources and
  reconciled both ways, making a new owner a **named** Tier 0 failure rather
  than a mystery rejection.  Running that derivation found six owners where the
  first guess named four, one of them (`BootstrapBuilder.objects : List`)
  already indexable: the ambiguity was live, not hypothetical.  And **a name is
  not a definition, in Lean too**: `Prop`-alias resolution accepted any alias
  with the same final component, so `B.Pred := Nat` read as specification
  because some other namespace declared a `Pred := Prop`.  Aliases carry
  qualified identities now and resolve against the use site's enclosing
  namespaces, longest prefix first — which is what the elaborator does, and the
  third case in its witness set is the one that stops the fix from degrading
  into *a bare alias never resolves*, since refusing valid specification text is
  a defect in its own right.

  Finally, the round's own mechanical lesson, and the second time this PR has
  paid for it: **an inline mutation with no assertion is an inert mutation.**
  Two of this round's mutation checks reported the fix as unverified and one
  reported it as verified when the edit had silently matched nothing — the
  difference being a `assert s.count(old) == 1` the throwaway script omitted.
  The harness asserts it; a one-off mutation run by hand must too.  And **a
  mutation must revert the whole defect**: the alias fix has two halves, and
  reverting either alone left a witness passing, while reverting both — the
  actual pre-fix state — failed immediately.

  **And a mirror of a part is not a mirror of the whole — sharing an
  implementation transfers its preconditions** (PR #895 review round 13,
  `v0.35.26`).  Round 12 said *when the property is about the whole artefact,
  build the artefact*, and meant a rendered document.  Round 13 is that rule
  meeting three different units, two of its three findings inside round 12's own
  fixes — the fourth consecutive round where findings land in the previous
  round's code.

  The one worth keeping is not a scanner.  `Reply.consumed` keeps a stack head's
  links, and its docstring says why in terms: *the pop that follows clears
  them*.  That sentence is a **precondition on the caller**, not a description —
  and `FrozenOps` adopted the record without it.  Sharing `consumed` between the
  live and frozen surfaces was *right*, by this file's own one-question-one-answer
  rule; what the sharing also moved, invisibly, was an obligation the frozen
  surface could not discharge, because it models no donation pop.  So a frozen
  state captured mid-chain left the answered Reply failing `Reply.isFree`
  forever: never re-linkable, never retypeable, and no passive server could
  complete a second call/reply cycle on it.  **When you reach for a shared
  answer, read what it requires of you, not only what it returns** — a function
  whose correctness depends on what runs *after* it is a contract, and adopting
  it is accepting that contract.

  Where the fix goes carries the second half.  `frozenEndpointReply` is refined
  against the **bare** `endpointReply`, which also leaves a head linked, and the
  differential scenario compares exactly that — so putting the pop inside it
  would have broken the refinement the surface exists to check, while fixing the
  symptom.  The frozen `.reply` *operation* is the reply leg **then** the
  donation return, as the live one is, so the composite is where the pop belongs
  and the refined mirror is left alone.  **Ask which unit the property is about
  before choosing where to fix it**: the leg refines, the operation composes, and
  a fix at the wrong level trades a visible defect for an invisible one.

  The two scanner findings are the same rule at smaller units, and both are the
  *unit* being smaller than the property.  A binder-default scan asked its
  question of the enclosing group's whole span, so a `let` in a nested group that
  had already closed suppressed a real default — filing an executable read as
  `SPEC region=sig`, the one region the Tier 1 reconciliation does not judge, so
  it bypassed **both** tiers rather than one; the span is walked at depth now,
  through the depth-zero walk every other top-level-token question in that file
  already used.  And the markdown enclosure axis round 12 created had one value —
  fenced code — where CommonMark's grammar has several: **HTML blocks hold raw
  text**, so a `# Safety` heading inside `<!-- ... -->` published nothing and
  satisfied the gate.  The axis is taken from the grammar rather than from the
  reported spelling: all seven block types, both end conditions, an unterminated
  block running to the end of the document, and type 7's inability to interrupt a
  paragraph.  **A new axis is enumerated at all of its values on the day it is
  added**, or the next round supplies the ones that were skipped.

  One mechanical note, and it is the *witness* rule again rather than a new one:
  each hidden matrix row is paired with a control that ends the enclosure, so the
  row is known to fail on the enclosure and not on the marker; and the census
  case for the binder fix is decisive only because round 12's own case keeps
  passing under the mutation — a fix that narrows a rule must be shown to narrow
  it rather than to disable it.

  **And six rules did not close this class, which is itself the finding**
  (PR #895 review round 14, `v0.35.27`).  Rounds 9 through 14 each added a rule
  to this section — *give it a check not a third telling*, *a witness drawn from
  a finding tests the finding*, *take the axes from the grammar*, *build the
  artefact*, *sharing an implementation transfers its preconditions* — and each
  round after it found more.  Do not read that as six failures of nerve; read
  the **distribution**.  Every one of those six rounds found at least one defect
  in `check_unsafe_block_justifications.py` or its shared view, and rounds 10,
  11, 13 and 14 each found one in the frozen surface.  Two artefacts, six
  rounds.  The rules were locally right and structurally beside the point.

  **Cause one: a gate that hand-implements a language front-end will be fed a
  construct it has not seen, forever.**  Those two files are 3,591 lines
  implementing Rust lexing, Rust item parsing and CommonMark; the store census
  implements Lean declaration parsing.  This is round 16's own observation —
  *the set of valid spellings that defeats a regex is unbounded while the set a
  gate has seen is finite* — arriving at the level of the whole gate rather than
  of one pattern.  The exit is round 17's, and it was taken **once**: the Lean
  classifier's verdict is reconciled against `findDeclarationRanges?` at Tier 1,
  and round 6 then confirmed the mechanism by finding it would have caught a
  defect it never saw.  It was never generalised, and the generalisation is not
  subtle: **Rust's front-end is `rustc`, and the `# Safety` question's front-end
  is `rustdoc`** — the tool whose output the property is defined by.  Round 12
  wrote *build the artefact* and then hand-rolled a markdown renderer instead of
  asking the renderer.

  **Cause two: a hand-written second implementation whose fidelity is checked by
  a hand-written list.**  `FrozenOps` mirrors live transitions and
  `frozenRunAgrees` would catch a divergence, but which pairs are driven through
  both sides is a handful of scenarios and the pairing itself is a Markdown
  table.  Rounds 10, 11, 13 and 14 are one shape — a *part* of a live operation
  reproduced with a step omitted that the live code pairs with it — and 13 and
  14 are the same defect twice, the second inside the first's fix.  That is this
  section's own strongest rule (*one question answered in two places will
  diverge*) meeting the artefact deliberately built to be two places.

  **And that artefact is not a test double** (the maintainer's correction,
  `v0.35.102`).  `FrozenOps` is the *execute* phase of this project's
  build → freeze → execute architecture: `Model.freeze` takes the **builder**'s
  `IntermediateState` to a `FrozenSystemState`, and `Platform/Boot.lean`'s
  `bootToRuntime_invariantBridge_empty` — *boot to runtime* — carries the
  invariant bundle across the freeze into `apiInvariantBundle_frozen`, which is
  a bridge worth proving only if the runtime is meant to run on the frozen
  representation.  What is missing is the dispatch: `API.lean` contains no
  occurrence of `FrozenOps`, `kernelStateRef` holds a `SystemState`, the boot
  installs `ist.state` rather than `freeze ist`, and `Model.freeze` has no
  executable caller anywhere under `SeLe4n/` — every occurrence in `Boot.lean`
  is inside a theorem statement.  So the duplication is an **interim**, the
  differential is the evidence that would license ending it, and every
  divergence found is a *deferred kernel defect* rather than a model one.
  Calling it a second implementation *kept so the live one can be compared
  against it* names the interim method and not the purpose, which reads the
  severity down; the register row says so since `v0.35.102`, and C.1 row 14 —
  the dispatch switch — gated on *benchmarks* and named no correctness gate at
  all, so the two preconditions lived in neither row.

  **What changed, and what did not.**  Both causes are now rows in
  `docs/REGISTERED_DEBT.md` table C with closure targets before v1.0.0, because
  the remedies are a reconciliation against the real tools and a derived
  differential coverage set — work, not wording.  What this cut *does* do is
  narrow cause two at its own site: a frozen mirror names the live function that
  **completes** a step (`frozenApplyReplyDonation` pairs the donation return with
  the deschedule) rather than the one nested inside it, so the pairing is
  structural.  **When a rule has been restated six times, stop restating it and
  write down what the restating measured.**

  **And a claim made at the wrong UNIT is a claim about something else** (PR #895
  review round 15, `v0.35.28`).  Round 13 said *ask which unit the property is
  about* and applied it to where a fix goes.  Round 15 is the same question asked
  of where a *verdict* is taken, in two artefacts that share nothing else, and
  the two together are why this is a class rather than two bugs.

  A Setext heading's content is the **whole** preceding paragraph (CommonMark
  4.3), and the round-14 check read the line directly above the underline — so
  `/// This is not a contract`, `/// Safety`, `/// ===` satisfied a gate whose
  subject is what a caller is told, while rustdoc titles that heading "This is
  not a contract Safety".  Fail-open, on the gate with an empty baseline.  And
  the frozen surface's differential coverage table said `.reply` was checked
  against `endpointReply` — the **bare** reply, a *leg*.  The live `.reply`
  *operation* is that leg plus the donation return plus a priority-inheritance
  revert, and nothing compared the frozen composite against it, so "reply:
  checked" stood through **four consecutive review rounds** in which that
  composite was found to be missing the donation pop, then the server's
  deschedule, then the inheritance revert, then a missing-server refusal.
  (Round 22 corrected the *counterpart* this round chose: the leg differential
  runs against `endpointReplyOnCore` and the operation one against
  `endpointReplyCrossCoreDispatch`, both read out of `frozenBranchLiveLeg` /
  `frozenBranchLiveOperation` rather than named in a comment.  Do not cite this
  paragraph for either name.)  In
  both cases the check ran, reported truthfully about the unit it examined, and
  that unit was not the one the claim was read as being about.

  **So name the unit in the claim, and make the smaller claim unable to stand in
  for the larger.**  The heading verdict is taken from the paragraph's first
  line, where its content begins.  The coverage table gained a second, separate
  claim (`frozenBranchOperationChecked`) with its own scenario list reconciled in
  both directions, three `decide` interlocks, and — the load-bearing part — a
  *stated reason* on every branch that has only a leg check, so the next step
  composed onto a live operation is a row somebody has to write.  Merging the two
  lists would have re-created the defect inside its own remedy.

  Two corollaries, both earned.  **A new unit changes which leaf blocks matter**:
  carrying the paragraph's first line means a thematic break and an ATX heading
  must now end the paragraph, one in each direction — the break so `Safety` /
  `***` / `===` is refused, the heading so `# Overview` / `Safety` / `===` is
  *accepted* — and each needs its own mutation, since a case that survives the
  pre-fix code tests nothing.  And **a mechanism worth building finds something
  on its first run**: the operation-level differential immediately failed, on a
  bug in the same cut's own fix — `frozenUpdatePipBoost` looked for the thread in
  the bucket its *old effective priority* names, where the live `updatePipBoost`
  asks whether the thread is in the queue at all and removes it from wherever it
  is.  The divergence is visible only on a state where a thread's bucket and its
  effective priority have already drifted apart, which is precisely the state a
  reversion exists to repair.  A mechanism that passes everything on the day it
  lands has not yet been shown to measure anything.

  **And when a real front-end exists, the scanner is not the authority — hand it
  the question** (the maintainer's instruction, `v0.35.28`).  The rule above
  fixes a verdict taken at the wrong unit; this one retires the artefact that
  kept taking them.  Round 14 registered the generalisation as debt and round
  15's P1 was the **seventh consecutive round** to find a defect in the same
  hand-written front-end, which is the measurement that registering it again was
  not the move.

  *The `unsafe` question's front-end is rustc; the `# Safety` question's is
  rustdoc.*  `sele4n-hal` and `sele4n-abi` deny
  `clippy::undocumented_unsafe_blocks` and `clippy::missing_safety_doc` at their
  crate roots.  The first is rustc's own parse of the block and of the comment
  run above it — no `//` versus `/*` versus `r#unsafe` versus attribute-nesting
  question can be got wrong, because there is no second parser to get it wrong
  in.  The second renders the item's documentation with the parser rustdoc uses,
  so fences, HTML blocks, Setext underlines and raw doc literals — four of the
  last seven rounds' findings — are decided by the tool whose output the caller
  actually reads.

  **Two things about turning a lint on were established by mutation, and either
  would have shipped a false green.**  `cargo clippy -- -W <lint>` reaches only
  the final compilation unit and is **silent** for every workspace member: the
  first run reported zero findings and deleting a real `// SAFETY:` comment
  still reported zero.  And the host lane cannot see the
  `#[cfg(target_arch = "aarch64")]` majority of a HAL: the same deletion yields
  **0** findings on the host and **2** on `aarch64-unknown-none`.  *A lint that
  is not running is indistinguishable from a lint that passes*, which is this
  file's inert-witness rule arriving at a tool nobody thinks to test.  Delete a
  real justification and watch the lane you rely on fail before believing it.

  **The scanner stays, and says what it now owns.**  Tier 0 runs before any
  build, so the fast approximation is still worth having; and three things
  structurally escape the lints — a non-`pub` `unsafe fn`, an `unsafe fn`
  declared inside an `extern` block (no lint requires a contract of a *foreign*
  declaration, and this tree has ten Lean upcalls that need one), and the ARM ARM
  citation census.  Its output prints its authority and its residue beside its
  ratio, because a number that implies an authority it does not have is the
  defect this section keeps recording.

  **And the same instruction applied inwards: a mirror must not re-answer a
  question that has a live answer.**  The round-15 frozen fix added five
  hand-written counterparts of live functions, which is more of the duplication
  that produced the churn.  Two were pure questions about a `TCB` record — and
  the frozen store holds the **live** `TCB` — so they are the live accessors
  now: `TCB.boostedPriority` and `TCB.blockingServer?`
  (`Model/Object/Types.lean`).  Under them sits `Priority.raisedBy`
  (`Prelude.lean`), "a base raised by an inherited boost", which was written
  inline at **eleven** sites across the scheduler, the IPC wake path, the
  priority-setting path and the frozen run queue.  Its base is a **parameter**
  because it is not always the thread's own: a `.bound` thread's base is its
  reservation's.  Fixing it at the TCB would have covered ten of eleven and left
  the eleventh spelling its own `match` — *an abstraction that does not fit its
  subject is how a duplicate survives a de-duplication.*

  Three things that cut records.  **An accessor ships with its frame**:
  `TCB.blockingServer?_congr` and `TCB.boostedPriority_congr` say which fields
  each reads, because a consumer that instead unfolds the accessor inside a
  `filterMap` also rewrites the tail's *bound* occurrences and desynchronises the
  induction hypothesis — a hazard one proof in `Compute.lean` had already
  documented one level up, and which reappeared the moment the accessor was
  introduced.  **A pin is not a substitute for an upstream answer, and a pin whose subject is
  gone is deleted, not kept**: `effectiveRunQueuePriority` and
  `ipcEffectiveRunQueuePriority` were two bodies because importing the scheduler
  from the IPC module would close an import cycle, held together by a `rfl`
  obligation stated in the first module that sees both names.  That pin is
  exactly what this project prescribes when a second implementation must exist —
  and it need not have existed, because the shared answer belongs in the
  **model**, upstream of both, where the cycle objection never applied.  *Look
  for the upstream home before reaching for the pin.*  Both names are now gone
  and every site calls `TCB.boostedPriority`; the pin went with them, because
  once one side is deleted it has no subject, and a theorem that can only be
  `rfl` asserts nothing while reading like a check — this file's own
  inert-witness defect, arriving as the *residue of a de-duplication*.  A pin is
  worth exactly the divergence it can still see.  And
  **the de-duplication's own grep missed a copy**: `effectiveBucketPriority`
  binds its base with a `let`, so a search for `Nat.max tcb.priority.val` did not
  see it; it surfaced only when a proof stopped closing.

  **And a fix retires more than it changes — sweep what was PINNING the thing
  you deleted** (PR #895 review round 16, `v0.35.29`).  Three findings, and the
  honest reading of them is that two were rules already in this file applied at
  one site and not at its sibling: `classify_extern_item` decided a foreign
  item's kind by *searching its interior*, which is round 15's wrong-unit rule
  one artefact over (the question is what the item **starts** with, so
  `decl!(#[doc = "…"] fn fake());` read as a plain `fn` and the macro was
  consumed rather than refused); and `lean_store_read_census.py` classified over
  raw bytes while its own `_SIGNATURE_END` comment asserted the view had blanked
  strings, which is *gates read code, prose reads prose* — the shared overlay
  keeps string contents **deliberately**, because a Tier 3 anchor may be about
  what an `asm!` template puts in the symbol table, and this census's question
  needs them gone.  The third is round 13's *a new axis is enumerated at all of
  its values*: the fence axis knew that a fence hides a heading and not
  CommonMark 4.5's rule that a **backtick** fence's info string may hold no
  backtick, so ```` ```rust`x ```` opened a fence that does not exist.

  The one worth writing down is the fourth, which no review reported and which
  the first fix *created*.  Replacing the interior search retired
  `_EXTERN_FN_ITEM`, `_MACRO_INVOCATION` and `_EXTERN_NON_FN_ITEM` — and a Tier
  3 anchor named the third, so it went on reporting PASS over a definition the
  classifier no longer consulted.  **A pin on a dead symbol is a tautology**: it
  says nothing about the live code while reading in the report exactly like a
  check that decides something.  And the way one is made is not by writing a bad
  anchor — the anchor was correct when written — but by **deleting the thing it
  watched**.  So a fix's blast radius includes the artefacts that watch what it
  changed, and those fail *silently by construction*, since reporting PASS is
  their ordinary output.  When a cut retires a definition, sweep every anchor,
  baseline, registry and census that names it.

  Two mechanical consequences.  The anchor is repointed at the symbol's **read**
  rather than its definition, because a pin on a definition is a presence check
  even when the symbol is live — the set can be defined here and consulted
  nowhere, which is the same tautology one step later.  And, this being the
  second tautological pin this PR has been shown, the response is the round-9
  one rather than a third telling: `scripts/check_anchor_symbol_liveness.py`
  (Tier 0) refuses any Tier 3 anchor naming a Python symbol its target binds and
  the tracked tree never reads.  Its domain is derived on both sides, a target
  that is missing or unparseable **fails** rather than being skipped, and its
  decisive case keeps the anchor and the definition and adds only a reader.


  And the same reading applied to the fix itself: `_skip_item_prelude` first
  re-derived the `[` position from a raw regex match and carried its own
  bracket-matching loop, while `attribute_opens_at` already answered the first
  and `attribute_spans` already inlined the second.  Both are one answer now,
  and the payoff is measured rather than asserted — one token-preserving
  mutation of `_matching_square` fails the self-tests of `rust_code_view`,
  `check_unsafe_block_justifications.py` **and** `check_kernel_entry_exports.py`.
  *Before writing a helper, find the one this tree already has.*

  Finally, the evidence for preferring a sweep to a count.  `v0.35.28` recorded
  `Priority.raisedBy` as collapsing **eleven** inline spellings; re-running the
  search over the landed cut found a **twelfth**, in
  `schedContextConfigureBoundPropagate`, which computed the bucket a reconfigured
  thread moves to from its `priority` argument while storing the record beside
  it.  It reads the stored record now, and the collapse is definitionally
  identical.  *A number in a changelog is what one search found; it is not the
  set.*

  **And a proxy can be the LENIENT side — check which tool the property is
  about** (PR #895 review round 17, `v0.35.30`).  Two findings, both in code
  written for round 16, which is five consecutive rounds landing in the previous
  round's fixes.  The first is this file's own *a recognised set is not a derived
  set* applied to a gate's **domain**, in the gate written last cut to close that
  shape one level up: `check_anchor_symbol_liveness.py` unioned every name read
  in any tracked module, so an unrelated `def helper(_DEAD)` kept a dead anchor
  green.  A read is **resolved** to the anchored module's symbol now — the
  target's own scope, an attribute on the imported module (plain or aliased), or
  a `from` import — with intra-module scope decided by **`symtable`**, CPython's
  own analysis, so shadowing by a parameter, comprehension target or nested `def`
  is not a form to enumerate.  *Round 17's instruction — ask the language's own
  front-end — applies to Python too, and `symtable` is it.*

  The second is why this entry exists.  `MD_SAFETY_HEADING` matched `Safety`
  case-insensitively on a word boundary, accepting four spellings
  `clippy::missing_safety_doc` rejects — and clippy does not examine a **private**
  `unsafe fn`, so there this scanner is the only enforcement.  The accepted set
  was then **measured** rather than recalled, with one `pub unsafe fn` per
  spelling compiled under the workspace's own clippy: `Safety`, `SAFETY`,
  `Implementation safety`, `Implementation Safety`.  That mattered in both
  directions — the review proposed restricting to the first two, which would have
  refused the two clippy accepts.

  **And the measurement found the two authorities disagreeing.**  For a Setext
  heading whose underlined paragraph spans lines, `cargo doc` renders
  `id="safetyand-more-text"` and `id="this-is-not-a-contractsafety"` — neither
  publishes a Safety section — while clippy **accepts both**, comparing each Text
  event of the heading rather than the heading's text.  On this shape the lint is
  the *lenient* one.  `v0.35.28` said the `# Safety` question's front-end is
  rustdoc and then reached for the lint that approximates it; the gate follows the
  **rendering**, because that is what a caller reads, and requires the paragraph
  to be a single line.  *So "hand the question to the real front-end" is not
  finished by naming a tool: when two tools answer, the one the property is
  defined by wins, and which that is has to be checked rather than assumed.*

  Two mechanical notes.  A previous round's recorded expectation is evidence, not
  authority: round 15's control asserted `True` for the multi-line Setext form on
  the strength of the first-line rule it had just introduced, and measurement
  corrected it while **vindicating** that round's actual finding.  And a
  hand-kept figure beside a derivation drifts on contact — the liveness gate's
  self-test printed `len(_CASES) + 3`, already wrong by two; it counts the checks
  that ran.

  **And an approximation is not the oracle — check whether the exact answer is
  already in reach** (PR #895 review round 18).  Three findings, all three in
  code this PR wrote, and all three the same thing: a gate deciding a question
  about a *language* with a pattern written by hand.  Round 14 named that class
  and registered it as debt on the reasoning that the remedy is "a reconciliation
  against the real tools — work, not wording".  Round 18 is the evidence that the
  deferral was partly wrong: **two of the three had an exact oracle in the
  standard library the whole time**, and the reason nobody used it is that nobody
  asked whether one existed.

  The identifier case is the clearest.  `[^\W\d]` is Python's *word* class and
  the question was `XID_Start`; rustc accepts `pub unsafe fn \u2118()` (Sm),
  `\u212e()` (So) and `\u1885()` (Mn), and `\w` matches none of them, so a
  declaration spelled with one raised **no obligation at all** and then failed
  its file as an unrecognised form.  Round 12 had already widened this class once
  for the same reason, which is the signal: *a class that needs widening a second
  time is not a class, it is a table someone is guessing at.*  **Python's
  identifier grammar is UAX#31 — the same one Rust uses** — so `str.isidentifier()`
  answers it, and the agreement is measured rather than assumed: over 28
  codepoints spanning every plausible category, 27 agree and the sole divergence
  is a lone `_`, which Python accepts as a whole identifier and Rust reserves as
  the wildcard.

  **That reading was half right, and round 21 supplies the other half.**  The
  rule really is shared; the *table* is not, and the 28-codepoint probe could
  not see that because every one of its codepoints was assigned in both
  editions.  `str.isidentifier()` was retired one round later — see **an oracle
  is exact only up to the version of the data it reads** below — so do not cite
  this paragraph as licence to reach for it.

  Two corollaries.  **The reach of a fix is the question, not the finding**: the
  reported site was one gate's declaration scanner, and the same question was
  being asked by seven hand-written classes across five files — so the remedy is
  round 9's, not a seventh patch.  One fragment derived from the oracle, and
  `bare_ident_literals` refusing a new ASCII class in any gate source, with
  `NON_RUST_IDENT_SOURCES` naming the files that legitimately ask a *different*
  language's question (a POSIX shell variable, a GAS label and a Lean identifier
  are all ASCII by their own grammars) and reconciled in both directions, so a
  stale classification fails as loudly as an unclassified pattern.  And **a
  measurement can carry the defect it is sizing**: the first scan for rebound
  import aliases reported three, all false, because it counted
  `os.environ["X"] = "y"` as rebinding `os` — a `Subscript` target mutates an
  object and binds no name.  The real count is zero, which is what makes the
  fail-closed fix free; had the false three been believed, the fix would have
  been weakened to accommodate them.

  **And when two authorities disagree, the accepted set is their INTERSECTION —
  and which one is strict can flip** (PR #895 review round 19).  Round 17 found
  `clippy::missing_safety_doc` and rustdoc disagreeing on a multi-line Setext
  heading and took the *rendering*, on the reasoning that the property is what a
  caller reads.  Round 19 is the same axis one level in — **inline markup inside
  the heading** — and it shows that reasoning was half the rule.  Measured on
  fifteen forms under this workspace's own toolchain: they disagree in **both**
  directions.  `` `Safety` ``, `&#83;afety`, `**Saf**ety` and `Saf<!-- c -->ety`
  all render `Safety` and clippy **refuses** each (a code span is a `Code` event;
  the other three split the title across two `Text` events); `[Safety]` clippy
  accepts while rustdoc renders `[Safety]` and warns `broken_intra_doc_links`.
  Following the rendering alone would let Tier 0 green a file the crate's own
  `-D warnings` lint then rejects — so *neither tool is "the" authority*, and
  naming one is not the end of the question even after you have measured it.
  The measurement stands and is what the gate's own output reports; what this
  round *did* with it — accept the intersection, by rendering the heading — was
  superseded one round later, for the reason its own closing paragraph gives.
  See **a rule stated in a docstring is not a rule in the code** below.

  The finding itself was the **fail-closed** direction — `/// # **Safety**`
  refused, a correctly documented `unsafe fn` rejected — which round 6 recorded
  as a defect in its own right and which this section otherwise spends its time
  on the opposite of.  *A spelling is not the text*: a heading's content is
  markup that renders to something else, which is *a spelling is not a read* one
  artefact over, at the one place round 12's "build the artefact" had stopped
  short — it built the markdown document and then matched the heading's raw
  bytes.

  **Two things about this round are worth more than the fix.**  First, round 18
  narrowed the debt row to "Rust item parsing and the CommonMark residue", and
  round 19 landed *inside the residue that row had just named*, one cut later.
  That is the narrowing working as a measurement and **not** working as a
  remedy: **predicting where the next finding will be is not preventing it**, so
  a narrowed row is evidence the analysis is right and no evidence at all that
  the gap is closing.  Second, round 18's own rule was applied *before* writing
  anything — *is an exact oracle in reach?* — and the answer here was **no**: no
  CommonMark implementation is available at Tier 0, which runs before any build.
  Recording the `no` is what makes the bounded reader honest rather than lazy;
  it refuses every inline form it cannot render, which keeps the site in the
  violation set (a visible failure) rather than clearing it silently.

  **And a rule stated in a docstring is not a rule in the code — the narrowest
  gap in this whole section** (PR #895 review round 20).  Round 19 closed by
  applying round 18's rule before writing anything and recording the answer:
  *is an exact oracle in reach?* — **no**, no CommonMark implementation is
  available at Tier 0 — and therefore "it refuses every inline form it cannot
  render".  That sentence is right, it is the correct engineering call, and it
  went into the docstring and into this file.  The code shipped in the same cut
  peeled emphasis runs and extracted link labels by hand.

  Round 20 is the two cells that gap produces, and they are worth naming because
  neither is exotic.  `# ** Safety **` is **inactive** emphasis — CommonMark 6.2:
  a left-flanking delimiter run may not be followed by whitespace — so rustdoc
  renders the asterisks literally and publishes no Safety section, while a
  peeler that strips a matched `**`/`**` pair reads `Safety`.  And
  an ATX heading whose content is a bracketed `Safety` label, an inline
  destination and a trailing `junk)` renders `Safetyjunk)`, while a label
  extractor anchored on the brackets reads `Safety`.  Both were accepted; both are the fail-open
  direction on the gate whose baseline is empty.

  **The distance between a stated rule and an implemented one is where this
  section's findings now live.**  Nine of the last twelve rounds found a defect
  in a hand-written front-end, and this file has said so since round 14 and
  registered it as debt; round 19 went further and *derived the right rule from
  first principles* — and then the hand-written renderer was written anyway,
  because refusing markup felt like it would reject valid documentation.  It
  does not: **measured before choosing**, every Safety heading in this tree is
  already written plainly (26 `/// # Safety`, 3 `/// ## Safety`, 3 `//! #
  Safety`, 2 `//! ## Safety`, zero carrying inline markup), so requiring the
  canonical spelling costs the tree nothing.  *Take the measurement that tells
  you the strict option is free, and the temptation to approximate disappears.*
  The heading's content must now **be** one of the four measured titles; every
  inline form is refused, including the seven both authorities accept, and the
  gate says which kind of refusal each is.  That is round 16's exit —
  **where the subject is code this project writes, require a canonical spelling
  and refuse the rest** — reaching the last construct in this file that was
  still being parsed.

  The round's second finding is the **enumeration** rule meeting a language that
  grew.  `rebound_import_names` was a hand-written `ast` walk over binding
  constructs, and the review reported one it missed: a `match` capture.
  Measuring the walk rather than patching the reported cell found the shape — it
  handled *every* binder Python had before PEP 634 and **none** of structural
  pattern matching's, which is four forms, not one.  An enumeration of a
  language's binders is a list of the ones that existed when it was written, so
  the next grammar addition empties it silently.  The exit is round 18's, and
  the oracle was already imported in the very cut that wrote the walk:
  **`symtable` is CPython's own binding analysis**, and `is_assigned()` is False
  for a name bound only by an import and True the moment anything else binds it.
  The enumeration is deleted; all eleven forms and both non-binding controls
  (`x.k[i] = v`, `x.attr = v`) are answered without the oracle being told they
  exist.

  Two mechanical notes, both earned.  **Measure the walk, not the cell**: fixing
  the reported `match` capture alone would have left three siblings live and the
  next round would have supplied one — and the same measurement corrected this
  file's own first draft of this entry, which claimed the walk had missed the
  walrus and `except ... as` too.  It had not; it handled both, and saying
  otherwise would have overstated the finding.  And **a conservative answer is
  defensible only when you have measured what it costs**: the whole-module
  binding query over-refuses a receiver shadowed only in an unrelated function,
  which the docstring declares — and across all 31 tracked `.py` files, zero
  import-bound names are assigned at module scope and zero at nested scope, so
  the conservative query and the exact one agree on the entire tree.  The
  alternative (ask the module scope alone) is fail-**open** for a shadowed read,
  which is the thing the gate exists to catch.

  **And an oracle is exact only up to the version of the data it reads**
  (PR #895 review round 21).  Round 18's instruction — *check whether the exact
  answer is already in reach* — is right, and this is the question to ask
  immediately after it: **what edition of what table is that answer computed
  from, and does the other side read the same one?**

  Three P2s, all three fail-**closed**, all three on valid Rust this tree would
  refuse.  `str.isidentifier()` and rustc both implement UAX#31 — the *rule* is
  genuinely shared, which is what made round 18's reasoning sound — but they
  read different editions of the Unicode table it ranges over.  Measured on this
  environment: CPython 3.11 carries Unicode **14.0**, where U+1C89 is
  *unassigned*, while rustc **1.94.1** compiles `pub unsafe fn Ᲊ() {}` with
  nothing worse than an `uncommon_codepoints` warning.  So a documented
  `unsafe fn` named with it raised no obligation and the explicit default branch
  then refused the whole file; and `\b`, defined against `\w`, saw a boundary
  *inside* the valid identifier `unsafeᲉ`, so `\bunsafe\b` matched its first six
  characters and Tier 0 demanded a justification of safe Rust.

  **Round 18's measurement was itself a recognised set** — this file's oldest
  domain rule, arriving inside the evidence that justified an oracle.  Twenty-
  eight codepoints spanning every plausible *category*, and category was the
  wrong axis: every one of them was assigned in both editions, so the probe was
  structurally blind to skew and would have reported 27/28 however far the two
  tables had drifted.  *When a measurement licenses a dependency, ask what it
  could not have seen.*

  The exit is **not** a third table.  Pinning rustc's XID data into a Python
  gate is the enumeration this project keeps retiring, and it goes stale at the
  next toolchain bump.  Instead the *question* changes to one no Unicode release
  can move: **every delimiter, operator and piece of punctuation in Rust source
  is ASCII** — rustc rejects non-ASCII punctuation outright — so outside
  comments and literals a non-ASCII character is part of an identifier.  That
  gives *a character may continue an identifier unless it is ASCII and neither
  alphanumeric nor `_`*, a fact about Rust's **grammar** rather than about a
  codepoint table, and for the two questions this tree actually asks it is
  **exact rather than merely safe**: a keyword adjacent to an identifier
  character is not a keyword but one longer identifier, and a name is only ever
  terminated by ASCII punctuation.  Where it does over-approximate — `×` and `·`
  are admitted and rustc refuses them — the self-test *asserts the
  over-approximation* rather than leaving a reader to rediscover it, because
  neither can stand beside a name in code that compiles.

  Two things the fix records.  **A retired oracle takes its dead API with it**:
  `is_rust_identifier` existed only to state round 18's `_` divergence, its sole
  readers were its own self-test rows, and its body was the retired call — a pin
  on a question nothing asks, which this file already names a tautology, so it
  is deleted rather than rewritten.  And **free exactness is still worth
  taking**: `ident_start` excludes ASCII digits, because `0-9` is a fact about
  ASCII and costs no table, even though the class beyond ASCII stays generous.

  The round's third finding is the same *whose question is this* shape in a
  different artefact.  `CARGO_TARGET_DIR` is **cargo's** setting, so a relative
  value resolves from the **invocation** directory; the gate joined it onto
  whatever root its scan had narrowed to, so `CARGO_TARGET_DIR=rust/target` run
  from the repository root excluded `rust/rust/target` — which does not exist —
  while cargo wrote to `rust/target`, which was therefore scanned.  Generated
  `.rs` under a build script's `OUT_DIR` is code no contributor wrote, so an
  unsafe site there would have failed Tier 0 against a file nobody can edit.
  *When you honour another tool's setting, resolve it the way that tool does.*

  **And the sweep found a fourth, in the check written to make sweeps
  unnecessary.**  Running this round's own rule — *when a fix names a relation,
  grep for every other place that asks it* — over Python's `\b` turned up two
  more Rust-keyword boundaries, and the reason `bare_keyword_literals` had not
  reported them is that it recognised **one shape**: `\b<keyword>\b`, a single
  keyword with a boundary on each side.  A keyword inside an alternation with a
  `\s+` tail (`check_claim_evidence_citations.py`'s Rust declaration head) and
  a one-sided boundary (`check_tlbi_broadcast_discipline.py`'s FFI export
  pattern) were both invisible.  Round 9 built that check so "the next such
  pattern fails on the day it is written"; **a discipline check that enumerates
  the shapes it has seen is the defect it exists to close, one level down.**

  The question is widened to the one being asked — *does this regex literal use
  a word boundary while naming a scanned keyword as a whole word?* — which
  over-approximates deliberately, because the remedy for a false positive is to
  compose `keyword()`, which is what the author wanted anyway; a literal
  genuinely asking another language's question goes in
  `NON_RUST_KEYWORD_SOURCES`, reconciled in both directions like every other
  classification here.

  One mechanical note, and it is this file's own rule repaying its cost
  immediately.  The widened question was first written to search the raw line,
  and the `b` of `\b` is an identifier character — so the whole-word lookbehind
  failed on `\bunsafe\b` and the derived question **missed the very spelling it
  subsumes**.  Nothing on the live tree would have caught that, because the
  plain pattern still ran beside it; what caught it was the witness asserting
  the *unchanged* row next to the new ones. **Keep the rows a fix does not
  change** — that is what distinguishes a fix that generalises from one that
  merely moves. A two-character regex escape is one token, so escapes are
  blanked before the keyword question is asked.
  **And the name a claim cites is its load-bearing half, so it cannot live in a
  comment** (PR #895 review round 22).  Four findings, and the pattern across
  them is one this file has been circling: three are *my own previous rounds'
  fixes*, and the fourth is a coverage claim whose counterpart was prose.

  The narrow one first, because it is the sweep rule failing at the smallest
  possible distance.  Round 14 found that **an angle bracket is not always a
  delimiter** — an array length and a const-generic argument are const
  *expressions*, so `[u8; 1 << 2]` in a signature raises a `<`-counting depth
  twice with nothing to lower it — and fixed it in `extern_block_items`, writing
  the reasoning into that function's docstring.  Round 18 then wrote
  `_body_open_brace` **one function above it**, counting `<` unconditionally,
  under a docstring asserting the opposite of the grammar (*"a comparison or a
  shift cannot appear in a type"*).  Both directions shipped: `-> [u8; 1 << 2]`
  never finds the body, and `-> [u8; 8 >> 1]` clamps the shared counter at zero
  and then lets the closing `]` drive it negative.  Each answers `FILE_SCOPE`,
  which no allowlist entry matches — so a **justified** site inside such a
  function is reported unjustified, Tier 0 refusing valid Rust.

  The remedy is not round 14's, and the difference is the point: dropping angle
  brackets is right when the subject is a `;` (which `[` and `{` already cover)
  and wrong when the subject **is** a brace, since `-> Foo<{ 1 }> { .. }` would
  answer with the const-generic block.  Two counters, with `<`/`>` read **only
  outside every bracket group**, is *exact* rather than merely safe, and for the
  reason round 14 gave: Rust requires a non-trivial const argument to be braced
  and an array length to sit inside `[` … `]`, so an operator `<` is always
  inside a bracket group and a delimiter `<` never is.  **The same grammatical
  fact answers both questions; only the direction differs.**

  **And the remedy for F1 is not the patch — it is that the question now has one
  owner.**  Two scans in that file asked *where does a Rust signature end*: one
  for the `;` that terminates a foreign item, one for the `{` that opens a body.
  The nesting rule is identical for both and was written twice, and the second
  copy reintroduced the defect the first had removed.  Patching the second would
  have left the file in exactly the state that produced the finding, so
  `signature_terminator` states the rule once — brackets nest, angles nest only
  at bracket depth zero, `->` is one token, a terminator counts only at zero on
  both counters — and both scans read it, differing only in which characters they
  pass as terminators.  The payoff is measured rather than asserted: **one**
  token-preserving mutation of that function now fails **four** witnesses across
  *both* questions, where before it would have failed only the body rows.

  That is the round-7 remedy (*give the sweep an artefact*), and round 9's lesson
  says it is not sufficient — sharing an answer stops two implementations from
  diverging and does not stop a **third** from being written beside them.  So the
  discipline is enforced too: `hand_rolled_angle_nesting()` refuses an
  angle-bracket *character* test anywhere in that file outside the owner, which
  is the shape such a scan is written in.  **The scope was measured before it was
  chosen** — the file holds exactly two such tests and both are in the owner,
  while every other one under `scripts/` asks a different language's question
  (Lean notation, a Lean arrow, a Markdown autolink, a CommonMark HTML-block end
  condition, a regex group name), so a whole-repository check would be mostly
  classification and this one costs nothing.  It is pinned in **both**
  directions, because a discipline check that cannot fire is indistinguishable
  from one that is wrong: removing the owner's exemption makes it report the
  owner's own two tests, and a probe appends a second implementation to a copy of
  the file and requires a hit.  Two things that probe records — a fixture must
  not be **self-referential** (the first version anchored on a `def` line whose
  text the probe's own source also contained, so the splice landed inside a
  string literal and the copy would not parse) and it builds its `<` from
  `chr(60)`, because a literal there would be a hit in the probe's own source and
  exempting the probe by location is the hole the check exists to refuse.

  The two other scanner findings are the same shape at their own level.  A
  foreign declaration may mark itself `unsafe` (RFC 3484's per-item marker,
  whose `safe fn` opt-out the gate already read), so the keyword pass **and**
  the foreign-item pass both yielded it: one declaration, two rows, every total
  and any baseline doubled — and invisible to a case list that only asks
  *"is each site found justified?"*, since both rows carry the same good
  justification.  A cardinality defect needs a cardinality witness, so the
  gate grew `_SITE_INVENTORY_CASES`, which name the declarations a fixture must
  produce and fail on a repeat.  The region now belongs to exactly one pass, and
  the direction is forced: the foreign walk is *derived* from the item structure
  and refuses a form it cannot read, so nothing inside the braces escapes it,
  while the keyword pass sees only what carries the token.  And
  `check_anchor_symbol_liveness.py` — the gate written last round to retire
  tautological pins — asked *"does this name occur as a global read"* where its
  question is *"does anything else read it"*, so `def _dead(n): return
  _dead(n - 1)` kept its own anchor alive.  That is this file's oldest rule
  inside the gate built to close one instance of it; reads are **attributed** to
  the declaration they occur in now, nesting carried, with the cycle residue
  stated rather than assumed away.

  The fourth is the one worth the entry's title.  Round 15 fixed *a claim made
  at the wrong UNIT* — leg versus operation — and left **which instance** of the
  unit, in a **comment**: `frozenBranchOperationChecked`'s only `true` row said
  it was checked against `endpointReplyWithDonation`.  That is the *single-core*
  composite, with no production caller, and it opens with the bare
  `endpointReply`, which keeps the `replier == expected` gate the cross-core
  spelling dropped (PR #822 review 6J-lYm: authority is the presented reply
  capability, and seL4-MCS reply caps are delegatable).  The live `.reply` arm
  dispatches `endpointReplyCrossCoreDispatch`, which accepts a delegate — and so
  does `frozenEndpointReply`.  So on a delegated input the frozen composite
  agrees with the **kernel** and disagrees with the named counterpart, and the
  row's `true` was read as the former.  Latent only because every fixture made
  the replier *be* the recorded server, where the two counterparts coincide.

  **A counterpart named in prose is a claim nothing reconciles**, so both
  counterparts are data now (`frozenBranchLiveOperation`,
  `frozenBranchLiveLeg`), each with a both-directions interlock — and the leg
  table is the sweep this round owed, because it asked the identical question
  with the identical answer wrong, which is round 11's *keep the tables
  symmetric* one artefact over.  A string is not a check and does not pretend to
  be: what pins the counterpart is a theorem **pair**,
  `endpointReplyCrossCoreDispatch_independent_of_replier` and
  `endpointReplyWithDonation_refuses_delegated_replier`, which together say the
  two are not interchangeable — the lesson `API.lean`'s `syscallDelegates`
  records from its own review round 11, that a *name* establishes a declaration
  exists and not that it says anything about the claim citing it.  The scenarios
  carry the delegated shape and assert the superseded composite **refuses** it,
  so the choice is measured at the point of use.  And the live steps the
  differential does not reach — the fault branch and the WS-RA delivered-message
  staging that `replyTransferOnCore` wraps the spine in — are **stated**
  (`frozenBranchOperationFrontier`) rather than implied, because a claim that
  stops at "checked" implies an authority over the whole arm it does not have.

  **And a bare NAME is not a declaration either — a suffix rename defeats it**
  (WS-RR RR8.16, `v0.35.197`–`v0.35.198`).  The same substitution at the
  smallest unit an anchor has: `rg '^theorem foo'` matches `theorem fooX`, so an
  anchor over a declaration with **no other consumer** — which is exactly what
  these anchors exist for — goes on reporting PASS once the name it pins is
  gone.  That is the tautological pin this file already retires, reached by a
  *rename* rather than by a deletion.  Cut C3b-iv (`v0.35.170`) recorded the
  rule, fixed the one anchor it was written for, and left the class; measured
  at **2543** of the tree's positive anchors.  Three things follow.  **Bound the
  name** with the delimiters a declaration name can be followed by — a class
  containing no alphanumeric, so the identifier-naming gate does not read a
  workstream code in it, and one both `rg` and the PCRE `grep` shim accept.
  **Negatives are out of scope**, and that is a decision rather than an
  omission: bounding a positive is strictly stricter, while bounding a negative
  can stop it firing on a name it was catching, so each of the tree's 27 is a
  judgement.  And **the sweep is driven by the gate's own anchor parser, not by
  a second regex** — a hand-rolled pattern is a recognised set and the parser is
  the derived one, which is what found the last 41 sites the hand-rolled sweep
  missed.  `unbounded_declaration_anchors`
  (`scripts/check_anchor_consistency.py`, Tier 0) refuses a new bare positive,
  with a deliberate FAMILY count — an `rg -c` against a threshold, where the
  prefix **is** the question — registered and reconciled both ways.  The sweep's
  own measurement is the argument for it: **eight anchors pinned nothing they
  name**, six naming the prefix `_preserves_ipcInvariant` where the declaration
  is `_preserves_ipcInvariantFull`, and one naming a file whose bare match was a
  different declaration entirely.
  **And an unbounded gap is not a region** (WS-OD OD3).  The region-scoped rule
  above assumes the scanner *has* a region; the cheapest way to write an anchor
  of the form "declaration `X` has property `Y`" is `X(.|\n)*Y`, and that gap runs
  to the end of the file.  The anchor then asserts only that `X` occurs somewhere
  before `Y` occurs somewhere — a presence check wearing the relation's comment —
  and it fails **open** in a positive check and fires spuriously in a negative
  one.  Both directions were live in `test_tier3_invariant_surface.sh`: a
  negative fired on a clean tree because it reached an unrelated theorem's
  hypothesis, and **eight positives were satisfied by text spanning a declaration
  boundary**, one of them crossing 43 declarations, so a lock footprint could have
  lost the member its anchor exists to pin with the gate still reporting PASS.
  Write the gap as `[^\n]*(\n([ \t][^\n]*)?)*` — the rest of the line, then any
  run of indented or blank lines — which cannot leave the declaration it started
  in, because a Lean declaration header sits at column 0.  Two earlier rounds had
  found this and abandoned the wildcard at the one site each was shown; the
  comments recording both were still in the file beside forty-nine live
  instances, which is the sweep rule failing in the way it describes.  **Bounding
  a positive is always safe** (strictly stricter, so it can only fail closed);
  bounding a negative is not, so each negative bounded in that sweep was
  mutation-tested in both directions — silent on the clean tree, firing on a
  mutation that keeps the token and moves it into the target declaration.

  **Three mechanical facts about writing one, two earned at `v0.35.140` and one
  at `v0.35.173`.**  The
  gap stops at the *first* column-0 line, so it cannot cross a **multi-line
  signature's own closing line** — a Python `) -> set[tuple[str, int]]:` or the
  equivalent sits at column 0 and is not a continuation.  That is the bound
  working rather than a defect, and the answer is to anchor from a line that is
  *inside* the declaration and unique to it (its docstring's first line), never to
  widen the gap.  And a `\"` inside a double-quoted `rg` argument inside single
  shell quotes **ends the argument early**, so an anchor over a Python or Lean
  docstring marker writes the quote `\x22`: the shell-quoting failure does not
  error, it silently decides nothing, which is the one outcome
  `check_anchor_consistency.py` exists to refuse.  And **a Lean `Name` literal's
  `` `` `` inside a double-quoted `bash -lc` argument is an EMPTY command
  substitution**, so it deletes itself from the pattern: five anchors written that
  way at `v0.35.173` searched for `whnfUntil applied SeLe4n.Kernel.…` — a string
  the file does not contain — and the changed-file sweep *deferred* all five as
  "substitutes a command" while printing PASS, so a mutation run over them reported
  every mutation as missed.  An anchor over a Lean name is written as bare argv
  with a single-quoted pattern (`run_check "INVARIANT" rg -F -n '``X.Y' file`),
  never through `bash -lc`; and the deferral **count** in a sweep's own epilogue is
  part of its verdict, not decoration.

  **And a DELIMITER that can occur in the data is not a delimiter** (PR #897's
  review, `v0.35.150`).  Six findings, one class, and it is this family's
  *domain* half rather than its predicate half: each gate answered "nothing
  here" for input it could not determine, which is silent by construction — the
  element is never examined, no count moves, and the report reads as a
  measurement of absence.

  The sharpest is in **shared infrastructure**.  `indexed_source.indexed_contents`
  wrote one `cat-file --batch` request per LINE and read one header per line, and
  a tracked path is a byte string that may hold a newline — which `listed_at`
  deliberately preserves, `-z` being exactly what it buys.  Measured: a two-file
  index in which one name holds a newline returned `{}`, **both** files absent
  and no exception, so every gate reading the staged domain through that helper
  reported a clean tree.  Three things the fix records.  `-Z` frames both
  directions, and git documents `-z` as deprecated *because the output stays
  ambiguous* — a framing fixed on one side only is half a framing.  The declared
  size is **checked against its terminator** rather than trusted, since `find`ing
  the next NUL re-synchronises after any drift and an off-by-one is absorbed at
  every entry.  And the walk must **consume the whole stream**: one response per
  request, which is precisely what the original defect violated (git answered
  three times for two wanted entries) and which no per-entry check can see.

  Five rules generalise from the six.  **A recorded failure must FAIL** — the
  changed-file anchor sweep's epilogue called `record_failure`, which only
  counts, on a path that never reaches `finalize_report`, so an anchor ending in
  `exit 0` printed the failure and the gate exited 0; the existing
  fatal-expansion control could not see it, because `set -u` exits 1 and the two
  agreed by accident.  **A rebinding is not a use** — crediting a bound fixture
  path when its name "occurs again" is satisfied by a second *assignment*, so a
  consumer that spells a path, overwrites the name and opens nothing passed the
  claim that the row names a gate which reads it.  **A call is not classifiable**
  — whether a call alters its argument before `lake` sees it is not a question a
  source scanner answers, so the probe locator's builder/consumer split (is the
  result used?  is the argument a `Name`?) was two proxies for an undecidable
  fact, and both were defeated within two review rounds; the exit is round 16's,
  *require a canonical spelling and refuse the rest* — probe text reaches Lean
  through a named template and `.replace` over literals, never as a call
  argument, with one structurally-incapable sink (`ast.parse` returns an AST)
  exempt by **resolution** rather than by spelling and reconciled both ways.
  **Every binding TARGET is seen** — a walk that skips any target which is not a
  bare `ast.Name` leaves `(PROBE,) = (<probe text>,)` binding nothing, so the
  name denotes no text and a transform through it builds a string carrying no
  marker: invisible in both directions at once.  And **the sweep is run, not
  stated** — `check_identifier_naming`'s own module docs record NUL-delimited
  discovery as its item 8, and seven sibling listings across five gates were
  still splitting on whitespace; the same sweep found a **third** copy of the
  `cat-file` loop that `v0.35.147` had collapsed two of.

  Two things about witnessing this class.  A mutation that keeps every token and
  changes the framing is caught only by a case whose *input* carries the
  delimiter — a fixture built from well-formed bytes proves nothing about a path
  with a newline in it, and the decisive cases here are git-driven because what
  was wrong is the REQUEST, which no parser fixture can exercise.  And **a
  harness that crashes where it should report hides the second defect**: a
  refusal raised on a success-path call escaped `indexed_source`'s self-test as a
  traceback and skipped every case after it, so one mutation masked another until
  the harness started reporting exceptions as case failures.

  **And the sweep found five more, one of them in the gate that blocks
  commits — so the rule gets a CHECK** (PR #897's review, `v0.35.154`).
  `v0.35.150` swept seven sibling listings for this class; the review then
  reported two it had missed, and sweeping the *question* rather than the
  reported spelling found three more.  The worst is
  `scripts/pre-commit-lean-build.sh`, whose `sorry` check reads three
  `mapfile -t` listings: staging `$'a\nb.lean'` holding
  `theorem bad : True := by sorry` produced **no finding**, because
  `git show ":\"a\\nb.lean\""` resolves to no object, so the gate whose stated
  job is to block a `sorry` passed it silently.  `select_changed_anchors` fails
  the same way in the other direction — a path that does not exist matches no
  anchor target, and the sweep reports **clean** while running nothing the real
  change invalidates.

  This file already said *the sweep is run, not stated*, and restating it a third
  time is the move that had failed twice.  `indexed_source.unframed_path_listings`
  is the check, in the module that already owns "run git correctly", wired into
  the self-test Tier 0 runs.  Three things it records.  **A NUL-framed stream
  cannot be piped through a line filter**, so the hook's `.lake/` exclusion became
  a path test rather than a `grep`; the framing is undone by the first consumer
  that splits on newlines.  **A path byte that is not valid UTF-8 must
  round-trip**, so the Python reader decodes with `surrogateescape` rather than
  raising on the one input the framing exists for.  And **the check resolves each
  line into the structure it stands for**, because two drafts of it cried wolf on
  this tree's own text: matching lines reported a diagnostic string, a Tier 3
  anchor quoting the call and a membership predicate, and matching every string
  argument of a call then reported six fixture builders whose arguments merely
  *include* an unrelated `"diff"` and an unrelated `"--cached"` — **a set standing
  in for a sequence, which is this file's own presence-for-relation defect inside
  the check written to close one.**  An argv is contiguous and identified
  structurally: a list whose first element is `"git"`, a callee whose name ends in
  `git`, or a shell command whose *head* word is `git`.  `--error-unmatch` is
  deliberately not a listing option — it prints nothing and is a predicate whose
  answer is the exit status.

  **And the check's OWN domain was a name resemblance, found by this cut's
  anchor sweep rather than by a review.**  `_python_git_argvs` recognised an
  invocation as a list argument whose first element is `"git"` **or a callee
  whose name ends in `git`** — and the second is a resemblance.  Measured over
  the tracked `scripts/*.py`: **30** functions run git, and **6** unframed
  listing call sites reach one through a helper named `g`, every one reported
  clean.  That is *a helper the scanner cannot see is a spelling that evades the
  metric*, inside the check written to close a domain miss, on its first day.
  `_git_wrapper_names` is the relation — a function whose body starts a process
  whose argv begins with the literal `"git"` IS a git wrapper, whatever it is
  called — resolved **intra-module**, because that is what `ast` can decide, with
  the name test **kept beside it** as a pin for the cross-module case rather than
  replaced.  The six sites are **fixed, not exempted**: an exemption is the
  enumeration the check exists to retire, so the harness asks git for paths the
  way the readers it tests do.  And the control is what keeps the derivation from
  becoming *any helper* — a same-shaped function running `hg` is not a wrapper,
  so dropping the `argv[0] == "git"` test fails a case rather than passing
  silently.

  **And the fail-closed fix's CALLER was admitting what it could not read**
  (`v0.35.150`, found by CI rather than by review).  Making a derivation raise
  moves the question to whoever decided it was available, and
  `check_workstream_plan.baseline_refs` decided it with `git rev-parse --verify
  -q <cand>` — an existence check for a ref NAME and a pure **syntax** check for
  a full hex sha, since git turns forty hex digits into a raw object id without
  consulting the object database.  Measured, on a sha this tree does not
  contain: `rev-parse --verify -q <sha>` exits **0**, `<sha>^{commit}` exits 1,
  `ls-tree` exits 128 with `fatal: not a tree object`.  A full hex sha is
  exactly what CI passes, so the guard was exact for every candidate except the
  one that matters, and both CI workflows already peeled — *one question, three
  askers, and the odd one out was the gate*.  `revision_is_readable` is the
  owner; an unreadable candidate is skipped and `baseline_is_complete` says so.

  Three things that cut records, each a rule already in this file arriving at a
  smaller unit.  **A fixture that inherits ambient configuration is not a
  witness**: three of four fixture cases pinned `SELE4N_PLAN_BASE_REF` and one
  did not, so under CI it listed a revision the fixture cannot contain;
  `_fixture_repo` is the one owner and it *pins* rather than pops, since popping
  sends the resolver to its `origin/main` fallback — the ambient repository
  again, one indirection out.  **Two halves can rescue each other**: with the
  peel in place, reverting the fixture leak leaves the suite green, because the
  unreadable sha is skipped and the case silently runs HEAD-only — which a
  *staged* deletion does not need a base for, though a *committed* one does, so
  the same leak one case over is a vacuous pass.  Hermeticity is therefore
  asserted directly, through the resolver inside the fixture, with a hostile
  ambient value by construction.  And **a negative anchor over a retired
  SPELLING is defeated by a reformatting revert**: the first one here kept the
  relation and MISSED its own mutation, because re-inlining the unpeeled call
  across two lines keeps every token and matches no single-line pattern.  Scope
  such a negative to the **location** — `baseline_refs` must not ask git at all
  — which is what makes extracting the owner the fix rather than a tidy-up; it
  then catches the inlined, the reformatted and the renamed-local revert alike.
  The explanatory measurement moves to the owner's docstring in the same step,
  since leaving it behind both duplicates the fact and trips that negative on
  prose.

  **And a RECEIVER may be parenthesised, which is the same substitution at the
  smallest unit a scanner has** (PR #897 review, `v0.35.151`).  The rule above
  polices the *question* a gate asks; this is the one where the question is
  right and the **text** it is asked of has a legal second form.  Lean permits
  redundant brackets around any expression, so `(st.objects)[k]?` *is*
  `st.objects[k]?` — the same access, on the same table — and every store-census
  pattern keys on the receiver's text.  Seven positions ask *which text denotes
  the object table*, the review reported one, and **all seven** keyed on the
  unparenthesised spelling.

  **Measured, and the measurement is what makes it a class rather than a
  nit**: four keyed reads in `Scheduler/Invariant.lean` are already spelled
  `({ st with objects := … }.objects)[tid.toObjId]?`, which `READ` could not
  see.  They sit in a `theorem`, so `STORE_READ_CODE`'s **enforced zero** was
  untouched — by accident, not by construction; the same expression in a `def`
  body walks around it.  That is `v0.35.12`'s *a spelling is not a read* and
  `v0.35.97`'s *a spelling is not a write* at the one position neither cut
  swept, and the qualified branch's second sub-shape
  (`RHTable.erase (spliceOutMidQueueNode st tid).objects k`, which `[\w'.]*`
  structurally cannot span) is a rename away from the same hole, the tree
  already writing that shape at five sites for theorem helpers.

  Three things follow.  **One owner, not seven patches**: `_RECV_OPEN` /
  `_RECV_CLOSE` are composed by every receiver position, so a widening reaches
  all of them by construction — a fix at whichever branch a review names leaves
  the other six open.  **Exact beats safe where the language decides it**:
  `_RECV_CLOSE` admits whitespace only INSIDE the bracket group and never
  between the last `)` and the accessor, because Lean's own lexer separates
  `x[i]` (a subscript) from `x [i]` (an application to a list literal), so
  `f (st.objects) [a, b]` is correctly refused — and that refusal is
  *asserted*, since the widening that admits the one is a whitespace class away
  from admitting the other.  And **the reconciliation is derived**:
  `branch_symmetry_violations` crosses `_TABLE_OPS` with `_OPERATION_SPELLINGS`
  rather than naming two spellings inline, so classifying an operation checks
  it in every spelling and adding a spelling checks it for every operation.

  Two mechanical notes, both earned by running the mutations rather than
  reasoning about them.  **Asking "was anything reported" is satisfied by a
  neighbouring assertion**: dropping the PARENTHESISED SUBSCRIPT check left the
  suite green because no case could reach it, so each reconciliation case now
  names the substring its violation must carry, and the two subscript cases are
  each other's controls — one requires a bracket where Lean does not, the other
  admits none where Lean does.  And **a negative over a spelling the fixtures
  deliberately carry must be scoped to its owner**: `self_test` holds the
  retired patterns as mutation inputs, so a tree-wide negative would fire on
  them; each is bounded to the declaration that must not ask the question the
  retired way, and verified by restoring the pre-fix reading inside it.

  **And a canonical-spelling contract is exactly as strong as its narrowest
  escape** (PR #897 review, `v0.35.152`).  Round 16's exit — *where the subject
  is code this project writes, require a canonical spelling and refuse the rest*
  — is the remedy this section arrives at twice, and `v0.35.150` applied it to
  probe text: *a probe reaches Lean through a named template and a `.replace`
  over literals, never as a call argument*, with one structurally-incapable sink
  (`ast.parse`) exempt "by RESOLUTION rather than by spelling".  Both escapes
  were then keyed on a **resemblance**: the exemption resolved that the receiver
  is *some* import rather than *which module*, so `import probe_builder as ast`
  satisfied it; and the unmodelled-form fallback answered "ordinary value" for a
  `Subscript`, so `[TEMPLATE][0].replace(…)` carried no marker and was not
  refused.  Both measured invisible in both directions at once.  So: **write the
  contract, then audit every branch that lets something past it** — an
  exemption resolves what its table NAMES (a module path, not a binding), and a
  default branch that cannot read its input answers *refuse* when the input
  reaches the thing the contract is about.

  Two corollaries the mutation run produced rather than the review.  **A third
  escape existed and no case reached it**: reverting the `FormattedValue` branch
  left the suite green, and measuring what it alone decides showed
  `f"{TEMPLATE}".replace(…)` passing without it — so the branch was right and
  unwitnessed, which is indistinguishable from wrong until a case is planted.
  And **a fourth clause measured the other way**: a marker-bearing literal
  written inline inside an unmodelled form is refused either way across five
  spellings, because an upstream reconciliation already catches it, so it is
  deleted with its measurement rather than kept for symmetry — *a filter
  positioned where it can only ever be wrong is not a filter*.

  **And "the view you read depends on the question" cuts both ways** (same
  round).  This file states that rule for *structure versus text*; the fixture
  catalogue needed it for *two code views of one language*.  `.sh` and `.py`
  consumers were read RAW under a docstring calling the over-approximation a
  loss of "precision on the diagnostic", and it was not: a shell gate containing
  only `# open("foo.expected")` satisfied the consumer claim, so a fixture could
  be indexed, hashed and opened by no executable code.  Both views already
  existed here, and the reason they are not in the shared overlay stands — a
  Tier 3 anchor may legitimately match a `.sh` or `.py` comment — so the remedy
  is a second table with a **stated** question and a reconciliation refusing the
  two to answer for one suffix, not a third lexer.  Where the existing view
  answers a *different* question, make the difference a **parameter**:
  `strip_shell` blanks a double-quoted span's message text, which is right for
  "which tokens are identifiers" and wrong for "does this script open that
  fixture", so the policy is the caller's and the lexing stays one answer.

  **And an anchor's inputs are not always in its own command.**  `test
  "${CIBUNDLE_CONJUNCTS}" -ge 5` names no path; the file it is about is named by
  the assignment above it.  Relating changed paths to the command alone dropped
  such an anchor from the changed-file selection **entirely** — not deferred,
  not reported, absent — so deleting conjuncts left that sweep green while
  direct Tier 3 failed.  *Resolve the text into the structure it stands for*: a
  variable reference is a reference to its producer, taken as the **last**
  assignment of that name before the anchor, and the relation, the disposition
  and the executed text are one answer.  An unbound name resolves to nothing at
  all rather than to a partial prelude.

  **And a new AXIS is only as good as the values you enumerate on it** (PR #897
  review, `v0.35.153`).  `v0.35.151` gave the store census's symmetry matrix a
  *receiver* axis and enumerated three of its five values; the two it skipped —
  a doubly parenthesised receiver and a NESTED application — were a live hole in
  the qualified branch, whose receiver was a FLAT paren group, so
  `RHTable.erase (f (g st)).objects k` was outside an enforced zero.  That is
  this file's own *a new axis is enumerated at all of its values on the day it is
  added* rule, unrun by the cut that created the axis.  **Take the axis's values
  from the grammar**: a Lean term in projection position is an identifier chain
  or a parenthesised term, which may nest or hold an application that nests, so
  the axis has five values and no others.  The same review found the same
  substitution one derivation over — `_TABLE_TYPE` wrote `(?:SeLe4n\.)?` on one
  of the type's three identifiers, at one of its qualifications, so a binder
  spelled `SeLe4n.Kernel.RobinHood.RHTable …` bound no receiver and its keyed
  accesses were in **neither** census.  A qualified Lean name denotes the same
  constant, so the qualifier is per identifier and bounded by a
  name-continuation lookahead.

  Three things that cut records.  **A regex cannot balance parentheses, so the
  qualified branch over-approximates to the LINE** and says so — a bounded
  nesting depth is the enumeration this file retires, and over-reporting a
  violation stops Tier 0 and names the declaration where under-reporting passes
  silently (measured: zero lines admitted on the live tree).  **The operation
  name's end is not `\b`** — Lean admits `?` in an identifier, so after `get?`
  there is no word boundary, and the crossing reported all three of its qualified
  spellings unrecognised before the branch ever ran against the tree.  And **a
  widening that admits a live site is a finding, not a failure**: the type
  widening surfaced `collectQueueMembers`, whose migration to the state accessor
  was *implemented and then reverted* — the walk and its six theorems port
  cleanly and two proofs shrink, but seven bundle transports in one module stop
  being definitional, against 320+ mentions across twelve files, because taking
  the table is what keeps the predicate unable to mention a non-object field.
  It is recorded in the indirect floor with that measurement.  *When a
  measurement kills the plan, that is the measurement working.*

  **And the view you read depends on the QUESTION, so one function that asks two
  needs two** (PR #897's review, `v0.35.154`).  The rule above is about a *value*
  a scanner could not read; this is about a scanner that read the right value
  through the wrong policy.  `check_fixture_consumers` asks a consumer *where is
  the fixture path mentioned*, which needs string contents **kept** because a
  path IS a string literal, and *is this occurrence of the bound name a read*,
  which needs them **gone** because a name inside a string is not a read.  One
  view answered both, so a consumer spelling `FIXTURE="foo.expected"` and then
  nothing but `echo "FIXTURE"` credited the literal as a use — a fixture could be
  listed in the README, hashed, named in a gate that never opens it, and still
  validate its `Used by` row, which is `v0.35.109`'s own *a checksum is not a
  comparison* one column over, in the check written to close it.

  **`v0.35.152` had already established that the two policies differ** — it gave
  `strip_shell` a `keep_quoted` parameter for exactly this reason — and used only
  one of them; this is that cut's own distinction applied at the second asker.
  Three things follow.  The blanking policy is a **parameter of the caller's
  question, not a second lexer**: `python_code_view` gained `blank_strings`, the
  shape `strip_shell` took two cuts earlier and the one `code_no_strings` has
  carried for Rust all along, so the tree keeps one Python lexer.  The two views
  are **byte-aligned**, which is what lets the mention be located in one and the
  read counted in the other at the same offsets.  And **the reconciliation's
  domain is derived, not the union of the two tables**: the first draft iterated
  `set(A) | set(B)`, so a suffix missing from *both* was in neither set and the
  check was silent about exactly the drop it exists to catch — deleting `.lean`
  from the identifier table was reported by **nothing**, which the mutation run
  said and no amount of reading it would have.  The domain is now what
  `consumer_code_view` can *answer* (`CONSUMER_VIEWS` plus the shared overlay's
  own `_STRIPPERS`), so "is this suffix answerable at all" has one owner.

  **And a LINE is not the declaration, nor is ONE decision drawn from two
  subjects** (PR #897's review, `v0.35.155`).  Two more of this family, and both
  are *the view you read depends on the question* at the level of the SPAN a gate
  reads.  `v0.35.153` over-approximated the store census's qualified branch to the
  LINE — correct reasoning, wrong unit: Lean wraps a long call, so
  `RHTable.insert\n  st.objects k v` matched **nothing** and an executable raw
  write could sit outside `STORE_WRITE_CODE = 0` while the gate printed the zero,
  with `READ` holding the same hole.  The unit is the **declaration**, spelled as
  the bounded gap this tree's anchors already use — a run of characters none of
  which begins a column-0 line, which a Lean declaration header always does — and
  written as one lazy alternation so it is linear rather than a nested quantifier.
  Measured before taking it: over all 405 tracked `.lean` files it admits **zero**
  matches the line bound did not, so the widening is free and every witness is
  planted.  `_WHITESPACE_PLACEMENTS` is the axis at all three of its values with
  `_DECLARATION_CROSSING` as its negative, because a gap that reaches a
  continuation line is one whitespace class away from reaching the next
  declaration's.

  The sibling is the same substitution in a *disposition*:
  `select_changed_anchors` computed `kind` from the anchor ALONE and compared it
  against `SEARCHING_KINDS`, while `missing` and `substitutes` beside it were
  computed from the command WITH its prelude — so a fully resolved threshold
  `test "${N}" -ge 5` reached `defer:tool`, and deleting bundle conjuncts left the
  changed-file sweep green while direct Tier 3 failed.  `v0.35.152` had fixed that
  split for `related`, the *provenance* question, and not for `kind`, the
  *executability* one.  **Recomputing `kind` is not the remedy and the measurement
  says so**: a compound `NAME=$( … ); run_check …` is not a line the classifier
  parses, so every such anchor would become `fail:unparsed` and fail Tier 0 on ten
  anchors that are correctly deferred.  Of eleven anchors with a resolved producer
  exactly **two** are runnable; the nine others are an array assignment the fold
  truncates, an EMPTY array (where the tool would run with no arguments and
  *pass*), a side-effecting `mktemp` feeding a build, or a redirection into the
  tree.  So round 16's exit again — **require a canonical spelling and refuse the
  rest** — with two details the measurement corrected: the substitution's closing
  parenthesis is the LAST character, since a `sed` pattern holds
  `\(theorem\|def\)` and a `[^)]*` bound stopped inside it, refusing one of the
  two anchors the contract exists for; and the pipeline is split on a **lexed
  word** through the module's own `_shell_words`, because a `sed` pattern holds
  `\|` and a `grep` pattern holds `| ` inside quotes.  **And the predicate needs a
  WIRING case of its own**: cases that exercise it directly leave a disposition
  branch which never consults it passing, which is *an unwitnessed condition is
  indistinguishable from a wrong one* at the point where a fix is plugged in.

- **Retired code is removed, not left to pollute the tree.**  When a cut
  supersedes a definition, a theorem, a resolver or a policy, the superseded
  thing is **deleted in the same workstream**, not kept beside its replacement.
  Two readings of one question is the duplication hazard this file spends most
  of its length on; a *retired* reading kept "for reference" is that hazard with
  a note attached, and it reads in a bundle, a footprint or a search result
  exactly like the live one.  The rule is unconditional — a superseded
  declaration has no grace period, and "it might be useful later" is what
  version control is for.

  Six things the WS-HP HP7 sweep (`v0.35.46`) established about doing this
  safely, each of which cost a measurement:

  1. **"Unused" is measured over the code view, and textual reference is not the
     only kind of use.**  A `lockSet_*_size_le` bound has *zero* textual
     consumers and is required **by name** by a Tier 1 census
     (`LockFootprintBoundCensus`, which derives the obligation from each
     footprint's own telescope and decides it by `isDefEq`); Tier 3 anchors
     consume symbols the same way.  A sweep that counted references and deleted
     the zeroes would have removed eleven live bounds.  So: count references over
     `scripts/lean_code_view.py --overlay`, then subtract what a **gate**
     consults — and where a declaration is genuinely consumed by nothing at all,
     anchor it rather than orphan it (next item) or delete it.
  2. **The derivations that replace a retired hypothesis are not retired.**
     HP7's whole content is that three *stated* coherence facts became
     consequences of the head-driven trigger; the theorems that say so
     (`answeredFrameHeadContext?_head_is_answered_reply`, `_donationHeadOf`,
     `_boundThread`) had no consumer either, and deleting them would have left
     the claim "derivable" with nothing behind it.  They are **anchored in Tier
     3** instead, because a derivation nothing consults reads exactly like one
     nobody checked.
  3. **A retired reading a witness needs moves into the witness, private, and
     nowhere else.**  A test that cannot name what it replaced cannot show that
     the replacement changed anything.  So the superseded spelling lives as a
     `private def` in the suite that refutes it —
     `bindingDrivenReplyServerDonation?` in `tests/SmpCrossCoreReplySuite.lean`,
     `bindingDrivenCancelledCallerDonation?` in `tests/SmpCancellationSuite.lean`,
     and `FrozenOpsSuite`'s `FO-042` for the frozen surface — computed beside the
     live one so the assertions are known to discriminate rather than merely to
     pass.  That keeps the *evidence* and deletes the *code*.
  4. **A positive anchor on a deleted symbol becomes a negative.**  `run_check`
     on a name a cut removed fails outright; worse, a `run_negative_check` on one
     silently passes forever, which is the tautological pin this file already
     retires.  Convert each positive to a negative that refuses the symbol
     tree-wide (*it must not come back*), and add a positive on whatever now
     carries the property.
  5. **Deleting a symbol means sweeping every citation of it.**  Prose naming a
     declaration that no longer exists reads exactly like prose naming one that
     does, and the deletion's blast radius includes docstrings, `CLAUDE.md` /
     `AGENTS.md`, the spec, the claim index, GitBook, the debt register, the plan
     and the `CITATION_EXEMPTIONS` table in
     `scripts/check_claim_evidence_citations.py`.  Leave a **tombstone** where
     the symbol was, naming what replaced it: a reader arriving from a citation
     you missed needs somewhere to land, and the tombstone is what makes the
     miss recoverable instead of mystifying.
  6. **A declaration's own docstring is not authority on its fate — and check
     that the gates which would catch the miss are running.**  Two things this
     sweep found, and neither was in the deletion's plan.  The predicate WS-HP
     HP7 was scheduled to retire turned out to be **live**, with twelve
     consumers, while **five** docstrings across `API.lean`,
     `DispatchPayoff.lean`, `DonationPreservation.lean`, `Endpoint.lean` and the
     plan itself said the phase retires it — a forward-looking claim written
     three phases earlier, propagated by every later cut that touched those
     files, and false.  So a sweep resolves what a symbol's *consumers* say, not
     what its docstring predicts, and it sweeps the **forward-looking** prose
     (`until X retires it`, `X is what retires this`) as well as the citations:
     a stale prediction reads exactly like a scheduled obligation.  And the
     sweep's own instruments need checking, because both of this tree's citation
     gates failed here in opposite directions: `check_workstream_plan.py` was
     **red at HEAD** and had been since the previous cut, on landing notes that
     cite a later sibling narratively where the gate — correctly, no scanner
     being able to tell a mention from a consumption — reads a forward
     dependency; and `check_claim_evidence_citations.py` matches a citation as
     `` `<ident>_<ident>` ``, at least one underscore, so **every Lean `def`**
     (lowerCamelCase) is outside its domain and a deleted one cited as evidence
     reports PASS.  That is fail-open, it is registered in
     `docs/REGISTERED_DEBT.md` §C with its measurement, and until it closes a cut
     that deletes a `def` sweeps the index by hand.  *A green gate you did not
     run, and a gate whose domain excludes what you deleted, are the same
     silence.*

- **Invariant/Operations split**: each kernel subsystem has
  `Operations.lean` (transitions) and `Invariant.lean` (proofs). Keep
  this separation.
- **No axiom/sorry**: forbidden in production proof surface. Tracked
  exceptions must carry a `TPI-D*` annotation.
- **Deterministic semantics**: all transitions return explicit
  success/failure. Never introduce non-deterministic branches.
- **Fixture-backed evidence**: `Main.lean` output must match
  `tests/fixtures/main_trace_smoke.expected`. Update fixture only with
  rationale.

  **And a checksum is not a comparison** (`v0.35.109`).  Every fixture carries
  a `.sha256` companion and the Tier 2 gate sweeps all of them, reporting
  "Fixture hashes verified (14 files)" — which reads as a measurement of
  agreement with the program and is a measurement of agreement with *itself*.
  A checksum's job is to force a fixture edit to be paired with a hash refresh
  in the same commit; it says nothing about whether the fixture still describes
  what the code does, and it is the fixture's *producer* that must be run to
  ask that.  This file's oldest rule, arriving at an artefact none of its
  instances had reached: *a presence check is not a relation check*, where the
  presence is a hash of the file by itself.

  Measured on the whole directory: **twelve of fourteen** fixtures were also
  compared against live output — by `test_tier2_trace.sh` for the main trace, by
  a `fixturePath` read inside the producing suite for ten more, and by
  `include_str!` in `rust/sele4n-abi/tests/conformance.rs` for the return-shape
  table, which is asserted on both sides of the ABI — and all twelve matched, so
  the sweep's value is entirely in the two it could not reach.  Those two are the
  ones nothing compared, and their drift was **total**: `robin_hood_smoke.expected` and `two_phase_arch_smoke.expected`
  are not golden output at all but `SCENARIO_ID | SUBSYSTEM |
  expected_trace_fragment` manifests, and **19 of 19** fragments named lines no
  suite printed.  The cause is the shape this file keeps recording: the only
  consumer, `scenario_catalog.py validate-registry`, parses `parts[0]` — the ID
  column — so the *fragment* column was read by nothing, and when the suites'
  `expect` labels lost the scenario-id prefix the manifests presuppose, every
  row went stale in silence.  `RobinHoodSuite.lean` carried **both**
  conventions, 19 labels with an id and 36 without, in one file.

  Four things new code must respect.  (1) **A fixture needs a gate that runs its
  producer, and the comparison is of SEQUENCES.**  Which gate it is belongs in
  `tests/fixtures/README.md`'s "Used by" column — where it was *false* for both
  manifests, naming suites that do not read their file.  And the main trace's own
  gate asked only the forward direction (every fixture fragment occurs in the
  output), computing the converse *inside the failure branch*, so a passing run
  never asked whether every output line is accounted for: a trace line **added**
  to the output left the fixture no longer enumerating the trace, while this file
  said "must match".  Both directions were asserted at `v0.35.110`, and the
  measurement is what licensed taking the strict one — 239 fragments, 239
  non-empty output lines, zero unaccounted, so it cost the tree nothing.  The
  mutation that decided there drops **one** fixture line and touches nothing else:
  the forward direction still passes at 238/238, and the pre-`v0.35.110` gate
  reported `Fixture comparison passed` on it.

  **And a set is not a sequence** (PR #897 review, `v0.35.113`).  Both of those
  directions are substring **containment**, so what the pair decides is set
  membership and nothing more — which is this file's oldest rule one level below
  the cut that added the second one, and it leaves three token-preserving
  mutations passing: a fixture line **duplicated** (the forward pass finds it
  twice, the reverse pass accounts for every output line), two fixture lines
  **transposed** (identical multiset, and neither direction reads order), and an
  output line **duplicated** (both copies independently find the same fragment, so
  the trace gained a line and the gate reported that both directions held).
  Measured against the superseded gate, the transposition passed and the
  duplication passed *reporting `240/240`* against a 239-line trace — a fixture
  claiming one more expectation than the program prints, called a pass.  What
  licenses the strict form here is the artefact's own contract rather than a
  judgement: `tests/fixtures/README.md` regenerates this fixture by redirecting
  the producer's stdout over it, so it **is** golden output, and the expectation
  sequence and the output sequence are byte-identical at 239 lines with no
  duplicate on either side.  The two loops are kept as *diagnostics* — a 239-line
  diff does not say which scenario id is missing, and which direction moved is
  what tells a maintainer whether the code or the fixture changed — and the
  sequence equality is the verdict.  (2) **The improvement direction is the code, not the
  fixture.**  The manifests were right and the labels had drifted, so the fix
  relabels 94 assertions rather than rewriting 19 rows — and it costs no fixture
  churn, because a manifest nobody edits keeps its checksum.  Rewriting the rows
  would also have made them *ambiguous*: `size correct` and `timer advanced` each
  name two assertions, so a fragment without its id identifies no scenario, which
  is the presence-versus-relation defect one level down.  (3) **The swept set is
  derived**: `list-manifests` classifies a fixture as a manifest by its row shape
  and reads its producer from the manifest's own `# Suite:` header, so a manifest
  added later is checked with no gate edit, and one that declares no producer
  **fails discovery** rather than dropping out of the domain while the gate
  prints PASS.  (4) **A regeneration recipe is a claim too**: the README told you
  to redirect each suite's stdout over its manifest, which replaces an ID table
  with raw output and breaks the Tier 0 registry gate (measured: 74 and 79
  differing lines).  A documented workflow that corrupts the artefact it
  maintains is worse than none, and a Tier 3 negative refuses its return.

  **And a table that claims to enumerate a directory is an enumeration standing
  in for a derivation.**  The same README's `## Files` table is where a reader
  learns which gate compares a given fixture, and it had omitted
  `syscall_return_shape.expected` and `qemu_boot_expected.txt` — the second found
  by `check-fixture-index` (Tier 0) on its first run, which is the criterion this
  file sets for a mechanism worth building.  Membership is a **row**, never a
  mention: a fixture named in passing in the prose names no gate, so accepting one
  would be the presence-for-relation substitution one artefact over.  The
  exemption set is reconciled in both directions, because an exemption nobody
  reconciles reads exactly like coverage.

  **And the machinery that closes a class is written by the same hands** (`v0.35.111`).
  The three paragraphs above are one rule — *a presence check is not a relation
  check* — applied to fixtures.  A review of the code that applies it found **three
  instances of it inside that code**, all fail-open, and the measurement worth
  keeping is not the instances but *where the witnesses were*: all twenty cases had
  been drawn from the drift that had already been observed, so they probed the
  boundary and never asked the property.  That is this file's own *a witness drawn
  from a finding tests the finding*, arriving in the cut written to obey it.

  The three, each a presence check standing in for the relation the function's own
  name asserts.  `check_fixture_index` joined the table's `|` lines into one blob
  and asked whether the filename occurred in it, so an **unlisted fixture passed
  whenever any cell quoted a longer name containing it** — its own `.sha256`
  companion, which every row in that table names — and the loop ran over the
  *directory*, so a row naming a **deleted** file was never inspected.
  `discover_manifests` skipped a file it could not parse, so one carrying a valid
  `# Suite:` header and a single malformed row was swept as golden output with
  `manifest_count` still nonzero and the gate still printing PASS — the exact
  silence the machinery exists to end, arriving through the classifier instead of
  through a stale row.  And `check_fragments` bound a fragment to nothing, so a row
  reading `RH-001 | … | [RH-002a insert then get]` **passed**: the fragment is
  emitted, by the wrong assertion, and `RH-001` could have been deleted from the
  suite outright with the gate green.

  Four things the remedies decide rather than inherit.  **Membership is a parsed
  CELL of a named section**: `fixture_table_filenames` reads the `Fixture` and
  `Hash` cells of the `## Files` table, scoped to that heading — so a filename
  backticked in a second table cannot satisfy a fixture's membership, which is the
  derived-domain rule applied to *which table the claim is about* — and only those
  two cells declare, because the real table's third column quotes
  `scenario_registry.yaml` in prose and would otherwise have declared it.  **Intent
  is what makes a skip reportable**: `classify_fixture` treats a `# Suite:`
  declaration *or* all-row content as manifest intent, and given intent anything
  short of well-formed is an error — with the control mattering as much as the case,
  since the same content without the declaration must stay a trace fixture or golden
  output would be run against a producer it never named.  **A binding is a relation,
  not a containment**: the id must be followed by an optional sub-case letter and
  then a character that cannot continue an id, so `RH-001` does not match
  `RH-0010a …`, which is the same defect one character down.  And **two
  classifications are none**: a file both exempt and named by a row now fails, as a
  missing `## Files` heading does — answering "nothing to check" is a silent pass
  and answering "every fixture is unlisted" names the wrong cause.

  One mechanical point that is genuinely new, and it corrected this cut rather than
  the tree.  **A negative anchor on a retired variable name is satisfied by a revert
  that renames it.**  The first negative written here forbade the retired membership
  expression verbatim; the mutation that reintroduces the joined-blob reading under
  any other local name left it silent, and the mutation run is what said so.  What
  the claim is about is *where the README's text is read*, so the anchor is scoped
  to `check_fixture_index` and forbids the read itself — the declaration-bounded
  form this file otherwise warns about, correct here because the claim really is
  about that declaration.  Ask of any negative: *what renames or relocations
  survive it?*

  **And a gate's own control must be identified by the REASON it fires**
  (`v0.35.113`, found while fixing the paragraph above).  The one artefact that
  claimed to exercise the comparison above was
  `scripts/audit_testing_framework.sh`, whose header says in as many words that
  it "synthesises a deliberately-broken trace fixture and asserts that
  `test_tier2_trace.sh` correctly rejects it (catching a class of *fixture
  compare silently passing* bugs)".  It copied the fixture to a `mktemp` path and
  asserted a non-zero exit — and `TRACE_FIXTURE_PATH` must name a **git-tracked**
  file, an injection guard that refuses any path outside the index, so the
  control was refused before the gate read a single line and would have reported
  success with the comparison deleted outright.  The script written to catch
  "fixture compare silently passing" was passing silently, and the class it names
  is the one the review then found.

  **"The gate could not read it" and "the gate checked it and it differs" must
  never produce the same verdict** — the rule this file already states for
  `check_anchor_consistency.py`, there in the PASS direction and here in the FAIL
  one.  So a control asserts the *message*, not the exit status, and a control
  whose claim is that one check decides asserts the others stayed **silent**: the
  five now in that script mutate the real fixture (with its `.sha256` refreshed,
  since the checksum sweep runs first and the mutation is exactly the consistent
  fixture edit a maintainer makes) and are each decided by their own subject — an
  appended expectation by the forward direction, a deleted one by the reverse, a
  **transposed** and a **duplicated** one by the sequence comparison alone, and an
  untracked path by the guard and by nothing else.  Two further things that cut
  measured.  A control that cannot be run **on its own** is a control nobody
  re-runs after touching the gate it is about, which is how this one stayed inert
  behind a tier stack it runs first: `--controls-only` is eleven seconds against
  tens of minutes.  And the mutated fixture is restored from the index after every
  control **and the restoration is verified**, because a crashed run that leaves a
  golden fixture edited is worse than a control that never ran.
  **And a prose COLUMN is a claim nothing reconciles — while a gate that repairs
  shared state must own it first** (`v0.35.116`).  The rule above says a fixture
  needs a gate that runs its producer and that *which gate it is belongs in*
  `tests/fixtures/README.md`'s "Used by" column.  That sentence had two readers
  and no checker: `check_fixture_index` parses the `Fixture` and `Hash` cells and
  ignores the third, so the column a reader is told is "the only place a reader
  learns which gate compares a given fixture" was read by nothing — and the same
  cut that wrote it *measured* the column false for two fixtures.  A new golden
  fixture could therefore be listed, hashed and compared by no gate at all with
  every fixture gate green, which is `v0.35.109`'s own finding one column over,
  and it is the *a counterpart named in prose* rule (PR #895 round 22) applied to
  a documentation table rather than to a Lean comment.

  `check_fixture_consumers` validates it per fixture **kind**, because what "its
  consumer" means differs: a scenario-traceability manifest is found by a glob
  that names no file, so its cell must name that gate and nothing else is
  checkable; every other fixture is opened by name, so a repository path its cell
  names must exist and must mention the fixture in its **code view** — the tree's
  own per-suffix table, hoisted out of `lean_code_view.overlay`'s local so the
  question "what is this file's code view" keeps one owner rather than two.  A
  suffix with no view is read raw and the docstring says so, since narrowing it
  would mean a third shell lexer.  Its first run caught the row the enumeration
  could not: `two_phase_arch_smoke.expected`'s cell read *"same two gates"*, a
  back-reference to the row above that a reader resolves by eye and a check
  cannot resolve at all.

  The second half is the audit harness, and it is a class this file had not
  written down.  `audit_testing_framework.sh` mutates the real trace fixture in
  place — the only way to reach the comparison, since the fixture-path guard
  refuses anything outside the index — and restores it with `git checkout --`
  before the first control and again on EXIT.  That **permanently discards an
  unstaged edit**, and a maintainer editing a fixture is exactly who runs
  `--controls-only`, which this file advertises as eleven seconds against tens of
  minutes.  **A gate that repairs shared state takes ownership of it first, and
  refuses rather than repairing what it does not own**: the check is fail-closed
  (a non-zero exit naming the files, never a skip), it runs *before* the tier
  stack rather than before the controls — a full run would otherwise spend tens
  of minutes and then discard the edits, and a legitimately regenerated fixture
  makes that stack **pass** — and the restore reads an ownership flag, because the
  trap is installed before the check can run and would otherwise fire the very
  restore it exists to prevent.  A *staged* edit is not dirty and is preserved,
  which is what makes `git diff --quiet` the right question: it asks precisely the
  unstaged one, and the index is what the restore puts back.
- **Typed identifiers**: `ThreadId`, `ObjId`, `CPtr`, `Slot`,
  `DomainId`, etc. are wrapper structures, not `Nat` aliases. Use
  explicit `.toNat`/`.ofNat`.
- **Internal-first naming**: every identifier — theorems, functions,
  definitions, structures, fields, test runners, file names, directory
  names — must describe the semantics of what it is (state update
  shape, preserved invariant, transition path, test subject).
  Workstream IDs, audit IDs, phase codes, and sub-task numbers
  (`WS-*`, `AN3-*`, `AK7-*`, `ak9ce_01`, `I-H01`, etc.) **must not**
  appear in any identifier or file name. Example: rename a test from
  `an3b_02_projection_typing` to
  `ipc_invariant_full_projection_signatures`. Workstream IDs are
  commit-time labels and age out as soon as a workstream closes —
  encoding them in identifiers creates documentation debt and hides
  what the code actually means. Legitimate places to reference a
  workstream ID: docstrings, commit messages, CHANGELOG entries, and
  `CLAUDE.md` / `docs/REGISTERED_DEBT.md` prose. Historical
  identifiers that already encode workstream IDs stay as-is until
  touched by a workstream that can rename them in the same commit;
  new code must comply from day one.  Enforced by
  `scripts/check_identifier_naming.py` (Tier 0), which scans every
  identifier token — and every path component — over every tracked
  non-documentation file rather than enumerating declaration forms,
  globs, or suffixes: Rust is held at zero, and every other code
  surface (Lean, Python, shell, config, assembly, data) is pinned by a
  baseline in `scripts/identifier_naming_baseline.json` counting
  occurrences per (identifier, file), so a grandfathered name's count
  may fall but never rise — a set of pairs alone cannot see a second
  use inside a file that already contains the name.  Prose is
  exempt, as are documentation paths — an audit report or workstream
  plan is *named after* the workstream it records, and CLAUDE.md and
  the website link manifest both cite those paths.  The exemption is
  by location, never by suffix: a `.json`, `.txt`, `.sha256` or
  `.expected` file outside `docs/` is code as far as this gate is
  concerned.  Within a file the prose exemption stops at any literal
  that supplies a linker-visible name — `#[export_name = "…"]`, an
  assembly `.global`, a linker-script `PROVIDE`, an `asm!` template —
  since each of those puts its string in the symbol table.  Paths and
  contents are both read from the git index, so the gate checks what is
  being committed rather than the working tree.  The gate's own
  mechanisms are pinned by `scripts/test_identifier_naming_gate.py`
  (Tier 0), since a scanner that under-reaches fails silently; the
  source-citation gate carries the same kind of witness suite in
  `scripts/test_source_line_citations_gate.py`, for the same reason.

## Implement-the-improvement rule

When an audit, code review, or any reading of the codebase surfaces a
discrepancy between the **code** and the **documentation, docstring,
comment, type signature, or design intent** that describes it, and the
description represents an *improvement* over the actual code (a more
complete behaviour, a more symmetric API, a stronger invariant, a
routed dispatch where the code is a stub, a function that "should"
exist but does not), the remediation is **always** to implement the
improvement so the description becomes true.

It is **forbidden** to weaken, dilute, qualify, or rewrite the
documentation to match inferior code. Documenting incorrect or
incomplete code in lieu of fixing it is not an acceptable engineering
outcome on this project.

Concretely:

- A comment referencing a function `X` that does not exist →
  **implement `X`**, never "remove the reference."
- A docstring describing a complete spec while the implementation is
  truncated → **complete the implementation**, never "document the
  truncation."
- A stub returning `NotImplemented` while the design says it should
  route to a verified entry point → **wire up the routing.**
- Two API call paths handling the same condition asymmetrically →
  **make them symmetric**, never "document the asymmetry."
- An implicit invariant maintained only by convention → **enforce it
  structurally** (record field, refinement type, smart-constructor
  obligation, opaque type whose constructors discharge the invariant),
  never "add an inline comment about the convention."
- A computed-and-proven data structure that the surrounding code does
  not consume → **wire it into the consumer** so the proof carries
  through to runtime, never "remove the unwired structure."
- Deferred items buried in source comments → **fix them** if the
  current scope permits; otherwise lift them into the project debt
  register (`docs/audits/`, `docs/REGISTERED_DEBT.md`). Never leave
  in-source TODOs that age out with the surrounding workstream.
- A "first hardware target" or similar capability claim while the path
  is non-functional → **make the path functional**, never qualify the
  claim with a stub-status caveat.

The single legitimate exception is when the documentation describes a
**worse** state than the code (e.g. a stale `STATUS: staged` marker on
a file that has since been wired into production, or a deprecation note
on a function the project has decided to keep). In that direction the
documentation is the inferior artefact and updating it to match the
better code is correct.

**Audit reports and remediation plans must apply this rule.** Findings
of the form "documentation describes feature X; code lacks feature X;
recommendation: weaken the documentation" are not acceptable. The
recommendation must instead be "implement feature X" — and where the
implementation is non-trivial, the audit must split the work into the
proper sequence of PRs (each one a coherent slice per the PR checklist)
rather than treating documentation surgery as a substitute for the
code change.

When the optimal implementation is genuinely out of scope for the
current cut, the correct outcome is to **defer the release**, not to
ship a documentation-only patch. Forced deferrals must be recorded as
tracked debt with an explicit closure target, not absorbed silently
into a weaker public claim.

## Documentation rules

When changing behavior, theorems, or workstream status, update in the
same PR:

1. `README.md` — metrics sync from `docs/codebase_map.json`
   (`readme_sync` key)
2. `docs/spec/SELE4N_SPEC.md`
3. `docs/DEVELOPMENT.md`
4. Affected GitBook chapter(s) — canonical root docs take priority
   over GitBook
5. `docs/CLAIM_EVIDENCE_INDEX.md` if claims change
6. `docs/REGISTERED_DEBT.md` if workstream status changes
7. Regenerate `docs/codebase_map.json` if Lean sources changed

Canonical ownership: root `docs/` files own policy/spec text. GitBook
chapters under `docs/gitbook/` are mirrors that summarize and link to
canonical sources. `docs/REGISTERED_DEBT.md` is the single canonical
source for workstream planning, status, and history.

## Third-party attribution

seLe4n is GPLv3+ licensed (see `LICENSE`). The Rust workspace pulls a
small set of **build-time only** crates (`cc`, `find-msvc-tools`,
`shlex`) to assemble ARM64 boot assembly; no third-party code is linked
into the runtime kernel binary. Their upstream MIT copyright and
permission notices are reproduced verbatim in
`THIRD_PARTY_LICENSES.md` at repo root. Rules:

1. If you add a runtime dependency (`[dependencies]` of any crate
   under `rust/`), update `THIRD_PARTY_LICENSES.md` in the same PR
   with the verbatim upstream MIT/Apache copyright lines and add the
   path to `scripts/website_link_manifest.txt` if it's not already
   there.
2. If you bump an existing external crate, re-check the upstream
   `LICENSE-MIT` and Cargo.toml for authorship/copyright changes and
   sync `THIRD_PARTY_LICENSES.md` accordingly. Also re-check for a
   new upstream `NOTICE` file (Apache-2.0 § 4(d) propagation).
3. Prefer `core::*` and hand-written minimal code over pulling in a
   crate. A microkernel's trusted computing base must stay small.

## Website link protection

The project website
([sele4n.org](https://github.com/hatter6822/hatter6822.github.io))
links to source files, documentation, scripts, assets, and directories
in this repository. Renaming or deleting any of these paths produces
404 errors on the website.

Protected paths are listed in `scripts/website_link_manifest.txt`. The
Tier 0 hygiene check (`scripts/check_website_links.sh`, called from
`test_tier0_hygiene.sh`) verifies that every listed path still exists,
on every PR and push to main.

To rename or remove a protected path:

1. Update the website (`hatter6822.github.io`) to use the new path
   first.
2. Then update `scripts/website_link_manifest.txt` to match.
3. CI will pass only when the manifest and the repo tree are
   consistent.

## Ignoring dev_history

The `docs/dev_history/` directory contains milestone closeouts, prior
audit reports, completed workstream plans, and legacy GitBook chapters
retained only for historical traceability. **Do not read or reference
files in `docs/dev_history/` unless explicitly instructed.** All active
documentation lives under `docs/` and `docs/gitbook/`.

## Active workstream context

**This section is a status index, not a history.**  It says what is in flight,
what each phase covers in one line, and where the detail lives.  Per-sub-task
landing notes, audit-pass refinements, review-cut narratives and closeout
details belong in the canonical sources and must not be restated here:

- [`docs/REGISTERED_DEBT.md`](docs/REGISTERED_DEBT.md) — the workstream
  *index*: current status, the open phases' obligations, and the project's
  single debt register.  Not the narrative.
- [`CHANGELOG.md`](CHANGELOG.md) — the per-version narrative, one entry per PR.
- `docs/planning/SMP_*.md` — the per-phase plans, linked from the table below.

When a cut lands, update the row's status/version here and write the detail in
`CHANGELOG.md` and `docs/REGISTERED_DEBT.md`.  A row that grows past one line
of summary is a sign the narrative belongs in those files instead.

### WS-RA Syscall Return ABI — COMPLETE (v0.33.37; RA.B.5b + RA.B.8 at v0.33.38)

The kernel returns seL4's ARM64 frame exactly: `x0` = badge / primary result at
full 64-bit width, `x1` = `MessageInfo` whose label carries the kernel status in
the **top** of the 20-bit label range (`0` = success, `errorLabelBase + d` =
discriminant `d` with `errorLabelBase = 0xFFF00`; every label below the base is
a delivered message's own — a fault handler's `seL4_Fault_tag`, for one),
`x2`-`x5` = message registers.  `SYSCALL_ABI_VERSION = 3`, pinned in Lean,
`sele4n-types` and the HAL.  Version 2 carried the status as label `d + 1`
and was retired at v0.34.44 (WS-RR RR4 audit round): a delivered fault
message's tag decoded in userspace as a kernel error, so no fault handler could
be written against `sele4n-abi`.  New code must not treat a nonzero `x1`
label as an error; `ofErrorLabel?` / `decode_response` decide by range.

What remains is owed to SM10.1: return-frame *delivery* at the context restore.
Until that seam flips, a blocked caller's frame is poisoned with the fail-closed
`blocked_resume_sentinel_regs()` so a stale request register can never decode as
a success.  A caller that took a fault at the seam is outcome tag 2
(`.faulted`) and is never poisoned-and-resumed: the core halts pending SM10.1
(PR #887 review round 5).

**A forcibly unblocked thread is staged an error frame** (WS-RR RR7.14,
v0.34.67) — the other half of §9's registered obligation, and closed.  A thread
taken out of a blocking IPC has no value to receive, and both unblocking paths
staged nothing, so the context restore would have delivered its own argument
spill back as a return value.  They now stage, and they stage **different**
errors because they are different facts: `timeoutThread` stages
`Architecture.timeoutFrame` (`.ipcTimeout` — the budget expired under a
well-formed operation, which the caller may reissue), and `cancelIpcBlocking`'s
four blocked arms stage `Architecture.cancelledIpcFrame` (`.ipcCancelled`, a
new `KernelError` at discriminant **57** — the operation was destroyed, so
reissuing may be meaningless and a userspace library cannot write a correct
retry against a conflated code; `timeout_and_cancelled_frames_differ` is the
pin).  seL4 answers this by setting the thread `Restart`; this kernel has no
restart state, so the crossing ends in a distinguishable error.  Three things
new code must respect.  (1) **Two paths stage nothing, deliberately**:
`cancelIpcBlocking`'s `.ready` arm commits no write at all, and `restoreToReady`
— the *resume* spelling of the same field clear — stages nothing because
`.tcbResume` restarts a thread where it was (RR4.11's
`retirePendingFaultForResume` is the fault half of the same posture), so
overwriting `x0`-`x5` would destroy the window the restart preserves.  Both are
pinned as negatives.  (2) **One field clear, two spellings**:
`restoreToReadyStaging` takes the frame as an argument and `restoreToReady` /
`restoreToReadyCancelled` are its `none` / `some` instances, so every framing,
`invExt`, `ipcInvariant`, `tcb_lookup`, identity and projection result is stated
once and instantiated twice, and a field added to one clear and not the other
fails to elaborate (`restoreToReadyCancelled_tcb`).  (3) **The staging is
confined to the TCB**: `contextMatchesCurrentOnCore` compares a core's register
bank against its **own current thread's** saved context and reads no other
TCB's, so `objects_change_preserves_schedulerInvariantStructuralRegNodup_smp`'s
`hReg` is scoped to the current thread and
`storeObject_tcb_preserves_schedulerInvariantStructuralRegNodup_smp` takes a
disjunction (the context is unchanged **or** the thread is current on no core);
demanding the equality at every thread — as it did — is strictly stronger than
the conclusion needs and refuses this write.  The information-flow half needs no
new argument because the frame goes into the victim's *own* TCB, which holds
only because `writeReturnFrameToTcb` deliberately does not touch `machine`.

Plan: [`docs/planning/SYSCALL_RETURN_ABI_PLAN.md`](docs/planning/SYSCALL_RETURN_ABI_PLAN.md).

### WS-CB Hierarchical constant-bandwidth servers — PLANNED (registered v0.34.49)

A `SchedContext` will be able to contain other scheduling contexts: a *server*
holds members instead of a thread, is charged whenever a thread in its subtree
runs, and admits its members against its own budget, so a component's threads
share one reservation and nothing outside the component is delayed by more than
that reservation.  The root scheduler becomes **EDF-first** (maintainer's
decision at planning time): deadlines are kernel-owned CBS deadlines, priority
is the tie-break for deadline-bearing threads and the order of the legacy
unbound class, and priority inheritance becomes deadline inheritance for the
EDF class — a change to the flat model that CB1 lands as three switch cuts,
each with its proofs and its fixture refresh, before any server exists.  Servers are core-homed, members
share the server's security label, and every generalising cut after CB1
carries the theorem that the model is unchanged on states without servers.
No sub-task has started.  The plan also records three pre-existing findings it
closes first: `schedContextConfigure` applies priority, domain and a
caller-supplied deadline to the bound thread under the SchedContext write right
alone, with no caller-MCP check (CB0.3, CB1.6); and the live tick's exhaustion
arm schedules a refill of at most one tick, so a bound thread receives about one
tick per period after its first window (CB1.6, which moves the engine to
per-window refills).  Thirteen review rounds on the planning PR reshaped the design
before any code exists — a transitive tie-break, a key-worsening reschedule
seam, reconfiguration that never mints budget, every reservation move
re-admitted per core, label uniformity over bindings, inheritance for bound
blockers only, the guarantee scoped to roots — and the plan's §14 records each
finding against its fix, and its §14 names the five classes the findings
fell into with the rule that closes each.

Plan: [`docs/planning/HIERARCHICAL_CBS_PLAN.md`](docs/planning/HIERARCHICAL_CBS_PLAN.md).

### WS-OD SchedContext donation chains — COMPLETE (registered v0.34.98; OD1 v0.34.108, OD2 v0.34.125, OD3 v0.35.1, OD4–OD6 v0.35.2)

`applyCallDonation` donated only from a **`.bound`** caller, and
`donateSchedContext` is the only operational construction site of a `.donated`
binding — so a scheduling context stopped at the first passive server and seL4's
passive-server pattern did not work at call depth ≥ 2, where the callee stayed
`.unbound` and could never run.  seL4-MCS's `maybeDonateSchedContext` reads the
sender's *effective* context, bound or donated, and passes it down the chain; so
does this kernel since **OD4** (`v0.35.2`).  Two register rows close here: that
gap, and the `passiveServerIdle` break the `v0.34.97` reclaim introduced.
**53 sub-tasks across OD1..OD6, all closed** — OD1 `v0.34.100` → `v0.34.108`,
OD2 `v0.34.125`, OD3 `v0.34.126` → `v0.35.1`, OD4–OD6 `v0.35.2`.

**The chain is transitive, and what new code must respect** (OD4–OD6, `v0.35.2`).
Six things.  (1) **The guard is the caller's *effective* context**:
`callDonationSchedContext?` and the footprint's `endpointCallDonatedSc?` both
answer `SchedContextBinding.scId?`, so a `.donated` caller donates exactly as a
`.bound` one does, and neither the transition nor its footprint can widen without
the other.  (2) **`donateSchedContext` is a four-store *push*** whose frame is the
donor's own `replyObject`, and it is **fail-closed** on that frame
(`donationPushFrame?`: no reply object, an unresolvable one, or one that already
donates are three refusals).  A donation with no stack frame is what lets the next
pop clear an *outer* caller's frame and settle a context on the wrong thread.
(3) **The `.call` footprint does not grow**
(`lockSet_endpointCallOnCore_covers_donationPush`) and `maxLockSetSize` is
unmoved: every key the push writes is a declared write member already.  (4)
**Every pop resolves its new owner** — all six sites run
`returnDonatedSchedContextResolved`, and the obligation that carries is
`replyStackOuterCallerValid` (with `cleanupDonationStackValid` and
`cancelDonationStackValid` as its two call-shaped siblings), vacuous wherever no
context heads a stack.  (5) **A Reply that still donates cannot be freshened or
retyped, and neither can a context that still heads a stack** — `linkReply` and
`lifecyclePreRetypeCleanup` refuse rather than clear, because clearing takes a
frame off a stack the context still heads and the walk would then stop mid-chain.
(6) **A cancelled *middle* caller is SPLICED out of the stack**
(`cancelledMiddleCallerPolicy = .spliceOutTheCut` since WS-HP HP6.8, `v0.35.45`,
proved by `cancelledMiddleCaller_splices_at_cut`): the frame above the cut takes
the cut frame's own downward link and the frame below links back up at it, so the
reservation goes on travelling outward to the caller the surviving stack names
(`.donated scId outer`) and no thread below the cut is touched.  **Up to `v0.35.44`
it severed** — `cancelledMiddleCallerPolicy = .severAtCut`, the innermost live
caller keeping the context `.bound scId` and its owner left `.unbound` for good —
and that is **what seL4-MCS does**, re-verified at `v0.35.40` against upstream
source at master, 13.0.0, 12.1.0, 12.0.0 and 11.0.0: `reply_remove`'s non-head
branch writes `REPLY_PTR(next_ptr)->replyPrev = call_stack_new(0, false)` under the
comment *"not the head, remove from middle - break the chain"*.  It writes
**zero**, not the cut frame's own `replyPrev`.  `v0.35.14` asserted the reverse
here and quoted a line that exists in no release; see *the removal does not
preserve the donation accounting* below for what that retraction cost.  So the
splice is an **improvement on upstream** rather than an adoption of it, measured at
reply-stack depth three in `tests/SmpIpcSuite.lean` §3.22 and stated as
`donationAccountingPreserved_atCallDepthThree`; what it provably cannot reach is
the depth-**two** loss, where both policies write `none` into the frame above a
bottom frame, and that is closed instead by the reservation's recorded origin
(`donationAccountingPreserved_atCallDepthTwo`, WS-HP HP10.9, `v0.35.53`).
One consequence for the suspend footprint:
the teardown can rebind the victim `.donated`, and the arm selector re-reads the
*post*-teardown binding, so the pipeline pops twice at depth ≥ 2 and
`suspendThreadOnCoreSchedLockSet`'s replenish segment carries a **triple** for
G3 alone (`v0.35.170` appends G2's own migration pair beside it, which is a
different thread's home and a different state).  The payoff
is `passiveServerHoldsDonatedContext_atCallDepthTwo`.

Six things new code must respect once this lands, and each is a decision the plan
records rather than a default it inherited.  (1) **The `passiveServerIdle` hole was
OD1, not a consequence of the chain**, and is **closed**: it was live on HEAD at
depth 1 — a server that Calls an endpoint with no receiver blocks
`.blockedOnCall` keeping its donation, and the reclaim then unbound it in place —
so fixing it last would have meant every later phase doing bundle work over a
known-false conjunct.  See the two standing constraints above for what the
reclaim now does.  (2) **The pop
lands before the push, and lands inert**: with the push first, a depth-2 chain is
serviced by the flat return, which writes `.bound` at the intermediate thread and
moves a context across a domain boundary in a state that *breaks no conjunct*.
(3) **`SchedContext.scReply` is built** — done at `v0.34.125`, because
`Reply.wellFormed`'s docstring already required the context's head to agree
with this reply, of a field that did not exist, and because without it the push must
read the owner's TCB and the outer reply, taking `lockSet_endpointCall` to ten
against a ceiling of nine.  Four things OD2 fixes about the surface new code
writes against.  The field is **erased by `projectKernelObject`** in the same cut
that adds it (`projectKernelObject_schedContext_scReply_invariant`), or the OD4
push would be observable in the interval; a **boot SchedContext heads no stack**
(`bootSafeObjectCheck` refuses one, since every admissible boot Reply is inert,
so a config-supplied head could only dangle); **`Reply.wellFormed` is no longer
`True`** but "a `prev` link only on a reply that is itself on a stack", with the
two store-level clauses its docstring also promised stated in
`donationChainWellFormed`, which carries it as its own first conjunct; and the
chain invariant is a conjunct of **`ipcReachable`**, not of `ipcInvariantFull`
(twenty, unchanged), *preserved* through `donationChainFrame` rather than
assumed.  The frame is stated over the two projections the walk actually reads
(`replyStackLinks?`, `schedContextStackHead?`), so it **is** the read set rather
than an over-approximation of it, and a field the chain starts reading has to
enter a projection before any frame can be re-proved.  And the predicate is
known to **decide** rather than refuse: it is discharged vacuously everywhere
today, so `donationChainWitness_wellFormed` proves it whole — completeness
clause included — of the store a depth-2 Call chain leaves, which is what stops
an over-strong conjunct from hiding behind an obligation that never fires.
(4) **The pop's new owner is an argument**, since the reply leg consumes the
target's reply link before the donation return runs.  (5) **The pop validates the
link it follows** — Reply objects are re-linked to new callers, so a stale
`prev` over a reused Reply would hand a thread's context to an unrelated thread
in another domain.  Since `v0.34.125` that validation is *structural*:
`donationChainFrom` follows a link only after checking the target's own
**upward** link against the frame that reached it, never its `caller`, and a
Reply carrying no upward link is provably on no chain
(`not_mem_donationChainFrom_of_unlinked` — the freshness fact the push
consumes).  Relinking clears both links (`Reply.isFree`), so a reused Reply
carries no answer back and the walk stops at it.  (6) **The binding's
`owner` stays the immediate donor**, which is what keeps all five donation
conjuncts true at depth `n` unchanged and leaves the *binding* graph chain-free —
the chain lives entirely in the reply stack.

**The pop validates what it hands out** (OD3.4, `v0.34.127`).
`returnDonatedSchedContext` refuses an outer caller that is not a *waiting donor*
— a stored TCB that is `.unbound` and `.blockedOnReply`, and neither of the two
threads the pop rewrites (`outerCallerAcceptable`, O(1), fail-closed, part of
`returnDonatedSchedContext_ok_storeChain`).  `donateSchedContext` has always
checked its donor side before minting a `.donated` binding; the pop mints one too
and checked nothing, which is why the depth-≥ 2 obligation was unusable — on the
reply path the answered caller is already `.ready`, so no consumer could discharge
it.  Three of `donationReturnOuterValid`'s four clauses are now consequences of
the operation succeeding; the fourth (`outerUnowned`) is whole-store quantified
and stays a caller obligation.  `replyStackOuterCaller?` is the pre-state resolver
the call sites will use: it walks exactly one link past the stack head, answers
three ways (bottom of stack / the outer caller / a link that does not validate),
and validates the frame below the head so a re-linked Reply cannot redirect a
context.  **New code must not read the frame as fixing the resolver's answer** —
`donationChainFrame` deliberately excludes `Reply.caller`, so it transports
resolvability only.  **All six call sites thread the resolver since OD4.4**
(`v0.35.2`): each runs `returnDonatedSchedContextResolved` on its own pre-state,
and the obligation that carries is `replyStackOuterCallerValid` — with
`cleanupDonationStackValid` and `cancelDonationStackValid` as its two
call-shaped siblings.  A site that passes a literal `none` is a site that has
not been threaded; OD3's `hBottom` condition on
`returnDonatedSchedContext_preserves_ipcInvariantFull` was removed by OD4.3,
which is what made the threading possible.

**And a receive rendezvous hands over the caller's *priority*, not only its
budget** (OD3.14, `v0.34.141`).  `resolveEffectivePrioDeadline` is
`max basePrio pipBoost`, and the inherited **boost** travelled by no route at
all on the `.receive` arm, which ran no `propagatePipChainCrossCore` while
`.call` and `.replyRecv` both did.  (At OD3.14 this row also read OD3.6's
donation as moving the caller's *base* priority to the donee.  It no longer
does: since `v0.35.3` a donee runs on the donor's budget, deadline and domain at
**its own** priority, so the chain walk described here is the **only** priority
route between a client and the server it calls — which makes this row
load-bearing rather than a second-order correction.)  A chain `D → C → S` — `D` blocked on `C`,
`C` dequeued into `.blockedOnReply` on the passive server `S` — therefore left
`D`'s priority stopping dead at `C`: unbounded priority inversion, on the arm a
passive server takes its *first* request with.  It bites with **no** donation
too, since `applyCallDonation` is the identity for an already-`.bound` receiver
that still gains the waiter.  Pre-existing rather than introduced by OD3.6, and
reported as a possible vulnerability before being fixed.  Five things new code
must respect.  (1) **The guard is read once, from the pre-state**:
`applyReceiveRendezvousHandoff` is OD3.6's donation and the walk under a single
`if`, so the two provably fire on the same states — a second reading on the
post-donation state would owe an `ipcState` frame lemma, and a Tier 3 negative
refuses it.  (2) **The walk starts at the receiver**, which is `.call`'s own
start point (`endpointCallCrossCoreDispatch`) and the one `.replyRecv` reaches
when its reply is not delegated.  (3) **The sibling gap closed in the same cut**:
`.replyRecv` walks from the *recorded server*, which is the receiver only on a
non-delegated reply, so `applyReceiveLegPipHandoff` adds the receiver's walk
**gated on the equality that makes the first walk be it** — the non-delegated
arm is unchanged, byte for byte.  (4) **The write set grew**: a chain walk
re-buckets run queues on the members' home cores, so `replyRecvBodyWriteSet`
carries a fourth leg (`receiveLegPipHandoffWriteSet`, read at the state that leg
runs at) and `.receive` declares `receiveRendezvousHandoffWriteSet`, whose chain
leg is a *parameter* because it runs at the post-donation state.  (5)
**`maxLockSetSize` does not move, and that is a decision**: a chain is
state-discovered and unbounded, so its locks are declared through the
`pipChainStart_<τ>` markers the SM3.C walker consumes rather than through
`lockSet_<τ>`, which is what keeps the static footprint honest.  The marker
family grows with the *walks*, not the syscalls — `pipChainStart_endpointReceive`
and `pipChainStart_replyRecvReceiveLeg`, with the reply leg's own marker
corrected to name the recorded server it actually walks from rather than the
caller the retired single-core transition walked from.

**And the receive-side arms declare it too, at the cost of the ceiling** (OD3.12
and OD3.13, `v0.34.137`).  `.receive` and `.replyRecv` pop the endpoint's **send**
queue or block on its **receive** queue -- the same two primitives, the same one
neighbour TCB -- and `.replyRecv`'s receive leg *is* `.receive`'s transition, so
one resolver (`receiveSideQueueStructureNeighbor?`) serves both.  `.replyRecv` was
at 13 of 13, so **`maxLockSetSize` is 14**: `admissibleCriticalSection` for the
1 ms tick falls 25 → **23 µs**, the uniform 60 µs envelope moves 2340 → 2520 µs,
and the sharp reachable `.replyRecv` bound goes 12 → 13 (the *gap* between
ceiling and sharp bound is unchanged at one).  Every one of those figures is
derived from the constant and moves with it, which is why they are theorems
rather than paragraphs.  Read the cost against the alternative: a footprint that
omits a written object is **false**, and every statement built on
`lockSetForSyscall` -- the 2PL serialisation results,
`boundedWait_under_2pl`, the CC-5 bound -- was *silent* about that TCB rather
than conservative.  **With this cut all eight declared syscall arms name every
object they write**, and the sweep that began at OD3.9 is closed.  Two mechanical
notes: the sharp bounds are *renamed*, not weakened -- OD3.13 spelled them
`lockSet_replyRecv_size_le_thirteen_of_owner_eq_target` and
`lockSet_endpointReplyRecvOnCore_size_le_thirteen`, and **neither name is live**:
the first was deleted at `v0.35.50` with the rest of the `_of_owner_eq_target`
family, whose merge HP6.2 refuted, and the reachable `.replyRecv` bound is
`lockSet_endpointReplyRecvOnCore_size_le_eighteen` -- and a new cut that widens a
footprint pays at `admissibleCriticalSection_rpi5Tick`, visibly.

**And `.send` / `.call` declare the queue-structure neighbour** (OD3.11,
`v0.34.136`).  Every `.send` / `.call` / `.receive` / `.replyRecv` either **pops**
the head of one endpoint queue or **enqueues** the caller on the other, and each
writes exactly one TCB besides the operation's two principals: the pop relinks the
popped thread's successor into the head, the enqueue relinks the queue's old tail.
No footprint named either.  Four things new code must respect.  (1) **One
definition** -- `endpointQueueStructureNeighbor?`, with the branch decided by the
same resolver the arm's receiver/sender member already comes from
(`endpointCallReceiver?` / `receiveRendezvousSender?`), so the footprint and the
transition cannot disagree about which branch a call takes; a Tier 3 negative
refuses re-reading the queue head at the instance.  (2) **An `Option`, not a
pair**: the two cases are mutually exclusive, so each arm grows by one member.
(3) **Restated at full arity everywhere** -- both size bounds, both
kind-consistency proofs, the four write-membership lemmas, the
`lockSetTransitions_within_bound` conjuncts, `KernelOperation.ofCall`, and the
WithCaps footprint, which *is* the base at `some destCnodeObjId`.  (4)
**`lockSet_endpointCallOnCore_capless` carries the resolver**: "capless" is a
property of the *message*, and a call carrying no capabilities still pops or
enqueues, so fixing the member at `none` there would describe a footprint the
transition does not declare.  `maxLockSetSize` is unmoved (`3 + 4 = 7`,
`3 + 6 = 9`).  `.receive` and `.replyRecv` are the same shape and not yet
declared.

**And `.notificationSignal` declares the two TCBs its dequeue relinks** (OD3.10,
`v0.34.135`).  The bound-delivery path runs `endpointQueueRemoveDual`, which writes
the removed thread's predecessor and successor TCBs, and `lockSet_notificationSignal`
named neither -- so a `.notificationSignal` on one core and a `.tcbSuspend` of a
queue-mate on another had provably disjoint footprints while both writing the same
TCB.  Latent rather than live (SM5.I's global entry lock serialises every kernel
entry, and nothing boots yet), which makes it a *verification* defect: everything
built on `lockSetForSyscall` was silent about those two objects rather than
conservative.  Four things new code must respect.  (1) **The resolver is derived
twice over**: `notificationSignalSpliceNeighbors?` takes its arm gate from
`boundDeliveryTarget?` -- the resolver the arm's other two members already come
from -- and its neighbour identities from `queueSpliceNeighbors?`, so neither the
footprint and the transition nor the two footprint families can disagree.  A Tier 3
negative refuses the inlined pair.  (2) **`cancelSpliceNeighbors?` is now
`queueSpliceNeighbors?`**, beside the link fields it reads: it was one family's
private spelling of a fact that is not cancellation-specific, and adding a second
reader without unifying it would have been OD3.9's divergence one level up.  Arm
*selection* stays per arm -- which thread is spliced is an arm question, who its
neighbours are is not.  (3) **Every statement about the footprint is restated at
the new full arity** -- the size bound, the kind-consistency proof, the three
write-membership lemmas and the `lockSetTransitions_within_bound` conjunct; a
bound left at a new argument's default is a different proposition, which RR7.18's
census refuses for sizes and which nothing covers for the others.  (4)
**`maxLockSetSize` does not move**: the shape is `3 + 5 = 8`, so
`admissibleCriticalSection` stays at 23 µs and the published contention bound is
unchanged.  The remaining arms the same sweep found -- `.send`, `.call`,
`.receive` and `.replyRecv`, each writing one queue-structure TCB (the new head
on a rendezvous, the old tail on a block) -- are the rows after this one.

**The three endpoint-queue removals write one definition** (OD3.9, `v0.34.134`).
`spliceOutMidQueueNode` -- the removal `.tcbSuspend` and thread destruction run --
patched its successor's `queuePrev` and not its `queuePPrev`, leaving it naming
the removed thread.  That is the field `endpointQueueRemoveDual` validates
(`pprevConsistent`), and after the splice it fails in *every* case there was a
successor: as the new head because it **is** the head, as an interior node
because its `queuePrev` now names its new predecessor.  So the successor could
never again be dequeued by the dual removal and every later bound-notification
delivery to it returned `.illegalState` -- reachable by suspending the thread
merely *ahead* of a passive server, over which the caller holds no authority, and
single-core logic rather than a race, so SM5.I's global entry lock does not mask
it.  Four things new code must respect.  (1) **What unlinking writes is
`queueUnlinkPredecessor` / `queueUnlinkSuccessor`** (`Model/Object/Types.lean`,
beside the fields they maintain), and the successor's carries both link fields;
a new removal calls them rather than spelling a record update.  (2) **The third
removal is tied to them by a theorem, not by a name**:
`endpointQueueRemoveDual_stores_queueUnlinkSuccessor` / `…Predecessor` are about
the object the operation *stores*, since that one spells its write through
`storeTcbQueueLinks`.  (3) **No `ipcInvariantFull` conjunct reads `queuePPrev`**,
which is why nothing caught either instance; the sharp pointwise readings
(`spliceOutMidQueueNode_tcb_value`, `sweptAndRestored_tcb_value`) now state the
field, so a reading that omits it is a statement about a different operation.
(4) **`endpointQueueRemove`'s comment claiming the dual removal is "the removal
every other kernel path uses" was false when OD1.1 wrote it** -- this is that
finding's third copy, and it survived eight cuts because the fix was applied to
the copy the finding named.  A removal added later is a fourth: sweep, do not
patch.
**...and the agreement between the two link fields is an INVARIANT, not a
per-site obligation** (WS-RR RR8.3, `v0.35.57`).  `queuePPrev` carries exactly
**one bit** beyond `queuePrev` — whether the node is linked into a queue at all —
and every other bit of it must agree: `.endpointHead` iff there is no
predecessor, `.tcbNext p` iff the predecessor is `p`.  Nothing stated that, and
that is *why* OD1.1 and OD3.9 each found a removal writing `queuePrev` alone: no
`ipcInvariantFull` conjunct read the field, so a stranded successor — one that can
never leave its endpoint queue again — was invisible to the proofs and to the
harness alike.  Six things new code must respect.

(1) **`queuePPrevAgreesWithPrev` is `dualQueueSystemInvariant`'s fourth
conjunct**, so `ipcInvariantFull` still has twenty and the bundle family is
untouched — and since `v0.35.99` its `none` arm says **`queuePrev = none`**
rather than nothing.  It read `True`, on the stated ground that
`tcbQueueLinkIntegrity` forbids a dangling `queuePrev`; that conjunct forbids a
`queuePrev` whose target does not point back and never mentions `queuePPrev`, so
a *queued* interior node carrying no back-pointer satisfied every conjunct while
the dual removal — whose guard takes a `QueuePPrev`, not an `Option` — refused it
outright and could never dequeue it.  The field was weaker than the one bit it is
documented to carry.  A new writer therefore states both back-pointers, which
every existing one already wrote: the strengthening cost six discharge sites and
changed no operation, no queue and no fixture — but every transition in the tree now carries it, and a new one must.
The cheap route is `queuePPrevAgreesWithPrev_of_frame` (every surviving TCB keeps
its two link fields) or, for a queue writer, the per-primitive siblings
`storeTcbQueueLinks_preserves_queuePPrevAgreesWithPrev` and
`storeObject_tcb_preserves_queuePPrevAgreesWithPrev`.  The bundle has **named
accessors** (`.endpointsWellFormed` / `.linkIntegrity` / `.chainAcyclic` /
`.pprevAgrees` / `.headDisjoint`) so the fifth conjunct `v0.35.106` added did not
shift a single projection path, and a positional `.2.2` into it is now a statement
about a pair.

(2) **The dual removal's precondition is a named definition the transition
reads.**  `dualQueueRemovalGuard` *is* `endpointQueueRemoveDual`'s
`pprevConsistent`, which was an anonymous `let` — which is why no caller could
state that it had established it.  A Tier 3 negative refuses the inlined spelling
coming back beside the named one, and eight proofs `unfold` the name, so deleting
it is a build failure rather than a silent pass.

(3) **The guard factors, and only one factor is the invariant's.**
`dualQueueRemovalGuard_eq_position_and_pair` splits it into
`queuePPrevHeadPositionAgrees` and `queueLinkPairAgrees`;
`dualQueueRemovalGuardHolds` discharges the second from the conjunct and the first
from **membership**, which stays a hypothesis because no invariant entails it — a
thread on *no* queue also has `queuePrev = none`, so `.endpointHead` alone cannot
say which queue's head it names.  Measured rather than asserted: a detached thread
carrying `(none, .endpointHead, none)` satisfies the pairing and fails the guard
(`tests/NegativeStateSuite.lean`).  Membership is spelled the way this tree
already spells it — the head itself, or reachable from it — and
`QueueNextPath.lastEdge` is what turns reachability into a predecessor, the
sibling `firstEdge` had lacked because the inductive is written forwards.
`dualQueueRemovalGuardHolds_of_dualQueueSystemInvariant` is the same discharge in
the shape callers hold, taking the endpoint rather than the queue.

(4) **The retype replacement is pristine in `queuePPrev` too, and that is not
derivable from `queuePrev = none` beside it**: a replacement carrying `.tcbNext p`
with no `queuePrev` *refutes* the pairing rather than satisfying it vacuously.  It
sits next to `queuePrev` in `retypeReplacementFresh`, because the two are one
back-pointer, at the cost of shifting twelve positional destructurings — which is
the price of keeping the pair together and was paid deliberately.

(5) **The unlink updates are where the pair is shown to travel together.**
`TCB.queuePPrevAgreesWithPrev_queueUnlinkSuccessor` (the successor inherits the
*removed* thread's own pair) and `…_queueUnlinkPredecessor` (only `queueNext`
moves) are the machine-checked form of the OD1.1/OD3.9 finding, composed by
`queueNeighbourPatch_preserves_queuePPrevAgreesWithPrev` into
`spliceOutMidQueueNode_preserves_queuePPrevAgreesWithPrev` — the third removal's
own statement, which the cancellation composite then consumes rather than
re-deriving.

(6) **The conjunct is checked at runtime, not only proved.**
`queuePPrevAgreesWithPrevChecks` is part of `stateInvariantChecksFor`, so every
harness state asserts it; the golden trace's `[PIP-005]` count moved 27 → 28,
which is the measurement that it runs.  Its witness is decisive in both
directions, and the mutation that decides **keeps every queue and every
`queueNext` chain and corrupts one back-pointer**.

**...and the head's back-pointer is the QUEUE's fact, not the TCB's — so it needed
a fifth conjunct** (PR #897 review, `v0.35.106`).  RR8.3 closed *present but wrong*
and `v0.35.99` closed *absent on an interior node*; what both left open is the
**head**.  `queuePrev = none` is what a detached thread carries **and** what a
queue's head carries, so `queuePPrevAgreesWithPrev` — a pointwise predicate over
one TCB — structurally cannot distinguish them, whatever its `none` arm is
strengthened to.  A queue whose sole member carried `(none, none, none)` therefore
satisfied every conjunct of the bundle while `endpointQueueRemoveDual` refused it
with `.endpointQueueEmpty`: the OD1.1 / OD3.9 stranding class a **fourth** time, and
this time on a queue that is not empty.  **And the tree had already decided it in
the other artefact**: `intrusiveQueueWellFormedB`, the check every harness state is
asserted against, has required `headTcb.queuePPrev = some .endpointHead` since it was
written — *one question answered in two places*, with the Bool right and the Prop
wrong, and the divergence sitting exactly where the proofs are silent.  Six things
new code must respect.

(1) **The clause lives in `intrusiveQueueWellFormed`'s P2**, beside `queuePrev =
none`, because it is a fact about a *queue's head* and a pointwise TCB predicate
cannot say it.  A new queue writer states both link fields of a head it installs;
`storeTcbQueueLinks_preserves_iqwf`'s `hHeadOk` carries the pair.

(2) **`endpointQueueHeadDisjoint` is `dualQueueSystemInvariant`'s FIFTH conjunct**,
and `ipcInvariantFull` still has twenty.  It says a thread heads at most one
endpoint queue, counting send and receive as different queues — which is what a
*clearing* writer needs, since with the back-pointer in P2 it must show the thread
it clears heads none of the queues it transports, and `endpointQueueNoDup` gives
disjointness only *within* one endpoint.  The bundle's named accessors gained
`.headDisjoint`, and that RR8.3 built them "before a fifth conjunct arrives" is the
measurement that the shape paid: no projection path moved.

(3) **It is a consequence of `ipcInvariantCore`, not a new assumption.**
`queueHeadExclusive` derives it from `queueHeadBlockedConsistent` — a head's
`ipcState` names *its* endpoint and *its* queue kind, and a thread has one
`ipcState` — with `queueHeadKindExclusive` the same-endpoint corollary (which
re-derives `endpointQueueNoDup`'s disjointness clause) and
`endpointQueueHeadDisjoint_of_queueHeadBlockedConsistent` the builder.  So nothing
*assumes* exclusivity; the conjunct exists so the bundle can **transport** it
without reading an `ipcState`, which is what keeps it inside this bundle's charter.

**...and it is checked at runtime too — since `v0.35.108`, not since it was added**
(PR #897 review).  RR8.3's item (6) had recorded the rule one cut earlier ("the
conjunct is checked at runtime, not only proved") and `v0.35.106` added the conjunct
with no check, so this is that rule unswept at the very next opportunity.  The gap
was not one omitted call: **nothing** in `stateInvariantChecksFor` was
cross-endpoint — `endpointDualQueueWellFormedB` is literally the two per-queue
checks of one endpoint — and nothing tied an endpoint queue's head to its own
`ipcState`, so a state the bundle refuses passed the entire surface.  Two endpoints
each holding `{head := some t, tail := some t}` over one thread the live enqueue
left with `(none, some .endpointHead, none)` is that state, and popping either queue
then clears `t`'s links and strands the other: the OD1.1 / OD3.9 stranding class a
fourth time, on a queue that is not empty.  `endpointQueueHeadDisjointChecks` asks,
per occupied head, whether any **other** `(endpoint, kind)` claims it — so it is
robust to a repeated index entry and it names the colliding pair, which is the whole
content of a disjointness failure.  Three things its witness records.  A violating
state **cannot** be reached by live operations (every kernel queue writer maintains
disjointness by construction, which is why the conjunct is provable), so the witness
writes the second endpoint's boundary by hand through `corruptEndpointQueueHeads`,
as the RR8.3 witnesses write a corrupted back-pointer by hand.  Its claim is a
**differential** against the control rather than "the only failing check is the new
one", because `baseState`'s TCBs are unsynced and two `threadState` checks fail on
both states — a plain claim there would have been false for a reason unrelated to
the finding.  And the strand is measured rather than described: the pop is taken
with `expectOkVal`, because `expectOkSt` asserts the invariant surface on the
post-state and that post-state is the corrupt one the finding is about.  The golden
trace's `[PIP-005]` count moved 28 → 29, which is the measurement that it runs.

(4) **A writer discharges it locally, from its own guard.**
`endpointQueueHeadDisjoint_of_singleQueueUpdate` (itself derived from the general
`_of_freshHeads`) takes two obligations, and each queue writer already has them: a
pop promotes a successor, which has a predecessor
(`not_queueHead_of_queuePrev_some`); an enqueue promotes a thread its own guard
refused a back-pointer to (`not_queueHead_of_queuePPrev_none` — the strengthened P2
paying for itself); a mid-queue removal and a tail append move no head.  The two
operations that clear a *victim's* links without owning its queues — the
notification purge and the reply-path restore — take the victim's off-boundary fact
as a **stated** hypothesis (`hOffEp`), which the composite holding the whole bundle
supplies from `queueHeadBlockedConsistent`, because a thread blocked on a
notification or a reply bounds no endpoint queue.

(5) **The payoff is a retired caller obligation.**  A queue member's `queuePPrev` is
now derived rather than hypothesised — at the head from P2, at an interior node from
`tcbQueueLinkIntegrity`'s forward clause plus the pairing — so
`queuePPrev_of_queueMember` joins the halves and
`dualQueueRemovalGuardHolds_of_member` is `dualQueueRemovalGuardHolds` with `hPPrev`
discharged.  `hMem` and `hTailLast` remain, because queue connectivity and the
tail's identity are what no conjunct of this bundle entails.  Its witness is
`tests/NegativeStateSuite.lean` case (5), which reads the field off both states
directly — asserting the *field* rather than a predicate's verdict is what makes it
about P2's strengthening rather than about the pairing beside it.

**...and the BOUNDARY the removals write is one definition too — and asking the
fact rather than a proxy for it is what retires a stated hypothesis** (WS-RR
RR8.4, `v0.35.58`).  OD3.9 unified what a removal writes to the *neighbours*;
the queue's own `head` and `tail` stayed two readings, and the plan row that
scheduled this collapse said they "write the same fields to the same values
today".  They did not.  Both moved the head on `q.head = some tid`; for the tail
`endpointQueueRemove` asked `q.tail = some tid` while `endpointQueueRemoveDual`
asked `removed.queueNext = none` and derived the new tail from `queuePPrev`.
Under a connected queue the two conditions coincide, and `ipcInvariantFull`
joins a queue's boundaries **nowhere** — it constrains the head, it constrains
the tail, and nothing relates them — so on a state it admits, a queued thread
with no successor that is not the tail, they part: there the inferring form
cleared the tail and **stranded the queue's real tail**, a thread that could then
never be dequeued, which is OD3.9's own defect class arriving through the field
OD3.9 did not unify.

`queueRemoveBoundary` (`Model/Object/Types.lean`, beside `queueUnlinkPredecessor`
and `queueUnlinkSuccessor` — the third and last piece of "what does unlinking
write") is the shared definition, with the four shapes a guarded removal writes
named once (`queueRemoveBoundary_{headLast,headMore,midLast,midMore}`, read by
both the dual's invariant proofs and the `endpointQueueRemove_agrees_*` family).
Five things new code must respect.

(1) **`q.tail = some tid` is the fact and `removed.queueNext = none` is a
proxy for it**, so the shared definition asks the fact — this file's own *a proxy
is not the fact* rule, applied to a field rather than to a core.  Which reading
survives is not an arbitrary pick: the proxy's failure mode is silent (a
well-formed-looking queue with a thread missing from it) and the fact's is loud
(a head cleared without its tail, which `intrusiveQueueWellFormed` refuses), so
the fact fails closed where the proxy fails open.

(2) **Asking the fact leaves the proxy's direction to be established, and the
removal CHECKS it.**  `queueTailPairAgrees` — the queue's `tail` field and the
removed thread's `queueNext` agree about whether this thread is the tail — is the
first factor of `dualQueueRemovalGuard`, so the dual **refuses** the state on
which the two readings part rather than mishandling it, and
`dualQueueRemovalGuard_eq_position_and_pair` is restated over three factors.  One
direction is free from the bundle (a tail has no successor, so a thread with one
is not the tail — `spliceTail_ne_of_hasNext`) and the other is the missing
invariant, which is why this is a runtime guard and not a fifth conjunct.  The
biconditional is stated because "the tail question has one answer" is what it
means; refusing the free direction as well costs nothing, the bundle already
excluding it.

(3) **WS-OD OD1.3's `spliceRemovedIsTailWhenLast` is DELETED, and the deletion is
not its closure.**  Every consumer was already conditioned on the dual
succeeding (`dualRemovalEnabled`), so the guard discharges what the hypothesis
supplied: `SpliceShape`'s two no-successor branches carry `hTail` outright
instead of the weaker `tail.isSome`, and `endpointQueueRemove_agrees_with_dual`,
`endpointQueueRemove_establishes_ipcInvariantFullExceptMembership` and
`abortPendingIpcOnEndpoint_preserves_ipcInvariantFull` each shed a hypothesis —
the agreement now needs the dual's success and nothing else.  But queue
connectivity is still a **missing invariant**: the fact is now
`dualQueueRemovalGuardHolds`'s `hTailLast`, an obligation on whoever *calls* a
removal, where it is discharged from where the thread sits in the queue, rather
than one carried by every theorem *about* one.  A cut that reads the deletion as
"connectivity is now entailed" has read it backwards.

(4) **The pin is asymmetric, and measured rather than assumed.**  The dual's
boundary write is buried in a five-step program, so only a theorem can state it:
`endpointQueueRemoveDual_writes_queueRemoveBoundary`, hypothesis-free, replacing
two consumer-less WS-L3 tail theorems that specified the retired inference.  The
single's body is straight-line and its four `endpointQueueRemove_ok_*` shape
theorems already state its post-store *per branch*, so they fail if its boundary
changes — measured: a no-op mutation of its Step 3 fails four of them — and a
fifth restatement was **not** added, because that is the duplication this file
spends its length retiring.  What neither side pins is the *sharing*: an inlined
copy of the identical record would satisfy every one of those theorems, so that
is a Tier 3 negative, and its mutation keeps the values and breaks only the
sharing.

(5) **A plan row's premise is a claim, and this one was false.**  "They write the
same fields to the same values today" was written from reading both bodies'
*head* computations and generalising; the tail was where they differed and where
the defect was.  The row is corrected in place rather than quietly satisfied,
because a premise that survives a cut it motivated will be cited by the next one.

**And the boundary question had FOUR askers, not two** — the sweep rule catching
this cut's own plan row.  RR8.4's row said "the two endpoint-queue removals", and
OD3.9 four sections above had already established there are **three**: the third
(`removeFromAllEndpointQueues`) splits the work, so `spliceOutMidQueueNode` writes
only the two neighbour TCBs and its *boundary* write is `removeThreadFromQueue`
(`Lifecycle/Operations/Cleanup.lean`) — a fourth spelling of the same expression,
found by asking who else computes a queue boundary rather than by trusting the
row's enumeration.  It already asked the **fact**, so unifying it is a
de-duplication and not a behaviour change (`removeThreadFromQueue_tcb_present` is
byte-for-byte the boundary it wrote before, and
`removeThreadFromQueue_eq_queueRemoveBoundary` is the relation stated over the
shared definition).  Its `lookupTcb`-absent arm is deliberately **not** routed
through `queueRemoveBoundary`: with no TCB there is no removed thread whose links
a boundary could inherit, so that arm is the *absence* of a removal and routing it
through a synthetic link-free TCB would make the shared definition describe a case
it is not about.

**And running the sweep again found a FIFTH**, which is the whole argument for
running it rather than stating it.  `frozenQueueRemove`
(`Kernel/FrozenOps/Core.lean`) is the frozen mirror of `endpointQueueRemoveDual`
and computed the boundary itself, with `==` where the live ones use `=`.  It is
the asker a kernel-tree sweep structurally missed — until `v0.35.60` the frozen
surface was in neither library root, built only by its own test target — and it
is the **fifth** time this project paid for that (WS-RM's census at `v0.35.12`,
HP4.7's trigger at `v0.35.38`, HP8's splice at `v0.35.47`, HP10.8's origin clear
at `v0.35.52`, and this boundary).  **This paragraph said "third" for two cuts
after it was five**, in the file whose own rules retire hand-kept counts; the
root cause is closed at `v0.35.60` — see *a surface outside every derived domain
is checked by whoever remembers it* below.  Because the frozen store holds the **live** `TCB` and `IntrusiveQueue`,
a *model*-level definition applies to it directly, which is why
`queueRemoveBoundary` lives beside the two unlink updates in
`Model/Object/Types.lean` rather than in the IPC layer.  Two results worth
keeping.  The mirror already asked the **fact**, so it was **right** on the tail
question where the operation it mirrors was wrong, and nothing in the tree
compared the two on the state where they part — a differential surface can hold
the better answer and never be asked.  And its *guard* is a different matter: it
refuses only `queuePPrev.isNone` where the live removal refuses three things, so
it **succeeds where the kernel refuses**, which is the direction that matters on a
mirror; the guard family lived in the kernel layer the frozen surface deliberately
does not import, so relocating it to the model was its own cut — **taken at
`v0.35.59`**, and the next paragraph is what it measured.

**A plan row's enumeration is a recognised set**; the sweep is what makes it a
derived one — and a sweep that stops where the build roots stop is still an
enumeration.

**And a surface outside every derived domain is checked by whoever remembers it**
(`v0.35.60`, the maintainer's correction).  Every domain rule above polices one
gate's input.  This is the same defect at the scale of a **subsystem**, and it is
the one that produced most of the frozen-surface findings in this file.

`SeLe4n/Kernel/FrozenOps/` was in neither library root and in no staged
allowlist, built only by its own `lean_exe`.  Measured at `v0.35.59`: that put it
outside the *derived* domain of **five of the six** Tier 1 censuses
(`IpcDethreadingEnvironmentCensus`, `BootEntryContract`,
`ExportCommitDisciplineCensus`, `LockFootprintBoundCensus`,
`StoreReadClassificationCensus` — the sixth, `ReplyStackWriteCensus`, reaches it
only because `v0.35.12` widened it *by hand, after a defect shipped through the
hole*), and outside `check_production_staging_partition.sh` entirely, which has no
opinion on a module that is neither production nor staged.  It was executed
(Tier 2 runs `lake exe frozen_ops_suite`) and anchored in Tier 3, so it was not
unchecked — it was under-**derived**, which is the failure mode this section
spends its length retiring.

**The cost was five after-the-fact corrections**, each found by a later cut rather
than by a gate, on a surface carrying the **live** `TCB`, `Reply`, `SchedContext`
and `IntrusiveQueue` records and mirroring the reply and cancellation spines: a
caller's Reply cleared bare and a link guard reading `caller.isNone` where the
live kernel reads `Reply.isFree` (`v0.35.12`); a binding-driven trigger after the
live path went head-driven, plus a missing recipient guard and a missing ID
promotion (`v0.35.38`); still severing after the live removal spliced
(`v0.35.47`); never clearing `donationOrigin` (`v0.35.52`); and a duplicated queue
boundary followed by a guard carrying **one of four** refusals with the wrong
error code (`v0.35.58`–`v0.35.59`).

**...and a sixth, after the promotion, which is the measurement that says what the
promotion did and did not close** (PR #897 review, `v0.35.96`).
`frozenSchedContextBind` and `frozenSchedContextUnbind` were still keeping a
`donationOrigin` the live kernel erases — the `v0.35.52` correction's own class,
one operation over — and sweeping the **operation** rather than the field found
three more: the live bind refuses four things and the mirror refused one, and it
did not propagate `sc.priority` to the bound TCB, so every frozen post-bind state
falsified `boundThreadPriorityConsistent`.  Every one of those was invisible to
the promotion, because putting a module in the library root fixes which
*definitions* a gate can see and says nothing about whether a mirror **agrees**
with what it mirrors.  That second half is `docs/REGISTERED_DEBT.md` table C's
open row — a second implementation (the architecture's own *execute* phase, not a
test double) whose fidelity is checked by a hand-written scenario list — and the measurement here is what it costs: the three
missing refusals sit on an operation `frozenBranchDifferentiallyChecked` does not
name, so no `frozenRunAgrees` comparison could have reached them and none did.
**Promotion into the root is necessary and is not the fidelity check**; until the
coverage set is derived, a cut that touches a live transition with a frozen mirror
sweeps the mirror by reading both, and a cut that adds a *field* to a shared record
sweeps every writer of it on both surfaces.

**...and a seventh, where the divergence is inside ONE DECLARATION: a primitive
that guards its principal and not its neighbours** (PR #897 review, `v0.35.146`).
The three queue primitives resolve the thread they are *about* through
`frozenLookupTcb` -- which refuses a reserved id exactly as the live `lookupTcb`
does -- and read the queue's **tail**, **predecessor** and **successor** with the
bare `getTcb?` two lines below.  So a queue whose neighbour sits at
`ThreadId.sentinel` was accepted here and refused `.objectNotFound` by
`endpointQueueEnqueue` / `endpointQueueRemoveDual`.  No scenario driving the
principal could see it, and **none driving the neighbour existed** -- every fixture
on this surface exercises the thread a primitive is *about*, which is the half
that was already guarded.  Not because the states are unreachable:
`Builder.createObject` accepts a reserved `ObjId`, measured, and the cut's own
first reading had asserted the opposite and built its fixtures by hand on the
strength of it.  (`BootstrapBuilder.withObject` does refuse the slot, and
generalising from that one builder to both was the error.)  **When a declaration
resolves two threads, ask whether it resolves them the same way**; a shared name
two lines apart reads as one convention and is not -- and *a claim about what a
builder will not accept is measured, not inferred from its sibling.*

**And a MISSING WRITE is not a refusal, so no refusal-set comparison can find
it.**  The fourth site in that cut is the one no review reported and the worse
of the two kinds: `frozenQueuePopHead` wrote **no successor patch at all**, where
the live `endpointQueuePopHead` promotes the successor to head.  The thread the
pop *makes* the head went on naming the popped one, which fails
`intrusiveQueueWellFormed`'s P2 and -- through `dualQueueRemovalEnabled`'s
`queuePPrevHeadPositionAgrees` factor -- made **every later removal of it
`.illegalState`**: stranded for good, by one ordinary `frozenEndpointSend`
rendezvous into a **two**-deep receive queue, with no hand-built state anywhere.
That is WS-OD OD1.1 / OD3.9's own class -- *a removal that writes one of a node's
two back-pointers and not the other* -- arriving on the surface that has no
theorems to catch it, five cuts after this file recorded the class twice.
Every existing scenario pops from a **one**-deep queue, where there is no
successor and the two programs agree by construction: FO-043's lesson on a
different primitive, *a sweep for fixtures that would break is not a sweep for
fixtures that would exercise*.

Two things that cut records.  **The sweep found no fifth site, and saying so took
the measurement**: six other frozen definitions read `getTcb?` and are *faithful*,
each mirroring a live counterpart that reads the store raw too -- which is why the
Tier 3 negatives are **declaration-bounded** rather than file-wide, a tree-wide one
firing on a clean tree and saying nothing.  And **the two kinds of divergence need
two kinds of anchor**: a respelled read is caught by a negative forbidding the
relation, while a *deleted* store is caught only by the positive over what replaced
it -- *test a gate by breaking the relation, not by deleting the token*, read in
the direction where the defect **is** a deletion.

So: **the gates' domains nearly all key on library-root reachability, which makes
"not in a root" a silent exemption from most of this tree's defences.**  A
mirror deliberately shaped to be compared against production therefore gets the
weakest derivation precisely because it is not production.  The remedy is not a
sixth hand-widened census — that is the recognised set again — but to put the
surface **in the root**, which `SeLe4n.lean` does at `v0.35.60` with two imports
(`FrozenOps.Agreement` and `FrozenOps.Invariant` reach all five modules; the
dependency runs frozen → production and never the reverse, so no cycle closes).

Three things that promotion measured, and the first is the argument for having
done it earlier.  **The build was clean and only one gate fired**: the
content-flow coverage gate's property (C), on `frozenTaintFlow` and
`frozenTaintClear` naming the taint-writing API from outside the declared
propagation surface — because `FrozenSystemState.declassificationTaint` is the
*same* `TaintTable` as the live field.  Tier 0, Tier 2, Tier 3 and the partition
gate all passed.  That the promotion is cheap is not evidence the deferral was
harmless; it is evidence the five corrections had already paid the behavioural
price one cut at a time, and what remained was the **declaration**.

**A frozen writer is declared as a mirror, never folded into the live surface.**
Nothing in `FrozenOps` can move `SystemState.declassificationTaint` — which the
gate's property (C2) decides type-resolved — so adding the two to
`DECLARED_TAINT_WRITERS` would dilute the live one-writer fact into "one live
writer and some others".  `DECLARED_FROZEN_TAINT_WRITERS` maps each frozen
primitive to the live counterpart it reproduces, reconciled in **both**
directions (a key the probe no longer reports is a stale exemption reading as
coverage; a value outside the live surface names a counterpart that does not
exist), which is the shape `ReplyStackWriteCensus`'s `.mirrors` constructor and
`frozenBranchLiveOperation` already use for this question — *find the answer this
tree already has*.  Both directions are mutation-tested.

**And the gate that fired had already written the finding down.**
`DECLARED_TAINT_CONSUMERS`'s own note records a "frozen/live taint-layer
mismatch" that "survived until a differential scenario could start from a tagged
state".  The gate knew the frozen taint layer diverges; it could not see the
divergence, because the constants were not in its environment.  **A gate's
comment naming a hazard it cannot reach is the clearest possible signal that its
domain is too small** — and it sat there unread while five corrections landed
around it.

**And the published METRIC had been calling it production the whole time — which
is why this was reported as a documentation contradiction rather than found by a
gate** (the maintainer's correction, `v0.35.60`).  This is the sharpest part, and
it inverts how the deferral looked from outside.

`scripts/generate_codebase_map.py` computes `prod_paths` as *everything not under
`tests/`*.  So all five `SeLe4n/Kernel/FrozenOps/` modules have been inside
`readme_sync.production_files` (330) and `readme_sync.production_loc` (385,265)
since those figures existed — and those two numbers are mechanically synced into
`README.md`, `docs/spec/SELE4N_SPEC.md`, all **eleven** `docs/i18n/*/README.md`
and GitBook.  Meanwhile the source-layout line said "(experimental)", `SeLe4n.lean`
excluded it, `check_production_staging_partition.sh` had no opinion on it, and
four C.1 rows deferred "promotion into the production chain".

**Four artefacts, three answers to one question, and the artefact that reads as
authoritative was the one nobody had checked** — because it is *derived* and
published in fourteen places, where the others are hand-written prose or a build
file.  A reader who trusts the metric over the prose, which is exactly what this
file tells readers to do everywhere else, concludes FrozenOps is production; a
reader who opens `SeLe4n.lean` concludes it is not.  Both were reading correctly.

Three things follow.  **"Is this production" is one question and must have one
answer**: the import chain is now that answer, and the metric agrees with it
because the metric already did.  **A derived figure is not automatically the right
derivation** — `not under tests/` is a *path* convention standing in for a
*reachability* fact, which is this section's own `a field name is not a receiver
type` shape at the level of a build classification; it was never wrong about the
line count, only about what "production" names.  And **a contradiction between a
published metric and a build file will be reported by a person, not a gate**,
because no gate reads both: the partition gate reads the roots and the map reads
the filesystem, and nothing reconciles them.  That reconciliation is the check this
class needs, and `v0.35.60` makes it *true* rather than *checked* — the surface is
in the root, so the two agree — which is a state a later cut can silently break.

**Running that reconciliation by hand found one more, and getting the number right
took three attempts.**  Of the **331** files the metric counts as production,
**251** are in this root's closure and the rest are reached by `Platform.Staged`,
by a Tier 1 census, or by one of the 71 `lean_exe` roots — all but **one**:
`SeLe4n/Kernel/RadixTree.lean`, a re-export hub with zero in-tree consumers that
**no build target compiled**.  Its three re-exports were therefore never checked
as a unit, so a re-export naming a renamed or deleted submodule was invisible.
`SeLe4n.lean` imports the hub now; the count is zero.

  **A fourth measurement, with the roots as the criterion, found five more**
  (`v0.35.76`).  The count above accepted a `lean_exe` or a census as reach,
  and that is not the criterion the Tier 1 censuses' environments use: each
  imports `SeLe4n` and `SeLe4n.Platform.Staged`, so a module reached only by a
  test executable is outside every one of them.  The store-access census's
  domain reconciliation (below) found the first — `ChainFootprint`, whose RR7.40
  header said PRODUCTION while no root imported it — and re-measuring with the
  two roots as the criterion found five non-test modules outside both: that one,
  its `CSpaceWalkFootprint` sibling with the same RR7.41 header, the
  `FrozenOps` and `Scheduler/PriorityInheritance` re-export hubs (RadixTree's
  shape, reached by test suites alone), and `Architecture/VSpaceARMv8`, which
  §8.15.1 of the spec had recorded as *test-anchored, not production-imported*
  for thirty minor versions.  Three went into the root (both hubs, and
  `ChainFootprint` with its one staged dependency `DynamicChainExtension`, every
  import of which was already production); two are staged with a `STATUS`
  marker each — `CSpaceWalkFootprint` because its conflict theorem is stated
  against SM3.E's `ktiSharesConflictingLock`, so its chain runs through
  `Serializability` → `Deadlock`, which the RR7.18 decision keeps out of the
  image, and `VSpaceARMv8` because it is on no execution path.  A header's
  PRODUCTION is a claim the import chain decides, and two such claims stood for
  fifty-two minor versions with nothing deciding them.

The three attempts are the finding's own epilogue, and they are this section's
*a measurement can carry the defect it is sizing* rule applied to me.  The first
reported **80** orphans, because the allowlist parser ignored the trailing
` # comment` on every entry and matched none of the 67.  The second reported
**7**, because it walked only the two roots, the staged anchor and the six
censuses, and forgot the `lean_exe` targets — which build most of what was left.
The third, reading all 71 roots out of `lakefile.toml`, reported **1**.  Two of
those three numbers would have justified a much larger claim than the tree
supports, and the only reason the first was not believed is that 80 looked wrong
enough to re-derive.  **A measurement that licenses a conclusion gets checked as
hard as the conclusion** — and a domain measured by hand needs its own domain
checked, which is the rule this whole section is about, arriving one level up.

**And a shared answer must be REACHABLE from every asker, or the unreachable one
grows its own** (`v0.35.59`).  This file's most-repeated rule is *one question
answered in two places will diverge*, and its remedy has always been to give the
question one owner.  The frozen removal is the case that shows the remedy is
incomplete: `dualQueueRemovalGuard` **had** one owner, in
`SeLe4n/Kernel/IPC/DualQueue/Core.lean`, and the one surface whose whole purpose is
to be compared against the operation that reads it **could not import it** — so it
answered the question itself, with one factor, and the divergence was not a second
implementation drifting from a first but a *layer boundary* standing between an
asker and the only answer.  The two failure modes are indistinguishable in a diff
and have opposite remedies: drift is fixed by deleting a copy, and this is fixed by
**moving the original down** to the layer both askers reach.  So: when a question
has one owner and an asker that cannot see it, the owner is in the wrong layer.
`dualQueueRemovalGuard`, `queueTailPairAgrees`, `queuePPrevHeadPositionAgrees`,
`queueLinkPairAgrees` and `tcbWithQueueLinks` are in `Model/Object/Types.lean` now,
beside the records they read and beside `queueRemoveBoundary` — the predicate is
over an `IntrusiveQueue`, a `ThreadId`, a `TCB` and a `QueuePPrev`, every one a
model record, so the IPC layer never had a claim on it.  Its **discharges** stayed
in the kernel layer (`dualQueueRemovalGuardHolds`,
`queueTailPairAgrees_of_wellFormed`), because those read `ipcInvariantFull`, and
that split is the test of whether a relocation is a layering fix or a layering
violation: the *predicate* moves, the *invariants that entail it* do not.

**And moving the answer is not enough if the QUESTION was never named — a named
condition beside unnamed ones is a subset, and reaching it through a shared
definition reads like agreement.**  This is the sharper half, and it was found by
auditing the fix rather than by a review: the first attempt relocated
`dualQueueRemovalGuard` and had the mirror call it, and that mirror **still**
succeeded where the kernel refuses.  `endpointQueueRemoveDual` refuses *four*
things before it writes anything, and only one of them had a name — the one an
invariant discharges, which is why it got named.  Beside it sat an unnamed
`if q.head.isNone || q.tail.isNone`, an unnamed `prevTcb.queueNext ≠ some tid` in
the predecessor patch, and an arm answering `.endpointQueueEmpty` where the mirror
answered `.illegalState` (and `frozenRunAgrees` compares codes, so that one was
visible to the differential all along, invisible only because nothing drove both
sides to it).  A state with an **empty queue** and `pprev = .tcbNext p` passes the
guard outright — `q.head ≠ some tid` holds vacuously for `none`, the link pair
agrees, and the tail pair agrees because both sides of it are false — so the
guard-carrying mirror would have unlinked a node from a queue that has none.

So the remedy is not a better shared *answer* but a named shared **question**:
`dualQueueRemovalEnabled` is the whole store-free precondition, both removals read
it, and a condition added to it reaches both by construction.  The one factor that
needs a store lookup cannot fold in, so it is `queuePredecessorNamesSuccessor`,
named and read by both sides, each resolving its own `prevTcb`.  **A checker for
this class must ask whether the refusal SETS agree, never whether a shared name is
called** — the anchors that pin it are the two removals' conditions *and* a
negative that refuses the guard-alone spelling coming back, because that spelling
keeps every token.  Generalising: when you relocate a definition so a second asker
can reach it, enumerate what the *first* asker does that the definition does not
cover; a named condition is the one a proof needed, not the one an operation
performs.

Four things this cut recorded rather than predicted.  **The registered cost was
wrong in the cheap direction, and that is an argument, not luck**: the debt row
said the closure must pay "whatever fixture cost the newly-refused states carry",
and it carried none — the newly-refused states are states the *kernel already
refused*, so nothing in the tree was on one, `frozenRunAgrees` is unmoved and the
golden trace is byte-identical.  A guard that only ever refuses what its subject
refuses cannot cost a fixture; that is what distinguishes tightening a mirror from
tightening an operation, and it is worth checking before deferring one.  **A
relocation that repairs no proof is the evidence the layer was wrong**: 233 lines
moved and nothing needed fixing, which is exactly what one expects when a
definition had no dependency on the layer it was sitting in.  **Collapsing two
`if`s into one costs a tactic, and the tactic says where the proofs were reading
structure**: eleven proofs across five modules needed `cases pprev` moved *ahead*
of their `split`, because unfolding the enabling condition exposes the guard's own
`match pprev` inside the `if`, and `split` takes that first — a mechanical repair,
and a reminder that a proof that splits on an `if` is coupled to how many `if`s
there are.  And **the witness must be decisive about *which* refusal is new**:
`FO-045` computes the retired `isNone`-only reading beside the live guard on a
state violating the **tail** factor and no other, and `FO-046` adds one half per
remaining refusal, each on a state that passes everything the previous half checks
and is refused by exactly one more thing.  All four were mutation-tested by
reverting the refusal each is about, and the fourth mutation is the one worth
keeping: `lake env lean --run` elaborates against existing oleans, so a mutation of
a *dependency* reads as PASS until the dependency is rebuilt — the first run of M1
reported green over the reverted fix.

**The cancellation footprint is arm-selected, and `.replyRecv` declares the
hand-off it was hiding** (OD3.5, `v0.34.128`).  Two changes with one cause: a
member the code writes and the footprint does not name is *false*, and this row
found both directions of that.

**The victim's splice neighbours are declared on the arm that splices.**
`queueSpliceNeighbors?` was the one resolver in the cancellation family that
did not key on `tcb.ipcState` — every other member selects an arm and this pair
was summed over all of them — so the reply and notification arms declared two
TCB write locks for a splice they do not perform.  `cancelArmSpliceNeighbors?`
is *derived* from `cancelBlockedEndpoint?`, so the arm question is asked once,
and the widest arm drops from ten members to eight
(`lockSet_cancelIpcBlockingOnCore_size_le_ten` since OD3.7 raised it again -- that
name is not live, the bound having been re-based since to
`lockSet_cancelIpcBlockingOnCore_size_le_thirteen` -- with
`_replyArm_eq` and `_endpointArm_covers_prev` / `_next` pinning both
directions).  Over-declaring is sound and **not free**: lock contention is an
observable channel (SM8.D's CC-5), so a footprint wider than its operation
carries contention that says nothing about the operation.  What licenses the
narrowing is checked rather than read off the definition, on every arm:
`cancelIpcBlocking_notificationArm_tcb_frame`,
`cancelIpcBlocking_replyArm_noDonation_tcb_frame` and — with the reclaim live —
`cancelIpcBlocking_replyArm_tcb_frame`, which composes the four frames the tree
lacked (`endpointQueueRemove_objects_ne`,
`abortPendingIpcOnEndpoint_other_tcb_eq`, `abortHolderPendingIpc_other_tcb_eq`,
`returnDonatedSchedContext_other_tcb_eq` — each stating a step's effect *outside*
its write set).  The arm rewrites exactly the holder, its two queue neighbours
and the cancelled caller, all four declared, so the victim's own links are stale
references to threads it never touches.  Two notes for new code.  (1)
`endpointQueueRemove`'s two link patches are pinned to `queueNeighbourPatch` by
`rfl` (`endpointQueueRemove_eq_patches`), so the removal's write set is one
lemma rather than a four-deep nested match, and the tree's third inlined copy of
that shape is gone.  (2) `returnDonatedSchedContext_other_tcb_eq` and
`_tcb_rewrite` are different statements and neither implies the other — one
permits a binding change at any key, the other permits no change at these keys —
so a footprint argument must reach for the former.

**`.replyRecv` performs two SchedContext hand-offs and declared one.**
`replyRecvReturnDonation` returns the recorded server's donation and then, when
the receive leg dequeues a queued `Call`, runs
`applyCallDonationOnCore nextThread tid` — whose `donateSchedContext` writes the
**new** caller's SchedContext, provably not the returned one.  That is the
passive-server steady state, not an edge case: the receiver is `.unbound` at
that point precisely because the return just made it so.  So the tree's
most-travelled IPC path wrote a kernel object under no declared lock, and a
`.replyRecv` on one core and a `.tcbSuspend` of that queued caller on another had
provably disjoint footprints while both writing it.  Four things new code must
respect.  (1) **The member is resolved through `.call`'s own resolver**
(`receiveRendezvousDonatedSc?` over `endpointCallDonatedSc?` at the send-queue head),
because it is the same question — `.call` has declared this member since SM6.A.5
and said why.  (2) **The recorded server's TCB is declared unconditionally**, so
a *delegated* reply declares like any other: PR #892 review round 6's refusal
(`lockSetForSyscall_replyRecv_delegated`, concluding `none`) is retired and
replaced by `_delegated_declares`.  (3) **`maxLockSetSize` is 11 at this cut**, and that is
the cost: `admissibleCriticalSection` for the 1 ms tick falls from 37 µs to
30 µs, and the CC-5 bound widens in proportion.  (OD3.7 moves it again, to 13 and
25 µs — see the bullet below.)  The alternative was a narrower
declaration on the hottest path, and this project rates a footprint that omits a
written lock worse than a wide one.  (4) **`SystemState.scThreadIndex` is an
`RHTable`**, so every donation and every return takes `stateLevelLock` — an
insert may rehash and back-shift the whole table, exactly as the CDT maps do
(RR7.9/RR7.11), and no per-object member can cover it.  Declared on
`lockSet_endpointCall`, `lockSet_endpointReply`, `lockSet_replyRecv`,
`lockSet_tcbSuspend`, `lockSet_cancelIpcBlocking` and `lockSet_cancelDonation`
conditioned on each one's own SchedContext resolver, and unconditionally on
`lockSet_schedContextBind` / `_Unbind`, whose index write is not optional on the
success path.  `.schedContextConfigure` is split out of their `permittedKinds`
row rather than widened with them: it writes no index.

**...and `.receive` performs one it never declared, because it never performed
it at all** (OD3.6, `v0.34.129`).  seL4-MCS's `receiveIPC` hands a dequeued
`Call` caller's scheduling context to a passive receiver (`reply_push` →
`schedContext_donate`); `.replyRecv` did that here and `.receive` did nothing, so
a passive server taking its **first** request with `seL4_Recv` ran the client's
work charged to no reservation while the same server taking its second and later
requests with `seL4_ReplyRecv` was charged correctly.  Nothing caught it because
the server is not wedged — `resolveEffectivePrioDeadline`'s `.unbound` arm falls
back to the legacy TCB priority, so it runs, on nobody's budget.  Five things new
code must respect.  (1) **The step is one definition**
(`applyReceiveRendezvousDonation` over `applyRendezvousCallDonation` and the
guard `rendezvousDequeuedCall`, in `IPC/Operations/Donation.lean`), called by
both `.receive` arms **and** by `replyRecvReturnDonation`: a second copy of the
donation would be the same defect one level up, and a Tier 3 negative refuses the
inlined `applyCallDonationOnCore` returning.  The resolver is shared the same
way — `receiveRendezvousDonatedSc?` is derived from `receiveRendezvousSender?`,
the resolver `receiveInstallsCaps` and the `senderTid` member already use, rather
than re-reading `sendQ.head`.  (2) **The guard *is* the caller-blocked
obligation**: `rendezvousDequeuedCall_blockedOnReply` discharges
`applyCallDonationOnCore_preserves_ipcInvariantFull`'s donor hypothesis from the
predicate the arm branches on, so the two cannot disagree about which states
donate; only the whole-store `hReceiverNotOwner` survives, as a `recvStage`
conjunct of `syscallDispatchQuiescence` stated over the receive stage's committed
state — the shape `replyRecvStage` already used for the reply leg.  (3) **The
step is inert where it must not fire**: `applyCallDonation` no-ops unless the
receiver is `.unbound` **and** the donor `.bound`, and the guard is false for a
receive that blocked and for a plain `Send` rendezvous, so every result taken
before OD3.6 survives on the states it held for.  (4) **The checked arm needs no
extra gate** — the donation writes only `schedContextBinding` and
`SchedContext.boundThread`, both erased by `projectKernelObject`, and the
endpoint→receiver flow it follows is gated above it; but the delegation theorem
and the `syscallDelegates .receive` obligation both **name** the step, since a
delegation claim that omits one is a claim about a different program.  (5)
**`lockSet_endpointReceive`'s state-level member is a disjunction**, and that is
not cosmetic: conditioning it on `installsCaps` alone omits it on exactly the
passive-server path, which donates and installs nothing.  `permittedKinds
.receive` gains `.schedContext`, the size bound is restated at the new arity
(`3 + 4 = 7 ≤ 11`), and `maxLockSetSize` does not move.

**...and the pop declares the two objects it reads below the head** (OD3.7,
`v0.34.130`).  `returnDonatedSchedContext` at call depth ≥ 2 walks one link past
the reply-stack head to find the outer caller (`replyStackOuterCaller?`) and then
reads that caller's TCB to validate it (`outerCallerAcceptable`).  Neither object
is covered by another member — the head Reply *is* the answered caller's own
`replyObject`, and the outer caller is provably neither thread the pop rewrites —
so a footprint that omits them is *false* at depth ≥ 2, and the TCB read is a
**validate-then-commit**, which makes an unlocked read a time-of-check/time-of-use
window on exactly the thread about to receive a scheduling context.  Five things
new code must respect.  (1) **The pop is O(1) at any chain depth** — one frame of
lookahead, no more — so this is a constant `+2` on the footprint rather than
`O(depth)`; a pop that traversed the chain could not be given a footprint at all,
since a `LockSet` is capped at `maxLockSetSize` and a chain is not.  (2) **Both
members are read-mode**, and Tier 3 negatives refuse the write spelling.  (3)
**One resolver answers for all three arms**: `replyStackBelowHeadReads?`, with
`cancelBelowHeadReads?` deriving the cancellation arm's pair from
`cancelledCallerDonation?` — the plan row named only the first read, and the
second is derived from the operation, which is the enumeration-versus-derivation
rule applied to a footprint.  (4) **`maxLockSetSize` was 13 at this cut and is
14 since OD3.13**: `admissibleCriticalSection` for the 1 ms tick fell to 25 µs
and then to **23 µs**, and the uniform envelope moved to 2340 and then 2520 µs,
all derived from the constant.  **Only `.replyRecv`
needed the raise** — `lockSet_endpointReply` reaches nine and the cancellation
reply arm ten (`lockSet_cancelIpcBlockingOnCore_size_le_ten` at that cut; the live
bound is `lockSet_cancelIpcBlockingOnCore_size_le_thirteen`) — and that is
asserted rather than described.  (5) **Both members are `none` on every state
this tree reaches**, so no live footprint widened; this declares ahead of OD4.4's
code, which is the order the numbering rule requires.

**And how much of that ceiling is slack is stated, not left to be re-derived**
(OD3.7 sharp bound, `v0.34.131`).  Thirteen is the union over *all* argument
values; a reachable `.replyRecv` declares **twelve**
(`lockSet_endpointReplyRecvOnCore_size_le_thirteen` at that cut; the live bound is
`lockSet_endpointReplyRecvOnCore_size_le_eighteen`), because the donation a reply
returns is owned by the thread the reply answers, so two arguments name one key
and `insertOrMerge` lubs the modes without moving the cardinality.  Three things
new code must respect.  (1) **The equality is a stated hypothesis**
(`replyDonationOwnerIsAnsweredCaller`), not a consequence of the bundle:
`donationOwnerValid` says only that the owner is `.unbound` and `.blockedOnReply
epId rt` for *some* `rt`, and relates `rt` to no donation — the gap WS-RR RR7.22
met from the cancellation end and closed with `donationHolderIsReplyTarget`, which
WS-HP HP5.3 re-keyed onto the frame as `donatedContextIsOwnerFrameHead`.  (2)
**One member is the whole of the sharpening**: the recorded server merges with
the invoking thread only on a *non-delegated* reply, a case split rather than an
invariant, and the delegated case is the one OD3.5 exists to declare.  (3) **The
sharp bound is not the ceiling** — `maxLockSetSize` is what
`boundedWait_under_2pl` and the WCRT surface consume and must stay true of every
argument value, so a Tier 3 negative refuses restating it as such.

**And the pop preserves the chain, which is what makes the predicate an
obligation** (OD3.8, `v0.34.132`).  Almost every transition in the tree
discharges `donationChainWellFormed` through `donationChainFrame` — it writes no
`Reply.prev`, no `Reply.next` and no `SchedContext.scReply`, so the two
projections the walk reads are fixed — and the pop is the exception that family
was designed against.  With
`returnDonatedSchedContext_preserves_donationChainWellFormed` the pop stopped
being that exception.  **The universal it established is not the state of the
tree at HEAD**, and a reader must not take it for one: `v0.35.4` made the stack
doubly linked, so the mid-stack *splice* is a second writer of chain data (it
preserves the predicate, `spliceReplyFrameOut_preserves_donationChainWellFormed`),
and the reply path's `consumeCallerReply` falsifies `prevLinkReciprocal` on a
frame that is not a head — the WS-RM residual recorded two sections above.  New
code must not assume `donationChainWellFormed` of a state reached by replying to
a caller whose frame has a frame above it.
Five things new code must respect.  (1) **Acyclicity is derived, not assumed**:
clearing the popped head's links is sound for the rest of that context's stack
only if no frame below links back to it, and `donationChainFrom_head_not_mem_tail`
reads that off the invariant's own *termination* clause — the walk is a function
of its starting point (`donationChainFrom_deterministic`, over
`donationChainFrom_mono_le` and `donationChainFrom_suffix_walk`), so a head
appearing again below itself would make the walk from that occurrence return the
whole chain, strictly longer than the suffix it must equal.  A `NoDup` conjunct
would have been an enumeration standing in for a derivation, and a Tier 3
negative refuses one.  (2) **The other half is freshness, and it already existed**:
`not_mem_donationChainFrom_of_not_donating` says the popped head, which donates
*this* context, is on no other context's chain — the same lemma OD4's push
consumes from the other side.  (3) **The congruence is chain-scoped**:
`donationChainFrom_congr` asks agreement at *every* key and is false of a step
that rewrites one, so `donationChainFrom_congr_on_chain` asks it only at the
chain's own members, which is exactly what the walk reads.  (4) **Unconditional in
`newOwner?`** — the pop's TCB stores write `schedContextBinding`, which is not
chain data at any depth, so unlike the `ipcInvariantFull` composite nothing here
is `hBottom`-conditioned.  (5) **Exercised on the `some` arm**: a theorem
discharged only where the context heads no stack is indistinguishable from one
whose writing arm is wrong, so OD2.4's depth-2 witness is popped
(`donationChainWitness_pop_wellFormed`) and the state the pop leaves is shown to
head exactly the *tail* of the stack it started with
(`donationChainWitness_pop_chain`).  At the time of that cut the predicate was
still vacuous on every state this tree reaches — the pop's writing arm needed a
stack nothing yet constructed — and the prose that said "no transition writes"
the three fields was corrected wherever it appeared.  **OD4.1 (`v0.35.2`) ends
the vacuity**: a depth-2 Call builds a two-frame stack, so the pop's `some` arm
is reachable and the exercised witness is the live shape rather than a
construction.

**The pop is live and inert** (OD3.1–OD3.3, `v0.34.126`).
`returnDonatedSchedContext` takes a `newOwner? : Option ThreadId` and is four
object writes — the SchedContext rebind **and** stack pop as one store, the pop
itself (`storeDonationHeadPop`: the head's links cleared, then the frame below
**re-headed** to this context), the target's
`donationReturnBinding scId newOwner?`, the server's `.unbound` — and
`returnDonatedSchedContext_eq_legacy_of_none` proves that at `newOwner? = none`
over a context heading no stack it **is** the pre-OD3 body.  All six call sites
thread OD3.4's resolver since OD4.4 (`v0.35.2`).  Six things new code must
respect.  (1) **The head validation is fail-closed**: `donationHeadOf?` refuses a
head resolving to no Reply, or to one donating a different context, rather than
reading it as an empty stack — the same posture as RR2.8's `boundThread` guard,
and what rules that arm out is `donationHeadResolves`, established either from
`donationChainWellFormed` or across any step writing no chain object
(`donationHeadResolves_of_frame`).  A theorem asserting the return **succeeds**
therefore states it.  (2) **The `_ok_storeChain` decomposition is the only
description of the operation**: `returnDonatedSchedContext_walk` is retired as
its weaker duplicate, and a new field frame is a corollary rather than a copy of
the case analysis — sixteen such copies went with the fourth store.  (3) **The
return writes a Reply**, so `_preserves_reply` is gone: `_reply_frame` says a
Reply survives with at most its stack links reset (`replyStackRewrite`), and its
`caller` — all the reply-freshness and stash invariants read — agrees exactly.
For the same reason `replyLinkageFrame.replyAgree` and
`donationReadAgreement.otherKind` state the **caller-level** correspondence;
a transition with full Reply identity supplies it through
`callerAgree_of_objectAgree`.  (4) **The binding trichotomy widens at the
target**: `_tcb_schedContextBinding_backward`'s middle clause is
`donationReturnBinding scId newOwner?`, and both its arms name the same context
(`donationReturnBinding_scId?`), so `scThreadIndex` is insensitive to stack
depth.  (5) **The depth-≥ 2 obligation is `donationReturnOuterValid`** — the
outer caller is a TCB that gave up its binding and waits on its reply, and is
neither the rebound thread nor the server — vacuous at `none`, and
`donationOwnerValid`, `donationOwnerUnique` and `donationBudgetTransfer` are
general under it.  The *composite*
`returnDonatedSchedContext_establishes_ipcInvariantFull_of_except` was not, and
said so: it took `hBottom : newOwner? = none`.  **OD4.3 (`v0.35.2`) removed
that**, before OD4.1's push made the arm reachable, so the composite now covers a
depth-≥ 2 return under `donationReturnOuterValid` like every other statement in
the family.  (6) **The return is invisible to every observer,
not merely a high one**: every field it writes is stripped by
`projectKernelObject`, so `returnDonatedSchedContext_preserves_projection` no
longer carries an observability hypothesis on the server.

**And the header's donation inventories were a third copy of `permittedKinds`**
(OD3.18, `v0.34.145`).  Found by running the sweep rule on the previous cut
rather than by a review: OD3.17 corrected a contract that denied a hand-off its
own footprint declares, and the same question was answered a second time --
wrongly, three ways -- in the same file's module header.  `.receive` sat under
*syscalls that do NOT need donation extension* for twelve cuts after OD3.6 gave
it a `donatedScId`; `lockSet_replyRecv`'s entry repeated the retired sentence
word for word; and `tcbSetPriority`, `tcbSetMCPriority` and `tcbSetAffinity` --
each writing the target's **bound SchedContext**, because priority and home core
live there -- were called *TCB-only config ops*, with `tcbSetAffinity` in neither
list.  Three things new code must respect.  (1) **`permittedKinds` is the
canonical inventory, and it is proven rather than parallel**: a footprint may
name a SchedContext lock exactly when `.schedContext ∈ permittedKinds <arm>`, and
the `lockSet_consistent_<arm>` family states `∀ p ∈ (lockSet_<arm> …).pairs,
p.fst.kind ∈ permittedKinds <arm>` at each footprint's **full arity**, so a
member added without the kind being permitted fails to elaborate.  A prose list
restating it is a copy that can drift and did.  (2) **The cut adds no checker,
deliberately.**  Its first attempt was a Tier 1 census walking each footprint's
elaborated body for `schedContextLock`; it took six corrections in a row -- a
name-prefix frontier a differently-named helper defeats, a tuned rather than
derived bound, a skip set right for the narrow frontier and wrong for the wide
one, a `getUsedConstants` that pushes per subterm -- which is
`unconditionalActions` again, for the reason recorded above: substituting `Expr`
for text moves the class down a level and does not close it.  It was deleted
before it shipped.  **Before writing a scanner, look for the fact the tree
already proves.**  (3) **The remedy for a duplicated inventory is deleting the
duplicate**, not adding a third artefact to reconcile the first two.

**And a donation moves budget, deadline and domain — never priority** (`v0.35.3`,
reported while closing this workstream).  `updatePrioritySource` classified
`.bound scId` and `.donated scId owner` identically, so `.tcbSetPriority` /
`.tcbSetMCPriority` on a thread *holding* a donated context wrote the **donor's**
`SchedContext.priority` — an authority crossing, since both arms are gated on a
TCB-write right over the *target* and the caller's MCP ceiling, and neither says
anything about the donor; the rewritten field then travelled back with
`returnDonatedSchedContext`.  The remedy is seL4-MCS's own split, not a refusal.
Five things new code must respect.  (1) **The classifier is
`SchedContextBinding.ownScId?`** — the SchedContext a thread *owns*, `some` on
`.bound` and `none` on `.unbound` and `.donated` — and it is where a *new
binding constructor* (WS-CB's hierarchical servers) must be classified.  It is
the counterpart to `scId?`, the one a thread *runs on*, and the two split a
thread's scheduling parameters: **reservation-owned** (budget, period, deadline)
read `scId?` at every binding, **thread-owned** (base priority, domain) are the
thread's, and — **at `v0.35.3`, when this was written** — were **stored in two
places** for a `.bound` thread: the TCB field and, mirrored onto it by the AK2-B
convention, `ownScId?`'s SchedContext.  Which one a *reader* took was not uniform
and that was the hazard — `threadBasePriority` read the *reservation* at `.bound`
while `TCB.boostedPriority`, which every run-queue insert is keyed by, read the
*thread* — so every writer of either had to move both, which is
`boundThreadPriorityConsistent` and which `v0.35.98` found `.tcbSetPriority` not
doing.  **The improvement named here — one home, not two kept in sync — was
taken**: `v0.35.133` for the band and `v0.35.136` for the domain, so no reader
consults a reservation for either and the standing constraint below is the live
text.  What the collapse did *not* do is retire the invariant, because the
**writes** remain two: PR #897's review found the pair falsifiable on a reachable
donation pop, which is its own table C row and which the two predicates'
docstrings now state.  `ownScId?` is a **narrowing** of `scId?`
(`ownScId?_eq_scId?_of_isSome`), so the two can never name different contexts.  (2) **The one answer is
`SystemState.threadBasePriority`**, and a new priority reader calls it rather
than matching the binding.  The three scheduler resolvers also need the
reservation's deadline or domain, so they split the arm and are tied back by
theorem — `resolveEffectivePrioDeadline_fst_eq_threadBasePriority` (new,
unconditional), `effectiveSchedParams_priority_deadline_eq_resolve`,
`effectiveBucketPriority_eq_resolveEffective`, and
`getCurrentPriority_eq_threadBasePriority` by `rfl`.  A Tier 3 negative refuses
the merged arm **per declaration**, because `hasSufficientBudget` three lines
above keeps it and a file-wide negative would fire on a clean tree; five budget
predicates are pinned as *still merged*, so the split cannot leak into the budget
question.  (3) **`boundThreadPriorityConsistent` ranges over `.bound` alone.**
Quantified over `scId?` it covered `.donated` too, and **the donation falsifies
it** whenever the donor's and the donee's base priorities differ: the
reservation's `priority` must equal the donor's before the hand-off and the
donee's after, and `donateSchedContext` writes neither field.  Nothing carries
it across either — the frame that transports it requires `schedContextBinding`
unchanged, which is precisely what the hand-off rewrites.  So it was false on
exactly the states WS-OD had just made reachable, and every result gated on it
was silent there.  (4) **The bucket invariants follow the read**: a donee's recorded
run-queue bucket is its own base priority, so `effectiveParamsMatchRunQueue`'s
`.donated` arm *is* its `.unbound` arm.  (5) **`propagatePipChainCrossCore` is
now the only priority route** between a client and the server it calls, which is
what keeps inversion bounded and what makes OD3.14's `.receive`-arm walk
load-bearing rather than a second-order correction.

**And the mirror crossing goes with it — the domain as well as the priority.**
`schedContextConfigure` propagates **both** thread-owned parameters into
`sc.boundThread`'s TCB, and after a donation `boundThread` is the **donee** — so
a capability on the *client's* reservation could rewrite the *server's* own base
priority and **migrate its scheduling domain**, permanently, since the donee
keeps both fields after the donation returns.  A domain is the partition
temporal isolation is defined over, which makes that half the more serious of
the two, and either would have been the one remaining route by which a client's
reservation sets a server's band.  Both halves maintain a `.bound`-only
invariant (`boundThreadPriorityConsistent`, `boundThreadDomainConsistent`), so
`schedContextConfigureBoundPropagate` takes the SchedContext's id and gates both
on the bound thread **owning** it, through **one** predicate
(`schedContextConfigurePropagates`) that both halves consult — so a later cut
cannot gate one and leave the other.  A reconfiguration still rewrites the
reservation itself, budget and period included: that is the object the caller
holds a capability for.  The reading side follows —
`effectiveSchedParams`'s `.donated` arm reports the donee's **own** domain,
because every live domain filter reads `tcb.domain`, so reporting `sc.domain`
described a partition the scheduler never puts a donee in; that component has no
live consumer today, which is why it had to be corrected rather than left for
the first one to inherit.  Registered debt closed;
`docs/REGISTERED_DEBT.md`'s WS-OD section records the closure.

**And the reply stack is doubly linked, so no frame is left on it with its caller
gone** (`v0.35.4`, reported while closing this workstream).  `severAtCut` was
implemented by *leaving a frame behind*: a cancelled middle caller's frame stayed
on its stack with its `caller` consumed, the later pop read it as the bottom of
the stack and bound the context outright, and that frame then **headed** the
context forever — the Reply object and the SchedContext could never be retyped,
and the Reply could never be linked to a new caller.  Reachable from an ordinary
`.tcbSuspend` on a client at call depth >= 3, with no more authority than a TCB
write right over a thread in one's own call chain.  Six things new code must
respect.  (1) **`Reply.donatedSc` is gone**; the upward link is
`Reply.next : ReplyStackLink`, a sum of `.frame above` and `.head sc`, so
"heads a context", "has a frame above" and "off every stack" are three states of
one value.  The context is recorded on the head frame **alone**, which is what
makes a mid-stack removal an `O(1)` repair of two neighbours rather than a walk
clearing a per-frame field below the cut.  (2) **`Reply.wellFormed` is
`caller = none → prev = none ∧ next = none`** — seL4's `reply_unlink` invariant —
and `Reply.isFree` is its decidable form, the one spelling of "this Reply may be
linked or retyped", shared by the link guard, the stash admission, the retype
guard and the boot check.  (3) **The walk validates reciprocity, not a donation**:
`donationChainFrom` follows a `prev` only when the target's own `next` answers the
frame that reached it, and the expectation **advances** (`.head scId` at the head,
`.frame` of the previous frame thereafter), so a frame claiming to head the
context at depth 2 is refused.  (4) **The pop writes the frame below the head**:
`storeDonationHeadPop` clears the head's links and then **re-heads** that frame,
so the below-head footprint member is a *write*, not a read.  (5) **The
cancellation path splices before it consumes** (`spliceThreadReplyFrameOut`
over `spliceReplyFrameOut`, between the reclaim and `consumeReplyLink`), and a
validated below-head frame whose caller was consumed is now an `.error`, never
the bottom of the stack.  (6) **`maxLockSetSize` went to 16 at this cut** — the
pop's new write plus the suspend pipeline's second pop; it is **21** at HEAD, and
the per-lock cost and envelope it implies are stated once, in the canonical
sentence this file carries above.

**And a delegated `.replyRecv` declares the invoking receiver's own pre-receive
return** (PR #894's review, `v0.35.5`).  That arm's receive leg **is**
`.receive`'s transition, so when the endpoint has no queued sender it runs
`cleanupPreReceiveDonationChecked` on the **invoker** — and the arm's own
donation return runs *after* the receive leg, so the invoker still carries
whatever `.donated` binding it entered with.  On a non-delegated reply the
recorded server *is* the invoker and the reply leg has just made it `.unbound`,
so that second pop is inert; **delegation is exactly what breaks the
coincidence**, and WS-OD OD3.5 had already retired the refusal
(`lockSetForSyscall_replyRecv_delegated`) that used to keep the delegated shape
out of the declared set.  Two threads cannot be bound to one scheduling context,
so the recorded server's members provably never alias the invoker's: a delegated
`.replyRecv` wrote a SchedContext, the previous owner's TCB and two Reply objects
under no declared lock, and read a third TCB it was about to hand a context to.
Four things new code must respect.  (1) **The five members are the same five
`lockSet_endpointReceive` declares**, resolved through the same two resolvers on
`replier` (`lockSet_endpointReplyRecvOnCore_covers_preReturn`); a Tier 3 negative
refuses resolving them on `target`.  (2) **The state-level member has a fourth
disjunct** — on a delegated reply whose recorded server holds no donation the
other three are all false, so without it the `scThreadIndex` write is undeclared
on exactly the shape the member exists for.  (3) **`maxLockSetSize` is 21**, and
that is the cost: `admissibleCriticalSection` falls to 15 µs on the 1 ms
tick, down from 20.  (4) **No
*reachable* state declares twenty-one**: the re-donation members fire exactly
when the endpoint has a queued sender and the pre-receive return exactly when it
does not, so `lockSet_endpointReplyRecvOnCore_size_le_eighteen` bounds every
state at **eighteen** with no hypothesis.  (The owner merge that used to take a
reachable `.replyRecv` to seventeen is retired at WS-HP HP6.2 — see below.)
Twenty-one is what the *definition* can produce,
which is what `boundedWait_under_2pl` and the WCRT surface must consume.  The
gap was excused by `lockSetForSyscall_replyRecv_refuses_donated_delegate`, **a
theorem that was never written**; it is deleted.

**And the bind guard asks reciprocity, not presence** (PR #894's review,
`v0.35.5`).  `replyFrameOnLiveStack` asked `r.next.isSome`, and `severAtCut`
deliberately leaves the frame *below* the cut with a stale upward link — so a
thread on no live stack, owed nothing, had its `schedContextBind` refused with
`.illegalState`, on a path the transition explicitly supports (it binds a
**blocked** thread).  The guard now asks the walk's own test: `.frame above`
counts only when `above.prev = some rid`, `.head sc` only when
`sc.scReply = some rid`.  It is `O(1)` and **exact** under
`donationChainWellFormed`, where `prevLinkReciprocal` and `headTerminates` make
one-step reciprocity equivalent to liveness, and a live frame still reads `true`,
so the fail-closed direction is unchanged.  In the same cut
`frozenSchedContextUnbind` gained the `isDonated` refusal its live counterpart
has carried since `v0.35.4` and its own docstring already claimed.

**The residual registered at `v0.35.4` is closed** (WS-RM, `v0.35.6`): both
removal paths run seL4's `reply_remove`, and the reply path's own section below
records what new code must respect.

Plan: [`docs/planning/SCHEDCONTEXT_DONATION_CHAIN_PLAN.md`](docs/planning/SCHEDCONTEXT_DONATION_CHAIN_PLAN.md).

### WS-RM seL4's `reply_remove` on the reply path — COMPLETE (registered v0.35.4; RM1–RM6 v0.35.6)

`v0.35.4` made the reply stack doubly linked and wired the removal (then a sever,
the splice since HP6.3) into the **cancellation** path, leaving the **reply** path
relying on the answered frame
being the head — which every reply of the nested Call pattern satisfies and a
*delegated* reply capability answering out of order does not.  Twenty-six
sub-tasks across six phases, all at `v0.35.6`.  Seven things new code must
respect.

(1) **One removal step, and both spines call it.**  `removeCallerReplyFrame
caller rid` is seL4's `reply_remove`: `spliceReplyFrameOutOrSelf` (the splice
folded to the identity on refusal — a non-reciprocating upward link means
"nothing above me on my stack", which the chain relation permits by design since
it is stated *downward*), then `SystemState.consumeCallerReply`.
`endpointReplyOnCore`, `endpointReply` and `endpointReplyRecv` all run it, and a
Tier 3 negative refuses a bare consume in any of the three.  **The order inside
it is the content** — the splice reads the link the consume clears — and a
second negative refuses the swap.  `removeCallerReplyFrame_eq_consume_of_no_frame_above`
is the definitional equality that makes every repair a case split whose `none`
branch is the pre-WS-RM proof verbatim.

(2) **The reply leg's head case is stated, not hidden.**  A frame that *heads* a
scheduling context keeps its links when its caller is consumed (`Reply.consumed`,
deliberately — the pop validates the head by them), so the leg's post-state
satisfies `donationChainWellFormedExcept … rid` and nothing stronger.  It stands
to the reply leg as `ipcInvariantFullExceptDonationOwner` stands to the bare
reply, and `endpointReplyCrossCoreDispatch_preserves_donationChainWellFormed` is
the composite that discharges it: the donation pop that follows in the same
transition re-heads the frame below.  `faultReplyOnCore_preserves_donationChainWellFormed`
and `replyTransferOnCore_preserves_donationChainWellFormed` (seL4's
`doReplyTransfer`) compose it; the staging writes frame the chain
(`stageDeliveredMessage_donationChainFrame` and its two siblings).

The composite carries **one** condition beyond the chain invariant, and it is a
**pre-state** fact: `answeredHeadContextIsServerDonation` — the context the
answered frame heads is the one the recorded reply server holds.  It is the
third of the tree's *local coherence facts* about a single reply, beside
`replyDonationOwnerIsAnsweredCaller` and `replyStackHeadIsAnsweredReply`, and
like them it is **stated rather than derived**: `donationOwnerValid` relates a
caller's recorded reply target to no donation, and `donationChainWellFormed`
carries no binding clause at all, by its own *what is deliberately absent*.
Vacuous wherever the answered frame heads nothing — every reply in a tree with
no donation — with both vacuity discharges named
(`answeredHeadContextIsServerDonation_of_no_caller` / `_of_no_reply`), and
`tests/SmpIpcSuite.lean` §3.21 exhibits its premises and its conclusion on a
state the live operations reach, since a hypothesis nothing exhibits is
indistinguishable from one that cannot hold.  It is at the **pre**-state exactly
as the bundle composite's `hDonationReturned` beside it is, and unlike
`hStackValid`: `replyStackOuterCallerValid`'s subject is a state the pop runs on,
whereas a `schedContextBinding` is something the reply leg provably does not
write (`endpointReplyOnCore_donationOwnerFrameExcept`), so the transport belongs
inside the proof rather than on every caller.  That is also what makes the reply
*transfer* carry the fact **once**: its two branches reply with `IpcMessage.empty`
and with `msg`, which at the post-state were two spellings differing only in a
message the question never reads.

(3) **`.reply` and `.replyRecv` declare the frame above the cut, which the splice
writes.**
`answeredReplyFrameAbove?` is resolved from the same
`(st.getTcb? target).bind (·.replyObject)` expression the arm's existing reply
member comes from, so the footprint and the transition cannot disagree about
which frame is answered.  **`maxLockSetSize` is 22** and the RPi5 per-lock cost
and envelope move with it, in the canonical sentence this file carries above.  No
*reachable* footprint grew: the new member and the donation-return members are
mutually exclusive, so `lockSet_endpointReplyRecvOnCore_size_le_eighteen` is
unmoved.  **And declaring a member is not proving the transition writes it** —
the Tier 3 anchor over each footprint's definition asks only that the resolver
*occur* there, which is a presence check.  The relation is
`lockSet_endpointReply_frameAbove_write_mem` and `lockSet_replyRecv_frameAbove_write_mem`
at full arity, with `lockSet_endpointReplyOnCore_covers_splicedFrameAbove` and
its `.replyRecv` twin resolved: the reply-path siblings of the coverage the
cancellation path has carried since `v0.35.4`
(`lockSet_cancelIpcBlockingOnCore_covers_splicedFrameAbove`), which the cut that
added the reply-path member did not sweep onto it.

**And running that sweep over every resolved footprint found one more.**
`lockSet_cancelDonationOnCore` had `_correct` and `_size_le` and no coverage
layer at all, while each of its parametric members already carried a
write-membership lemma — so nothing tied a member to the **resolver** the
resolved footprint reads it from, which is the whole content of a resolved
coverage theorem.  Neither neighbour stands in for it: `_correct` is about the
*kinds* of the members present and `_size_le` about how many there are, and
a footprint can satisfy both while naming the wrong object.  The six are
`lockSet_cancelDonationOnCore_covers_victim` (both arms of the resolution),
`…_covers_bindingSchedContext` and `…_covers_stateLevel` (through
`cancelBindingSc?`), `…_covers_donatedOwner` (through `cancelDonatedOwner?`),
`…_covers_pop` and `…_covers_outerCaller_key` (through
`cancelDonationPopMembers?`) — the last a declared **key** rather than a write,
because the pop *reads* that TCB to check it is a waiting donor, with a Tier 3
negative refusing the write spelling.  `lockSet_notificationWaitOnCore` has no
coverage layer and needs none: it resolves nothing, so its parametric lemmas are
already the statement at full arity.

(4) **`.replyRecv` pops the donation *between* its two legs**, which is
seL4-MCS's own `doReplyTransfer` → `reply_remove` → `receiveIPC` order — and it
has to be.  The receive leg re-links the very Reply `rid` the reply leg just
answered, and `Reply.isFree` reads **both** stack links, so a frame still heading
a context is not linkable: with the pop last, `linkCallerReply` and the
server-first stash both refused `.replyCapInvalid` and **no passive server whose
client had donated could ever complete a `seL4_ReplyRecv`**.  That was a live
defect on the MCS steady state, found while closing this workstream and fixed in
the same cut.  The fused `replyRecvReturnDonation` is retired and split into
`replyRecvPopDonation` (between the legs) and `replyRecvPostReceiveDonation`
(after the receive leg, taking the popped context as an argument), each with its
own bundle theorem stated at the state its own step runs on.  New code must not
read the fused name as live.

(5) **The dispatch payoff's receive-leg hypotheses are stated at the post-pop
state.**  `replyRecvPostPopState` and `replyRecvPoppedDonation` are *total*
accessors over the pop (the second was `replyRecvPoppedContext` until
`v0.35.149`, when the pop's result became the `(context, holder)` pair), so `syscallDispatchQuiescence.replyRecvStage` stays a
flat pre-state-computable pack rather than a quantification nested under the
pop's own success; the pop's two obligations (`hSrvIdle1`, `hStackValid1`) are
stated at the reply leg's committed state, which is where it runs.  Stating the
receive-leg fields at the reply leg's own state is a claim about a state the
receive leg no longer runs on.

(6) **Every reply-stack write names a chain result.**
`SeLe4n/Testing/ReplyStackWriteCensus.lean` (Tier 1) derives the write-site set
from the elaborated environment — by **two** derivations, and a site found by
either is a site: a project definition whose own body references one of the
chain-write primitives (`SystemState.consumeReply` and
`SystemState.consumeCallerReply` among them), and one that builds a `Reply` or
`SchedContext` record and stores it, which is what catches a writer that names no
helper at all.  Both are reconciled against a registry in both directions.  A
site either **states** its chain results (each named theorem must mention the
site *and* a `donationChain…` form) or is recorded as a **half-step** of the
composite that completes it, and the half-step chain must terminate in a stating
entry.  The counts are **printed by the census** and deliberately not mirrored
here: a hand-kept figure beside a derivation is the shape this file warns about,
and this one went stale the first time the frontier widened.  A new
definition that consumes a caller's Reply bare is a build failure on the day it
is written — which is the shape this workstream exists to close, and the one
level above the frontier the census deliberately stops at (composites inherit by
`donationChainFrame`'s algebra, which is a composition rather than a claim).

**And "every" meant every module either root reaches** (PR #895 review,
`v0.35.12`).  `SeLe4n/Kernel/FrozenOps/` was reached by neither, and was in no
staged allowlist: it was built only by its own `lean_exe` target
(`tests.FrozenOpsSuite`) — **the root cause closed at `v0.35.60`, which put it in
the library root** — so the closure this census claims held for every
module except one that writes the live `Reply` record — `FrozenKernelObject.reply` carries `SeLe4n.Kernel.Reply`, links and
all, and `Model.freeze` copies a live state's Reply objects verbatim, so a
frozen state taken mid-call-chain holds a real reply stack.  And the gap was not
theoretical: `frozenEndpointReply` cleared a caller's Reply **bare**, which is
WS-RM's own defect surviving on the surface nothing was looking at.  Bringing it
in cost three things.  The frozen reply now runs a frozen `reply_remove`
(the removal then the consume, in that order, since the removal reads the link the
consume clears; **WS-HP HP8.2** made that removal `frozenSpliceReplyFrameOutOrSelf`,
which splices rather than severing).  `frozenLinkCallerReply`'s guard read
`caller.isNone` where `Model.linkReply` reads `Reply.isFree` — a fifth guard
deciding one question differently, so a frame still on a live stack was linkable
there while the live kernel refuses it; it reads `isFree` now.  And the
discipline gained a third constructor, `mirrors`: `donationChainWellFormed` is a
predicate on `SystemState` and the frozen store is a `FrozenMap`, so demanding a
`donationChain…` result of a frozen site would demand a theorem that cannot be
written, while accepting no record would be the silence this census refuses.  A
`mirrors` entry names the live twin, which must itself resolve to a stating
entry — a frozen writer with no live twin is a transition the live kernel never
performs, which is a finding rather than an exemption.

(7) **`donationChainFrame_of_objects_insert` is public and lives beside the
predicate.**  It was private to the cancellation shape module; the fault-reply
path needs the same fact, and a second copy in a module the first does not import
is the one-question-two-answers shape this tree keeps paying for.

**And the removal does not preserve the donation accounting — the cost, measured,
and whose it is** (the post-landing audit, corrected at `v0.35.14`).  Taking a
caller out of the *middle* of a chain is destructive to which thread ends up
owning the scheduling context: the removal moves no context, and the later pop
donates to whatever the remaining stack says is outermost.  On
`owner → middle → server`, a delegate answering `owner` out of order leaves
`owner` **`.unbound` permanently**, and the server's in-order reply then settles
the context **`.bound` on `middle`** — which the in-order unwind would instead
have left `.donated … owner`, still owed outward.  So a callee that delegates
its caller's reply capability to a confederate can capture that caller's
reservation.  New code must not read WS-RM as accounting-preserving, and must not
read a successful pop as evidence that the context reached its owner.

**The cost is `cancelledMiddleCallerPolicy`'s, not the removal's, and a
depth-two witness cannot tell the difference.**  A two-frame stack's lower frame
is its *bottom*, so `severAtCut` (write `prev := none` into the frame above) and
the alternative `spliceOutTheCut` (write the cut frame's own `prev`) write the
same value, and §3.20 measures a shape both policies share.  §3.22 of
`tests/SmpIpcSuite.lean` is the depth-three witness where they differ: every
frame below the cut leaves the context's stack, so the reservation settles on a
thread strictly *inside* the chain and its owner is left `.unbound` two hops
outside the cut, while the same stack unwound in order delivers it outward still
owed.  Three frames is the shallowest stack on which any of that is visible.

**Why the splice was not taken at WS-RM, and the order that had to be respected.**
Up to `v0.35.37` this kernel decided whether a reply pops a donation from the
**recorded server's binding** (`endpointReplyServerDonation?`), not from whether
the answered frame heads a context; `severAtCut` is exactly what kept those two
facts equivalent, and it is what the three *stated* pre-state coherence hypotheses
(`replyStackHeadIsAnsweredReply`, `replyDonationOwnerIsAnsweredCaller`,
`answeredHeadContextIsServerDonation`) needed — no invariant in this tree entails
them.  Splicing re-heads a frame whose recorded server is gone and `.unbound`, so
under that trigger answering it would have run no pop and left a consumed frame
heading a context: the state `replyStackOuterCaller?_of_consumed_frame` refuses and
the pinning `v0.35.4` closed.  Recovering the accounting therefore meant moving the
pop's *trigger* to head-ness first, which is what **WS-HP HP4** (`v0.35.38`, the
reply path) and **HP5** (`v0.35.39`, the cancellation path) did, and only then the
sever to a splice, which is **HP6.8** (`v0.35.45`).  That ordering was enforced
rather than described: `severAtCut_pop_leaves_no_head` was HP2.3's pin on it, and
HP6.8 deleted it because its first conjunct was the policy constant at the old
value.  New code must not read this paragraph as a live reason against the splice —
the splice is the live policy and the depth-≥ 3 accounting is
`donationAccountingPreserved_atCallDepthThree`.  The depth-**two** residue the splice
provably cannot reach was WS-HP HP10's, and it is closed at `v0.35.53` by
`donationAccountingPreserved_atCallDepthTwo`, so the accounting now holds at every
depth; what the register still carries is HP10.10's documentation closure alone.

**And `severAtCut` IS seL4-MCS's removal — the `v0.35.14` retraction was itself
wrong, and how it went wrong is the finding** (re-verified at `v0.35.40`).
`reply_remove`'s non-head branch, at master, 13.0.0, 12.1.0, 12.0.0 and 11.0.0 —
every release that has the function — is

```c
if (next_ptr) {
    /* not the head, remove from middle - break the chain */
    REPLY_PTR(next_ptr)->replyPrev = call_stack_new(0, false);
}
if (prev_ptr) {
    REPLY_PTR(prev_ptr)->replyNext = call_stack_new(0, false);
}
```

It writes **zero** into the frame above, which is `severAtCut`, and upstream's own
comment says so.  `v0.35.14` claimed the opposite and cited
`REPLY_PTR(call_stack_get_callStackPtr(reply->replyNext))->replyPrev =
reply->replyPrev` as the evidence; **that line is in no release**.  So the
paragraph before this one describes the accounting cost correctly and attributes
it wrongly: the cost is seL4-MCS's too, and WS-HP's splice is an **improvement on
upstream** rather than an adoption of it.  v1.0.0 may claim seL4-MCS reply-stack
removal semantics today; what it must not claim, of either kernel, is that
completing a call chain returns a client's reservation at chain depth ≥ 3.

**Quoting is not reading.**  This file's rules all police a *scanner* substituting
a slice of text for a question about a program.  This is the same substitution with
no scanner in it: a claim about an **external artefact** was marked "checked against
upstream source ... and not assumed", in the very sentence that made it false, and
the quoted C was reconstructed from what `reply_remove` *ought* to do rather than
copied from the file.  A verbatim quotation is the strongest-looking evidence a
prose claim can carry and the easiest to fabricate without noticing, and nothing in
this tree could catch it — no gate reads seL4.  Two things follow.  **Cite the
revision, not the repository**: a claim about upstream names the tag or commit it
was read at, so the next reader can re-run the check rather than re-trust the
quotation, and this tree's upstream claims now do.  And **a retraction is a change
of claim and gets the same scrutiny as the claim**: `v0.35.14` swept a *correction*
across four files and three docstrings, and the sweep worked — it propagated the
error everywhere, in the sentence asserting it had been verified.  The three
docstrings it "fixed" had been right.

**And a claim about upstream is about a named OPERATION, not a named kernel** — the
third rule, and the one this cut paid for itself.  Its own first draft said upstream
"permanently strands a cancelled caller's reservation", which is true of `cancelIPC`
and false of the kernel: `reply_remove` returns the context and `finaliseCap` runs it
on reply-capability revocation, which is the behaviour the Reference Manual
documents.  `cancelIPC`, `reply_remove` and `reply_remove_tcb` are **three
operations**, and this tree had been treating them as one name for eight cuts — which
is how `Suspend.lean` came to carry both readings at once, the docstring naming
`reply_remove` and the inline comment at its own call site naming `reply_remove_tcb`.
So a divergence claim names the operation it diverges from, and where two upstream
operations answer differently, saying which is the whole of the claim.  The
maintainer caught this one from the manual, which is the evidence for the rule: the
error is invisible to anyone reading only the function the claim happens to name.

Two divergences survived the correction at `v0.35.40`, both smaller and both in
the direction of this kernel being the weaker one.  **The first is closed and the
direction has reversed** (WS-HP HP6.3/HP6.7, `v0.35.45`): upstream clears the frame
*below*'s upward link (`prev->replyNext = 0`), this tree used to leave it stale and
work around it by validating reciprocity at every read (`donationChainFrom`,
`replyFrameOnLiveStack`), and the splice now **writes** it —
`removeCallerReplyFrame_splices_reciprocally` — so the pair either side of the cut
reciprocates, which is stronger than clearing.  A stale upward link is still
*reachable*, because `spliceFrameBelow?` refuses a frame below that does not
reciprocate and degenerates to the sever there, so the reciprocity checks stay and
stay load-bearing.  **The second survives and is about HEADS**: upstream clears the
removed frame's own links, and `Reply.consumed` keeps them *when the frame heads a
context*, deliberately, because the pop that follows in the same transition
validates the head by them.  On a non-head `Reply.consumed` already cleared both,
and since HP6.3 the splice clears the cut frame's `prev` itself — seL4's
`reply_unlink` downward half — which is what makes `donationChainWellFormed`
survive the removal outright rather than transiently.  So the residual is the head
case alone; a claim that HP6 closes it is an over-claim, and one was retracted from
that workstream's plan at `v0.35.45`.

**And the cancellation reclaim is upstream's semantics moved earlier, not an
invention and not a permanent strand** — the maintainer's correction to this
section's first draft, which said upstream "permanently strands a cancelled
caller's reservation".  That described one of four paths and attributed it to
upstream as a whole.

**Upstream returns a donated context when the caller's Reply object is finalised,
not when the caller's IPC is cancelled** — four paths, all read at master, 13.0.0,
12.1.0, 12.0.0 and 11.0.0.  (1) The server replies: `doReplyTransfer` →
`reply_remove` → head ⇒ `reply_pop` ⇒ donate to the answered caller, guarded
`if (tcb->tcbSchedContext == NULL)`.  (2) **The reply capability is revoked** while
its caller is still `BlockedOnReply`: `finaliseCap` runs the *same*
`reply_remove`, so the context returns to the caller — the Reference Manual's "if
the reply capability is revoked while the callee currently holds the scheduling
context, the scheduling context will be automatically returned to the caller".
(3) The same revocation when the caller's frame is **not** the head, because a
deeper server holds the context: the non-head branch runs, no donation happens,
and the caller is removed from the call chain — the manual's deep-call-chain case,
and the same *break the chain* write the removal-policy correction above rests on.
(4) `cancelIPC` — a `seL4_TCB_Suspend` on the caller, an endpoint deletion, a
fault: `reply_remove_tcb` ⇒ **no** donation, and its `reply_unlink` then clears
`reply->replyTCB`, so a later revocation of that reply capability finds nothing to
do (`finaliseCap` guards on `reply->replyTCB`) and the context stays with the
server until an SC-capability holder rebinds it.

So `returnDonationToCancelledCaller` applies **upstream's `reply_remove`
semantics at the cancellation point**, where upstream defers them to Reply-object
finalisation.  The difference is *when*, not *whether* — and this kernel's binding
typing forces the earlier point: `.donated scId owner` names its owner, so
`donationOwnerValid` is false the instant that owner stops being reply-blocked,
where upstream's flat `tcbSchedContext` pointer carries no such obligation.

Two consequences for new code.  A claim that this kernel diverges from upstream on
the *cancellation* reclaim must name the operation: it diverges from `cancelIPC`
and agrees with `reply_remove`.  And "adopt seL4's cancellation semantics" is not
a licence to delete the reclaim — deleting it reaches a state
`donationOwnerValid` forbids, which is the Medium finding WS-RR RR7.22 reported.

Plan: [`docs/planning/REPLY_FRAME_REMOVAL_PLAN.md`](docs/planning/REPLY_FRAME_REMOVAL_PLAN.md).


### WS-HP The head-driven donation pop — COMPLETE; the depth-2 accounting re-opened at v0.35.141 and CLOSED at v0.35.157 (registered v0.35.16; HP1 v0.35.35, HP2 v0.35.36, HP3 v0.35.37, HP4 v0.35.38, HP5 v0.35.39, HP6 v0.35.41 → v0.35.45, HP7 v0.35.46, HP8 v0.35.47, HP9 v0.35.48, HP10 v0.35.49 → v0.35.54; post-landing audit v0.35.61 → v0.35.62)

The reply path decided whether to pop a donated scheduling context from the
**recorded server's binding** (`endpointReplyServerDonation?`), not from whether
the answered frame heads a context.  `severAtCut` is exactly what kept those two
facts equivalent, and the consequence was measured rather than described: at
reply-stack depth ≥ 3 a middle removal dropped the frames below the cut, the
reservation settled `.bound` on a thread strictly *inside* the chain, and its
owner was left `.unbound` for good (`tests/SmpIpcSuite.lean` §3.22; §3.20's
depth-two witness structurally cannot show it, because a two-frame stack's lower
frame is its bottom and both policies then write the same value).

**HP6 closed that at `v0.35.45`.**  Both triggers read the answered frame
(HP4, HP5), the removal splices rather than severs (HP6.3, HP6.8), and
`donationAccountingPreserved_atCallDepthThree` is the statement: at depth ≥ 3 a
middle removal leaves the reservation **owed outward** and the pop that answers the
bottom frame delivers it home.  §3.22 inverted from a COST witness to a PAYOFF
witness in the same cut.  What was left was depth two, which the splice provably
cannot reach — both policies write `none` into the frame above a bottom frame — and
which needed the reservation's *origin* on the `SchedContext` rather than stack
reachability.

**HP10 addressed that at `v0.35.53`, and the workstream's phases closed at `v0.35.54` — but the depth-2 half did not hold, and is re-opened at `v0.35.141`.**
`SchedContext.donationOrigin` records the thread that owned a reservation when it
first left, written on a **first** push and cleared by every step that ends the
loan, and `replyDonationRecipient` reads it in place of stack reachability at the
bottom of a stack.  `donationAccountingPreserved_atCallDepthTwo` is the statement,
**under its own two guard hypotheses**.  Two fragments survive the closure,
deliberately: the footprint/transition resolution asymmetry HP10.8 found keeps its
own open register row, and `CancelledMiddleCallerPolicy.severAtCut` is **kept** as
a constructor, because it names the behaviour upstream still has and an
improvement is only statable against something.

**And the depth-2 half was NOT closed at HP10 — the guard was a proxy, and its
decline was a TRANSFER** (PR #897's review, `v0.35.141`; **closed at `v0.35.157`**).
Until `v0.35.157` `donationOriginRebindable` refused an origin that is
`.blockedOnReply`, as a stand-in for "some live `.donated _ origin` binding names
it".  The two are not the same: a client answered out of order is woken `.ready`
and `.unbound`, and its next **ordinary Call donates nothing** —
`callDonationSchedContext?` reads `SchedContextBinding.scId?`, which is `none` at
`.unbound` — while putting it `.blockedOnReply` again.  No binding names it; the
proxy refused it anyway; the pop fell back to the *answered caller*, which at
depth 2 is the intermediate caller of the chain — the reservation bound to that
caller, the client left `.unbound`, `donationOrigin` erased, so the kernel could
never return it, and a callee delegating its caller's reply capability to a
confederate could arrange it.

**What closed it is the bind's own admissibility, asked of the origin.**  The
redirect *is* a bind of the reservation to its recorded owner, so
`donationOriginRebindable` now asks `schedContextBind`'s question — is the origin's
reply frame on a **live** stack (`replyFrameOnLiveStack`, one-step reciprocity,
relocated to `IPC/Operations/Endpoint.lean` because both askers read it) — on both
surfaces.  That admits the re-called client (its new frame is on no stack) and
refuses the two shapes the proxy could not tell apart from it: an origin whose
frame *heads* a context, which is a live owner, and one whose frame sits *inside*
a live stack, which is owed a pop that a binding made now would make refuse.
Four things new code must respect.  (1) **Soundness is the coherence fact, not
the `ipcState`**: `donationOriginRebindable_no_owner` derives "no live binding
names it" from the guard under `donatedContextIsOwnerFrameHead` — WS-HP HP5.2's
binding → head fact, relocated upstream to `IPC/Invariant/Defs.lean` and restated
over the reply path's own `answeredFrameHeadContext?`, with the cancellation form
its corollary (`donatedContextIsOwnerFrameHead_cancelledCallerDonation?`).  The
reply path carries it as `redirectedOriginFrameCoherent`, gated on the trigger,
the resolver and the distinctness from the answered caller — the one thread the
fact is genuinely false at in the pop's own state, its frame consumed while the
holder's binding still names it — so a reply that redirects nothing owes nothing,
and the dispatch packs' two reply stages each gained the conjunct.  (2) **The
depth-2 payoff derives its rebindability**: `donationAccountingPreserved_atCallDepthTwo`
takes `donationRecipientAcceptable` and the origin's resolution as hypotheses and
nothing else, because the removal that fires the redirect has just taken the
owner's frame off the stack (`removeCallerReplyFrame_replyObject_none`,
`donationOriginRebindable_of_no_reply`) — where the proxy was false again the
moment the owner re-Called, the structural guard stays derivable through that
window.  (3) **The witness computes the retired reading beside the live one**:
`tests/SmpIpcSuite.lean` §3.25's PAYOFF group drives the live pop on the re-called
client, with the `.blockedOnReply` proxy spelled as a `private def` in the suite
and nowhere else, and its two NEGATIVE groups plant the live owner (with the binding
that names it) and the interior frame, each with the CONTROL that the recipient
guard alone admits the thread.  (4) **The claim is lifted**: v1.0.0 **may** claim
that completing a call chain returns a client's reservation at every reply-stack
depth — the depth-≥ 3 half by HP6's chain-preserving removal, the depth-2 half by
the recorded origin under a guard that is the fact rather than a proxy for it.  The
accounting row in `docs/REGISTERED_DEBT.md` table C is **closed**.

**The splice is an improvement on seL4-MCS, not an adoption of it** (`v0.35.40`,
re-verified against upstream source at five revisions).  `reply_remove`'s non-head
branch *breaks the chain* exactly as `severAtCut` does — see the WS-RM section
above for the C and for what the `v0.35.14` retraction cost — so upstream strands
the reservation at depth ≥ 3 too.  What HP6 buys is therefore a property neither
kernel has today, and the workstream's value does not depend on the mistaken
attribution: a callee that delegates its caller's reply capability to a confederate
could capture that caller's CBS reservation at depth ≥ 3, and the chain-preserving
removal is what closed it at `v0.35.45`.  Two things upstream *does* confirm, both landed: the pop's trigger is
`call_stack_get_isHead(reply->replyNext)` (HP4, HP5), and `reply_pop` donates only
`if (tcb->tcbSchedContext == NULL)`, which is HP4.6's `donationRecipientAcceptable`
with upstream's own reason.

The correction was **two changes in a forced order**, not one: the splice alone is
unsound under a binding-driven trigger, because it re-heads a frame whose recorded
server is by then `.unbound`, so answering it would run no pop and leave a consumed
frame heading a context — the object pinning `v0.35.4` closed.  So the trigger moved
first (HP4 `v0.35.38`, HP5 `v0.35.39`), then the sever became a splice (HP6.8
`v0.35.45`), and HP2.3's `severAtCut_pop_leaves_no_head` made that ordering a
machine-checked fact rather than a note — HP6.8 deleted it, because its first
conjunct was the policy constant at the old value and a theorem whose conclusion has
become false can only be retired.  A tombstone comment beside the `WS-HP HP2.3`
banner in `IPC/Invariant/Defs.lean` records what replaced it.

| Phase | Status | Version | Scope (one line — detail in the canonical sources) |
|-------|--------|---------|----------------------------------------------------|
| HP1 | LANDED | v0.35.35 | The trigger's resolvers and the splice's below-frame resolver, both inert |
| HP2 | LANDED | v0.35.36 | The two triggers are equivalent on every coherent state, and the splice breaks it |
| HP3 | LANDED | v0.35.37 | The removal's below-frame footprint member; `maxLockSetSize` 22 → 23 |
| HP4 | LANDED | v0.35.38 | **The reply path's trigger flips** — both spines, the recipient guard, the payoff's packs, and the frozen mirror (HP4.7) |
| HP5 | LANDED | v0.35.39 | **The cancellation path's trigger flips** — the resolver, the coherence fact re-keyed, two sentences turned into theorems, and the first witness that fires the reclaim (HP5.5) |
| HP6 | LANDED | v0.35.41 → v0.35.45 | **The splice replaces the sever** — the family renamed (HP6.1), the two reply footprints repointed (HP6.2), then the primitives, the algebra, the policy flip and the depth-three payoff as one cut (HP6.3–HP6.9) |
| HP7 | LANDED | v0.35.46 | **The three stated coherence hypotheses retire** — nine declarations deleted with the binding-driven resolver, HP7.1 already done at HP4.4, HP7.4 vacuous, and the fourth stated fact found LIVE |
| HP8 | LANDED | v0.35.47 | **The frozen mirror splices** — the sever's family deleted, the census's three mirrors, and `FO-043`: the depth-3 witness every shallower scenario structurally could not be |
| HP9 | LANDED | v0.35.48 | **Witnesses, anchors, documentation, closure** — the depth-4 witness (§3.23), the upstream facts recorded at the code, and acceptance box 10 struck as wrong rather than ticked |
| HP10 | LANDED | HP10.1–HP10.5 v0.35.49, HP10.6 v0.35.50, HP10.7 v0.35.51, HP10.8 v0.35.52, HP10.9 v0.35.53, HP10.10 v0.35.54 | **The reservation's origin**, so the return does not depend on chain connectivity — the depth-2 residue the splice provably cannot reach; the redirect is live on both surfaces, **`donationAccountingPreserved_atCallDepthTwo` is the payoff**, and the debt row is closed |

**What new code must respect since HP4 (`v0.35.38`).**  Seven things.

(1) **Both reply spines pop on the FRAME, and take it as an argument.**
`applyReplyDonation st rid targetVtid`, `applyReplyDonationOnCore st rid
targetVtid holderHome ownerHome` and `replyRecvPopDonation rid target` all read
`replyFrameHeadHolder? st rid`.  The `rid` is an argument and has to be: the reply
leg's `consumeCallerReply` clears the answered caller's `replyObject`, so
`answeredFrameHeadContext?` answers `none` at every state the pop runs on.  It is
resolved on the pre-state through `answeredReplyObject?`, the one expression the
arm's footprint members also come from; `answeredFrameHeadContext?` is now that
composition rather than a second spelling.  Everything the pop *decides* — which
context the frame heads, which thread holds it, which caller is outer — is read at
the pop's own state, which is what keeps `returnDonatedSchedContext`'s
`boundThread` guard vacuous.

(2) **The pair's second component is the thread that LOSES the context**, where
`endpointReplyServerDonation?`'s was the one that gains it.  Same type, opposite
role, and under the flip the pair also moves from `returnDonatedSchedContext`'s
`originalOwner` position to its `serverTid` one.  A substitution that swaps them
typechecks; `answeredFrameHeadContext?_boundThread` is the theorem that the
component *is* `sc.boundThread`, and Tier 3 negatives refuse the swap at each
site.

(3) **`replyDonationReturn?` is NOT the trigger and was not re-keyed.**  It
answers "does this thread hold a donated context", which the two pre-receive
cleanups, the cancellation reclaim and the witnesses still ask.  Its argument
means the holder; the trigger's means the answered caller.

(4) **The pop refuses a recipient that already holds a binding**
(`donationRecipientAcceptable`).  The head-driven recipient is the answered
caller, which no binding the operation reads constrains, so without the guard a
caller that acquired a reservation while blocked would have it silently
overwritten.  Inert on every reachable state; `returnDonatedSchedContext`'s
`_ok_storeChain` carries it as a tenth component, so a consumer destructuring that
chain by position gains one `_`.

(5) **The priority-inheritance reversion still walks from `recordedReplyServer?`**,
because it keys on waiters rather than on donations — a walk from the context's
`boundThread` would start at the wrong thread on exactly a delegated reply.  And
the `.replyCapInvalid` arm still distinguishes "no recorded server" from "no head
context": collapsing them would turn every donation-free reply into an error.

(6) **The two reply footprints resolved their donation members through the
binding until HP6.2** (`v0.35.44`), with the gap held closed by
`lockSet_endpointReplyOnCore_covers_headDrivenPop` — a footprint that omits a
written object is false.  That repoint had to land *before* the splice: under the
sever the two resolvers agreed — `severAtCut_pop_leaves_no_head` was the statement,
retired with the policy at HP6.8 — and the splice is the change that makes them
disagree, so a window with the splice landed and the repoint outstanding would carry
a footprint that omits what the pop writes.  The paragraph on HP6.2 below says what
landed.

(7) **The FROZEN mirror is head-driven too, and its binding-driven resolver is
gone** (HP4.7).  `frozenEndpointReplyWithDonationReturn` reads
`frozenReplyFrameHeadHolder? st replyId` — no resolution needed on that surface,
because `replyId` *is* the presented capability and `frozenEndpointReply` refuses
it unless the target's own `replyObject` names it — and hands the context to
`targetId` rather than to a binding's recorded owner.  The flip belongs to HP4
rather than to HP8 because HP4 is the cut that makes the live operation
head-driven, and `frozenBranchOperationChecked .endpointReplyToBlockedCaller =
true` is a machine-checked claim that the two are run beside each other: a
binding-driven mirror of a head-driven operation is *one question answered in two
places* with the divergence already scheduled at HP6.
`frozenEndpointReplyServerDonation?` is deleted, not kept beside the new reading.
`FO-042` is what makes the claim a measurement — `FO-041` had never given the
recorded server a `.donated` binding, so through four review rounds the frozen
donation return was compared on neither side — and its second half is the state
where the two triggers disagree, which is the mutation that decides the flip.
Asking the question also found the frozen pop **missing HP4.6's recipient guard**
under a docstring claiming it carried every live one: `frozenDonationRecipientAcceptable`
is the counterpart, in the live position, and `FO-042`'s third half is its witness.
A mirror missing a guard *succeeds* where the kernel refuses, which is the
direction that matters on a differential surface.  The same question found the
live step's **ID promotion** missing too — `applyReplyDonation` refuses a holder
`toValid?` will not promote — added as `holder.isReserved`, because this surface
uses `toValid?` nowhere and `frozenLookupTcb` (which *is* `isReserved`, exactly
`= sentinel`) is how it already asks that question; a Tier 3 negative keeps
`toValid?` out of both frozen modules so the convention stays one.  HP8 owned
the **splice** half alone, and landed it at `v0.35.47`.

**What new code must respect since HP5 (`v0.35.39`).**  Six things.

(1) **The cancellation reclaim reads the victim's own reply FRAME.**
`cancelledCallerDonation? st _tid tcb` is `replyFrameHeadHolder? st rid` at
`tcb.replyObject` under the `.blockedOnReply` arm gate — the same frame-keyed
resolver both reply spines read since HP4.1, not a second spelling
(`cancelledCallerDonation?_eq_answeredFrameHeadContext?` ties it to the reply
path's own form).  The victim's id is **not consulted**: the binding reading's
`owner == tid` check is what the structure replaces, and
`cancelledCallerDonation?_independent_of_victim` pins that rather than leaving a
reader to infer it from an underscore.  The arm gate stays, because it is the
*arm selector* every exclusivity lemma in the cancellation family reads.

(2) **`donationHolderIsReplyTarget` is GONE** — WS-RR RR7.22's fact about a
cancelled caller's recorded reply target, which nothing reads any more.  Its
head-keyed successor is `donatedContextIsOwnerFrameHead`: the donation the victim
owns is the one its own frame heads, and the reclaim's trigger finds it.  It runs
binding → head, the opposite direction from the reply path's
`answeredHeadContextIsServerDonation`, because here the *consumers* quantify over
bindings while the trigger reads frames.  `…_of_donationOwnerValid` is the builder
and it measures what the fact costs: everything but two clauses comes out of
`donationOwnerValid`, and what is left — the frame-head link and the holder's
promotability — is what no invariant in this tree entails.

(3) **A holder the head reading names may resolve to nothing.**  The
binding-driven resolvers read a thread out of a stored binding, so the store held
it by construction; `SchedContext.boundThread` is tied to no stored TCB by any
invariant.  What rules the case out is the **pop declining**
(`returnDonatedSchedContext_ok_server_not_reserved`), with
`abortHolderPendingIpc_eq_self_of_lookup_none` the frame that lets a consumer act
on it.  New code must not read a resolved `(scId, holder)` as evidence that
`holder` is a live thread.

(4) **`returnDonatedSchedContext_ok_under_invariants` is now an instance.**  The
general form is `_ok_of_boundAndRecipient`, which takes the context, its bound
thread and the recipient's `.unbound` as *arguments* — the head reading supplies
the first two off the trigger and has no binding to read the third from — with
the binding-keyed form derived from it.  A new success argument reaches for
whichever form it can discharge, never for a second proof.

(5) **Two claims are theorems now, and were not stateable before.**
`cancelReclaimHead?_eq_replyObject` — the head the pop clears **is** the victim's
own reply object, which is `replyStackHeadIsAnsweredReply`'s content seen from the
cancellation end — and `cancelSplicedFrameAbove?_of_donation` /
`cancelSplicedFrameBelow?_of_donation`, a reclaim excludes both removal members.
Both were sentences about "every reachable state" in footprint docstrings; the
binding reading could not have stated either, since it reached the context through
a binding that relates to no reply frame.  Cite the theorems.

(6) **Below the cut the reclaim declines on the STACK.**
`cancelledCallerDonation?_none_below_the_cut` and
`cancelledCallerDonation?_some_of_frame_head` (renamed from
`…_some_of_immediate_donee` for what it now says) are stated over
`replyFrameAbove?` and `replyFrameHeadContext?` and carry **no** binding
hypothesis — a frame with a frame above it heads nothing, so the pop's trigger and
the splice's are exclusive by construction.  That is strictly cheaper than what it
replaces, and it is the fact HP6 consumes.

One thing HP5 measured rather than predicted, and one it got wrong first.  The wake
and both below-head footprint members needed **no** re-resolution, because
`cancelAbortedHolderWake?`, `cancelAbortedHolderWakeCore?` (the wake's resolvers,
retired with the wake at `v0.35.158` for `cancelUnboundHolder?` /
`cancelUnboundHolderCore?`, which derive the same way), `cancelBelowHeadReads?`
and `cancelReclaimHead?` are all *derived from* the trigger — the derivation
discipline paying off where an enumeration would have needed five edits.

The fixture sweep is the one it got wrong, and the shape is this file's own: the plan
named three files, **a sweep over a named list is a recognised set standing in for a
derived one**, and the three came back clean while the *golden trace* then failed —
`SeLe4n/Testing/MainTraceHarness.lean` was not among them.  The derived set is every
tracked test or harness file mentioning `.donated`, thirteen of them, and it holds two
live defects.  `SCO-020b/c/d` built a `.donated` binding with **no Reply object at
all**, so the reclaim became the identity and all three lines flipped to `false`; they
carry the stack a live `Call` builds now, which keeps `main_trace_smoke.expected`
byte-identical.  And `tests/SmpIpcSuite.lean`'s OD5.2 pair was passing **vacuously** —
its store's `pushOuter` named no reply object though `pushOuterReply.caller` named it
back, and both assertions handed the resolver a TCB without the field, so "fires" and
"declines below the cut" declined for the same reason.  **A suite's assertions can pass
vacuously; an exact golden trace cannot** — which is why the trace found what the suites
hid, and the reason to run it early in a flip rather than last.

The gap the sweep did surface is HP5.5: **nothing in the tree fired the reply-arm
reclaim with the head reading available**, so the flip would have landed untested.  A
sweep for fixtures that would *break* is not a sweep for fixtures that would
*exercise*, and only the second measures a flip.  HP5.5 is that witness:
`tests/SmpCancellationSuite.lean` §3.20 fires the reclaim on the agreeing shape and on
the orphan head, computing **both** readings side by side (the retired one spelled in
the suite and nowhere else) so the assertions are known to discriminate.  A behavioural
revert never reaches them — it fails four theorems in `Lifecycle/Suspend.lean` first,
because HP5 *states* the head reading rather than merely computing it.

**What new code must respect since HP6.1 (`v0.35.41`).**  The removal family was
renamed for the operation it becomes, and for four cuts **the name ran ahead of the
body**: `spliceReplyFrameOut{,OrSelf}`, `spliceThreadReplyFrameOut` and
`cancelSplicedFrameAbove?` wrote `above.prev := none` — the sever — until HP6.3
(`v0.35.45`).  Three things that row decided and one it found.  (1) **The name and
the body were separated by two facts, and neither was the other**:
`cancelledMiddleCallerPolicy` is the *declared policy* and
`spliceReplyFrameOutOrSelf_store_cases` states the *body's* writes, so the splice
could not land without changing that lemma's statement — which it did, from one
store to a three-step existential.  **Not** `cancelledMiddleCaller_severs_at_cut`:
its policy conjunct was `rfl` on the constant and its cut shape a hypothesis, so it
was a statement about the *pop* given a severed cut rather than about the removal
that produces one — the shape this file calls a theorem whose conclusion is one of
its own hypotheses.  It is `cancelledMiddleCaller_splices_at_cut` now.  (2) **The
FROZEN family keeps its `frozenDetach…` names**, because it still severs; HP8
renamed it in the cut that made it splice (`v0.35.47`), so a `frozenDetach…` beside
a live `splice…` read as the schedule rather than as a drift.  (3) **The English word
"detach" in prose describing what the operation does was accurate at that version**
and was deliberately left alone — prose follows behaviour at HP6.3, where the name
followed the design here, and that sweep is part of the same cut.  **That sweep was
not run**: the post-landing audit's second pass (`v0.35.62`) found the operation
still called *the detach* — and, at nine sites, the sever still described as what it
does — across some 120 docstrings, comments, test labels and documentation
sentences in 35 files, and swept them.  (4) A rename is a
sweep, and this one found a **dead citation**: WS-RM RM1.1 retired
`detachCancelledCallerFrame` at `v0.35.6` and four *live* claims still named it —
this file's own WS-OD item 5 and `SELE4N_SPEC.md` §8.12.7 twice.  That is the
tautological-pin shape one artefact over: prose citing a declaration that does not
exist reads exactly like prose citing one that does.  HP6.8 paid the same cost in
reverse, deleting `severAtCut_pop_leaves_no_head` and having to sweep its five prose
citations.

**What new code must respect since HP6.2 (`v0.35.44`).**  The two reply
footprints resolve their donation members through **the pop's own trigger**:
`lockSet_endpointReplyOnCore` and `lockSet_endpointReplyRecvOnCore` read
`answeredFrameHeadContext? st target`, the expression
`applyReplyDonationOnCore` itself reads, so the footprint and the transition
cannot disagree about which context is popped or which thread is unbound.  Six
things follow.

(1) **The pair's second component is the thread the pop UNBINDS**, and the
parameter says so: `lockSet_endpointReply`'s and `lockSet_replyRecv`'s
`donatedOriginalOwnerTid` is renamed `donatedScHolderTid`.  A resolved footprint
that passes the *recipient* there declares a lock for a write the pop does not
perform and omits one it does — the recipient needs no member, because the
head-driven pop hands the context to the answered caller and that is
`replyTargetTid`.

(2) **Coverage is definitional, and stated on both arms.**
`lockSet_endpointReplyOnCore_covers_donationPop` and its `.replyRecv` twin take
**no hypothesis**; HP4.4's `lockSet_endpointReplyOnCore_covers_headDrivenPop`,
which needed `donationOwnerValid` and `answeredHeadContextIsServerDonation` and
reached the holder's TCB by *proving it was the recorded server*, is deleted.  A
behavioural revert does not reach a witness — it fails the coverage theorem
first, which is where this relation belongs.

(3) **Three write-membership lemmas had to be added**, and their absence is the
finding: the second donation member had **none** on either footprint, and
`lockSet_replyRecv`'s SchedContext member had none either, so nothing could state
that the objects the hottest IPC arm's pop writes carried declared write locks.
The stand-in had routed around the gap through `callerTid`'s lemma.  Found by
asking the table to be symmetric, not by a review round.

(4) **`server` stays keyed on the RECORDED server**, because that is the thread
`propagatePipChainCrossCore` walks from and rewrites, and the splice can make it a
different thread from the holder — so both are declared.  Measured against the
composite's three write sites rather than reasoned from the resolver.

(5) **`lockSet_endpointReplyRecvOnCore_size_le_eighteen` is now unconditional**,
where it took `donationChainWellFormed` and `replyStackHeadIsAnsweredReply`: under
this trigger a frame that heads a context has no frame above it and none below
(`answeredReplyFrameAbove?_none_of_headContext`), so the exclusion is structural.
That is strictly stronger than what it replaces.

(6) **`lockSet_endpointReplyRecvOnCore_size_le_seventeen` is RETIRED**, and this is
what the repoint costs.  Its single merge was `replyDonationOwnerIsAnsweredCaller`
— the *owner* is the answered caller — and the head reading's second component is
the thread *running on* the context while the answered caller is
`.blockedOnReply`, so that coincidence occurs on **no** state this arm reaches:
the merge is false, not unproved.  The available substitute is *holder = recorded
server*, which is `answeredHeadContextIsServerDonation`'s content and exactly what
the splice falsifies, so a seventeen resting on it would stop holding in the cut
after next.  One unit of slack traded for two hypotheses and a figure that
survives HP6.  Both coherence facts had **no consumer at all** after this row,
which is the verification HP7.2 asked for and HP7 (`v0.35.46`) then ran — and
having run it, HP7 **deleted** both, so a sharper reachable bound cannot be built
on *holder = recorded server*: the splice falsifies it on reachable states.

**What new code must respect since HP6.3–HP6.9 (`v0.35.45`).**  The removal is
seL4's `reply_remove` with the middle case **spliced** rather than severed, and the
name has caught up with the body.  Eight things.

(1) **The splice is THREE stores, and the third is not optional.**
`spliceReplyFrameStores` writes `above.prev := some below`, `below.next := some
(.frame above)` and `rid.prev := none` — the last being seL4's `reply_unlink`
downward half.  A two-store splice leaves the cut frame with `prev = some below`
while nothing below names it back, which falsifies `prevLinkReciprocal` at the cut
frame, so the bare splice would owe a relaxed predicate and
`ReplyStackWriteCensus` would have to accept a half-step where the sever stated its
result outright.  With the third store `donationChainWellFormed` is preserved
**outright** (`spliceReplyFrameOut_preserves_donationChainWellFormed`,
`removeCallerReplyFrame_preserves_donationChainWellFormed`), and it is **free**: the
cut frame's lock is already a declared write member on both removal paths, so
`maxLockSetSize` was unmoved by it, at HP3.5's twenty-three (HP10.6 has since
taken it to twenty-four, for a member of its own).

(2) **The below side does not refuse — it degenerates.**  `spliceFrameBelow?` is an
`Option`: a `prev` that does not resolve, one naming the frame above, and a frame
below whose own `next` does not link back are all *not followed*, and the removal
then writes `above.prev := none`, which is the sever.  So this operation's refusal
set is **exactly** the pre-WS-HP one and every refusal theorem carries verbatim,
`spliceReplyFrameOutOrSelf`'s fold soundness included —
`spliceReplyFrameOut_eq_sever_of_no_frame_below` is the definitional equality that
makes every repair a case split whose `none` branch is the pre-HP proof.  A
consequence: a **stale upward link is still reachable**, so the reciprocity checks
(`donationChainFrom`, `replyFrameOnLiveStack`) stay and stay load-bearing.

(3) **`spliceReplyFrameOutOrSelf_reply_next` is GONE**, because the splice moves a
`next` from one `.frame` link to another and its old conclusion (`rq.next =
rp.next`) is false.  Its successor
`spliceReplyFrameOutOrSelf_preserves_reply_caller_and_headLink` is a disjunction,
which is still exactly what its one consumer needs: no reply's `next` acquires a
`.head` link, so `removeCallerReplyFrame_preserves_donationChainWellFormed` may read
`hNotHead` on the pre-state.

(4) **The composed store step is a write site, registered as a half-step.**
`spliceReplyFrameStores` is in `chainWritePrimitives` and registered `.halfStep
spliceReplyFrameOut`, exactly as the pop's two component stores are half-steps of
`storeDonationHeadPop`.  It cannot state a chain result of its own: given only
`above` and the two records, nothing says the frame above is the one whose `prev`
names `rid`, and the three reciprocal links are coherent only under the resolution
the operation performs.  `spliceReplyFrameOutOrSelf_store_cases` is spelled as a
three-step **existential** rather than a named relation, because a `Prop`-valued
relation whose body mentions `storeObject` is reported by the census's store
frontier and registering a relation as a write site is not an option — it writes
nothing.

(5) **The removal's write set is FOUR keys** — the consumed Reply, the answered
caller's TCB, and the two frames either side of the cut — so
`removeCallerReplyFrame_objects_frame` takes a fourth exclusion and
`spliceReplyFrameOut_objects_ne` takes two (the frame below, and the cut frame
unconditionally).  The information-flow half needs `hSetInv` threaded, because the
frame below is written at the *intermediate* state and its index membership is read
there.

(6) **The two facts the sever could not state.**
`removeCallerReplyFrame_splices_reciprocally` — after a middle removal the frame
above names the frame below and the frame below names the frame above — and
`donationAccountingPreserved_atCallDepthThree`, the pop that follows delivering the
reservation to the caller the surviving stack names.  Both are stated with **no**
key-distinctness hypothesis, derived instead from the store's contents (a key
holding a `.reply` is one at which the consume's own TCB lookup fails), because
`ReplyId.toObjId` and `ThreadId.toObjId` are two wrappers over one `ObjId` and a
collision is representable.  `removeCallerReplyFrame_getSchedContext?_eq` is the
same shape and is what lets a post-removal head be resolved against the pre-state
context record.

(7) **Cite the live policy's consumers, not the retired ones.**
`cancelledMiddleCallerPolicy = .spliceOutTheCut`;
`replyStackOuterCaller?_follows_policy` concludes `.ok (some outer)` at a frame with
one below it, where it used to conclude `.ok none` at a cleared `prev`; and
`cancelledMiddleCaller_splices_at_cut` gives the target `.donated scId outer`, where
`cancelledMiddleCaller_severs_at_cut` gave `.bound scId`.  `severAtCut_pop_leaves_no_head`
is **deleted**.  `CancelledMiddleCallerPolicy.severAtCut` is **kept** as a
constructor: it names the behaviour this kernel diverged from and that seL4-MCS
still has.

(8) **The orphan head is reachable now.**  A frame heading a context whose recorded
reply server is gone and `.unbound` is what the splice produces, so
`answeredHeadContextIsServerDonation_false_of_orphan_head` changed from a
*prohibition* into a *fact about reachable states* — and that, with both coherence
facts having no consumer since HP6.2, is the warrant HP7 spent: HP7 (`v0.35.46`)
**deleted the predicate and this theorem with it**, a refutation having no subject
once the thing it refutes is gone.  What carries the evidence instead is an
*executed* witness — `tests/SmpCrossCoreReplySuite.lean` computes the retired
binding-driven reading beside the live one at an orphan head.

**What new code must respect since HP7 (`v0.35.46`).**  The three *stated*
coherence facts the binding-driven pop needed are **deleted**, together with the
resolver and the scaffolding that consumed them — nine declarations, not three.
Six things.

(1) **Do not restate a retired fact as a hypothesis.**
`replyDonationOwnerIsAnsweredCaller`, `replyStackHeadIsAnsweredReply` and
`answeredHeadContextIsServerDonation` are gone, and Tier 3 refuses each of them
tree-wide.  The last is not merely unused but **false on reachable states** since
HP6.8: the splice re-heads a frame whose recorded reply server is gone and
`.unbound`, which is the orphan head.  A proof that wants one of these is a proof
asking for a premise the kernel refutes.

(2) **What replaced them is the HP2.4 family, and it is where to reach.**
`answeredFrameHeadContext?_head_is_answered_reply`, `…_donationHeadOf` and
`…_boundThread` are the *derivations*: under the head-driven trigger the resolver
reads the context off the answered frame's own `.head` link and validates that
context's `scReply` against the same frame, so each retired hypothesis is a
consequence of the trigger firing — no hypothesis at all.  They are anchored in
Tier 3 because a derivation nothing consults reads exactly like one nobody
checked.

(3) **The fourth stated fact is LIVE, and its docstring used to say otherwise.**
`replyFrameHeadHolderDonation` (HP4.2's rename of `answeredHeadHolderDonation`) is
the one binding fact the trigger does **not** witness — that the holder's binding
*is* a donation of the context its frame heads — and it has twelve-plus consumers,
the dispatch packs' two reply-stage fields among them.  Its own docstring claimed
HP7 retires it; that claim is corrected rather than acted on.  Of the row's three
facts, two are *eliminated* and one is *migrated*.

(4) **`endpointReplyServerDonation?` does not exist.**  The reply path's
binding-driven trigger was deleted, not kept beside the live one: two readings of
one question free to drift is this project's worst shape, and these two *disagree*
on reachable states.  `recordedReplyServer?` beside it is **not** retired — the
priority-inheritance chain walk reads it, because that walk keys on waiters rather
than on donations, and on a delegated reply the recorded server is not the holder.

(5) **The retired reading lives in the witness that refutes it, and nowhere
else.**  `tests/SmpCrossCoreReplySuite.lean`'s `private def
bindingDrivenReplyServerDonation?` computes it beside the live resolver on the
agreeing shape and on the orphan head, so the assertions are known to
discriminate rather than merely to pass — the pattern
`tests/SmpCancellationSuite.lean` §3.20 set at HP5.5 and `FrozenOpsSuite`'s
`FO-042` set for the frozen surface.  That keeps the *evidence* HP2 produced and
deletes the *code*.

(6) **The dispatch packs shed nothing here, and that is recorded rather than
claimed closed.**  `syscallDispatchQuiescence`'s eleven fields and
`checkedSyscallDispatchQuiescence`'s two never carried one of the three; HP4
re-keyed the reply-stage conjuncts onto the head-driven reading in the cut that
flipped the trigger, which is where a pack field belongs — one stated at a state
its own step no longer runs on is a claim about a different state.  So HP7.4 is
**vacuous**, and the phase's acceptance criterion was corrected to something
checkable instead of being reported as met.

**What new code must respect since HP8 (`v0.35.47`).**  The frozen execution
surface's removal **splices**, and the sever's names are gone.  Five things.

(1) **`frozenDetachReplyFrameAbove` and `…OrSelf` do not exist.**  The family is
`frozenSpliceFrameBelow?`, `frozenSpliceReplyFrameStores`,
`frozenSpliceReplyFrameOut` and `frozenSpliceReplyFrameOutOrSelf`, each clause for
clause with its live counterpart, and Tier 3 refuses the retired names tree-wide.
HP6.1 kept the sever's names deliberately — a `frozenDetach…` beside a live
`splice…` read as the *schedule*, where a `frozenDetach…` whose body splices would
read as a drift — and this is the cut that discharges that, because the name and
the body move together.

(2) **The three stores are the same three, and the third is masked here.**
`above.prev := some below`, `below.next := some (.frame above)`,
`rid.prev := none`.  The third is seL4's `reply_unlink` downward half and it is
*not observable through the frozen reply composite*: the `Reply.consumed` that
follows clears the cut frame's links anyway on a frame heading nothing, so the
suite still passes with that store deleted.  It is load-bearing regardless — a cut
frame keeping a `prev` nothing names back is what the store exists to prevent, and
it becomes observable the moment `consumed` changes — so `FO-043`'s last half
drives `frozenSpliceReplyFrameOut` **directly**, beside the live primitive, which
is the only place its deletion fails.  A new assertion about the cut frame's own
links taken from the composite's post-state is testing `consumed`, not the splice.

(3) **The below side declines rather than refusing**, for the reason it does live:
the `…OrSelf` fold turns a *refusal* into the identity, and that is sound only
because a refusal means nothing links down to the cut frame.  A below-side refusal
folded to the identity would leave a reciprocating frame above naming a frame whose
caller has been cleared.  So the refusal set is unchanged from the sever's, and
`frozenSpliceReplyFrameStores_eq_sever_of_no_frame_below` is the equality that
makes every pre-HP8 scenario answer as it did.

(4) **Depth ≤ 2 cannot measure this flip, and the suite was green before it.**
A two-frame stack's lower frame is its bottom, so both policies write the same
value there; `FO-031` and `FO-041`/`FO-042` all sit on such stacks and passed
byte-identically when the splice landed.  `FO-043` is the three-frame witness with
the answered caller holding the **middle** frame, mutation-verified in both
directions.  A new frozen removal scenario that asserts a connectivity property
must be at depth ≥ 3 or it is asserting about the fixture.

(5) **The census carries three frozen splice entries where the sever had two.**
The store step is registered on its own — as the live `spliceReplyFrameStores` is,
because it performs the writes with none of the removal's resolution or validation
— and each is a `.mirrors` entry naming the live counterpart of the *same shape*,
so the store step's chain terminates in a stating entry two hops out, through the
live `.halfStep`.  The census prints its own counts; they are not restated here,
for the reason the WS-RM section's item (6) gives — this paragraph carried them
until the post-landing audit (`v0.35.61`) found it doing so.

**What new code must respect since HP9 (`v0.35.48`).**  Five things, and three of
them are about what the phase did *not* do.

(1) **The depth-4 witness measures the splice's COMPOSITION, not its stores.**
`tests/SmpIpcSuite.lean` §3.23 cuts the third frame of a four-frame stack, so
**two** frames sit below the cut — the shallowest shape on which the splice's
transitivity is a proposition at all, since at depth 3 "the stack reconnects" and
"the frame beneath the reconnection survives" are one statement.  Three successive
pops then carry the reservation home, where §3.22 needs two.  What it deliberately
does **not** catch is a change to the three stores: `spliceReplyFrameStores_cases`
states them exactly, so both candidate mutations — the full sever, and a
reconnection that clobbers the frame below's own downward link — fail to
*elaborate* rather than failing a test.  A new reply-stack scenario that asserts a
store shape is duplicating a theorem; one that asserts a *walk* or a *pop chain* is
measuring something no theorem states.  And a pop chain **follows** the resolver's
answer rather than supplying it: `returnDonatedSchedContextResolved` reads
`replyStackOuterCaller?` of its own state, so each row asserts where the kernel says
the reservation is still owed and the next row pops at that same thread.  A chain
whose recipients are chosen by the fixture measures the fixture.

(2) **The upstream facts live beside the code they justify.**
`donationRecipientAcceptable`'s docstring carries all three — `reply_pop` donates
only under `if (tcb->tcbSchedContext == NULL)`, the trigger is
`call_stack_get_isHead(reply->replyNext)`, and `reply_remove`'s non-head branch
writes **zero** into the frame above — each naming the revisions read.  A claim
about an external artefact belongs at the code it justifies, and it names a **tag**
rather than a repository, because `v0.35.14` asserted the opposite, quoted a line
that exists in no release, and swept that error across nine prose sites and three
docstrings that had been right.

(3) **The anchors are where their cuts put them, not in a closing sweep.**  HP9.2
asked for positives and negatives over the splice, the trigger and the recipient
guard; every one of them had already landed with HP6.5, HP7 or HP8, mutation-tested
in both directions at the time.  So HP9 added only the depth-4 witness's own,
and **retired one it had first written**: a standalone check that the scenario is
*called* duplicated the WS-OD contiguous-run anchor, which already names every
runner of that group **in order** — and which is what caught the insertion, exactly
as its own comment says it caught OD3.1's and OD4.1's.  A new scenario in that
group therefore extends that anchor rather than adding a sibling; adding parallel
anchors to satisfy a row would have been the duplication this file spends its
length retiring.

(4) **The donation-accounting register row is still OPEN, and HP9's acceptance box
saying otherwise is struck through rather than ticked.**  That box was written
before `v0.35.42` found the depth-**2** loss, where the removal takes the client's
frame off the *bottom* of its stack and both policies write `none` into the frame
above — so the splice provably cannot reach it.  What WS-HP earned is the depth-≥ 3
half.  Closing the row would corrupt the artefact RR8.15's hand-off check reads, so
at HP9 v1.0.0 could still not claim that completing a call chain returns a client's
reservation *unconditionally*: that was HP10's, and **HP10.9 (`v0.35.53`) earned
it** — `donationAccountingPreserved_atCallDepthTwo`, closed by the reservation's
recorded origin rather than by any change to the removal.  The row itself retires at
HP10.10, which is why it is still open at HEAD.

(5) **An acceptance box is a present-tense claim, so a later phase that deletes its
artefacts must sweep it.**  HP9's closure read the plan's acceptance list against the
tree and found box 3 — *the two triggers are proved equivalent … and the theorem that
the splice breaks that equivalence exists* — citing two declarations that survive only
as tombstones: HP6.8 deleted `severAtCut_pop_leaves_no_head` because its first
conjunct was the policy constant at the old value, and HP7 deleted HP2.1's equivalence
with the binding-driven resolver it was stated over.  Both deletions were right, and
both were cuts whose own citation sweeps missed this box, because a criterion reads as
*history* while being written as a live claim.  It is corrected by recording the
lifecycle rather than by weakening the criterion: an **ordering pin** exists to make a
sequence machine-checked *while the ordering is still ahead*, and once the ordering is
taken its subject is gone — so the box says it is not re-verifiable by grep, names the
cut that earned it, and names what replaced each artefact.  A box whose artefacts a
later phase consumed, left in the present tense, reads exactly like a box nobody
checked.

**What new code must respect since HP10.6 (`v0.35.50`).**  Both reply footprints
declare the TCB a bottom-of-stack pop will redirect the reservation to, and
`maxLockSetSize` is **24**.  Seven things.

(1) **The resolver is `donationOriginRecipient?`, and it is the expression the arm
will read.**  It answers `some o` only where all three of the pop's own conditions
hold: `replyStackOuterCaller?` says bottom of stack (which *is*
`returnDonatedSchedContextResolved`'s `newOwner? = none`, so the member is declared
on exactly the states the pop writes it), the context records an origin, and that
thread passes HP4.6's recipient guard — and, since HP10.7, `donationOriginRebindable`.
It is a *distinct* key exactly on the out-of-order removal this phase exists for,
which is the state HP10.7's pop writes a different TCB on.

**HP10.6 claimed this member is live at depth 1, and HP10.8 measured that it is
not.**  The footprint resolves on the syscall's **pre-state**, where the answered
caller is `.blockedOnReply` — it is waiting on this very reply — so HP10.7's
rebindability guard refuses it and the member is `none` there.  The *transition*
resolves after the reply leg, which wakes that caller, so it may answer `some
answeredCaller`; the pop then writes `replyTargetTid`, which the footprint declares
unconditionally, so nothing is undeclared.  Two consequences a reader must not
lose.  The `insertOrMerge` collapse asserted in `tests/DeadlockFreedomSuite.lean`
is a statement about the **argument value**, not about a reachable resolution.  And
the footprint and the transition read the resolver at **different states**, which
every other member of this family avoids by construction — the asymmetry is
registered rather than assumed away (`docs/REGISTERED_DEBT.md`, WS-HP).  `donationOriginRecipient?_eq_some_iff` is
the one characterisation the three consumers read — a second case analysis over the
same four-way match is the duplication this file spends its length retiring.

(2) **The guard is applied to the CANDIDATE, not to the argument.**  That is the
whole difference between a recovery and a regression: a stale origin makes the
resolver answer `none` and the pop falls back to the reachability recipient, where
applying the guard after the choice would *refuse* the pop.  A resolver that
answered `some` unconditionally passes every positive anchor and breaks this; a
Tier 3 positive pins the `if … then some origin else none` shape.  **And since
`v0.35.61` a candidate is first of all a thread that resolves.**  Both guards pass
a thread with no TCB (their `_of_none` arms exist so the *operation's* argument
keeps its own error code), so as first landed a recorded origin naming no thread
was answered as a candidate and the pop's own `lookupTcb` then refused the reply
with `.objectNotFound` — a refusal on exactly the shape this item says falls back.
Unreachable, because objects are never erased and `clearDonationOriginReferences`
clears the field when the thread it names is retyped, and closed anyway: a
contract the code does not decide is one a later cut can break silently.  The
resolver resolves the origin through `lookupTcb` before it consults either guard,
`replyDonationRecipient_resolves` is the no-refusal fact the pop now has (whenever
the answered caller resolves, so does the recipient), the frozen mirror does the
same through `frozenLookupTcb`, and §3.25 and FO-044's third half are the
witnesses — each with the two-guard CONTROL that makes the decline attributable to
the resolution check alone.

(3) **The member is a WRITE, and coverage is a relation rather than a presence
check.**  `lockSet_endpointReply_originRecipient_write_mem` and its `.replyRecv`
twin state the membership at full arity, and
`lockSet_endpointReply{,Recv}OnCore_covers_originRecipient` state it of the
*resolved* footprint under the trigger's own answer.  The Tier 3 anchor over each
definition asks only that the resolver occur there, which is the presence check
those theorems replace.

(4) **The ceiling moved and the reachable figures did not — by theorem.**  The
origin member is live only at the bottom of a stack, and there the two below-head
members are both absent (`replyStackBelowHead?_of_originRecipient`, over
`replyStackBelowHead?_of_outer_none`), so a reachable footprint trades **two**
members for one: `lockSet_endpointReplyRecvOnCore_size_le_twenty` and
`…_size_le_eighteen` are unchanged, now by a case split on the redirect, and
`tests/LockSetSuite.lean` exhibits the redirecting shape at **seventeen** —
one *narrower* than the popping shape it is measured against at the same operands.
What moved is the union over all argument values, which is what
`boundedWait_under_2pl` and the WCRT surface consume.

(5) **The cost is not restated here.**  `maxLockSetSize` moved and the RPi5
per-lock cost and envelope moved with it; all three live in the canonical sentence
this file carries above, which `scripts/check_lock_ceiling_figures.py` derives from
the Lean sources and holds every prose copy to.  A second copy of the figures in
this paragraph would be a hand-kept number beside a derivation, which is the shape
that drifts on contact — and the gate refuses a near-miss of the canonical phrase
rather than skipping it, which is how this paragraph's first draft was caught.

(6) **The redirect's SCOPE is the reply path, and the declaration is what fixes
it.**  All six pop call sites thread `returnDonatedSchedContextResolved`, and only
the two reply footprints declare an origin member — so a redirect placed in that
shared resolver would make `lockSet_endpointReceive`, `lockSet_replyRecv`'s
pre-return group, `lockSet_cancelIpcBlocking`, `lockSet_cancelDonation` and
`lockSet_tcbSuspendOnCore` **false** of their own transitions.  HP10.7 therefore
redirects in `applyReplyDonation`, `applyReplyDonationOnCore` and
`replyRecvPopDonation` only; widening it is a cut that declares first.  That is
also the right scope on the merits — the registered defect is the reply path's, and
the cancellation reclaim's recipient comes off the victim's own frame head
(`cancelledCallerDonation?`), which is a different question.

(7) **Seven sharp bounds are DELETED, and one of them is a Tier 3 negative now.**
HP6.2 established that the owner merge — the returned donation's holder *is* the
thread the reply answers — is **false** on every state the arm reaches, retired the
resolved `…_size_le_seventeen` it licensed, and left five `_of_owner_eq_target`
bounds and two `_of_no_donation` corners with no consumer in the tree.  A sharp
figure resting on a refuted hypothesis is worse than no figure, so they are gone
with a tombstone naming what replaced them, and `_size_le_twentytwo_of_owner_eq_target`
must not come back.  The four live sharp bounds carry `_of_no_origin` in their names
because they are stated at the origin's absence; the three
`_of_no_belowHead` bounds beside them are the branches on which the redirect fires.

**What new code must respect since HP10.7 (`v0.35.51`).**  The reply path's
bottom-of-stack pop hands the reservation to the recorded **origin**.  Six things.

(1) **`replyDonationRecipient` is the one answer, and all three reply-path pops
read it.**  `applyReplyDonation`, `applyReplyDonationOnCore` and
`replyRecvPopDonation` take it; a second spelling of "which thread receives the
reservation" is the duplication this project spends its length retiring, and these
two readings *disagree* on exactly the states the phase exists for.  It is the
identity wherever HP10.6's resolver is silent
(`replyDonationRecipient_eq_of_no_origin`) and on every `some`-arm pop
(`_eq_of_outer_some`), so every pre-HP10.7 result is a case split whose `none`
branch is the old proof verbatim.

(2) **The scope is the reply path, and the declaration fixes it.**  All six
operational pops thread `returnDonatedSchedContextResolved` and only the two reply
footprints declare an origin member, so a redirect placed in that shared resolver
would make `lockSet_endpointReceive`, `lockSet_replyRecv`'s pre-return group,
`lockSet_cancelIpcBlocking`, `lockSet_cancelDonation` and
`lockSet_tcbSuspendOnCore` **false** of their own transitions.  Widening it is a
cut that declares first.

(3) **The guard is a CONJUNCTION, and the second half is soundness rather than
depth.**  `donationRecipientAcceptable` asks that the recipient hold no binding of
its own; `donationOriginRebindable` asks that no *other* thread's binding name it
as owner.  `donationOwnerValid` requires that owner to be `.unbound`, so a thread
can pass the first while a live binding is counting on it — and `.bound scId`
there falsifies that binding's clause.  Reachable with ordinary syscalls: a client
answered out of order is woken `.ready` and `.unbound`, and may bind a second
reservation and Call with it while the first is still parked on a server whose
stack records it as the origin.  **Since `v0.35.157` the second half is the
bind's own admissibility** — the origin's reply frame is on no live stack
(`replyFrameOnLiveStack`) — and `donationOriginRebindable_no_owner` derives "named
by no live binding" from it under `donatedContextIsOwnerFrameHead`; until then it
read the origin's `ipcState`, a proxy that refused the re-called client and
transferred its reservation (PR #897's review, `v0.35.141`).  An origin the guard
declines **falls back** to the reachability recipient rather than refusing the
pop, which is the difference between a recovery and a regression and the reason
HP10.6 applied the guard to the candidate.

(4) **The bundle splits the recipient from the binding's recorded owner.**  One
thread used to play three roles — the operation's argument, the binding's owner,
and the relaxation point of `ipcInvariantFullExceptDonationOwner` — and exactly
**one** conjunct argument cared: `donationOwnerUnique`, `donationBudgetTransfer`,
`passiveServerIdle`, the scheduler frame and the read agreement all take the
recipient purely as the operation's argument.  `donationOwnerValid` is the
exception, and `returnDonatedSchedContext_establishes_{donationOwnerValid,
ipcInvariantFull}_of_except_redirected` are where `hNoOwner` lands.  A new
argument reaches for the conflated form when the recipient *is* the binding's
owner and for the redirected one otherwise; the conflated form is the instance,
not a weaker statement.

(5) **The replenishment migration's DESTINATION follows the redirect.**
`ownerHome` was `determineTargetCore st1 target` — the answered caller's home —
and a redirect that moves the reservation without moving the queue leaves
`replenishQueueAffinityConsistentOnCore` false from the instant it commits, which
is the standing constraint every SchedContext hand-off in this tree is held to.
`replyDonationRecipientHome` mirrors HP4.3's source resolver clause for clause and
the three readers that must agree all take it: the live dispatch, the affinity
proof, and the SM8.B per-core write set that mirrors the dispatch's control flow.
`hOwnerHome` is quantified over the trigger's answer now — HP4.3 recorded that the
two home hypotheses swapped conditionality, and the redirect makes **both**
conditional.  A Tier 3 negative refuses the answered caller's home in that
position.

(6) **The witness is decisive, not merely green.**  `tests/SmpIpcSuite.lean` §3.25
resolves the redirect to a *different thread* on a *different core*, and each
guard's negative is paired with a **control** asserting the other guard admits
that state — so a decline is attributable to the guard it is about.  Reverting the
redirect does not reach the witness: it fails to elaborate, because
`replyDonationRecipient_eq_origin` and its siblings pin the definition
structurally.  A new scenario in that group **extends** the contiguous-run anchor
rather than adding a sibling.

**What new code must respect since HP10.8 (`v0.35.52`).**  The frozen mirror
redirects too, and running it beside the live arm found two defects.  Five things.

(1) **`frozenReplyDonationRecipient` is the mirror, and it had to land within one
cut of HP10.7.**  `frozenBranchOperationChecked .endpointReplyToBlockedCaller =
true` is a machine-checked claim that the two programs are run beside each other,
so a window in which the live arm redirects and the mirror does not makes that
claim an **over-claim** rather than a failing test — every existing scenario keeps
passing, because none of them recorded an origin that differs from the answered
caller.  That is HP4.7's situation verbatim, and this is why the plan's HP10.8 row
says *same cut*: HP10.7 landed alone at `v0.35.51`, and closing the window was the
first thing `v0.35.52` did.

(2) **The frozen return clears the origin on the bottom arm — it did not before,
and FO-044 is what found it.**  HP10.4 landed the field's clears on the live side
only; `FrozenOps` carries the **live** `SchedContext` record, so the field was
there and unswept.  A frozen state left with a stale origin is the thread-id-reuse
hazard the field's own docstring names, one surface over, and nothing could see it
until a frozen scenario recorded an origin at all.  **A field added to a shared
record is a sweep of both surfaces**, not of the one whose transition motivated
it.

(3) **The differential is what catches a mirror that agrees on the headline and
diverges underneath.**  FO-044's eleven earlier assertions all passed — both
surfaces bound the reservation to the origin, both left the answered caller
unbound — and `frozenRunAgrees` still failed, on the `donationOrigin` field no
per-object assertion mentioned.  A scenario that asserts only what it set out to
measure would have reported the flip as clean.

(4) **The answered caller's own frame HEADS the context at the state the resolver
reads, so the redirect DECLINES it and the recipient comes from the fallback.**
(Until `v0.35.157` the decline read its `.blockedOnReply` instead; the frame is
what the guard reads now, and the verdict there is the same.)  Same thread,
different route — and it is what makes FO-044's second half discriminating, since
a selector that fired unconditionally passes every outcome assertion and fails the
resolver one.  It also retires HP10.6's claim that this
member is live at depth 1: see the correction in that block, and the registered
asymmetry between the state the **footprint** resolves at and the state the
**transition** resolves at.

(5) **Both guards are mirrored, and mirroring one would be worse than mirroring
neither.**  `frozenDonationOriginRebindable` is `donationOriginRebindable`'s
counterpart because the frozen surface models the same bindings; a mirror carrying
the recipient guard alone would redirect on states the kernel refuses, which is
the direction that matters on a differential surface.  The resolution check is
mirrored too since `v0.35.61` (`frozenLookupTcb`), with FO-044's third half the
witness on both surfaces.

**What new code must respect since HP10.9 (`v0.35.53`).**  The depth-two payoff is
stated and measured, so the donation accounting holds at **every** reply-stack
depth.  Six things.

(1) **`donationAccountingPreserved_atCallDepthTwo` derives the reachability answer
and the rebindability, and hypothesises the recipient guard, and the split is not
stylistic.**  `replyStackOuterCaller? st' scId = .ok none` — the very answer that
names the wrong thread — is a **conclusion**, read off the removal through
`removeCallerReplyFrame_clears_prev_of_bottom_frame`, so no hypothesis hands the
payoff over.  `donationOriginRebindable st' origin` is a **conclusion too since
`v0.35.157`**: the removal took the owner's frame off the stack and cleared its
`replyObject` (`removeCallerReplyFrame_replyObject_none`), and a thread holding no
reply object is on no live stack (`donationOriginRebindable_of_no_reply`) — where
the retired `.blockedOnReply` proxy was false at the pre-state, true after the
wake, and false again the moment the owner re-Called.  `donationRecipientAcceptable`
stays a **hypothesis**, because nothing about the removal says the owner holds no
reservation of its own.  The origin's *existence* at that state is the other
hypothesis since `v0.35.61`, for the same reason: the removal's success says
nothing about the thread the field names (`consumeCallerReply` is total on an
absent caller), and the resolver now names only a thread it can resolve.  A cut
that "simplifies" the statement by hypothesising the resolver's answer, the
reachability answer or the rebindability has gutted it; Tier 3 negatives refuse
all three.

(2) **The sever-direction sibling is where the depth-two shape lives.**
`removeCallerReplyFrame_clears_prev_of_bottom_frame` is
`removeCallerReplyFrame_splices_reciprocally`'s counterpart: nothing sits below a
bottom frame, so `spliceFrameBelow?` answers `none`, the splice degenerates to the
sever, and the frame above is left `prev = none` — *the same value either policy
writes*, which is the whole reason HP6 could not reach this and HP10 had to.  Its
`above ≠ rid` is derived from bottom-ness (a frame that were its own frame above
would carry `prev = some rid`), not assumed; a Tier 3 negative refuses the
hypothesis.

(3) **The depth-three payoff is byte-identical, and that is the measurement.**
§3.22 and §3.23 are untouched and the golden trace is byte-identical, so this
phase is confined to the reachability gap rather than changing the chain — the
same criterion HP6.9 met in the other direction.  It is *structural* rather than
lucky: at depth ≥ 3 the pop sits at a `some` arm, where
`replyDonationRecipient_eq_of_outer_some` makes the redirect the identity by
theorem.

(4) **§3.20's accounting halves are PAYOFFs now, and they measure the live `.reply`
SPINE.**  They measured `returnDonatedSchedContextResolved` directly, which was an
accurate proxy for the pop while nothing redirected and is a proxy that *omits* the
redirect since HP10.7 — *a proxy is not the fact*.  `replyRemovalOutcome` drives
`endpointReplyCrossCoreDispatch`, so leg, pop, reversion and migration are all in
the measurement.  The retired `PAYOFF/COST` and `COST` labels are refused
tree-wide.

(5) **The decisive comparison is a differential WITHIN the suite, because no
mutation is available.**  Every mutation of the production code here — the origin
write, the resolver, the three pops, the dispatch's recipient — fails to
**elaborate** rather than failing the suite, which is the situation §3.23 recorded
for the splice's store shape.  So `replyRemovalOutcome` takes the chain as a
**parameter** and is applied twice: to a chain whose first push recorded an origin,
and to `pushStore`'s, which predates HP10.4 and records none.  One function, two
chains differing in exactly one field, opposite outcomes.  A new witness on this
surface should reach for that shape rather than for a mutation that will not
compile.

(6) **HP10.4's production write is measured, and it was not before.**  Every
fixture that carried an origin set the field by hand, so nothing asserted that
`donateSchedContext` records one — *a witness whose field is supplied by its
fixture asserts nothing about the production write that is supposed to supply it*.
`pushOwnerStore` is `pushStore` with the first push undone and `replyRemovalChain`
runs the live push **twice**, so §3.20 measures both directions of HP10.4: a
**first** push records the origin, an **onward** push leaves it alone, which is
what distinguishes an origin from a duplicate of `.donated scId owner`.  The same
construction asserts that the first push reproduces `pushStore`'s own shape, so
the hand-built fixture is known to be a state the kernel reaches.

One mechanical note, and it is this project's own silent-skip rule catching a gate
defect rather than a code one.  A Tier 3 anchor added in this cut lost the closing
quote of its `bash -lc '…'` argument, so it swallowed the following lines, ran a
search against the wrong file and **never decided** — `bash -n` passes, the gate
prints PASS, and only a mutation of its subject reveals the silence.  The mutation
harness reported it (as a negative that would not fire), and
`scripts/check_anchor_consistency.py` refuses it by name for exactly the stated
reason that *"the gate could not read it" and "the gate checked it" must never
produce the same PASS line*.  **Mutation-test a new negative anchor by breaking the
relation it forbids** — and read its verdict as a statement about the anchor, not
only about the tree.

**And the splice is not the whole remedy — depth 2 needs HP10** (registered
`v0.35.42`).  The register scoped this defect to reply-stack depth ≥ 3 and that
was its own error: at depth **2** the delegate answers the client out of order,
the removal takes the client's frame — the stack's *bottom* — off the stack, and
the later in-order pop finds the remaining frame at the bottom and binds the
reservation to the **intermediate** caller.  Both policies write `none` into the
frame above a bottom frame, so the splice **provably cannot** reach it: the
sentence that explains why §3.20 cannot measure the depth-≥ 3 defect is the
reason the depth-2 defect survives HP6 — and HP6.9's own acceptance criterion,
that §3.20's depth-two halves pass byte-identically, is the measurement that it
does.  §3.20 exercises the depth-2 *structural*
outcome and asserts nothing about where the reservation ends up, so this half was
in the tree's reach and in neither its witnesses nor its register.

The cause is not seL4-MCS and not the removal policy: the recipient is derived
from **stack reachability**, so removing a frame changes who the kernel believes
owns the context — and upstream's `reply_pop` donates to the answered frame's own
`replyTCB`, so it has the depth-2 loss too.  HP10's remedy is one `SchedContext`
field recording the reservation's **origin** and one arm reading it, with the
answered caller as the fallback, so it is a strengthening with no state on which
it is worse than today.  Three things new code must respect once it lands: the
origin is **history the kernel validates, not an invariant** (no
`donationChainWellFormed` clause can state it, because "or a thread whose frame
was removed" is unstateable from the store — the pop's
`donationRecipientAcceptable` guard is what makes reading it safe); **thread-id
reuse is the hazard**, closed by `lifecyclePreRetypeCleanup` clearing a stale
origin before anything reads the field; and **the footprint grows**, because
redirecting the recipient changes which TCB the pop writes —
`maxLockSetSize` 23 → 24.  It lands in WS-HP rather than WS-CB, whose plan has no
sub-task started and would defer a correctness fix indefinitely; WS-CB inherits
the field.

Three things a reader should take from the plan rather than infer.  (1) **The
payoff is larger than the accounting**: under the head-driven trigger the three
*stated* pre-state coherence hypotheses the reply path used to carry
(`replyStackHeadIsAnsweredReply`, `replyDonationOwnerIsAnsweredCaller`,
`answeredHeadContextIsServerDonation`) became derivable and are **deleted** at HP7
(`v0.35.46`) — no invariant in this tree entailed them, HP4 had already retired the
third from the chain composite for the strictly weaker `replyFrameHeadIsBound`, and
HP6.2 left none of the three with a consumer.
(2) **The cost is stated**: `maxLockSetSize` 22 → 23 and the RPi5 per-lock cost
15 → 14 µs, because the splice writes the frame below and no footprint named it
(HP3.5).  The splice's *third* store, added at HP6.3, costs nothing further — the
cut frame's lock was already declared on both paths.  (3) **HP5 was not optional**, and its reason was
derived rather than assumed: after the splice a frame becomes the head whose
recorded reply target is gone, so a *cancellation* there would leave a `.donated`
binding naming a `.ready` owner.  It landed at `v0.35.39`; the paragraphs above say
what it changed.

Registered in
[`docs/REGISTERED_DEBT.md`](docs/REGISTERED_DEBT.md) table C, closed there at
`v0.35.54`, **re-opened at `v0.35.141` on the depth-2 half** — see the paragraph
above for what PR #897's review measured — and **closed again at `v0.35.157`**,
when the redirect's guard became the bind's own admissibility rather than a proxy
for it.  So v1.0.0 may claim both halves: a middle removal leaves the reservation
owed outward (HP6's chain-preserving removal), and a completed call chain returns
a client's reservation at every reply-stack depth (the recorded origin, under a
guard that is the fact).  What it must still not claim is *parity* with seL4-MCS
on reply-stack removal at depth ≥ 3: upstream severs and this kernel splices, so
the honest claim there is an improvement on upstream rather than a match for it.

**The post-landing audit (`v0.35.61`) — what reading the code against its prose
found.**  The whole of WS-HP, RR8.1–RR8.4 and the `v0.35.59`/`v0.35.60` cuts were
re-read with every docstring treated as a claim to check rather than a description
to trust.  The code held: each resolver, guard, pop, splice store and frozen
mirror does what its section above says; the deleted `detach*` theorems all have
splice twins; objects are never erased, so a recorded origin always resolves; and
the recipient guard is inert on reachable states because `schedContextBind`
refuses a thread whose frame is on a live stack.  What did not hold was prose
**about the future, or about the sever** — ten docstrings and comments across six
Lean files, and the plan's HP4 narrative.  `replyFrameHeadIsBound`'s docstring and
the chain composite's both said *"HP7 is where it becomes a clause of the chain
invariant"*, and HP7 did no such thing — no plan row ever scheduled it; the rest
still read *"once HP4 lands"*, *"once HP6 makes the removal a splice"*, *"the
sever today, the splice after HP6.3"*, *"the one HP10 will have to keep true"*,
or described the removal as clearing the frame above's `prev`, each about a phase
that had landed.  The retired-code section's rule — *sweep the forward-looking
prose when the phase it names closes* — is the one that catches these, and
WS-HP's own closure had not run it over WS-HP's own docstrings.  Three findings
beyond prose.  (1) **A contract the code does not decide is one a later cut can
break silently**: `donationOriginRecipient?` promised that a stale origin *falls
back rather than refusing*, and decided it only for an origin failing a guard — a
recorded origin naming no thread passed both guards and reached the pop's own
lookup as `.objectNotFound`.  Unreachable, and closed on both surfaces (item (2)
under HP10.6 above).  (2) **One thread, two spellings**: `replyRecvPopDonation`
passed `holderV.val` / `targetV.val` to the return and `holder` / `target` to the
migration, and four proofs carried `toValid?_some_val_eq` rewrites to reconcile
what one `let` now states once.  (3) **A hand-kept figure had crept back in**:
HP8's paragraph restated the reply-stack census's totals a few paragraphs after
the WS-RM section says why that shape drifts — accurate that day, deleted anyway.
And the two stated coherence facts HP7 left standing — `replyFrameHeadIsBound`
and `replyFrameHeadHolderDonation`, true on every reachable state by arguments
their docstrings carry and entailed by no invariant — had no register row; they
have one (`docs/REGISTERED_DEBT.md`, table C).

**The second pass (`v0.35.62`) — a sweep the closure claimed and had not run.**
HP6.1 recorded that the word *detach* was accurate at that version and that HP6.3's
cut would sweep it; the operation had been a splice for seventeen cuts and the
sweep had reached one docstring.  Measured rather than estimated: some 120 sites in
35 files still called the splice *the detach*, and nine of them described the
**sever** as its behaviour — "`spliceReplyFrameOut` sets its `prev := none`",
"clears the `prev` of the frame above", "the `severAtCut` policy is unchanged and
is now carried out by the detach", "the frame above becomes the bottom of the stack
it heads" — in `LockSetTransitions.lean`, `Endpoint.lean`, `Cancellation.lean`,
`CancellationReplyShape.lean`, `SchedContext/Operations.lean`, `Reply.lean`,
`Defs.lean`, the spec's §8.12.7 and GitBook 12.  Each now says what the splice
writes, and where the sever is still the truth — the *degenerate* arm, taken at a
bottom frame or when the frame below does not reciprocate — says that instead.
Three stale **figures** rode along, none of them in a theorem: two docstrings still
called the splicing `.replyRecv` branch *sixteen, two below* the popping one, on
theorems whose conclusions read seventeen (`lockSet_replyRecv_size_le_seventeen_of_no_sender_of_no_head_of_no_origin`,
`lockSet_endpointReplyRecvOnCore_size_le_eighteen`); `maxLockSetSize`'s own
docstring narrated the ceiling to twenty-three and stopped, one raise short of the
constant beneath it, and cited `lockSet_endpointReplyRecvOnCore_size_le_nineteen`,
renamed at HP3.2; and `tests/DeadlockFreedomSuite.lean` labelled a `.replyRecv`
shape *declares 22* while asserting `maxLockSetSize - 1`, which had been 23 since
HP10.6, with its negative pinned at the literal 21 rather than at the ceiling's
minus two — both derive from the constant now, and the Tier 3 anchor on the label
moved with it.  Two dead citations: `Endpoint.lean` named `replyDonationOwnerHome`
(retired at HP4.3) as live discipline, and `EndpointReplyDispatchInvariant.lean`'s
HP6.2 block said `answeredFrameHeadContext?_implies_serverDonation` was *not*
retired, forty lines below the HP7 comment recording that it was.  And
`SchedContext.donationOrigin`'s docstring pointed at §3.20's `PAYOFF/COST` rows,
which HP10.9 renamed.  One inert attribute went with the prose:
`cancelledCallerDonation?_independent_of_victim` was `@[simp]`, and a rewrite rule
whose right-hand side has a free variable can never fire.  What the pass
**re-verified**: every one of the 122 declarations this PR deleted has a splice or
head-driven twin or a documented retirement, every one of the 31 theorems whose
hypotheses changed is recorded in the section above, no added line carries a
`sorry`, `axiom`, `native_decide` or `partial`, and every declaration-shaped name
the CHANGELOG cites either resolves or is named as retired.

Plan: [`docs/planning/DONATION_POP_TRIGGER_PLAN.md`](docs/planning/DONATION_POP_TRIGGER_PLAN.md).

### WS-SM SMP multi-core completion — IN FLIGHT (v0.31.2 → v1.0.0)

Unified workstream merging WS-RC's remaining R6..R14 phases with the SMP-specific
SM-phases (SM0..SM10).  Closes at v1.0.0 with a bootable verified SMP microkernel
on Raspberry Pi 5.

**Binding decisions**: per-object RW fine locks; path-a `Vector` state
replacement; hierarchical-by-kind lock order (`LockKind` levels 0..9 from SM0.I);
SMP enabled by default at v1.0.0; `numCores` via `PlatformBinding.coreCount`
(RPi5 = 4); verified `TicketLock` + `RwLock` with formal mutex/fairness theorems;
SGI INTID 0..4 reserved for kernel SMP coordination (SM0.H).

| Phase | Status | Version | Scope (one line — detail in the canonical sources) |
|-------|--------|---------|----------------------------------------------------|
| SM0 | CLOSED | v0.31.3 | Foundational types, honesty patches, lock hierarchy |
| SM1 | CLOSED | v0.31.8 | Rust HAL: PSCI, per-CPU, secondary init, TLBI, SGI, QEMU |
| SM2 | LANDED | v0.31.9; SM2.C-defer closed v0.34.50 | Memory model, TicketLock, RwLock, FFI bridge, refinement (WS-RR RR6 closed the deferred completion: the deployed lock is `QueuedRwLock` and refines the FIFO spec) |
| SM3 | CLOSED | v0.31.9 | Per-object locks, lock sets, 2PL, deadlock-freedom, serializability |
| SM4 | LANDED | v0.31.37 | Per-core Vector state, SchedulerState, register banks, invariant migration, idle bootstrap |
| SM5.A–H | LANDED | v0.31.38–62 | Per-core scheduler: selection, switch, wake, timer, idle, PIP, domain, CBS |
| SM5.I | LANDED | v0.31.61; entry lock v0.32.142 | Per-core invariant suite + register banks; the global kernel-entry ticket lock (see the standing constraint below — the table read v0.31.38–62, which the constraint contradicted) |
| SM5.J | LANDED | v0.31.63→64 | WCRT under fine locks; per-core eventually-scheduled liveness |
| SM5.K | LANDED | v0.31.63→64 | Scheduler tests + fixtures: 4-thread/4-core aggregate suite, WCRT suite, golden trace |
| SM6.A | LANDED | v0.31.65→67 | Endpoint call across cores, live `.call` dispatch + SGI-firing seam |
| SM6.B | LANDED | v0.31.68→76 | Notification across cores + bound notifications, live |
| SM6.C | LANDED | v0.31.77 | Reply path across cores + live `.reply` / `.replyRecv` dispatch |
| SM6.D | LANDED | v0.32.58→59 | IPC across-core invariant bundle (`ipcInvariantFull_perCore`) |
| SM6.E | LANDED | v0.32.60→66 | Cancellation across cores; live `.tcbSuspend` cross-core dispatch |
| SM6.F | LANDED | v0.32.67→68 | SM6 closure: IPC + notification suites, 4-core golden fixture |
| SM7.A | LANDED | v0.32.72→75 | TLB shootdown descriptor + per-core pending/ack state |
| SM7.B | LANDED | v0.32.76→79 | Shootdown protocol, complete and live (Theorem 3.3.1, round lock, bounded wait) |
| SM7.C | LANDED | v0.32.80→83 | Per-core TLB model, mounted and wired to the shootdown protocol |
| SM7.D | CLOSED (model level) | v0.32.94→102 | Cache maintenance broadcast — the instruction-cache half of SMP-C4 |
| SM7.E | LANDED | v0.32.103 | SM7 closure: shootdown storm, cross-cluster mock, golden fixture |
| SM7.F | LANDED | v0.32.84→105; F.5 v0.32.150–151 | Operative per-core TLB fills; round-generation-tagged descriptors |
| SM8.A | LANDED | v0.33.2→4 | Per-core observable state — the SMP information-flow observer |
| SM8.B | LANDED | v0.33.5 | Per-core non-interference — the SMP lift of the whole NI surface |
| SM8.C | LANDED | v0.33.7→8 | Per-core declassification audit + the producer that did not exist |
| SM8.D | LANDED | v0.33.9→22 | Information flow under fine locks; CC-5 contention channel bounded |
| SM8.E | LANDED | v0.33.23 | SM8 closure: surface anchors, observer golden fixture |
| SM9.A | LANDED | v0.33.42→50 | Audit-trail reader + drain — the 256-entry fail-closed cliff, closed |
| SM9.B | LANDED | v0.33.51 | Refusal auditing — the trail's blind spot (refused downgrades), closed |
| SM9.C | LANDED | v0.33.52 | Data-carrying declassification — the first deliberately visible flow |
| SM9.D | LANDED | v0.33.53→56 | Causal declassification provenance — the laundering detector stops guessing |
| SM9.E | LANDED | v0.33.100 | Tests + closure: acceptance scenarios run live and pinned as golden fixtures; seam boundary coverage of both declassifying syscalls; the epoch exercised with survivors |
| SM9 | CLOSED | v0.33.100 | Declassification completion — reader, refusal auditing, data-carrying signal, causal provenance, acceptance fixtures |
| SM5 runtime seams | LANDED | v0.34.1 | The three seams SM5's docstrings promised between the verified per-core scheduler and the hardware IRQ path — IRQ vector redirect, `.reschedule` SGI receiver, secondary bring-up entry — all dormant behind the per-core `lean_ready` gate until SM10.1 |
| WS-RR | **COMPLETE** | v0.34.26–v0.35.203 (RR0 v0.34.26; RR1 v0.34.41; RR2 v0.34.42; RR3 v0.34.43; RR4 v0.34.44; RR5 v0.34.48; RR6 v0.34.50; RR7 v0.34.47 → v0.34.92; RR8 v0.35.55 → v0.35.203, RR8 having grown 5 → 16 rows at v0.35.56) | Pre-SM10 remediation: the audit's 3 blockers, 11 security findings, fault IPC, de-threading closure, lock completion (**198** subs across RR0..RR8 — the figure the plan declares and the gate holds it to; this cell read 187 until v0.35.203) |
| SM10 | **UNBLOCKED v0.35.203** | — | Release closure (→ v1.0.0); SM10.1's content is **WS-BP** (see above), which opens first |

**Plans**: master overview at
[`docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md`](docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md);
per-phase plans at `docs/planning/SMP_*.md`, beginning with
[`SMP_FOUNDATIONS_PLAN.md`](docs/planning/SMP_FOUNDATIONS_PLAN.md) (SM0), which
the glob covers but no canonical index named until WS-RR RR7.32 made that
checkable.

### WS-BP The bare-metal boot path — IN FLIGHT (registered v0.34.59; absorbs WS-XV as BP0 at v0.34.124; BP0, BP1, BP2, BP3, BP4, BP5.1, BP5.2 and BP5.3 v0.36.2)

SM10.1 is not a release cut's first phase; it is a **bare-metal Lean runtime
port**, and holding the two in one plan produced a phase goal ("all substantive
SMP work is complete") that was false of the phase's own first row.  WS-RR
RR7.5 + RR7.15 split it out: [`docs/planning/SMP_BOOT_PATH_PLAN.md`](docs/planning/SMP_BOOT_PATH_PLAN.md)
sequences **48 sub-tasks across 9 phases `BP0..BP8`** in execution order — the
cross-implementation gates, the aarch64 Lean object code, bare-metal runtime
hosting, the RPi5 deployment, the boot seam and its install ordering, the
image, per-core readiness, the context restore, and first boot — with an acceptance gate whose every box is ticked by
an *executed run* rather than by an artefact existing.  **BP0 and BP1 landed at
`v0.36.2`**, and so did **BP2.1** (the Lean heap), **BP2.2** (the kernel's own Lean runtime, in Rust), **BP2.3**/**BP2.4** (the library initializer, failing closed), **BP2.5** (the host witnesses, which landed with the first two) and **BP2.6** (the boot map built from constants), and **BP3** (the RPi5 deployment, which boots, and the proof-layer bundle of the state it installs), and **BP4.1**/**BP4.2** (the `lean_kernel_main` entry, and the install ordered before the secondaries by a type), and **BP4.3**/**BP4.4** (the firmware's device tree reaching Lean, and the entry booting on it), and **BP4.5** (the boot image cleaned to the Point of Unification before any thread can fetch), and **BP4.6** (the verified board's RAM mapped above the guaranteed gigabyte), and **BP4.7** (that RAM handed to the root task as untypeds), and **BP5.1** (the kernel image, a bare-metal binary entered at `_start` under `link.ld`), and **BP5.2** (the Lean kernel linked into that image, under `--gc-sections` from the archive lane's own roots), and **BP5.3** (the firmware's boot files, `kernel8.img` and `config.txt`, cut from that image and checked against it); BP5.4..BP8 have not started.  **WS-BP is unblocked since `v0.35.203`**, WS-RR RR8 having closed.  BP7.8 was added
at that version by RR8.16's hand-off check, which re-homed the registered `MR4`-onward
IPC-buffer write there rather than leaving it owned by a finished phase; BP5.5
(the firmware's EL2 entry) and BP7.9 (per-thread FP/SIMD state) were added at
`v0.36.2` by the FP-free-kernel cut below.

Four things new code must respect.  **WS-BP takes its own prefix and renumbers
nothing**: `SM10.1.1` still means the image *packaging* the release cut
consumes, and `BP5.3` is the sub-task that produces what it packages — the
collision between "numbering is execution order" and "IDs in CHANGELOG entries
are frozen" resolved the way `SMP_RELEASE_CLOSURE_PLAN.md` §1.1 named it.  And
the three `contextRestoreSeamLive` prerequisites are now scheduled rather than
only described: `BP7.1`/`BP7.2` (the `VSpaceRoot → TTBR0` binding and its
install), `BP7.3` (the full outgoing-frame save — `writeFfiRegistersToTcb`
spills only x0–x5 and x7 today), `BP7.4` (per-core staging), with `BP7.6` the
flip they gate.

And **the boot map is BP2.6's, not the device tree's** (the maintainer's
correction, recorded as a scheduled row rather than as prose, and landed at
`v0.36.2` — the BP2.6 paragraph below).  `init_mmu` used to parse the firmware
blob *before* translation was enabled, to obtain a RAM *size* the boot map does
not need; the verified Lean parser is now the only reader of the blob's memory,
so the device-tree half of the WS-XV pair stopped existing rather than being
gated — which is what [`docs/REGISTERED_DEBT.md`](docs/REGISTERED_DEBT.md)
table C named as that pair's remedy.

And **WS-XV is BP0, not a workstream** (`v0.34.124`).  The cross-implementation
findings registered at `v0.34.114` were never given a plan file, and reading
their five rows back showed why: XV1 was always a WS-BP obligation and became
**BP2.6**; XV2 and XV3 were interim *by their own text* ("only if XV1 is far
off"), and BP2.6 retargeted them onto the half of the pair it kept (the Rust
structure walk the bootargs reader runs); XV4 and XV5 sit on surfaces this plan modifies
— the ABI BP7's context restore delivers, and the boot map BP2.6 rebuilds.
Half of WS-XV is deleted by WS-BP's own work and the other half is a harness
over what WS-BP changes.  BP0 is first because its value decays as the rest
lands, and it is the one phase that may run **in parallel** with any other:
nothing in BP1..BP8 consumes it, and the only coupling was BP2.6 retargeting two
of its rows and updating a third.  `docs/REGISTERED_DEBT.md` keeps the WS-XV
*finding* — the evidence that nominal gates miss behavioural drift — and no
longer a work list.

**BP0 — the three Lean/Rust pairs are driven through shared fixtures** (`v0.36.2`).
Four things new code must respect.  (1) **A question answered on both sides
of the boundary is compared by running both, never by a literal beside a
comment naming the other side.**  The device-tree readers share
`tests/fixtures/dtb/` (hand-written expectations in
`scripts/generate_dtb_corpus.py`, never in the rendered files); the ABI's bit
layout, register assignment and bounds share `tests/fixtures/abi_layout.expected`;
the boot map and the Lean memory map share `tests/fixtures/boot_map.expected`.
Both Lean tables go through `SeLe4n.Testing.checkSharedFixture`, and a new
two-sided table does too.  (2) **A divergence the fixtures expose is fixed on the
side that is wrong, never recorded as an exception**: the first run fixed thirteen
Rust and eight Lean refusals, so both readers now share one rule set — the Rust
walk runs `fdt_structure_check` first, the Lean parser bounds depth
(`fdtMaxDepth`), extent count (`fdtMaxMemoryExtents`) and 64-bit ends, and neither
reads a cell width that is not one `<u32>`.  (3) **A Rust FDT walk's bound is the
structure block's size** (`fdt_token_bound`), never a fixed fuel: 4096 tokens
refused a large well-formed device tree the Lean parser reads whole.  (4) **The
boot map is held to the Lean map**: every address it maps Normal is RAM in every
variant, its device window is exactly the Lean one (the BCM2712's SoC-bus
window, both ends 2 MiB aligned), and on the smallest variant its
RAM is exactly the variant's; `check_physical_address_width.sh` no longer
regex-parses `Board.lean` — the driven test decides it.

**The kernel is FP-free, and FP/SIMD traps at EL1** (`v0.36.2`, found while
scoping BP1).  Rust's `aarch64-unknown-none` enables `neon` and `fp-armv8`, and
the HAL built for it carried 129 FP/SIMD instructions (vector zeroing, `d8`–`d15`
spills) while the trap frame saves general-purpose registers only and nothing
wrote `CPACR_EL1` — so on hardware the first vector instruction either trapped
unhandled or, with FP access left on by firmware, every trap silently overwrote
the interrupted thread's `q0`–`q31`.  Latent (no core runs the Lean runtime
yet) and closed before it could ship.  Four things new code must respect.  (1)
**The HAL's target is `aarch64-unknown-none-softfloat`** — `rust-toolchain.toml`,
the cross gate, CI and every script that names it — so FP-freedom is a property
of code generation, as it is for seL4's kernel; the Lean C is compiled with
`-mgeneral-regs-only` for the same reason (BP1.2).  (2) **Both boot entries open
with `msr cpacr_el1, xzr` then `isb`**, trapping FP/SIMD/SVE/SME at EL0 and EL1
before anything else runs on the PE, and `build.rs`'s `scan_fp_trap_prologue`
requires exactly that prologue at `_start` and `secondary_entry` and refuses any
other write to `CPACR_EL1` in either spelling (`S3_0_C1_C0_2` included) in any
`.S` file or `asm!` template.  There is no encoding that traps EL1 alone, so a
**user** FP instruction traps too and is delivered as a `userException` fault
until BP7.9 gives threads an FP context — fail-closed, and the known cost.  (3)
**`scripts/check_fp_simd_free_objects.py` is the evidence rather than the flag**:
the cross gate's step [5/7] disassembles the release rlib and the assembly
archive and refuses any FP/SIMD/SVE register operand or `FPCR`/`FPSR` access,
reading operands only and refusing input it cannot decide, and
`check_aarch64_cross_target.py` requires that step — executed, over those two
release objects, not followed by `&&`/`||` (which exempts a command from
`set -e`; that check now covers the cross builds and the lint too).  (4) **It is
conclusive only on the linked image**: the target's own `compiler_builtins` is
*not* FP-free (the complex-arithmetic helpers and `__negsf2`/`__negdf2` use
`d`/`v` registers, and `__negdf2` takes a hard-float `d0` argument no soft-float
caller supplies), so the gate also runs over the linked image, where the link
decides which members are in (BP5.2: none of them is).  And the firmware enters the RPi5 at **EL2**, which
`boot.S` does not handle at all — BP5.5.

**BP1 — the kernel's Lean object code for the target is built and checked**
(`v0.36.2`, `scripts/build_lean_aarch64_archive.py`, lane
`scripts/test_lean_aarch64_archive.sh`, CI job `Lean aarch64 Archive`).  Five
things new code must respect.  (1) **The image's Lean is the elaborator's
closure of `SeLe4n`**, refused unless it equals Lake's `SeLe4n:modules`, holds
nothing outside `SeLe4n`/`Init`/`Std` and is disjoint from the staged allowlist
and `SeLe4n.Testing` — so importing `Lean.*` from a production module, or a
staged module, fails the lane rather than putting the elaborator in the kernel.
(2) **The allocator is a relation**: every object is compiled against
`rust/sele4n-hal/lean_include/lean/config.h`, the toolchain's with
`LEAN_MIMALLOC` swapped for `LEAN_SMALL_ALLOCATOR` and nothing else, and the
archive must call `lean_alloc_small` and no `mi_*`; the kernel's runtime
(BP2.2) serves the same allocator.  A macro the toolchain adds to its `config.h` stops the
build until it is classified.  (3) **The compile is soft-float and `-Werror`**
(`-mgeneral-regs-only -mabi=aapcs-soft`, the toolchain's own clang), and the
generator's two by-construction diagnostics are classified per instance — an
`x_N` temporary holding a discarded `BaseIO Unit`, an import-less initializer's
`res` — so any other warning, or either kind in another shape, fails.  (4) **The
stdlib C is regenerated, and proved to be the toolchain's**: each of the 609
closure stdlib modules must define exactly the global symbols the toolchain's
own `libInit.a`/`libStd.a` object for it defines — keyed by the member's
initializer, never its name, since `libInit.a` holds two `Grind.o`.  (5)
**Every unresolved symbol is attributed to a provider derived from that
provider's own object code or declarations** — allocator, the HAL (a production
module's `@[extern]`), the kernel's runtime (BP2.2), Rust `compiler_builtins`
for the target, or *unreachable* (an upstream runtime function or stdlib
`@[extern]` the reachable link proves nothing names) — and an unattributed one
stops the build.  Measured: 382 unresolved, **no libc symbol at all**.  And
`check_kernel_entry_exports.py` decides on **both** archives: a requirement is
met where both define it, an exemption stale where either does, and
`--require-cross` makes an absent cross archive a failure.  Since BP2.1 the
lane also holds the HAL-provided classes to the HAL's own object code: every
`allocator`, `hal` and (since BP2.2) `runtime` symbol, and the whole
small-allocator API, must be a global **function** of `sele4n-hal`'s rlib for the
target (193 of 193 at `v0.36.2`).

**BP2.1 — the Lean heap is one arena the linker places** (`v0.36.2`,
`rust/sele4n-hal/src/lean_heap.rs`).  Five things new code must respect.  (1)
**The arena's extent is `link.ld`'s, and nothing else's**: a `NOLOAD`
`.lean_heap` of `LEAN_HEAP_SIZE` (64 MiB) above the image and both stacks, three
`ASSERT`s (whole pages, page-aligned, inside the smallest board's `[0, 1 GiB)`),
each proved live by `scripts/check_link_script.py` — the cross lane's step
[6/7], which links a probe under the script and mutates it until every
assertion fires, because nothing else links `link.ld` before BP5.  (2) **One
heap, one exhaustion condition**: the HAL exports `lean.h`'s `lean_alloc_small`
/ `lean_free_small` / `lean_small_mem_size` under `hw_target`, and the kernel's
runtime (BP2.2) allocates its big objects and scratch buffers through
`Heap::alloc` / `Heap::free` on the same arena — upstream's `alloc.cpp` is not
linked at all.  (3) **All allocator state is out of band**, so the allocator never
touches the memory it serves, every free is validated in release builds (a
double free is refused, not absorbed), and every operation is bounded; a new
allocator feature must keep its state in the metadata pages, never inside an
object.  (4) **The C entry points halt** on a refusal and on exhaustion, after
releasing the heap's leaf lock — `lean.h`'s inline paths do not test the result,
so there is no error to return.  (5) **The boot map covers the arena, and a
device tree inside the image is refused**: the arena lies in the guaranteed RAM
the map covers, and `init_mmu` refuses a device-tree window overlapping
`[_start, __lean_heap_end)` (`mmu::kernel_extent`, `dtb_disjoint_from_image`) — the firmware places the blob by the image *file*'s
size, and everything past it is `NOLOAD`.  Placing the arena also found that no
boot refusal stops an untyped over kernel memory (`bootSafeUntypedCheck` accepts
every region); not attacker-reachable, registered in `docs/REGISTERED_DEBT.md`
table B, owned by BP3.2.

**BP2.2 — the kernel's Lean runtime is its own, in Rust** (`v0.36.2`,
`rust/sele4n-hal/src/lean_runtime/`; maintainer's decision: no C++ in the image).
Upstream's `libleanrt` is C++ over the standard library, threads and an OS; the
kernel provides the part its Lean objects reach.  Seven things new code must
respect.  (1) **The surface is derived**: the archive lane links `libsele4n.a`
with `--gc-sections` rooted at the library initializer — `initialize_seLe4n_SeLe4n`,
package-prefixed; an earlier probe rooted at `initialize_SeLe4n` measured 62
because the root was silently absent — and every production `@[export]`, and
every symbol that link leaves undefined must be a global function of the HAL's
rlib or `compiler_builtins`' (the builder prints how many).  The upstream
functions the runtime omits are *unreachable* by that link, so the image link
(BP5.2) uses `--gc-sections` over the same roots — read from the one file the
builder writes.  (2) **Each symbol is
faithful, environmental or fail-closed, and says which**: faithful ones are
ported from `lean4` at the toolchain's commit; the environmental ones answer for
a machine with no OS (platform queries, `Lean.githash` pinned to
`lean --githash` by the lane, zero-byte entropy, temporary files failing with
`unsupportedOperation`); `Float` formatting, `scaleB` and `pow`/`powf` halt, the
last two overriding `compiler_builtins`' **weak** libm port by the linker's own
rule (the lane refuses a strong one).  (3) **Upstream is the oracle**:
`tests/LeanRuntimeConformanceSuite.lean` runs on upstream's runtime and holds
`tests/fixtures/lean_runtime_conformance.expected` (9 215 results over the
representation edges, signs, zero divisors and every UTF-8 width) to what
upstream computes; `lean_runtime::conformance` recomputes every line with the
kernel's runtime, on both the exclusive and shared paths of each mutating
string operation, checks each result canonical, and ends leak-free.  A
primitive added to the runtime gets fixture lines, or a stated reason it cannot.
(4) **What the environmental answers rest on is proved**:
`SeLe4n/Testing/RuntimeEnvironmentCensus.lean` (Tier 1) walks everything every
production `@[export]` reaches, through bodies **and `implemented_by`** — what
compiled code actually calls — and fails if it meets `IO.stdGenRef` or a
constant implemented by one of the nine unprovided symbols; its list and
`io::UNPROVIDED_SEMANTICS` are held equal by a Rust test.  (5) **The runtime
never calls back into the program it serves**: `build.rs`'s readiness scanner
refused the first draft's call to Lean's exported `IO.Error` builder, so the
constructor is built directly and its tag pinned by the fixture.  (6) **No
object is ever multi-threaded, and no task or promise exists**: nothing marks
one, the kernel's Lean code runs one core at a time under the kernel-entry lock,
and every path that would meet one halts.  `panic!` returns `default` and
reports — that is what the proofs describe, so halting there would make the
kernel diverge from its model on the paths the model covers.  (7) **A function
that dereferences an object pointer it was handed is an `unsafe fn`**, with a
`# Safety` section saying what the pointer must be — private helpers included.
The first cut had fifteen safe helpers (`array`, `string`, `ref_cell`,
`nat_val`, `slots`, `del_core`, …) whose `// SAFETY:` comments read *every
caller passes a live …*: a caller's promise inside a safe signature, which the
compiler then lets any safe caller break, and which no gate sees —
`clippy::not_unsafe_ptr_arg_deref` covers `pub` functions only, and the
justification scanner asks whether a block is *commented*, not whether the
comment discharges anything.  A helper over state it owns (`Building`, the
persistence `WorkStack`, the `apply` argument buffer) stays safe.

**BP2.3/BP2.4 — the library initializer runs first, and the order is a type**
(`v0.36.2`, `rust/sele4n-hal/src/lean_entry.rs`).  Four things new code must
respect.  (1) **`lean_kernel_main` is reachable only through
`enter_lean_kernel`**, which consumes a `LeanLibraryInitialised` token that only
a successful `initialise_with` constructs — private field, neither `Clone` nor
`Copy` — so entering the kernel uninitialised, or twice from one
initialization, does not compile.  A new Lean entry on the primary takes the
token too.  (2) **A second initialization is refused by a guard set before the
initializer runs**, because Lean's generated initializer marks itself done
before it calls anything: a retry after a failure would answer `ok` without
re-running what failed.  (3) **Success is exactly a heap constructor of tag
0**; a scalar or any other tag is *malformed* and refused rather than read as
success, and the result's reference is released on every path.  A failure
halts the **system** (`gic::halt_all`), not the PE: it is the one barrier every
boot-fatal refusal uses, and since BP4.2 it also runs before any secondary is
released, so it costs nothing to use it here too.  (4) **A
HAL-declared `initialize_…` symbol is Lean code** to `build.rs`'s readiness
derivation (`is_hal_declared_lean_symbol`, shared with the `link_name` alias
scan), so the initializer call is one of the two entries in
`LEAN_UPCALLS_OUTSIDE_THE_GATE`, and `check_kernel_entry_exports.py` requires
both archives to define it.  Upstream's `lean_initialize_runtime_module` and
`lean_io_mark_end_initialization` are not called: the kernel's runtime has no
per-thread heap, task manager or initialization flag, and the reachable link
names neither.

**BP2.6 — the boot map is built from constants, and nothing is parsed before
translation is on** (`v0.36.2`, `rust/sele4n-hal/src/mmu.rs`, `link.ld`).  Five
things new code must respect.  (1) **The map is a function of the address and
the image's layout, nothing else** (`boot_mapping_for(addr, layout)`):
`[0, GUARANTEED_RAM_TOP)` — the 1 GiB every Raspberry Pi 5 has — is Normal, the
device window Device, everything else unmapped.  The driven BP0.4 test requires
every Normal address to be RAM in **every** variant's Lean map and the Normal
window to equal the smallest variant's RAM.  RAM above the gigabyte is BP4.6's,
mapped after the verified Lean parse (the BP4.6 paragraph below); before that
nothing past the gigabyte is Normal and cache maintenance there fails closed.  (2) **W^X at EL1**: the text `[_start, __text_end)`
is read-only and executable, the read-only data read-only and never executable,
and every writable page never executable.  The retired single Normal descriptor
was writable and PXN-clear while `SCTLR_EL1.WXN` is set — which makes a writable
page execute-never — so the first fetch after `enable_mmu` would have faulted,
invisible only because no image had run.  A new mapping picks one of
`BLOCK_KERNEL_TEXT` / `BLOCK_KERNEL_RODATA` / `BLOCK_NORMAL` by what it maps;
`no_page_is_writable_and_executable_and_the_text_executes` walks every page.
(3) **The section boundaries are `link.ld`'s, assigned inside the sections they
bound**: `lld` attaches a location-counter change written *between* sections to
the section that follows, so a boundary written there moves with the gap it
exists to detect.  `__rodata_start == __text_end` is an `ASSERT`, so no orphan
section can land between them and be mapped executable, and
`scripts/check_link_script.py` proves each boundary `ASSERT` live by mutation.
`link.ld`'s RAM region ends at `GUARANTEED_RAM_TOP`, so the linker cannot place
the image where the map does not reach.  (4) **`init_mmu` reads nothing of the
blob** (a Tier 3 negative refuses any `cmdline` call in its body).  It only
checks that `dtb_window` — `MAX_DTB_SIZE` from the pointer, the bound every
reader enforces before forming a slice — lies in guaranteed RAM and outside
`[_start, __lean_heap_end)`, and refuses otherwise; BP5.3's `config.txt` pins
the placement to `link.ld`'s `.dtb_window`.  (5) **The bootargs reader stays, in Rust, with translation on**:
it is a Rust-only question with no Lean counterpart, and the QEMU lanes use it.
So "is this structure block readable" is still two-sided, and the shared corpus
was **retargeted rather than retired**: its manifest carries a hand-written
`structure` verdict both suites drive, and its `regions` column is the Lean
parser's alone.  Retired with a Tier 3 negative each: `ram_top_from_dtb`, the
`/memory` walk, fold and contiguity machinery, `clamp_ram_top`, `boot_ram_top`,
`dtb_dereferenced_range`, `boot_ranges_mapped_under`, `boot_critical_ranges_mapped`
and the RAM-top constants.

**BP3 — the RPi5 deployment boots, proved by evaluation** (`v0.36.2`,
`SeLe4n/Platform/RPi5/Deployment.lean`, in the library root).
The deployment (`rpi5PlatformConfigFor`, over a board account) has two domains as `confinedDeploymentLabeling` declares
them. The root task sits at the lower witness `2`, with its CNode, a VSpace on
ASID 1, the notification every SPI signals, and untypeds over
`[256 MiB, 1 GiB)`. The untrusted initial thread sits at the upper witness
`0x10_0000`, with its own CNode and VSpace on ASID 2. No capability crosses the
boundary. Six things new code must respect.

(1) **The boot admits a configured VSpace root, and installs every object one
way.** `createBootObject` is `createObject` plus the ASID registration the
runtime store performs (`bootEntryAsidTable`), and both `foldObjects` and
`installBootVSpaceRoot` are it. The retired `noVSpaceRootsInInitialObjects`
refused every configured root because the builder omitted that write — a refusal
standing in for a missing write. Its replacement at the same cascade position is
`bootVSpaceAsidsDistinct`, since a registration is an insert. A new boot install
path goes through `createBootObject`.

(2) **A configured root is a thread's, never the kernel's.**
`bootSafeObjectCheck`'s `.vspaceRoot` arm is `bootSafeUserVSpaceRootCheck`: a
user ASID and **no mappings**, because a configured mapping would name physical
memory no boot check places. The binding's root keeps `bootSafeVSpaceRootCheck`,
and `bootSafeObjectCheck_refuses_rpi5BootVSpaceRoot` pins that the two cannot
stand in for each other. A later cut that maps a root task image widens the user
check with a placement check for its frames, never by reusing the kernel's.

(3) **A boot untyped describes only memory it may.** `untypedPlacementRespected`
is `wellFormed`'s seventh conjunct: every untyped lies inside one declared region
of its own kind, clear of `MachineConfig.kernelReserved`, and disjoint from every
other boot untyped. It also discharges the proof bridge's `untypedRegionsDisjoint`
(`PlatformConfig.wellFormed_untypedRegionsDisjoint`). A projection path into
`wellFormed` must use the named accessors, which absorbed the new conjunct
without moving.

(4) **The reserved extent is one number in three places, held by a shared
fixture.** The three are `rpi5KernelReservedEnd`, `link.ld`'s
`KERNEL_RESERVED_END` and `mmu::KERNEL_RESERVED_END`. The Lean suite writes the
value into `tests/fixtures/boot_map.expected`, and the HAL test and
`scripts/check_link_script.py` read it back. The image must end inside the
extent, which a live-by-mutation `ASSERT` checks. The device-tree window must too
(`dtb_window_admissible`), so no untyped can describe the blob. Growing the image
past 256 MiB means moving all three together.

(5) **A concrete configuration's gates are decided, never asserted.** The boot's
duplicate checks run an opaque hash set, so `irqsUnique_eq_transparent` and
`objectIdsUnique_eq_transparent` rewrite them to the transparent forms, and
everything after that is `decide`. No `native_decide` anywhere.
`bootFromPlatformChecked_ok_objects_of_mem` — every configured object is in a
successful boot's state, at its own id — is how a deployment's threads are read
off the configuration rather than evaluated out of the boot. `BaseIO` has no
`LawfulMonad` instance in this toolchain, so an IO equation closes by `rfl`
(`bootAndInitialiseRPi5OrHalt_rpi5PlatformConfigFor`), not by rewriting.

(6) **The state the hardware boot installs satisfies the proof-layer bundle,
and there is one argument for it** (BP3.5).
`bootFromPlatformCheckedWithIdleThreadsFor_proofLayerInvariantBundle` covers the
checked, idle-enqueued boot of every configuration the checked boot accepts,
`bootToRuntime_invariantBridge_checked` adds the freeze, and
`rpi5DeploymentBootStateAt_invariantBridge` is the deployment's instance. Both
boots, checked and unchecked, are instances of
`proofLayerInvariantBundle_of_bootShape`: every object is `bootObjectShape`,
the quiescent fields are defaults, the ASID table is consistent, and the
scheduler supplies its run-queue facts. A new boot install step must keep all
four, or say which it breaks. And **a runtime check must decide every clause
the Prop-level predicate states**: `bootSafeCnodeCheck` looked at a CNode's
shape and not at its slots, so a reply capability or an out-of-range badge
booted, and the soundness bridge was partial under a docstring saying the
clauses were checked elsewhere. `bootSafeCapCheck` refuses both, and
`bootSafeObjectCheck_sound` concludes all of `bootSafeObject`.

**BP4.1/BP4.2 — the entry exists, and the install precedes the secondaries by a
type** (`v0.36.2`).  Four things new code must respect.  (1) **The hardware boot
entry is `SeLe4n.Platform.RPi5.kernelMain`** (`SeLe4n/Platform/RPi5/KernelMain.lean`,
in the library root): `@[export lean_kernel_main]`, exactly
`Platform.FFI.bootAndInitialiseRPi5FromDtbOrHalt dtb rpi5IrqTable rpi5InitialObjectsFor none`
since BP4.4 (the item after this block), and `kernelMain_installs` states the
program it is.  `BootEntryContract.lean` now
**refuses** an environment with no entry, so a second one, a moved one or a
deleted one fails Tier 1.  (2) **`EXPECTED_UNRESOLVED` is empty**: every HAL
`extern "C"` declaration is a requirement both archives must meet, and a seam
declared before its provider goes there with its reason.  (3) **Releasing a
secondary consumes a `lean_entry::SecondaryReleasePermit`**, which
`smp::bring_up_secondaries_inner` — the one function every bring-up path reaches
— takes by value.  On an image that links the kernel (`hw_target`) the only
permit is what `enter_lean_kernel` returns after the install;
`SecondaryReleasePermit::no_lean_kernel` exists only without `hw_target` (and in
tests).  So `rust_boot_main` installs in Phase 5, releases in Phase 6 and refuses
a PE-topology mismatch in Phase 7, and a reordering that releases first does not
compile.  (4) **The install is the eighth committing seam, recorded unbracketed**
in `ExportCommitDisciplineCensus` with that ordering as its reason, and the
reachability census's pin shrank by the nineteen boot-path transformers it now
reaches.  A new step the boot entry reaches is therefore *live*, not pinned.
(5) **A Lean function crossing the C boundary returns its VALUE, and each side
must declare exactly the C the Lean compiler generated.**  Lean 4.28 passes no
world argument and wraps no `IO` result: a `BaseIO Unit` export returns
`lean_box(0)`, a `BaseIO UInt64` one a `uint64_t`, and only a module
**initializer** (`initialize_*`) returns an `IO` result constructor.  So a HAL
declaration of a `BaseIO Unit` export returns `lean_runtime::LeanBaseIoUnit`
and its caller hands it to `lean_runtime::discharge_base_io`, which accepts
`lean_box(0)` and halts on anything else; the initializer's is
`lean_runtime::LeanIoResult`, classified by `consume_io_result`.  Both wrappers
are `#[must_use]` and `#[repr(transparent)]`.  In the other direction, a HAL
**definition** of an `@[extern]` binding returns what the generated C declares
— a `BaseIO Unit` binding is `lean_object* f(…)`, so it returns
`lean_runtime::base_io_unit()`: a definition returning nothing leaves whatever
was in `x0` to be read as an object reference.  **The linker checks names,
never types**, so `check_kernel_entry_exports.py` holds every HAL foreign
declaration of a Lean-generated symbol **and** every HAL definition the
generated C calls to the prototype the Lean compiler wrote under
`.lake/build/ir`, and `ExportCommitDisciplineCensus` proves every `@[export]`
returns `Unit` or a C scalar — which is what makes "a boxed export result is
`lean_box(0)`" sound.  (BP4.1 first read the export results as `IO`
constructors, so the discharge refused `lean_box(0)` and the first tick on a
ready core would have halted it; and thirty-three HAL bindings returned
nothing.  The post-BP4.5 ABI audit fixed both.)

**BP4.3/BP4.4 — the device tree reaches Lean, and the entry boots on it**
(`v0.36.2`).  Four things new code must respect.  (1) **The entry takes the
firmware's blob, not its pointer**: `kernelMain (dtb : ByteArray)` is
`bootAndInitialiseRPi5FromDtbOrHalt dtb rpi5IrqTable rpi5InitialObjectsFor none`,
and `BootEntryContract.lean`'s `approvedBootCall` is that wrapper, with the
blob required to be the entry's **own parameter** — a fixed blob, an edited
copy, and the retired `bootAndInitialiseRPi5OrHalt` call are refused witnesses.
(2) **The HAL copies, and does not decide**: `lean_entry::enter_lean_kernel`
reads the blob through `cmdline::dtb_blob_from_ptr` inside the window `init_mmu`
admitted and copies it onto the kernel's Lean heap
(`lean_runtime::array::byte_array_of`); a pointer that yields no blob is handed
over as the **empty** array, which the verified parser refuses
(`kernelMain_refuses`), so whether this board may boot has one owner.  (3) **The
deployment is proved on every board, not one**: `rpi5PlatformConfigFor board`
and `rpi5BoundPlatformConfigAt v` replace the smallest-board
`rpi5PlatformConfig` (retired, with a Tier 3 negative), every gate is decided on
each of the five variants, and `bootAndInitialiseRPi5_rpi5PlatformConfigFor`
holds for every account because `rpi5VariantFor` always names a member.  A
deployment change that breaks the boot on any variant fails to elaborate.  (4)
**What the bridge accepts is the deployment**:
`rpi5PlatformConfigFromDtb_ok_eq_fromDeviceTree` says an accepted result is the
parsed tree's account around the caller's half, so `kernelMain_installs` names
the state it installs — the variant the device tree selected — without
re-running the parse, and `tests/Ak9PlatformSuite.lean` runs that decision on
1, 2, 3, 4 and 8 GiB boards.

**BP4.5 — the boot image is cleaned to the Point of Unification before any
thread can fetch** (`v0.36.2`, closing SM7.D's deferred item 4).  Four things
new code must respect.  (1) **Both kernel code-write sites emit**:
`kernelCodeWriteEmitted .bootImageLoad` is `true`, and
`kernelCodeWriteSites_all_emitted` replaces `kernelCodeWriteSites_emission_pending`
(retired, with a Tier 3 negative), so a site added to `KernelCodeWriteSite`
must emit or the `decide` fails.  (2) **The extent is the image's loaded
bytes**, `link.ld`'s `[_start, __image_load_end)` — text, read-only data and
initialised data, the only memory the boot makes present that a thread could be
handed as code.  Everything else it writes (the Lean heap, `.bss`, the stacks,
the boot tables) is in `MachineConfig.kernelReserved`, which no boot untyped
describes and no boot VSpace maps, and memory a thread receives otherwise comes
through a re-type, which cleans it itself.  `__image_load_end` sits between
`__rodata_end` and `__bss_start` by a live-by-mutation `ASSERT`.  (3) **The
operand is the model's**: `cache::boot_image_icache_operand` is
`CleanRangeIallu` over that extent — op tag 3, `Architecture.bootImageIcacheOp`,
which `bootImageIcacheOp_discharges_obligation` proves discharges the
obligation and which a bare `IC IALLUIS` would not.  (4) **The permit certifies
it**: `lean_entry::enter_lean_kernel` runs `cache::clean_boot_image_to_pou`
after the install and immediately before it mints the `SecondaryReleasePermit`,
so no secondary is released, and the boot core reaches no scheduling point,
before the clean; a Tier 3 anchor holds the order, and a clean moved after the
permit or commented out fails it.  Observing the clean on hardware is BP8.1's.

**BP4.6 — the verified board's RAM above the guaranteed gigabyte is mapped,
and the boot map is sealed before a secondary exists** (`v0.36.2`).  Five things
new code must respect.  (1) **Lean decides the extent, and derives it**: the
device-tree wrapper's accepting arm runs `extendBootRamMap
(rpi5BootRamExtensionsFor config.machineConfig)` before the install, and
`bootRamExtensionsOf` is every RAM region of the *bound* variant's map above
`rpi5GuaranteedRamTop`, clipped to it — `mem_bootRamExtensionsOf` and
`bootRamExtensionsOf_covers` prove it is exactly that RAM in both directions, so
the RAM the HAL maps and the RAM the installed state's machine configuration
declares are one variant's.  A new variant changes its memory map, never a list.
(2) **The HAL writes only invalid entries, and decides every refusal first**:
`mmu::extend_boot_tables` is two passes over one per-gigabyte walk — validate,
then write — so a refused range (`RamExtensionRefusal`) leaves the tables
byte-identical; it writes 1 GiB level-1 blocks, and 2 MiB blocks in the device
window's gigabyte (the only one with a level-2 table), all Normal, writable and
never executable.  Never rewriting a valid descriptor is what makes the change
safe with no break-before-make and no TLB invalidation (a faulting translation
is never cached); the table extent is cleaned to the PoC, as `enable_mmu` does, so a
secondary enabling translation with its cache off reads it, then one `DSB ISH` + `ISB`; a partial gigabyte outside
the device window is refused rather than given a table.  (3) **The cacheable
window moves with the tables, by one call**: `extend_boot_ram_map` records each
region after the barrier and `is_boot_cacheable_range` is the union
`ram_range_covered` over guaranteed RAM and the record — no longer a `const fn`.
(4) **The boot map is sealed before the permit**: `enter_lean_kernel` calls
`mmu::seal_boot_map` immediately before it mints the `SecondaryReleasePermit`,
and every later extension is refused `Sealed`, so the tables have one writer;
a refusal of any kind halts the system (`ffi_extend_boot_ram_map` →
`gic::halt_all`).  (5) **It is driven, not mirrored**:
`tests/fixtures/boot_map.expected` carries each variant's `extend` lines, and the
HAL test applies them and requires the extended Normal window to be **exactly**
that variant's RAM on every variant.  What BP4.6 does *not* do is hand the RAM to
anyone; that is BP4.7's (the paragraph below).

**BP4.7 — the RAM the boot maps is the RAM the root task owns** (`v0.36.2`).
Four things new code must respect.  (1) **A deployment's objects are a function
of the variant**: `rpi5PlatformConfigFromDtb` and the device-tree wrapper take
`initialObjectsFor : BCM2712Config → List ObjectEntry` and apply it to
`rpi5VariantFor dt.machineConfig`, the variant the board check just read, and
the RPi5 deployment's is `rpi5InitialObjectsFor v`; a caller whose objects do
not depend on the board passes a constant function.  The variant-independent
`rpi5InitialObjects` and `rpi5RootTaskCNode` are retired, with a Tier 3
negative.  (2) **The untypeds are derived from the extensions, never listed**:
`rpi5RootTaskRamUntypeds v` is one normal-memory untyped per
`rpi5BootRamExtensions v` entry, at id `8 + i` and root-CNode slot `7 + i`, and
`rpi5RootTaskRamUntypeds_regions` states its regions **are** the RAM BP4.6 maps.
(3) **The boot bounds a CNode's slot count, not its indices**, so
`rpi5RootTaskCNodeFor_slotsAddressable` decides per variant that every root-CNode
slot is below sixteen; nine extensions fit, and a variant needing more must
widen the root CNode's radix.  (4) **The coverage is the direction the placement
conjunct cannot state**: `untypedPlacementRespected` bounds the untypeds from
above, and `rpi5InitialObjectsFor_covers_ram` says every RAM address outside the
kernel's reserved extent lies in some root-task untyped, on every board, with
`rpi5DeploymentBootStateAt_ramUntypedInstalled` that the boot installs each.
`BootEntryContract.lean`'s `approvedBootCall` did not move; the object function
is data like the rest of the wrapper's arguments.

**BP5.1 — the kernel is one bare-metal binary, and it is checked as an image**
(`v0.36.2`).  Four things new code must respect.  (1) **`sele4n-kernel` is the
tree's only final binary** (`rust/sele4n-hal/src/bin/sele4n_kernel.rs`,
`no_std` / `no_main`), so image-wide decisions live there and nowhere else.  It
requires the `kernel_image` feature, and the HAL's build script passes
`-T link.ld` to that binary's link alone and only when `target_os = "none"`.
A new binary target gets its own `[[bin]]`, since declaring one disables
auto-discovery.  (2) **A panic halts the system**: the `#[panic_handler]` is
`gic::halt_all`, not the per-PE `cpu::fatal_halt`, and prints nothing because
the UART writer takes a lock the panicking core may hold.  A Tier 3 anchor pins
that body.  (3) **The image is checked as an image**, not as objects:
`scripts/check_kernel_image.py` (the cross lane's step [7/7], required by
`check_aarch64_cross_target.py`) refuses an entry other than `_start` at
`link.ld`'s `ORIGIN`, any undefined symbol (weak ones too, which a static link
resolves to `0`), and any allocated section `link.ld` does not name or places
out of order.  It also refuses a `NOLOAD` section with file bytes and a loaded
section outside `[_start, __image_load_end)`.  The allowed sections are derived
from `link.ld` itself, so an orphan placed by the linker fails the lane.  The
FP/SIMD gate reads the linked image too.  (4) **The cross lane's image is the
HAL half**: it builds without `hw_target`, because with it `build.rs` links the
Lean archive, which that lane does not build; that image boots the Rust half
(`SecondaryReleasePermit::no_lean_kernel`).  The cross clippy lane builds with
`hw_target,kernel_image --lib --bins`, so the panic handler — compiled for the
bare-metal target only — is linted.

**BP5.2 — the image carries the Lean kernel, linked from the roots the proof is
about** (`v0.36.2`).  Four things new code must respect.  (1) **One roots file,
two links**: `scripts/build_lean_aarch64_archive.py` writes
`libsele4n.roots.ld` beside the archive — `EXTERN(...)` naming the library
initializer, then every production `@[export]` — and both its reachable link
and the image's link read that file, so the runtime-surface proof and the image
cannot be taken over different root sets.  A new kernel entry is a new
`@[export]`, and it reaches both links by construction.  (2) **`build.rs` links
it under `hw_target` on a bare-metal target only**, with `--gc-sections`, by
path: a missing archive or roots file stops the link naming the file, never a
kernel linked without its Lean half.  The three paths are constants the
builder's self-test holds equal to its own `OUT_DIR`, `ARCHIVE` and
`ROOTS_SCRIPT`.  (3) **The Lean archive lane owns the kernel image**: step
[4/4] of `scripts/test_lean_aarch64_archive.sh` removes the stale image,
builds it release with `hw_target,kernel_image` after the archive, runs
`check_kernel_image.py --lean-kernel` over it (the roots begin with the
initializer, name `lean_kernel_main`, and are all the image's text), then the
FP/SIMD gate — and `check_aarch64_cross_target.py` holds those four relations
(both features on one release build, after the archive build, each check after
the image build, none exempted from `set -e`).  (4) **The FP/SIMD gate is
conclusive here**: none of `compiler_builtins`' FP-using members is in the
linked image, so a change that pulls one in fails the lane.  The cross gate's
shell expander now resolves a variable whose value names another
(`ARCHIVE_DIR="${PROJECT_ROOT}/.lake/build/${CROSS_TARGET}"`) to a fixpoint;
one pass in length order left it half-substituted.

**BP5.3 — the firmware's boot files are cut from the image and checked against
it** (`v0.36.2`).  Four things new code must respect.  (1) **The device tree's
window is `link.ld`'s**: a `NOLOAD` `.dtb_window` of `DTB_WINDOW_SIZE` after the
Lean heap, with `ASSERT`s (each proved live by `check_link_script.py`) that it
is that size on a page, after `__lean_heap_end` and inside
`KERNEL_RESERVED_END` — the two conditions `mmu::dtb_window_admissible`
refuses without — and `DTB_WINDOW_SIZE` equals `cmdline::MAX_DTB_SIZE` by the
HAL's test.  A section added after `.lean_heap` goes before `.dtb_window` or
moves it, never between it and the reserved extent's end unchecked.  (2)
**`config.txt` is generated, and a key it does not set is refused**:
`scripts/rpi5_boot_files.py` writes exactly `arm_64bit`, `kernel`,
`kernel_address` (the image's entry, `_start` and `ORIGIN`),
`device_tree_address` and `device_tree_end` (the linker's window), and its
check refuses an unknown key, a repeated or missing one, and a conditional
`[...]` section, since each could move the load or the blob where the check did
not look.  A new firmware option is added to `CONFIG_KEYS` with the relation
it must hold, never by hand to the file.  (3) **`kernel8.img` has two
readings that must agree**: `llvm-objcopy -O binary` cuts it, and the check
rebuilds `[_start, __image_load_end)` from the section headers
(`check_kernel_image.Section.offset`) and requires byte identity.  (4)
**Packaging is the Lean-linked image's**: `scripts/build_rpi5_image.sh` runs
`check_kernel_image.py --lean-kernel` first, `package` always ends in `check`,
and the archive lane runs the script as step [5/5] over the image it linked,
which `check_aarch64_cross_target.py` holds (after the image build, not
exempted from `set -e`).


**The RPi5 binding is the BCM2712's address map** (`v0.36.2`, found while
scoping BP5.4).  Until then the model and the HAL both carried the **BCM2711**'s
(Raspberry Pi 4) map — UART `0xFE20_1000` at 48 MHz, GIC-400 `0xFF84_1000` /
`0xFF84_2000`, a device window `[0xFE00_0000, 0xFF85_0000)`, RAM capped at
`0xFC00_0000` — all of it DRAM on the BCM2712, and `Board.lean`'s checklist
marked every one **Validated**.  Four things new code must respect.  (1) **The
map follows `bcm2712.dtsi`**: DRAM contiguous from 0 (`[0, ramSize)`, one RAM
region per variant, one boot extension above the gigabyte), the SoC-bus window
`[0x10_7C00_0000, +64 MiB)` as the one device region (`socPeripheralBase`,
`mmu::DEVICE_WINDOW_BASE`), UART10 at `0x10_7D00_1000` clocked at 9.216 MHz,
GIC-400 at `0x10_7FFF_9000` / `0x10_7FFF_A000`; `peripheralBaseLow` is retired,
and a Tier 3 negative refuses any BCM2711 address returning as a live constant.
(2) **A driver's base is compared with the Lean one by running both**: the Lean
suite writes `mmio uart|gicd|gicc` lines into `tests/fixtures/boot_map.expected`
from `mmioRegions`, and the HAL's UART and GIC tests read them
(`mmu::lean_mmio_window`) — the literal-beside-a-comment tests those replace are
how both sides agreed on the wrong board.  (3) **The window is block aligned**,
so the boot map's device-tail L3 table is deleted and a Tier 3 negative refuses
it returning.  (4) **Cross-checked is not validated**: the constants are the
device-tree source's (`raspberrypi/linux` `rpi-6.6.y`, read 2026-09-25), and
what a real board's firmware reports is BP8.1's readback to confirm.

Plan: [`docs/planning/SMP_BOOT_PATH_PLAN.md`](docs/planning/SMP_BOOT_PATH_PLAN.md).

### WS-LC Lock datatype completion — COMPLETE (v0.34.51 → v0.34.55; closure audit v0.34.56)

The two SM2.C **datatype** residuals RR6 re-registered rather than absorbed —
`RwLockOp` had no withdrawal and `RwLockExecution` no notion of time.  Scoped
ahead of WS-RR RR7 because the fine-lock migration tracks widen `withLockSet`
footprints onto more syscall arms, and the withdrawal is what makes those
footprints unwindable.

| Phase | Status | Version | Scope (one line — detail in the canonical sources) |
|-------|--------|---------|----------------------------------------------------|
| LC1 | LANDED | v0.34.51 | The abstract withdrawal: `RwLockOp.cancel`, INV-R preservation, the liveness restatement, the CAS-retry bridge |
| LC2 | LANDED | v0.34.52 | The ticket-FIFO refinement of the withdrawal: the withdrawal word, skip-aware promotion, the capstones over live entries |
| LC3 | LANDED | v0.34.53 | The deployed withdrawal: `QueuedRwLock::cancel`, loom, miri, Tier-5, and the foreign-function surface |
| LC4 | LANDED | v0.34.54 | The two-phase-locking consumers: `cancelAll`, the revalidated refusal unwind, the `withLockSet` unwind |
| LC5 | LANDED | v0.34.55 | SM2.C-T: the timed execution and the cycle-denominated bounds; LC5.10 retired both debt rows |

**Plan**: [`docs/planning/SMP_LOCK_DATATYPE_COMPLETION_PLAN.md`](docs/planning/SMP_LOCK_DATATYPE_COMPLETION_PLAN.md)
(51 sub-tasks across LC1..LC5).

### Standing constraints and registered debt

These are *current facts about the tree*, not history — they change what new
code may assume:

- **Kernel entry is serialised by one global ticket lock** (SM5.I, v0.32.142,
  `rust/sele4n-hal/src/kernel_entry.rs`), acquired outside
  `SHOOTDOWN_ROUND_LOCK` and self-servicing pending shootdowns while spinning.
  It brackets all five state-committing entries (syscall dispatch, per-core
  timer tick, `.reschedule` SGI receiver, secondary bring-up entry, cross-core
  suspend); the primary's `lean_kernel_main` boot install remains outside, and
  needs no bracket because it runs before any secondary is released — a
  bring-up consumes the `SecondaryReleasePermit` only the install returns
  (WS-BP BP4.2; see kernel_entry.rs module docs).
  The lock-order tripwire asks **ownership**, not held-ness (PR #889 review):
  the round lock records its holder (`round_lock_held_by`, owner word
  `core + 1`, `0` free), so a core entering while *another* core's shootdown
  holds the round lock waits and self-services its acknowledgment, and only
  the holder itself re-entering halts — a held/free flag halted every innocent
  core for the length of every shootdown, in release builds.  The two
  release-surviving tripwires — this one and the VBAR alignment check — are
  pinned in `build.rs` together with the operation each protects
  (`RELEASE_SURVIVING_TRIPWIRES`), and the scanner requires the tripwire
  among the statements **dominating** every occurrence of that operation
  (`tripwire_dominates_protected_operation`, PR #889 review round 6): a
  branch that halts but is no longer reached before the acquire or the VBAR
  write is refused, and (round 7) the branch must end in `fatal_halt` itself
  (`statement_halts`) — a `return` diverges from the helper, not the core.
  The branch must be a top-level statement of the helper, or sit under a
  block that executes unconditionally on the image — a bare or `unsafe`
  block, or one under exactly `#[cfg(target_arch = "aarch64")]` (round 8,
  `tripwire_branch_halts` / `unconditional_block_interior`): an
  exact-condition `if` nested under a further condition halted only when
  that condition held, and the dominance check, which asks whether the
  *helper* is called, could not see it.  Nothing may **leave** the helper
  before that branch either (round 9, `statement_may_exit`): an
  `if <the same condition> { return; }` above it returns exactly when the
  failure condition holds, so an earlier statement carrying a `return` or a
  panicking macro refuses the tripwire.
  Live WCRT is therefore weaker
  than `PerCoreWcrt.lean`'s fine-lock bound, which remains a statement about the
  intended discipline.  **And that bound carries no number** (WS-RR RR7.31): it is
  `maxLockSetSize · (numCores − 1) · tCs`, and `tCs` — a per-object critical
  section on a Cortex-A76 — is measured nowhere in this tree, so the whole surface
  is parametric in it.  The master plan's §7.2 used to instantiate it as
  `4 × 3 × 60 µs ≈ 720 µs`, "comfortably within the 1 ms timer tick"; the first
  factor was a *typical* footprint size rather than `maxLockSetSize` (11 since
  WS-OD OD3.5, 9 since RR7.11, and 8 before that), and at 60 µs the tick admits
  **five** locks and
  refuses six.  What the tree states instead is the budget condition solved for the
  measurable factor: `admissibleCriticalSection budget` is the largest per-lock cost
  a budget admits at the declared ceiling, with
  `WCRT_lockSet_le_budget_of_admissible` the payoff and
  `rpi5Tick_refuses_sixty_micro_sections` the `decide`-checked negative.  At
  HEAD, the declared lock-set ceiling is **24**, the RPi5 tick admits **13 µs** per lock, and the uniform 60 µs envelope is **4320 µs**.
  Those three figures are **derived**, and since WS-OD OD3.15
  `scripts/check_lock_ceiling_figures.py` (Tier 0) holds every prose copy of them
  to the Lean sources: the constants and the formula that combines them are read
  out of `LockSet.lean`, `Types.lean` and `PerCoreWcrt.lean`, and every tracked
  Markdown and Lean file outside `CHANGELOG.md` and `docs/dev_history/` is scanned
  for the canonical spelling above.  Narrative may name an old value freely
  (`OD3.5 raised the ceiling to 11`); a **live** claim is written in that spelling
  or it is not checkable, and a phrase that comes close without matching is
  reported as a gate defect rather than skipped.  Five documents are pinned to
  carry the statement, so deleting the sentence is not a way to satisfy the gate.
  Four consecutive review rounds each found a stale copy the previous round's
  sweep had missed, which is what made this a mechanism rather than a correction.  New code
  must not quote a numeric syscall WCRT for this kernel; measuring `tCs` on the
  target is an acceptance criterion of RR7.39–RR7.41 and fine-lock Track D.
- **The syscall seam brackets; the scheduler entries do not** (WS-RR RR7.12,
  v0.34.65).  `syscallDispatchCrossCoreEntry` runs its atomic step inside the
  footprint `lockSetForSyscall` declares for the operation its own registers
  decode to — resolve, acquire, **re-resolve at the state the growing phase
  ended in**, refuse on change, unwind — via
  `syscallDispatchCrossCoreBracketedStep`
  (`SeLe4n/Kernel/SyscallLockBracket.lean` holds the mechanism).  Four things
  new code must respect.  (1) **The fallback is exactly the pre-RR7.12 seam**
  (`syscallDispatchCrossCoreBracketedStep_undeclared`, definitional), which is
  what makes bracketing safe while twenty-seven arms are still undeclared:
  falling back is always sound, claiming a footprint that does not cover a write
  never is.  (2) **The operands come from the entry's own decode**, tied by
  `abiEntryPlan_dispatches` — a footprint resolved from a decode the dispatch
  does not use is a footprint for a different operation.  (3) **A multi-level
  CSpace resolution declares nothing**: the footprint's only CNode member is the
  caller's root, a `LockSet` is capped at `maxLockSetSize` and a CSpace path is
  not, so a deeper walk selects the target through CNodes no declared lock
  covers and the resolver refuses.  (4) **A refusal returns `.illegalState` and
  commits nothing but the unwinding**
  (`syscallDispatchCrossCoreBracketedStep_refused`); it is unreachable today,
  since `modifyGetKernelState` is one global read-modify-write and the growing
  phase writes nothing the resolver reads, and a dedicated `.lockContention`
  becomes worth its ABI cost when the commit is partitioned.  The per-core scheduler path
  brackets too since **WS-RR RR7.39** (v0.34.89), which gave `SchedLockId` the
  state words it never had (`SystemState.schedulerLocks`) and made the
  revalidating bracket shared — `Concurrency.runBracketed`, of which RR7.12's
  `runUnderDeclaredLockSet` is now definitionally the object-domain instance.  So
  the timer tick, the `.reschedule` SGI receiver and the secondary bring-up entry
  run inside the footprints SM5.B–G declared for them, with the write set proved
  inside the footprint on both steps (`perCoreRescheduleStep_coversWrites`,
  `perCoreTimerTickStep_coversWrites`).  Two things new code must respect.  (1)
  **The tick's footprint names every core's run-queue write lock**, not the boot
  core's and its own: the replenish drain and the bound-exhausted timeout both
  wake via `determineTargetCore`, so the two-lock segment was a *false* footprint
  from SM5.F onward, and RR7.39 fixed it — the widening is free, because every
  tick footprint already holds the object-store *table* lock
  (`timerTickOnCoreCompleteLockSet_serialises_pairwise`), and `maxLockSetSize`
  does not move.  (2) **The scheduler domain is not fully covered**: what remains
  is the *syscall* seam's scheduler writes — an `endpointSend`'s receiver wake —
  because `lockSetForSyscall` returns a `LockSet` whose `LockId` cannot name a
  run-queue lock at all.  That was `UncoveredLockDomain.syscallSeamSchedulerDomain`,
  owner RR8, and it needed per-arm resolved wake targets rather than the free
  over-approximation.  **Closed at WS-RR RR8.12 Cut C6h (`v0.35.181`)**: the seam
  brackets on `schedulerLockBracketDomain` over one unified footprint, and its own
  stated reason — that the object-domain footprints hold `stateLevelLock` *"rather
  than the table lock"* — was **false**, the two being one word
  (`schedAcquireLock_objStore_congr`), which is why the cut unifies rather than
  nests.  Live WCRT is still the global lock's for the arms neither domain
  declares, and `PerCoreWcrt.lean` says which half acquires.
  **How much of the kernel that is, is measured rather than asserted** (RR7.13,
  v0.34.66): `SeLe4n/Testing/ExportCommitDisciplineCensus.lean` derives the
  state-committing `@[export]` set from the elaborated environment — transitive
  `getUsedConstants` reachability to a `kernelStateRef` write — and reconciles it
  against a registry in **both** directions, so an unclassified committing seam
  and a stale entry are each a build failure.  **Seven seams commit; five
  bracket** (WS-RR RR7.39 — the two syscall seams and, since it gave the
  scheduler domain a runtime, the three per-core scheduler entries; two before
  it).  A body recorded `bracketed` must reach `runUnderDeclaredLockSet` or
  `Concurrency.withLockSet`; one recorded `unbracketed` must carry a reason.  New
  code adding an `@[export]` that commits kernel state must classify it there —
  that is where the project's coverage figure is read off, and the two
  fault-delivery seams (`lean_handle_fault`, `lean_handle_unknown_syscall`) are
  recorded unbracketed because a fault is not a syscall and `lockSetForSyscall`
  declares no footprint for one.
- **SM3.C.9's `@[export]` body migration is otherwise deferred**: outside the
  syscall seam and the raw `suspend_thread_cross_core` entry, the bodies are not
  wrapped in `withLockSet`, so the per-object fine locks remain a model-level
  discipline there.  **Eight of the
  thirty-five arms are declared** since WS-RR RR7.11 (v0.34.64) — that suspend
  plus the seven IPC hot-path arms `.send`, `.receive`, `.call`, `.reply`,
  `.replyRecv`, `.notificationSignal` and `.notificationWait` — and twenty-seven
  answer `none`, which `declaredFootprintSyscall` names and
  `lockSetForSyscall_undeclared_none` enforces.  Declaring is not bracketing, and RR7.12
  (v0.34.65) closed the gap at the syscall seam: the eight declared arms now run
  inside their footprints there, the twenty-seven undeclared ones run exactly as
  before, and the per-core scheduler entries still bracket nothing.  Three things new code must respect.  (1) `.send` and `.call` answer
  `none` without a **message**: whether the footprint includes the receiver's
  CSpace root and the state-level lock is a property of what the message carries,
  so defaulting to the capless shape would declare a footprint that omits the two
  members the caps path writes.  (2) The **receive** side writes the CDT too —
  `ipcTransferSingleCap` is one function, so a receive that dequeues a
  caps-bearing sender mints a derivation node and adds an edge exactly as a send
  does; RR7.7 declared that on the two sending arms and RR7.11 on the two
  receiving ones, and `capsCarryingIpcArms_footprints_share_serialization` is the
  statement that no two of the four are ever disjoint.  (3) **`maxLockSetSize` is
  21** (PR #894's review; 16 at `v0.35.4`, 14 at OD3.13, 13 at OD3.7, 11 at OD3.5,
  9 at RR7.11, 8 before that): the widest declared
  footprint is a `.replyRecv` that returns a donation, re-donates, installs
  capabilities, was answered through a *delegated* reply capability, reads the
  two objects below its reply-stack head, names the head its pop clears and the
  old head its push rewrites, and declares the five objects the **invoking**
  receiver's own pre-receive return touches.  The WCRT headline
  `maxLockSetSize · (numCores − 1) · tCs` is
  parametric in it — `admissibleCriticalSection` reads **15 µs** off it for the
  1 ms tick, down from 20 — and a theorem named `_size_le_maxLockSetSize` must
  state the
  constant, never the numeral — five in the scheduler pinned `≤ 8` literally,
  which is why the constant now lives in `Locks/LockSet.lean` where every
  footprint-declaring module can name it.  (4) **`.replyRecv` declares for the
  recorded server too, and for the second hand-off** (WS-OD OD3.5).  PR #892
  review round 6 made the arm *refuse* a delegated reply — one answered by a
  thread other than the one the Reply records — because
  `replyRecvReturnDonation` writes that server's TCB and there was no room for
  its lock.  OD3.5 found that the same function performs a **second**
  SchedContext hand-off the footprint named nowhere:
  `applyCallDonationOnCore nextThread tid` runs whenever the receive leg dequeues
  a queued `Call`, and `donateSchedContext` writes the new caller's context —
  provably not the returned one, and the passive-server steady state rather than
  an edge case, since the receiver is `.unbound` at that point *because* the
  return just made it so.  So the arm was writing a kernel object under no
  declared lock on the tree's most-travelled IPC path, and a `.replyRecv` on one
  core and a `.tcbSuspend` of that queued caller on another had provably
  disjoint footprints while both writing it.  Both members are declared now
  (`receiveRendezvousDonatedSc?`, `recordedReplyServer?`, both threaded through
  `lockSet_endpointReplyRecvOnCore`), the delegated case declares
  (`lockSetForSyscall_replyRecv_delegated_declares`) rather than falling back to
  the coarse serialisation, and `lockSetForSyscall_replyRecv_delegated` — which
  concluded `none` — is retired.  New code must not read that refusal as live.
  The
  migration plus commit partitioning is planned in
  [`docs/planning/SMP_FINE_LOCK_MIGRATION_PLAN.md`](docs/planning/SMP_FINE_LOCK_MIGRATION_PLAN.md),
  whose High-severity revocation-precision finding is **closed** at v0.33.88
  (§3.1).  It took five cuts because the first three patched the operation that
  destroyed the slot — synthetic source (v0.33.59→60), delete guard
  (v0.33.62), CNode retype and the revoke sweep (v0.33.64) — and the set of
  slot-destroying operations is open-ended.  The guarantee sits in two halves,
  neither implying the other: the single creator of an `.ipcTransfer` edge
  declines (`CapTransferResult.sourceRevoked`) when the **source** node has no
  live slot, which holds against destroyers not yet written; and revocation
  consumes the derivations still parked in senders' `pendingMessage`
  (`revokePendingTransfersFrom`, v0.33.88), because revoking a derived subtree
  leaves the source slot live and so never trips the creator's check.  New code
  must not assume a carried `TransferCap` will install.
- **A footprint's same-kind core segment is `schedCoreSegment`, over a core
  *set*** (WS-RR RR8.12, `v0.35.87`).  A cross-domain footprint that names
  several cores' run queues or replenish queues declares them through
  `schedCoreSegment (f : CoreId → SchedLockId) (cs : List CoreId)`
  (`Scheduler/Operations/PerCoreChooseThread.lean`), whose canonical form is
  `Concurrency.canonicalCores` — `allCores.filter (· ∈ cs)`, so ascending,
  duplicate-free and bounded by `numCores` because `allCores` is.  Three things
  new code must respect.  (1) **The arity is an argument, not a definition.**
  `sortedSchedCorePair` and `sortedSchedCoreTriple` were this question at two
  arities and are **deleted**, with a Tier 3 negative refusing each tree-wide;
  a footprint needing four cores passes a four-element list, and a footprint
  resolved from a *walk* passes whatever the walk found
  (`pipChainSchedFootprint` does).  (2) **A hand-inlined `if`-chain over two
  cores is the same defect**: `cancelDonatedDonationOnCoreSchedLockSet` carried
  one for eleven cuts, forty lines below a comment asserting the shared
  definition was used everywhere below it, and its uniqueness and ordering
  proofs were 30 and 35 lines of branch analysis for a fact the shared lemmas
  state once.  (3) **`allCores`'s ordering is `allCores_pairwise_le`, never a
  `decide`**: a `decide` at the literal `numCores` stops reducing the moment a
  multi-platform build parameterises it by `PlatformBinding.coreCount`, which is
  what `allCores_nodup`'s own docstring says and what one chain-footprint proof
  had done anyway.

- **...and a whole operation's footprint is `schedFootprintOfCores`, over two
  core sets** (WS-RR RR8.12 sixth cut, `v0.35.94`).  The segment above is one
  kind; a footprint of a whole kernel operation is the three-domain ladder
  `(object, .write) :: runSegment ++ replenishSegment`, and that was spelled at
  **seven** definitions with **four** byte-identical twenty-five-line
  `_pairwise_le` proofs — one question with four answers, about to become nine
  as the remaining syscall arms are declared.  `schedFootprintOfCores (runCores
  replenishCores : List CoreId)` is the one answer, with `_pairwise_le`,
  `_write_only`, `_keys_nodup`, `_length_le`, `_subset` and the single
  characterisation `mem_schedFootprintOfCores_iff` its consumers read instead of
  each running the same three-way case analysis.  Four things new code must
  respect.  (1) **The criterion is the *shape of the argument*, not a list of
  names**: a footprint whose cores form a set — two or more of a kind, an
  `Option` joined with another, a segment resolved from a walk — is this
  constructor; one at a fixed single core of each kind
  (`wakeThreadLockSet`, `descheduleThreadLockSet`,
  `cancelBoundDonationOnCoreSchedLockSet`) is a literal, because there is
  nothing to sort and nothing to merge and its ladder is a two-element `simp`.
  A literal that gains a second core of a kind becomes this constructor in the
  same cut.  (2) **"The argument is a set" is a theorem, not a claim**:
  `Concurrency.canonicalCores_congr` and `schedFootprintOfCores_congr` say two
  resolvers that discover the same cores declare the same footprint, and
  `canonicalCores_singleton` is the `Option CoreId` arm.  That is what retired
  `cancelIpcBlockingOnCoreSchedLockSet`'s hand-written deduplication — `if
  placed = some c then … else … ++ [(runQueue ⟨c⟩, .write)]`, a question about a
  set answered by an `if`-chain over its two possible elements, which is item
  (2) above one level up and which RR8.12's first cut did not sweep onto its own
  sibling.  With the branch gone,
  `cancelIpcBlockingOnCoreSchedLockSet_contains_wake_runQueue_write`
  (`…_contains_holder_runQueue_write` since `v0.35.158`) is
  **unconditional**, where it used to need `placed ≠ some c`.  (3) **A composite
  covers a component by `schedFootprintOfCores_subset`**, not by a second
  member-by-member case analysis; over-declaring is the safe direction and the
  lemma is stated that way round.  (4) **`Scheduler/PriorityInheritance/
  ChainFootprint.lean` is deliberately not this shape**: its object segment is a
  *per-thread* TCB lock per chain member rather than the single table lock, so
  its ladder is a different proposition and it keeps its own — which is why the
  Tier 3 negative that refuses a re-inlined `runQueue_lt_replenishQueue` is
  scoped to `SeLe4n/Kernel/IPC/` and `SeLe4n/Kernel/Lifecycle/` rather than
  tree-wide.

- **...and the first three syscall arms declare one** (WS-RR RR8.12 seventh cut,
  `v0.35.95`).  `UncoveredLockDomain.syscallSeamSchedulerDomain` recorded that
  `lockSetForSyscall` returns a `LockSet` whose `LockId` cannot name a run-queue
  lock at all, so an `endpointSend`'s receiver wake was outside the footprint the
  RR7.12 seam acquired (that entry is retired at Cut C6h, `v0.35.181`).  `.notificationSignal` (through the **bound** arm the
  live dispatch routes to), `.notificationWait` and `.send` now have one —
  `schedLockSet_notificationSignalBoundOnCore`,
  `schedLockSet_notificationSignalOnCore`,
  `schedLockSet_notificationWaitOnCore`, `schedLockSet_endpointSendOnCore`, all
  **inert** until the bracket cut.  Four things new code must respect.  (1) **A
  footprint is `schedFootprintOfCores` of the arm's SM8.B write set**, never of a
  second resolution of the same cores: `notificationSignalOnCore_confinedToCores`
  is *stated at* `notificationSignalWriteSet` and the footprint is that list, so a
  footprint and a confinement claim naming different cores is unstateable rather
  than merely refuted.  (2) **The write sets moved to production for that
  reason.**  `notificationSignalWriteSet`, `notificationSignalBoundWriteSet` and
  `endpointSendWriteSet` were declared in
  `InformationFlow/NonInterferenceCrossCore.lean`, which is staged and imports
  `Kernel.API`, so the production footprint could not read them; they now sit
  beside the transitions they describe and the confinement theorems that consume
  them stay staged.  `wakeThread_replenishQueueOnCore` moved the same way, out of
  the staged `PerCoreCbs.lean` where its `_local` suffix was the signal.  (3) **An
  empty replenish segment is a theorem, not a reading of the body**: these three
  arms move no scheduling context — only `.call`, `.receive` and `.replyRecv`
  donate — and `notificationSignalOnCore_replenishQueueOnCore`,
  `notificationWaitOnCore_replenishQueueOnCore`,
  `notificationSignalBoundOnCore_replenishQueueOnCore` and
  `endpointSendCrossCoreDispatchChecked_replenishQueueOnCore` say so, because a
  footprint that omits a written lock is false and `observableSlotsConfinedToCores`
  covers six per-core slots of which the replenish queue is **not** one.  (4)
  **`.receive` and `.replyRecv` are deliberately still undeclared at this cut**:
  both donate, so their replenish segments are non-empty and their cores come from
  the migration rather than from a confinement write set, and `.receive`'s chain
  leg is not pre-state computable at all (`receiveRendezvousHandoffWriteSet` takes
  the post-donation state) — those cores are declared through the dynamic chain
  extension, as the object domain declares them.  `.receive` is declared at Cut
  8a-ii (`v0.35.107`, the bullet below), `.replyRecv` at Cut C2 (`v0.35.162`, the bullet after that), `.call` and `.reply` at Cut C3a (`v0.35.163`, the bullet after those), and the three TCB-control arms at Cut C3b-i (`v0.35.167`, the bullet after that).  **And that sentence named two arms where the
  derivation gives many more** (`v0.35.104`, found by running the sweep on this
  note rather than by a review): four arms declare a scheduler footprint and the
  staged non-interference module holds **24** per-core write sets, so `.call`,
  `.tcbSuspend`, `.tcbResume`, the three SchedContext arms, `.tcbSetPriority`,
  `.tcbSetAffinity` and the retype are undeclared too and were in neither list.
  *A recognised set is not a derived set*, in the note written one cut earlier to
  record which arms remain — read the `schedLockSet_` inventory and
  `schedLockSetForSyscall`'s own `match`, never this paragraph, for what is left.
  (`UncoveredLockDomain.syscallSeamSchedulerDomain` was the register entry until
  Cut C6h retired it; the inventory is the derivation that outlives it.)

- **...and the first DONATING arm declares one, so the first with a non-empty
  replenish segment** (WS-RR RR8.12 Cut 8a-ii, `v0.35.107`).
  `schedLockSet_endpointReceiveOnCore` is the live `.receive` arm's
  scheduler-domain footprint — the object-store table write lock, the run-queue
  write lock of the one core the receive leg moves, and the replenish-queue write
  locks of the two endpoints WS-OD OD3.6's donation migrates between — **inert**
  until the bracket cut.  Seven things new code must respect.  (1) **Every core is
  DERIVED; nothing is a parameter — and the first shape of this cut got that
  wrong.**  The run segment is `schedFootprintOfCores` of the arm's SM8.B write
  set, as Cut 7 requires.  The replenish segment has no write set to take —
  `observableSlotsConfinedToCores` does not read the replenish queue at all — and
  the first shape therefore took the donation's two cores as **parameters**, on the
  reasoning that `applyRendezvousCallDonation` resolves them at the *post*-receive-leg
  state, so a pre-state reading would answer the question at a state the migration
  does not run at.  Three things were wrong with that.  It breaks this file's own
  rule that **a parameter is a place for a caller to be wrong** (PR #895 round 10:
  the fix is not a better argument but *no* argument), since a caller could declare
  locks for a migration between two cores the transition never touches.  A bracket
  resolves a footprint **before** the transition runs, so Cut 9 could not have
  supplied them at all and the form would have had to be rewritten anyway.  And it
  left three frames Cut 8a had promoted *for this footprint* with no consumer, which
  is the measurement that said so: a frame nobody asks for is a question nobody
  asked.  The replenish segment is `endpointReceiveHandoffReplenishCores`, read on
  the **pre**-state, licensed by
  `endpointReceiveDualWithCapsOnCore_determineTargetCore_eq_of_rendezvous` — *the
  receive leg moves no thread's home core*, because `determineTargetCore` reads
  `cpuAffinity` and only `.tcbSetAffinity` writes it — and
  `endpointReceiveHandoffReplenishCores_of_donating_call_rendezvous` (the
  `_of_call_rendezvous` of this cut, re-keyed at Cut C1) states that the pre-state
  list **equals** the pair the donation resolves, not that it agrees with or
  over-approximates it.  So this *closes*, for `.receive`, the
  footprint/transition resolution asymmetry WS-HP HP10.8 registered for the reply
  arm's origin member rather than adding a second instance of it.  A Tier 3 positive
  pins both segments in one anchor, a second pins the equality, and a negative
  refuses the parameter names coming back; each is mutation-tested by keeping every
  other token.  (2) **The declaration is TRUE by theorem, not by reading the body**:
  `schedLockSet_endpointReceiveOnCore_covers_donation` covers
  `applyCallDonationOnCoreSchedLockSet` member for member, hence — through
  `applyCallDonationOnCoreSchedLockSet_covers_migration` — the SM5.H migration's
  two slots; and in the other direction
  `endpointReceiveDualOnCore_replenishQueueOnCore_of_rendezvous` and its WithCaps
  sibling say the receive **leg** writes no replenish queue on a rendezvous, so
  every core in that segment comes from the donation and none from the leg.  On
  the block path the segment is `[]` for a receiver holding no loan
  (`schedLockSet_endpointReceiveOnCore_no_replenishQueue_of_blocked`, conditioned
  on `endpointReplyDonation?` answering `none` since `v0.35.161`): a receive that
  parks itself donates nothing, and over-declaring is not free — lock contention
  is an observable channel (SM8.D's CC-5), which is why OD3.5 *narrowed* a
  footprint for the same reason.  A receiver that parks holding a **loan** is the
  other case, and until `v0.35.161` it was wrong on both sides: the block arm's
  pre-receive return rebound the context to its owner across cores and migrated
  nothing, and the whole-leg frame that pinned *the leg writes no replenish queue
  on either path* was true only because the transition omitted the write.  The arm
  runs `cleanupPreReceiveDonationMigrated` now, the segment names the receiver's
  home and the owner's through `receivePreReturn?`
  (`endpointReceiveHandoffReplenishCores_of_blocked_returning`, with
  `…_eq_migration` the licence that the pre-state pair **is** the migration's),
  and the whole-leg frame is retired for per-path ones — see the standing
  constraint on the pre-receive return below.  (3) **The chain walk is declared
  dynamically, not statically.**  The arm also runs `applyReceiverPipHandoff`,
  whose cores are state-discovered; `PriorityInheritance.pipChainSchedFootprint`
  declares them per walked member and `pipChainStart_endpointReceive` is the SM3.C
  obligation that ties the walk to it.  A static footprint that tried to
  enumerate them would be a footprint over an unbounded set.  (4) **Two more
  production relocations, for the reason `v0.35.59` states.**
  `endpointReceiveDualWriteSet` and
  `endpointReceiveDualWithCapsOnCore_scheduler_eq` were declared in the staged
  `InformationFlow/NonInterferenceCrossCore.lean`, which imports `Kernel.API`, so
  the production footprint and its replenish frame could not read them; a frame
  lemma about a production transition belongs beside that transition, not in the
  staged surface that first happened to need it.  Both are refused there by a
  Tier 3 negative.  Two more of the same class surfaced from the **build** rather
  than from reading, and both are the shape `v0.35.59` names — *when a question has
  one owner and an asker that cannot see it, the owner is in the wrong layer*:
  `storeTcbIpcStateAndMessage_determineTargetCore_eq` is a frame over an IPC
  *primitive* and sat in a cross-core *arm* module the receive leg's own frame does
  not import, while `endpointReceiveDualOnCore_preserves_objects_invExt` is a frame
  over a transition and sat **downstream** of the module that declares it.  Four
  relocations in one cut is the signal that the class is a layering convention, not
  four accidents.  (5) **The frames the licence needed, and where they live.**  The
  `*_determineTargetCore_eq` family gained `linkCallerReply_…` (a Reply store then
  a TCB store, `cpuAffinity`-`rfl` on both) and `ipcUnwrapCaps_…` (whose own TCB
  frame holds at every key in *both* directions, so the whole `getTcb?` projection
  is fixed — strictly stronger than the affinity the licence needs, which is why no
  per-field argument appears in it).  Both sit in the family's home module, not
  beside their operations, because that is where every other member lives.  The
  composite is stated on the **rendezvous** branch, and that is the claim's own
  subject rather than an economy: the segment is `[]` on the block path, so there is
  no core there for a pre-state reading to get wrong.  (6) **The one missing frame is a corollary, not a second case
  analysis**: `cleanupPreReceiveDonationChecked_scheduler_eq` goes through
  `cleanupPreReceiveDonationChecked_ok_eq_cleanup`, the bridge that already
  settles that the checked and defensive variants agree on `.ok` — re-deriving it
  from the checked body would let the two disagree about a branch.  And the
  layering worry that deferred this cut was unfounded: `IPC.Invariant.Defs` *is*
  reachable from `IPC/CrossCore/EndpointReply.lean`, through
  `Scheduler.Operations.PerCoreWake → IPC.Invariant.PerCore`; the grep that
  suggested otherwise measured which cross-core module happens to cite those
  frames, not which can.  (7) **The scheduler-footprint family has no census, and
  the measurement is what says so.**  A footprint's `_write_only` / `_pairwise_le`
  are `schedFootprintOfCores`' own lemmas at that footprint's arguments, so
  restating them per footprint is a delegation with no content — Cut 7's four arms
  omit them and this one does too, with the reason stated where a reader looks for
  them.  What is **not** a delegation is a run-segment coverage lemma, and asking
  the whole family who consumes those found **33 of its 47 theorems with neither a
  consumer nor a Tier 3 anchor** — every RR2.4 / RR2.10 / RR8.12 footprint property,
  silently deletable.  Their consumer is the bracket cut, which is the ordering the
  numbering rule requires, so the answer is not to delete them; it is that the
  scheduler domain has no `LockFootprintBoundCensus`, which the object domain has
  had since RR7.18 for exactly this reason.  Deriving one is Cut 8c; the eight hand
  anchors this cut adds are the stopgap, and a hand-written list is what that census
  retires.

- **`ipcInvariantFull` has its dispatch payoff, under stated packs and
  confinements** (WS-RR RR3.15–RR3.26, `v0.34.43`; compressed here at RR8.14,
  `v0.35.88`).  The bundle family is de-threaded end to end and
  `scripts/check_ipc_invariant_dethreading.py` (Tier 0) keeps it so, holding the
  family size stated in prose to its own measurement — the figure and the
  narrative of how it drifted live in `docs/spec/SELE4N_SPEC.md` and
  `CHANGELOG.md`, not here.  Four things new code must respect.  (1) **Cite the
  right tier.**  `dispatchCapabilityOnly_preserves_ipcInvariantFull`
  (`SeLe4n/Kernel/API.lean`) is **production** and covers every capability-gated
  arm; `dispatchWithCap_preserves_ipcInvariantFull`,
  `dispatchSyscall_preserves_ipcInvariantFull` and their two `…Checked` twins
  (`SeLe4n/Kernel/IPC/Invariant/DispatchPayoff.lean`) are **staged**, because the
  `.call` arm composes the staged `EndpointCallInvariant` surface, and production
  code must not cite them; they relocate when that surface promotes.  (2) **The
  payoff holds *under the packs***: every field of
  `capabilityDispatchQuiescence` / `syscallDispatchQuiescence` /
  `checkedSyscallDispatchQuiescence` is a pre-state fact, with the state-shaped
  ones collected as `ipcReachable`
  (`SeLe4n/Kernel/IPC/Invariant/Reachability.lean`, boot-inhabited by
  `ipcReachable_default`), so a caller supplies the pack rather than citing the
  theorem bare.  (3) **The packs are inhabited, per arm** — an unsatisfiable
  field cannot hide behind a vacuous witness (`DispatchPayoff` §7b); the two
  interiors beyond the retype and binding levers' reach are registered debt.
  (4) **The confinements are stated, not implied**: `.notificationSignal` is
  covered on the unbound-delivery path only, the `.replyRecv` composite excludes
  a live donation edge naming the woken caller, and the retype and suspend arms
  demand `retypeTargetDetached` / `threadIpcFieldsQuiescent` — revoke, suspend,
  cancel and (`tcbNotBound`, since `v0.35.164`) unbind *before* retype or
  suspend; the arm the retype's cleanup runs is what makes a violation of the
  last one safe rather than what the pack rules out.
- **A cancelled caller gets its donated SchedContext back** (WS-RR RR7.22
  residual remediation, v0.34.97).  `cancelIpcBlocking`'s `.blockedOnReply` arm
  is `consumeReplyLink (restoreToReadyCancelled (spliceThreadReplyFrameOut
  (returnDonationToCancelledCaller st tid tcb) tcb) tid) tid tcb` — seL4-MCS's
  `reply_remove` (the splice joined the chain at `v0.35.4`; this sentence
  omitted it for fifty-nine cuts).  Before it, the server
  kept `.donated scId caller` while the caller left `.blockedOnReply`, which
  `donationOwnerValid` forbids and which permanently transferred the caller's CBS
  reservation.  Four things new code must respect.  (1) **The return runs before
  the restore**, because it reads the `.blockedOnReply` state the restore clears;
  a Tier 3 negative refuses the old order.  (2) **The holder is the thread the
  caller's own reply frame's head context is bound to** (`cancelledCallerDonation?`;
  it was the caller's *recorded reply target* until WS-HP HP5.1 re-keyed the
  resolver), and that no invariant entails — `donationOwnerValid` relates a donation
  to no reply object and `donationChainWellFormed` carries no binding clause — so
  `donatedContextIsOwnerFrameHead` states it, having replaced
  `donationHolderIsReplyTarget` at HP5.3; the *behaviour* needs no hypothesis, only
  the payoff `cancelIpcBlocking_reply_no_donation_to_victim` does.  (3) **The SM5.H
  replenishment migration is at the cross-core layer** (`cancelIpcBlockingMigrated`),
  where this tree resolves home cores for every donation-carrying path, which is
  what keeps `cancelIpcBlocking` an objects-only write; that it *establishes*
  `replenishQueueAffinityConsistent_smp` is proved at WS-RR RR8.11 (`v0.35.86`,
  `cancelIpcBlockingMigrated_establishes_replenishQueueAffinityConsistent_smp` and its
  cross-core lift), which also moved the migration's **destination** onto the bound
  thread's post-teardown home — see the hand-off constraint below for why the
  victim's pre-state home was wrong.  (4) **The return
  is invisible to every observer, not merely a high one**: `projectKernelObject`
  strips `schedContextBinding` and `boundThread`, so writing a possibly-low
  server's TCB on a high caller's cancellation leaks nothing
  (`returnDonationToCancelledCaller_preserves_projection`).  `cancelIpcBlocking_lifecycle_eq`
  was made conditional on there being no donation, because `storeObject` maintains
  bookkeeping the arm's other writes bypassed — and it is **deleted** at WS-RR
  RR8.5 (`v0.35.63`), when the teardown started writing through `storeObject`
  too: the definitional lifecycle frame would then need `tcb.replyObject = none`,
  which no reachable `.blockedOnReply` state satisfies, and nothing consumed it.
- **...and the reclaim ends the holder's outstanding send or call first**
  (WS-OD OD1.4, v0.34.104).  The hand-back is
  `returnDonatedSchedContext (abortHolderPendingIpc st holder) holder scId tid`.
  Without the prefix the reclaim leaves the holder `.unbound` while it is still
  `.blockedOnCall` — reachable at depth 1 with no chain, when the server Calls an
  endpoint with no receiver waiting — which `passiveServerIdle` forbids.
  Semantically it is what a timeout is in MCS: the budget the operation was
  issued on has been revoked, so the operation fails with `.ipcTimeout`.  Five
  things new code must respect.  (1) **The abort runs before the hand-back**, for
  the reason the hand-back runs before the restore, one level down: with the
  return first the intermediate state *is* the violation being closed, and a
  Tier 3 negative refuses the swapped order.  (2) **The prefix is
  `abortPendingIpcOnEndpoint`, not `timeoutThread`** — the timeout's objects-only
  half, without the wake and the priority-inheritance revert — because
  `cancelIpcBlocking_scheduler_eq` has four cross-core consumers and must stay
  true.  (3) **The reclaim is all-or-nothing**: a refused return discards the
  abort, since `cancelledCallerDonation?` resolves through the *holder* and can
  answer `some` for a caller with no TCB; committing the abort there would end a
  live server's IPC for a reclaim that did not happen and would falsify
  `returnDonationToCancelledCaller_eq_self_of_getTcb?_none`.  A Tier 3 negative
  refuses the committing error arm.  (4) **Every fact the hand-back reads
  survives the abort**, which is why the donation is resolved once, on the
  pre-state: the abort writes no `schedContextBinding`
  (`abortHolderPendingIpc_binding_backward` / `_forward`) and no SchedContext
  (`abortPendingIpcOnEndpoint_schedContext_forward`), so
  `donationOwnerValid` carries across it — given the holder holds a binding,
  which it does, since owners are `.unbound` and the holder is `.donated`
  (`abortHolderPendingIpc_preserves_donationOwnerValid`).  (5) **The abort is
  projection-*visible* and the reply arm's NI result says so.**  It writes the
  holder's endpoint, its queue neighbours and its own `ipcState` / queue links —
  none of which `projectKernelObject` erases — so
  `returnDonationToCancelledCaller_preserves_projection` and
  `cancelIpcBlocking_blockedOnReply_preserves_projection` now carry
  `abortHolderProjectionStable`.  That is the endpoint-queue label-uniformity gap
  the three *queue* arms already carry, reaching the reply arm through the holder
  rather than the victim; it is discharged outright wherever the abort is inert
  (`abortHolderProjectionStable_of_allowed`, from
  `abortHolderPendingIpc_eq_self_of_allowed` — the abort is the identity unless
  the holder is blocked sending or calling), so no result that held before the
  remediation is weakened on the states it held for, and the general discharge is
  registered WS-OD debt.  New code must not read either projection theorem as
  unconditional.
- **...and the holder the reclaim UNBINDS is descheduled, not woken**
  (`v0.35.158`; WS-OD OD1.7's wake of it from v0.34.108 until then).
  `cancelIpcBlockingOnCore`'s state is `descheduleAtPlacement
  (cancelIpcBlockingReclaimed victim tcb st) victim`, and the reclaim-complete
  teardown is the migration followed by `descheduleUnboundHolder` — the holder
  the pop unbound, taken off the scheduler slot the post-teardown state places
  it on.  OD1.7 had placed that holder on its home core's run queue, on the
  reasoning that an unbound thread is fully schedulable in this model; it is,
  **at its legacy TCB band charged to no reservation**, refilled by
  `timerTickBudgetOnCore`'s `.unbound` arm forever — which PR #897's review
  measured on the live `suspendThreadOnCore`: a server that Called onward and
  blocked, plus an ordinary `.tcbSuspend` of its *client*, left the server
  runnable and unbudgeted, outside CBS admission entirely.  The premise the wake
  rested on read `.unbound` as *legacy time-sliced* where the passive-server
  pattern reads it as *MCS-passive*, and every other donation pop in the tree
  takes the second reading (`applyReplyDonation`, `applyReplyDonationOnCore`,
  `replyRecvHolderDeschedule`, and seL4-MCS's `schedContext_donate`, which
  dequeues the previous holder); the reclaim was the one deliberate outlier.
  Six things new code must respect.  (1) **The trigger reads the POP's two
  writes off the post-teardown state** (`cancelUnboundHolder?`): the holder's
  binding cleared and the victim's installed, which is exactly the pop having
  landed and distinguishes it from a refused, all-or-nothing reclaim.  It reads
  no `ipcState`, so it fires on a blocked holder and on a queued one alike —
  the wake's `.ready`-gated trigger was silent on exactly the queued server this
  cut is about.  (2) **`holder ≠ victim` is structural**
  (`cancelUnboundHolder?_ne_victim`): one thread cannot answer both conjuncts,
  so the composite's own deschedule of the victim is stated with no case on the
  holder (`cancelIpcBlockingReclaimed_placedCoreOf?_victim` is an equation where
  the wake left a disjunction over a degenerate self-insert no state reached).
  (3) **The step is `descheduleAtPlacement`**, the one removal every other pop
  performs: the identity on a holder placed nowhere — every holder the abort
  unblocked, and every holder blocked in receive — and a removal from the
  holder's own placement otherwise.  A scheduler-only write, so
  `cancelIpcBlockingOnCore_objects_eq` and the whole `CancellationNI` surface
  hold verbatim; no SGI is surfaced, because both `.tcbSuspend` entry paths
  derive their pokes from the committed pre/post diff, whose
  `currentSlotChangeSgis` rule reaches a holder taken off a remote current slot.
  (4) **What the holder is left with**: `.ready`, `.unbound`, on no slot, with
  the `.ipcTimeout` frame the abort staged (WS-RR RR7.14) still in its register
  context — delivered the first time it is dispatched, which is the first time
  it holds a reservation.  Its own manager recovers it: a `.tcbSuspend` then a
  `.tcbResume`, or a `schedContextBind` once that arm places a parked thread
  (seL4-MCS's `schedContext_bindTCB` ends in `SCHED_ENQUEUE`; this kernel's bind
  re-buckets only an already-queued thread — the divergence
  `docs/REGISTERED_DEBT.md` table C keeps, owner WS-CB).  What no ordinary
  client suspension can do any more is hand a server the CPU on nobody's
  budget.  (5) **The declared scheduler footprint names the holder's PLACED
  core**: `cancelIpcBlockingOnCoreSchedLockSet` takes a `holderPlaced : Option
  CoreId`, resolved by `cancelUnboundHolderCore?` through the same
  `placedCoreOf?` the step reads (the wake's member was the holder's *home*),
  and `…_covers_holder_deschedule` is the relation; a footprint naming only the
  victim's core would be *false* of the transition.  (6) **The per-core locality
  clause excludes that core on BOTH halves**: `cancellation_cross_core_correct`'s
  run-queue and current-slot halves are conditioned on
  `cancelUnboundHolderCore?`, where the wake's insert had needed the exclusion
  on the run-queue half alone.  The bundle frame the removal owes — an insert
  owed none — is discharged from the abort that runs first
  (`cancelIpcBlocking_unboundHolder_binding_or_allowed`, under the reply arm's
  own `owed` premise), and the information-flow obligation is
  `descheduledHolderHigh`, `abortHolderWakeHigh`'s successor with the same
  discharge (`descheduledHolderHigh_of_donationOwnerFlowsToHolder`): a removal
  is filtered by the removed thread's own observability exactly as an insert is.
- **...and the live `.tcbSuspend` performs that step — since `v0.35.90`, and not
  before** (WS-RR RR8.12, second cut; the step was OD1.7's wake until
  `v0.35.158`).  OD1.7's wake and WS-RR RR7.22/RR8.11's
  replenishment migration were both added to `cancelIpcBlockingOnCore`, a
  composite **no production path calls**: the live arm and the
  `suspend_thread_cross_core` seam run `Lifecycle.Suspend.suspendThreadOnCore`,
  whose G4 performs its own placement removal and whose G2 therefore reached for
  the *bare* teardown.  So on the only path a syscall takes, neither fix was
  present — measured on the live transition, an aborted donation holder ended
  `.ready` and `.unbound` on **no** run queue on any core (the strand OD1.7
  describes, reachable from an ordinary `.tcbSuspend` on a thread in one's own
  call chain), and the reclaimed reservation's replenishment stayed on the
  holder's home core while the `.bound` arm purged the victim's, leaving an entry
  naming a deactivated SchedContext.  Five things new code must respect.  (1)
  **The shared step is the composite's PREFIX, and it has a name**:
  `cancelIpcBlockingReclaimed` is the teardown with its migration and its holder
  deschedule, `cancelIpcBlockingOnCore` is that plus the victim's deschedule
  (`cancelIpcBlockingOnCore_eq_reclaimed_deschedule`, `rfl`), and G2 is the
  prefix — so every object-level, bundle and information-flow result about the
  composite's teardown half reaches the live path with no second statement.  (2)
  **A step added to the cancellation *teardown* goes in the prefix**; only a step
  about the victim's own placement belongs to the composite.  A composite whose
  prefix a second consumer needs is a shared answer that consumer cannot reach,
  which is how two cuts each believed they had closed this.  (3) **The state pair
  is `(st, cancelIpcBlockingMigrated … st)`** — `descheduleUnboundHolder` reads
  the pre-state to resolve the holder and the post-teardown state to check the
  pop landed and to place the removal, and handing it a state further down the
  pipeline is a different predicate.  (4) **Both declarations grew by the
  holder's core**: `suspendThreadOnCoreSchedLockSet` takes a `holderPlaced :
  Option CoreId` (the run-queue segment is the placed and executing cores *plus*
  it; it was the wake's home core until `v0.35.158`) and
  `suspendThreadOnCoreWriteSet`'s first entry is no longer `[]` — a write set that
  omits a written core is as false as a footprint that does, and both were silent
  because the pipeline performed no such step.  `maxLockSetSize` does not move:
  a `SchedLockSet` carries no cardinality bound.  (5) **The guarantee is proved of
  the whole pipeline, not only measured** (`v0.35.92`, RR8.12's fourth cut;
  inverted at `v0.35.158`): `suspendThreadOnCore_holder_unplaced` lifts the
  reclaim's payoff through the six stages after G2 — the chain reversion, the
  donation arm, the placement deschedule, the pending-state clear, the
  `.Inactive` store and the G7 scheduling point — and
  `tests/SmpCancellationSuite.lean` §3.26 exhibits its premises and its
  conclusion on a state the live operations reach, computing the retired wake
  beside the live deschedule on the blocked, the queued and the running holder,
  because a hypothesis nothing exhibits is indistinguishable from one that cannot
  hold.  (Until `v0.35.158` the theorem was `suspendThreadOnCore_holder_still_placed`,
  the opposite fact about the wake, retired with it.)  Three things new code must
  respect.  **`holder ≠ victim` is derived, not assumed**:
  `cancelUnboundHolder?_ne_victim` reads it off the trigger's own two conjuncts,
  which ask the holder's binding to be `.unbound` and the victim's not to be —
  it had been a sentence in the G4-precapture comment, and a sentence is not a
  licence.  **Single placement is a hypothesis, not a bundle**: one removal is a
  removal from every core only if the holder sat on at most one, which the
  scheduler maintains by construction, and the statement takes that fact so a
  caller holding only the scheduler invariant can discharge it.  And
  **well-formedness travels to the scheduling point where resolvability used
  to**: a scheduling point places a thread only by dispatching it, and the
  dispatched thread is one the chooser took out of the executing core's run
  queue (`chooseThreadEffectiveOnCore_some_mem_runQueueOnCore`, stated under that
  queue's well-formedness), so every stage carries `wellFormed` forward
  (`handleRescheduleSgiOnCore_preserves_unplaced`,
  `switchToThreadOnCore_preserves_unplaced`) and the holder's TCB is never
  consulted; the placed direction's resolvability chain
  (`propagatePipChainCrossCore_getTcb?_isSome` and its siblings) went with it.
  The chain walk's run-queue and `current` frames
  moved to `Scheduler/PriorityInheritance/Propagate.lean` for the reason the second
  cut named a prefix — `IPC/Invariant/FaultProgress.lean`, where they sat, imports
  `IPC.CrossCore.Fault`, which imports `Cancellation` — and its three
  `_not_mem_of_not_mem` forms were retired with them, the biconditional being the
  answer.  **And the single-core reference path reads it too, since `v0.35.93`**
  (RR8.12's fifth cut): `cancelIpcBlockingReclaimed` and the wake family (the
  holder-deschedule family since `v0.35.158`) were
  declared in `IPC/CrossCore/Cancellation.lean`, which *imports*
  `Lifecycle/Suspend.lean`, so `Lifecycle.Suspend.suspendThread`'s G2 could not see
  them and the same strand was reachable on it.  They are declared beside the
  teardown they complete now — *when a question has one owner and an asker that
  cannot see it, the owner is in the wrong layer* — keeping the `SeLe4n.Kernel`
  namespace they were declared in, so the move renames nothing.
- **...and its replenish segment follows the donation's own guard, not "is the send
  queue non-empty"** (PR #897 Codex review, `v0.35.112`).  Cut 8a-ii's own docstring
  rejected over-declaration in as many words — *a segment naming two cores would be
  a footprint wider than its operation, and lock contention is an observable channel
  (SM8.D's CC-5)* — and applied that to the **block** path only.  The segment keyed
  on `receiveRendezvousSender?` while WS-OD OD3.6's donation fires only on a dequeued
  **`Call`**, so **every ordinary `seL4_Send` rendezvous declared two
  replenish-queue write locks for a migration that provably does not happen**: the
  defect the paragraph above it rejects, on the more common path, which is this
  file's own *a fix applied at one site and not its siblings*.  Seven things new code
  must respect.

  (1) **The pre-state guard and the post-state guard are two spellings of one
  question and both must exist.**  `rendezvousSenderIsCall` is
  `rendezvousDequeuedCall`'s pre-state sibling, clause for clause, because a dequeued
  `Call` sender is `.blockedOnCall` *before* the receive leg and `.blockedOnReply`
  *after* it.  Asking for the post-state constructor at the pre-state answers `false`
  for exactly the sender that *will* donate, so a footprint derived from it would
  **omit** a lock the transition writes — and a footprint that omits a written lock
  is false, where one wider than its operation is merely expensive.  That asymmetry
  is the whole reason the narrowing is safe in one direction and not the other.

  (2) **It reads the leg's OWN branch condition.**
  `endpointReceiveDualOnCore` branches on the TCB `endpointQueuePopHead` *returns*,
  which no consumer could name until
  `endpointQueuePopHead_popped_tcb_eq_lookup` — the twin of WS-RR RR2.6's
  `endpointQueuePopHead_popped_eq_head` — said that record **is**
  `lookupTcb st head`.  Without it a pre-state resolver is a *second* reading of the
  same question, which is the shape this file spends its length retiring.

  (3) **The licence is unconditional in the result, and that is why it names
  `.blockedOnSend` rather than "not a `Call`".**  On the refusal branches the leg
  returns the *pre*-state, where a sender already `.blockedOnReply` would satisfy the
  weaker hypothesis and refute the conclusion; `ipcStateQueueMembershipConsistent` is
  what says `.blockedOnSend` is the reachable non-`Call` shape on a send queue.  The
  proof needs **no** distinctness between sender and receiver, because the last write
  at the sender's key is `.ready` either way.

  (4) **The rename is the claim.**  `_of_rendezvous` asserted the
  segment/migration equality for *every* rendezvous, which on a plain `Send` is now
  false (the segment is `[]`), so it became `_of_call_rendezvous` with the hypothesis
  the name promises, and a Tier 3 negative refuses the retired spelling — and Cut C1
  re-keyed it once more, to `_of_donating_call_rendezvous`, see (5).  Its four
  citations were swept, and the two positive anchors **failed loudly** at the rename —
  which is *sweep what was pinning the thing you deleted* working in the direction it
  is meant to.

  (5) **The residual was a LAYERING defect, registered rather than glossed — and
  CLOSED at `v0.35.160` (WS-RR RR8.12 Cut C1, register row 55).**  A dequeued `Call`
  whose donation prerequisites fail migrates nothing either, and the transition's
  guard for that is `callDonationSchedContext?`; transporting its pre-state answer
  across the receive leg is the backward `sameSchedContextBindings` frame.  Two
  things stood in the way, and each was a rule this file already carries.  **The
  frame was declared where the resolver could not see it**:
  `IPC/Operations/Donation.lean`'s closure contained neither
  `IPC/Invariant/Defs.lean` nor the reverse, so the bridge had no home beside the
  resolver — *a shared answer must be reachable from every asker* (`v0.35.59`),
  remedied the same way, the owner moved down.  The predicate and its `refl` /
  `trans` / `of_objects_eq` live in `IPC/Operations/Endpoint.lean` now, beside the
  two primitives that write the field they frame; the two invariant consumers stay
  in `Defs.lean`, and the `SeLe4n.Kernel` namespace is kept so nothing was renamed.
  **And the receive leg had no frame at all**: the two theorems that needed one
  (`endpointReceiveDual_preserves_donationBudgetTransfer`,
  `…_donationOwnerUnique`) each inlined the whole rendezvous composition, so it was
  extracted — `endpointReceiveDual_sameSchedContextBindings_of_rendezvous`, and
  `…_of_blocked` from the state the pre-receive cleanup leaves — and both became one
  case split over the frames, the de-duplication that is the evidence the frame was
  missing rather than merely unnamed.  (This item first said the per-primitive
  frames were unreachable from the footprint's module; they were, through a
  nine-edge production path, and *a module's layer is a fact about the import
  closure*.)  Six things new code must respect.  (a) **The segment keys on
  `receiveRendezvousDonatingSender?`**: the `Call`-narrowed resolver narrowed once
  more by `callDonationSchedContext?`, asked of the same two threads the transition
  asks it of, on the pre-state.  (b) **The bridge is one direction, and it is the
  right one**: `callDonationSchedContext?_some_of_sameSchedContextBindings` pulls a
  post-state `some` back to a pre-state `some`, which is exactly *the transition
  migrates ⟹ the footprint declares*; the forward direction is neither given by the
  backward frame nor needed, since declaring on a `some` the transition then
  declines is merely wide.  (c) **The licence is the leg's binding frame** —
  `endpointReceiveDualOnCore_sameSchedContextBindings_of_rendezvous` and its
  WithCaps twin, composed from the per-primitive frames and the pointwise
  `sameSchedContextBindings.of_objects_getElem_eq` for the wake of a `.ready`
  thread — so a pre-state `none` is the post-state's answer
  (`endpointReceiveDualWithCapsOnCore_callDonationSchedContext?_none_of_none`).
  (d) **Three payoffs, at three units**: the donation step is the identity
  (`applyReceiveRendezvousDonation_eq_self_of_no_donation`, over the general
  `applyReceiveRendezvousDonation_of_no_donation` in `Donation.lean`), the arm's
  whole hand-off writes no replenish queue
  (`applyReceiveRendezvousHandoff_replenishQueueOnCore_of_no_donation` — not the
  identity, since the chain walk still runs), and the footprint declares no
  replenish lock
  (`schedLockSet_endpointReceiveOnCore_no_replenishQueue_of_no_donation`).
  (e) **The coverage claim is stated at the donation's OWN resolver on its OWN
  state**: `schedLockSet_endpointReceiveOnCore_covers_donation`'s `hDon` is the
  post-receive-leg resolver, the guard `applyCallDonationOnCore` migrates on, bridged
  back to the pre-state reading the segment keys on — hypothesised on the
  footprint's own reading it would be the footprint vouching for itself.  The
  licence theorem is `endpointReceiveHandoffReplenishCores_of_donating_call_rendezvous`
  now, with the pre-state `some` as a hypothesis, and `_of_call_rendezvous` is
  refused tree-wide for the reason `_of_rendezvous` was.  (f) **The object-domain
  members were not narrowed in this cut and are since `v0.35.189`** — the bullet
  below; until then `receiveRendezvousDonatedSc?` and `endpointCallDonatedSc?`
  declared a SchedContext write lock for a donation the resolver declines.

  (6) **The claim is made about the step the ARM runs, not only about the donation.**
  `API.lean`'s `.receive` arm calls `applyReceiveRendezvousHandoff`, which is the
  donation **and** WS-OD OD3.14's priority-inheritance walk under one guard, so
  `applyReceiveRendezvousHandoff_eq_self_of_blockedOnSend` sits beside the
  donation-level fact — *a proxy is not the fact*, and a consumer reaching for the
  component would be reasoning about a sub-step of the transition it brackets.  The
  walk writes run queues rather than replenish queues (declared dynamically through
  `pipChainSchedFootprint`), so the replenish segment's own licence is still the
  donation half; both exist so neither can be read as the other.

  (7) **The witness computes the retired readings beside the live one.**
  `tests/SmpIpcSuite.lean` §3.26 drives three shapes through the live operations —
  a `Call` to a passive server (both cores declared, and the donation hands the
  context over at the state it runs on), a plain `Send` (the sender-keyed reading
  declares two cores, the live one none) and, since Cut C1, a `Call` to an
  **active** server (the `Call`-keyed reading declares two cores, the live one
  none) — with both retired segments computed as `private def`s beside the live
  one, so every assertion is known to discriminate.  Each empty segment is asserted
  against the donation step moving no replenishment, on the replenish *entries*
  rather than on state equality, because that is the proposition the footprint is
  about — `SystemState` has no `DecidableEq`, and reaching for one would have been
  a claim about the wrong thing.

- **...and the OBJECT-domain donation members follow the same guard** (WS-RR
  RR8.16, `v0.35.189`; register row 56).  Cut C1 narrowed the *replenish* segment
  and recorded that the two object-domain members had the same gaps one lock
  domain over: `endpointCallDonatedSc?` read the caller's own effective context
  with no test that a receiver was waiting or that it was passive, and
  `receiveRendezvousDonatedSc?` read the queued sender's through it — so a plain
  `Send`, and a `Call` to a receiver that already holds a reservation, each
  declared a SchedContext **write** lock (and a donation-old-head reply lock) for
  a migration that provably does not happen.  Sound, and not free: lock
  contention is an observable channel (SM8.D's CC-5), which is WS-OD OD3.5's own
  reason for narrowing a footprint.  Five things new code must respect.

  (1) **Each member resolves the OTHER party and asks the transition's own guard
  of the pair**: `endpointCallDonatedSc? st endpointId caller` is
  `(endpointCallReceiver? st endpointId).bind fun receiver =>
  callDonationSchedContext? st caller receiver`, and
  `receiveRendezvousDonatedSc? st endpointObjId receiver` is
  `(receiveRendezvousCallSender? st endpointObjId).bind fun sender =>
  callDonationSchedContext? st sender receiver`.  A member that inlines a binding
  read is the defect returning, and a Tier 3 negative refuses one at each.

  (2) **The owner moved DOWN, and the layering was measured rather than read off
  module paths.**  `IPC/CrossCore/EndpointCall.lean` and
  `IPC/Operations/Donation.lean` are **incomparable** — neither is in the other's
  import closure — and both reach `IPC/Operations/Endpoint.lean`, so
  `callDonationSchedContext?` and its four lemmas live at the join, with a
  tombstone at the old home (`v0.35.59`: *when a question has one owner and an
  asker that cannot see it, the owner is in the wrong layer*).  The same rule
  moved three binding frames out of the **staged** `EndpointCallInvariant.lean`
  into production — `endpointCallOnCore_preserves_objects_invExt`,
  `wakeThread_sameSchedContextBindings_of_ready`,
  `endpointCallOnCore_sameSchedContextBindings` — since the footprint and the
  licence are production and could not read a frame declared in the staged
  surface.  The first attempt wrote a *second* copy of the third and the build
  refused it as already declared: *before writing a helper, find the one this tree
  already has*, caught by the elaborator rather than by a review.

  (3) **Soundness is a proved relation in ONE direction, and that is the
  direction a footprint needs.**  A footprint that omits a written lock is false,
  so a narrowing owes *the transition migrates ⟹ the footprint declares* — and
  because the footprint resolves on the state the bracket acquires at while the
  donation branches at the state its leg leaves, that is **post `some` ⟹ pre
  `some`**: `endpointCallDonatedSc?_some_of_post` and
  `receiveRendezvousDonatedSc?_some_of_post`, each through Cut C1's backward
  binding frame (`callDonationSchedContext?_some_of_sameSchedContextBindings`)
  over the arm's own leg, with `endpointCallWithCapsOnCore_sameSchedContextBindings`
  the sending side's new whole-leg frame.  The forward direction is neither given
  by a backward frame nor needed: a footprint that declares on a pre-state `some`
  the transition then declines is *wider* than its operation, which is sound.

  (4) **The two lock domains ask ONE question, and that is stated.**
  `receiveRendezvousDonatedSc?_isSome_iff_donatingSender` says the object member
  and Cut C1's scheduler segment declare on exactly the same rendezvous, both
  composing `receiveRendezvousCallSender?` with `callDonationSchedContext?` at the
  same two threads — a shared *spelling* is not that fact.  The object member
  deliberately does **not** route through `receiveRendezvousDonatingSender?`,
  which already asks the guard to decide its own answer, so composing through it
  would ask the same question twice and leave two places for the answer to be
  read.  The `.call` arm has no such equality **by design**: its scheduler segment
  resolves at the WithCaps *post*-state and its object member on the pre-state,
  which is exactly what the `_some_of_post` licence is for.

  (5) **The narrowing is measured, not only proved, and it costs nothing.**
  `tests/SmpIpcSuite.lean` §3.36 drives five shapes through the live operations —
  a passive receiver (CONTROL), a bound receiver (the `.call` defect), a queued
  `Call` from a bound client (CONTROL), a queued plain `Send` and a queued `Call`
  to a bound receiver (the two receive-side defects) — with **both** retired
  readings spelled as `private def`s in the suite and nowhere else and computed
  beside the live resolver on every shape, each wrong on exactly one of them; a
  tree-wide negative refuses either escaping the witness.  `maxLockSetSize` is
  unmoved, both reachable `.replyRecv` bounds are unchanged (a narrowing can only
  lower a bound) and the golden trace is byte-identical.  Two things the cut
  records about its own register row, rather than quietly satisfying them: the
  blast radius was **35 call sites across six files**, not the registered 55
  across nine (that figure counted every occurrence of the two names, the
  hypotheses of theorems *about* them included), and it did **not** ride Cut C4,
  which restated each arm's members without touching these two — so it is a cut of
  its own after Cut C4 rather than inside it.
- **...and `seL4_CNode_Revoke` has an arm** (WS-RR RR8.16, `v0.35.190`).  The
  revocation family was verified machinery with **no ABI path**: `API.lean` had
  no revocation arm at all, so no capability a thread could present revoked
  anything — the register row RR8.12's reachability census opened on its first
  run, closed the way this project's implement-the-improvement rule says to close
  one.  `SyscallId.cspaceRevoke` (discriminant 35) is the arm.  Seven things new
  code must respect.

  (1) **It dispatches `cspaceRevokeCdt`, and that is its whole security
  content.**  The local `cspaceRevoke` reaches only the *containing* CNode, so a
  derived capability copied into any other CSpace survives it; the CDT walk
  follows the derivation tree across arbitrary CNodes.
  `tests/SyscallDispatchSuite.lean` SD-059 computes the local-only reading beside
  the live arm on a state whose derivation lives in a **second** CNode — spelled
  in the suite and nowhere else — so its assertions are known to discriminate,
  and a mutation of the arm to the local variant fails exactly the one that names
  the claim.  **And since `v0.36.1` no entry point opens with that local sweep**
  (PR #900 review).  It matches on the **target**, so as `revokeCdtScaffold`'s
  prologue it destroyed an independently rooted capability to the same object
  and the source's own parent in the same CNode, and left their CDT nodes mapped
  to emptied slots — which made *their* derivations unrevocable by anyone, since
  every revocation begins with a lookup of its slot.  The prologue is a read of
  the source slot now (`cspaceLookupSlot`: the same refusal set, no writes), so
  every entry point destroys exactly the source's CDT descendants, in every
  CNode, which is seL4's `cteRevoke` (read at `13.0.0`).  Every live install path
  records its edge, which is what makes dropping the sweep safe in the direction
  that matters: SD-059 asserts a same-CNode derivation is still destroyed and an
  independent sibling is not, and `tests/OperationChainSuite.lean`'s
  `revokeLeavesIndependentSibling` is PR #873 round 18's scenario inverted, at
  all four entry points, with the retired sweep computed beside it.  The local
  `cspaceRevoke` stays an operation — `lifecycleRevokeDeleteRetype` runs it and
  the non-interference catalogue carries it — and is recorded in the
  reachability census as reaching no syscall.

  (2) **The source slot survives, and that is what makes the delete's refusal
  dischargeable.**  Revocation destroys a capability's derivations, not the
  capability, so `cspaceDeleteSlot`'s `.revocationRequired` is answered by
  *revoke, then delete* — both halves run in the witness.  The arm takes the
  delete's one-register ABI (`decodeCSpaceDeleteArgs`), since both name one slot
  of the invoked CNode, and requires `.write`: `.grant` authorises **creating** a
  derivation (mint/copy/move), and destroying one is not that authority.

  (3) **A `donationReadAgreement` no longer demands `pendingMessage`
  EQUALITY.**  `revokePendingTransfersFrom` — the in-flight sweep the scaffold
  ends with — is the one transition in the tree that rewrites a
  `TCB.pendingMessage` to a *different* value while the thread stays blocked, and
  every bundle transport demanded the field be unchanged.  Equality was strictly
  more than the bundle reads: only `allPendingMessagesBounded` and
  `blockedThreadsPendingMessageConsistent` read it, the first needs the payload
  still bounded and the second needs a blocked sender still to *have* one.  So
  the relation is `pendingMessageReadAgrees` (presence agrees; boundedness
  transfers), the sweep's write is a **drop** (`TCB.pendingCapsDropped`: every
  other field equal, registers kept, capability array shorter), and a drop
  satisfies both.  A new transition that shortens a parked message reaches for
  those two; one that rewrites the field arbitrarily still has no transport, and
  that is correct.

  (4) **The scaffold's case analysis and the traversal's induction are
  predicate-free and live beside their definitions.**
  `revokeCdtScaffold_ok_decompose` says what a successful revocation *consists
  of* (the source slot resolves, then the traversal and the sweep, or the state
  unchanged), and `revokeCdtFold_induct` / `revokeCdtMaterializedTraversal_ok_induct`
  carry any `P` through the fold — so the capability bundle's argument and the
  IPC bundle's are **one** answer.  Each was the capability bundle's alone,
  spelled inside its preservation module; a second copy per predicate is the
  duplication this file spends its length retiring.  `revokeCdtFoldBody` moved to
  `Capability/Operations.lean` with them and `revokeCdtMaterializedTraversal` is
  *defined* through it — keeping the fold body in an invariant module is what had
  forced that traversal's proof to `change` its way into an inlined lambda.

  (5) **`.cspaceRevoke` declares NO static lock footprint, and that is a
  decision.**  The CDT walk's CNode set is state-discovered and unbounded while a
  `LockSet` is capped at `maxLockSetSize`, so a footprint naming only the source
  CNode would be **false** of the transition — which this project rates worse
  than no footprint at all.  `permittedKinds .cspaceRevoke` says which kinds a
  future declaration may contain, in the shape the PIP chain walk's
  `pipChainStart_<τ>` markers take for the same reason.  The inventory's coverage
  claim is therefore stated over `declaresStaticLockFootprint` — a total
  classification with its own `_false_iff` pin — rather than against
  `SyscallId.count`, because demanding an entry for this arm would force a
  footprint to exist in order to satisfy a number.

  (6) **`SyscallId.count` is 36, and the exhaustive tables moved with it**: the
  ABI mirrors in `sele4n-types` and the HAL, the return-shape table on both sides
  of the ABI (`.unit`, with `tests/fixtures/syscall_return_shape.expected`
  regenerated deliberately), `refusalSeamClass` (`.exempt`),
  `capFaultReceivePhase?` (`some false` — a send-phase capability fault),
  `frozenOpCoverage` (`false`: the per-node step ends in `cdt.removeNode`, a key
  *removal*, and the frozen CDT is four `FrozenMap`s with no `erase` — the same
  reason `lifecycleRetype` and the two service ops give), the enforcement
  boundary (`capabilityOnly "cspaceRevokeCdt"` — the composite a capability
  reaches, never the inner local step), and a `sele4n-sys` wrapper
  (`cspace::cspace_revoke`) so the conformance sweep can drive it.

  (7) **What the reachability census still lists is a narrower claim.**  The
  three *reporting* variants (`cspaceRevokeCdtStrict`, `…Streaming`,
  `…Transactional`) with their traversals, the streaming BFS and the reporting
  fold step remain outside the live closure: each is the same scaffold at a
  different traversal, offered to **in-kernel** callers that want a structured
  failure report or an `O(branching-factor)` walk, and the syscall dispatches the
  materialized one because a userspace invocation has no channel to receive a
  report through.  A variant with no in-kernel caller either gains one or is
  retired.
- **A capability is installed only at a slot the target CNode can address**
  (WS-RR RR8.16, `v0.35.201`).  `CNode.resolveSlot` extracts a slot by masking
  with `2 ^ radixWidth`, so an index at or above `slotCount` can be **stored**
  and can never be **reached**; `cspaceInsertSlot` — the one primitive every
  capability install passes through — asks `CNode.slotAddressable` before it
  asks about occupancy, and refuses with `.invalidArgument`.  Before it, a
  `seL4_CNode_Copy` whose `dstSlot` came verbatim from a message register grew a
  fixed-size kernel object without bound and falsified `cspaceSlotCountBounded`,
  a conjunct of `capabilityInvariantBundle`, on a state one ordinary syscall
  reaches.  Six things new code must respect.

  (1) **The chokepoint is the primitive, not the four arms.**  `cspaceCopy`,
  `cspaceMint`, `cspaceMove` and the IPC capability transfer all reach
  `cspaceInsertSlot`, so the range check is stated once — the *creator is exactly
  one function* principle `ipcTransferSingleCap`'s own comment already invokes
  for the revocation window.  A new install path inherits it by calling the
  primitive; one that writes a CNode directly is the defect returning.

  (2) **The transfer path answers `.noSlot`, it does not refuse.**
  `ipcTransferSingleCap` scans with `findFirstEmptySlotChecked`, so a receiver
  CNode with no free in-range slot yields an outcome the transfer summary already
  models rather than an error — and `findFirstEmptySlotChecked_slotAddressable`
  is what makes its `.ok` provably not the guard's refusal.  Its sibling
  `resolveSlot_slotAddressable` is the other half of the claim: the guard refuses
  exactly the slots no CPtr can name.

  (3) **A helper written for a hazard and never wired is the hazard, unfixed.**
  `findFirstEmptySlotChecked` was written by AK8-F for *precisely* this, proved
  `findFirstEmptySlotChecked_within_radix`, said in its own docstring that the
  zero-width window ensures no out-of-range slot is ever produced — and had **no
  production consumer at all**, in the whole of this repository's visible
  history, which begins at `v0.32.69` and in which the checked variant is
  present from the first commit, while `findFirstEmptySlot` sat on the live
  transfer path.  The tree held the fix and
  the defect at once.  *A helper whose docstring names the hazard it prevents is
  a claim that the hazard is prevented; check who calls it.*

  (4) **A fixture built on the defect makes the defect invisible to every test,
  and landing the guard is what finds it.**  Six fixture CNodes were malformed,
  the trace harness's own **bootstrap root CSpace** among them: CNode ⟨10⟩
  declared `radixWidth := 0` — *one* slot — while holding capabilities at 0, 5
  and 6, so `cspaceSlotCountBounded` was **false** of the state every trace
  scenario starts from and every capability but slot 0's was unreachable.  No
  audit of the guard's *call sites* could have shown that; the diff after
  landing it did, in one run.  Two of the six carried a **comment naming the
  radix the code did not have** (`S2-G-05`: *"Build a CNode with radixWidth=2 …
  fill slots 0-3"* over `radixWidth := 0`) — a defect report nobody read.  *A
  fixture comment that names a parameter the code does not have is a finding.*

  (5) **An invariant no runtime check asserts is one a fixture can violate
  silently** — which is *why* (4) could persist for as long as those fixtures
  have existed: `slotCountBounded` appeared nowhere under `SeLe4n/Testing/`.
  `cspaceSlotAddressableChecks` is part of `stateInvariantChecksFor` now, and it
  asserts the **structural** property rather than the cardinality: slot keys are
  unique, so *every occupied index is below `slotCount`* entails the count bound
  and, unlike it, names the offending slot.  This is RR8.3's *the conjunct is
  checked at runtime, not only proved* rule meeting a conjunct that predates
  this repository's visible history and had been checked never.  What the boot still
  bounds is the **count** and not the **indices**, so a `PlatformConfig` CNode
  may hold four capabilities at slots 0, 9, 17 and 33 in four addressable slots;
  that is registered rather than assumed away.

  (6) **A scanner for this class must resolve indirection, and the runtime check
  is the authority.**  The static sweep written to size the damage read slot
  indices out of CNode literals and **missed** `strictSeed`, whose slots are
  spelled `strictRootSlot.slot` — *a helper the scanner cannot see is a spelling
  that evades the metric*, arriving inside the measurement written to size the
  class.  The runtime check named it in one run.  And a guard forces a sweep of
  every **re-derivation** of the operation it guards: a successful insert's
  decomposition was re-derived inline at **eight** sites and the guard broke all
  eight, so they read `cspaceInsertSlot_ok_decompose` now and three frames moved
  beside the primitive (`_cdt_eq` relocated out of a preservation module,
  `_cdtNodeSlot_eq` and `_objects_eq` new, the last replacing a `private` copy).
  With the fixtures repaired the golden trace is **byte-identical** but for the
  post-dispatch check count the new runtime check moves (29 → 32), which is the
  measurement that the guard refuses only what was already unreachable.
- **A definition that transforms kernel state is wired or recorded** (WS-RR
  RR8.12 third cut, `v0.35.91`).
  `SeLe4n/Testing/KernelTransitionReachabilityCensus.lean` (Tier 1) derives every
  project `def` whose **result type** mentions `SystemState` — 528 of them —
  partitions that domain by whether one of the 7 committing `@[export]`s can
  reach it (288 do), and reconciles the other 240 against a pin in **both**
  directions: a new non-executed transformer fails, and so does an entry that
  has become live.  New code adding a state transformer that no seam runs must
  either wire it or record it there.

  Four things it decides and one it does not.  (1) **The commit predicate and
  the auxiliary filter are imported, not restated** —
  `ExportCommitDisciplineCensus.commitsState` and
  `ReplyStackWriteCensus.isAuxiliary` — so the three censuses cannot disagree
  about what installs kernel state or about what the compiler generated; the
  three generated shapes the second does not reach are named with the
  measurement that found them.  (2) **The domain over-approximates on purpose**:
  an `Option SystemState` resolver qualifies, which is the safe direction, since
  a member wrongly included must be explained and a member wrongly excluded is
  never looked at.  (3) **The 240 carry no per-entry prose**, deliberately —
  that many shallow reasons read as justification while asserting nothing — so
  the obligation falls on whoever adds the next entry.  (4) **The known residue is
  named in the pin's docstring rather than left to read as unexamined**: four
  transformers consumed by nothing, which carry a register row because each needs the
  wire-or-retire judgement `v0.35.78` made for the capability-reference table.

  **What it does not decide, and this corrects the row that asked for it**:
  reachability sees a *new* non-executed transition and **cannot** see a step
  added inside an already-registered one — which is the defect that motivated
  it, since `cancelIpcBlockingOnCore` already existed and was already
  unreachable.  The register row claiming the census "would have failed on the
  day" that step was added was wrong and is corrected.  What sees it is
  `standsBesideLive`: a row names the non-executed surface, the live definition
  that re-composes it, and a **pin theorem** that RELATES them, so a step added to
  one side alone fails the build — measured by inserting one into
  `cancelIpcBlockingOnCore` and watching
  `cancelIpcBlockingOnCore_eq_reclaimed_deschedule` stop elaborating.  *Relates*,
  not *mentions* (PR #897 review, `v0.35.96`): the check asked whether the
  statement named both programs, which a conjunction of reflexive equations
  satisfies while relating nothing — this file's oldest rule failing inside the
  gate written to enforce a different one.  `pinRelatesPrograms` requires an `Eq`
  or `Iff` conclusion with **each program on exactly one side, on opposite
  sides**, so one side is built from the surface without naming the counterpart
  and the other from the counterpart without naming the surface; three witness
  theorems carry the shapes the superseded check accepted and the census asserts
  all three are refused, because a check that cannot fire on this tree is
  indistinguishable from one that is wrong.  Two rows are pinned today; a
  registered surface with no pin makes **no** agreement claim, and extending the
  pinned set is what closes the class rather than the instance.
- **An endpoint queue's membership lives in its members' TCBs, and those members'
  labels differ** (WS-RR RR8.8, `v0.35.83`).  Three facts new code must respect,
  and the first is the one that decides the other two.  (1) **The admission gate
  is an order, not an equality**: the live send / call gate is
  `endpointFlowGate ctx ep (threadLabelOf sender) (endpointLabelOf ep)` and the
  receive gate its mirror, so a *lower*-labelled and a *higher*-labelled sender
  are both admitted onto one higher-labelled endpoint —
  `publicLabel → kernelTrusted` being the flow
  `securityFlowsTo_prevents_label_escalation` documents as intended.
  `endpointAdmissionAdmitsMixedObservability`
  (`InformationFlow/Projection.lean`) is that admission as a `decide`-checked
  theorem, with an observer that sees exactly one of the two.  So **an
  endpoint/notification queue label-uniformity invariant is unestablishable**, not
  merely absent; it was the registered closure for `abortHolderProjectionStable`,
  `abortHolderWakeHigh` (`descheduledHolderHigh` since `v0.35.158`) and the three
  queue arms' `hTeardownProj`, and it is retracted.  A proof that reaches for it is asking for a premise the gate
  refutes.  (2) **What the gate gives is the other direction, and with one
  added conjunct it is enough for everything but the neighbours.**  Every
  waiter's label flows to its endpoint's **flow** label
  (`endpointFlowGate_implies_securityFlowsTo`, no hypothesis) — but
  `objectObservable` decides visibility from `objectLabelOf`, and
  `LabelingContext` carried `endpointLabelOf` and `objectLabelOf` as
  *independent* fields with nothing relating them, so "the endpoint object is
  non-observable whenever a waiter is" was **not derivable** and `v0.35.83`
  asserted it anyway.  `LabelingContextValid.endpointObjectCoherence`
  (`v0.35.84`) is the missing conjunct — an endpoint's flow label flows to its
  own object's label, so the object is at least as sensitive as the flows the
  endpoint admits — discharged structurally for every constructed context from
  `DeploymentLabeling.hEndpointObjectCoherence`, which the one base constructor
  meets by reflexivity.  A new `DeploymentLabeling` must supply it; a new
  labelling *question* about an endpoint must say which of the two fields it is
  about.  With it, `endpointObjectHigh_of_admittedThreadHigh` covers the
  endpoint's own queue boundaries and `donationHolderHigh_of_donorHigh` covers
  the aborted holder's TCB, through `donationOwnerFlowsToHolder` — the state
  form of `label victim ⊑ label endpoint ⊑ label holder`, established where a
  donation is minted because the state records no trace of the two gates that
  licensed it.  The **queue neighbours** are covered by nothing: their labels are
  constrained only against the endpoint's.  So `abortHolderWakeHigh` is
  **reduced to that fact** (`abortHolderWakeHigh_of_donationOwnerFlowsToHolder`,
  `v0.35.84`; `descheduledHolderHigh_of_donationOwnerFlowsToHolder` since
  `v0.35.158`, a removal being filtered by the removed thread's own
  observability exactly as an insert is) — it is a single `threadObservable` of
  the holder and needed no queue reasoning at all — while
  `abortHolderProjectionStable` and
  `hTeardownProj` reduce to the neighbour class and no further
  (`abortHolderSpliceHigh_of_victimHigh`, over the shared
  `endpointSpliceHigh`).  **Read that as a reduction, not a closure**: `v0.35.84`
  called it *discharged*, which is what it would be if the fact it reduces to were
  a fact about reachable states, and for two cuts it was a `Prop` nothing
  established — see item (4).  **And a reduction to a predicate is not a
  connection to the OPERATION** (`v0.35.193`): for nine cuts
  `abortHolderProjectionStable` went on carrying its *whole* obligation as a
  hypothesis, because the reduction stopped at `endpointSpliceHigh` and nothing
  related that predicate to `abortHolderPendingIpc` — the prefix runs the
  **single** `endpointQueueRemove`, and only the **dual** removal had a projection
  lemma (RR7.22).  The labelling layer was proved and the wire was missing, which
  in a bundle search reads exactly like a closed obligation.  The single removal
  has one now (`endpointQueueRemove_preserves_projection{,_and_invExt}`, beside
  `endpointSpliceHigh` in `InformationFlow/Invariant/Operations.lean`, built from
  raw-insert frames because the removal's four writes are `RHTable.insert`s in one
  record update rather than four store primitives), and with it
  `abortHolderPendingIpc_preserves_projection` and the discharges
  `abortHolderProjectionStable_of_{spliceHigh,neighbourHigh}` — so what a caller
  supplies is the neighbour clause and nothing else.  The one mismatch that
  crossing needed is a mismatch of *spelling*: `endpointSpliceHigh` names the
  predecessor through `queuePPrev` and the single removal reads `queuePrev`, and
  RR8.3's `TCB.queuePPrevAgreesWithPrev` is exactly the statement that those are
  one thread (`endpointSpliceHigh_queuePrev_high`), read at a thread through
  `queuePPrevAgreesWithPrev_lookupTcb` rather than by re-opening the
  `getTcb?` / `objects[…]?` bridge at each consumer.  **When a reduction stops at
  a predicate, ask what still connects that predicate to the transition**; a
  hypothesis and its labelling layer can both be right while nothing joins them.
  (3) **The residue is
  representational and the remedy is forced**: `queuePrev` / `queuePPrev` /
  `queueNext` survive `projectKernelObject`, so an observable thread's projection
  already names a non-observable one's identity with no operation having run —
  the same class as the `replyObject` erasure SM6.D landed — and a splice then
  rewrites an observable field.  *Stripping* the links is **unsound** rather than
  coarse: the projection would stop determining the next dequeue, so two
  low-equivalent states would step to states differing in the endpoint's own
  visible `head` and the step-level NI theorems would become false.  A queue's
  content must live in an object whose label **dominates** every member's, which
  the endpoint is and a member's own TCB is not — so the closure is non-intrusive
  endpoint queues, registered in `docs/REGISTERED_DEBT.md` table C with its
  measurement.  Until it lands, **v1.0.0 must not claim that a low observer
  cannot learn a high thread's identity from endpoint queue state.**  (4) **A
  predicate only consumed as a hypothesis is an assumption wearing a definition's
  name** (WS-RR RR8.16, `v0.35.126`, PR #897 review).  `v0.35.83` and `v0.35.84`
  introduced `blockedSenderFlowsToEndpoint` and `donationOwnerFlowsToHolder`, argued
  from the *gates* in their docstrings — which is the right argument — and then
  consumed both as hypotheses and nothing else: no theorem established either where
  the fact is created, none transported it across a step, and no state inhabited
  either.  So the reduction above was not composable for a live state, and the word
  *discharged* was reading a reduction as a closure.  Four things new code must
  respect.  **Only ONE of the two needs a story**: `donationFlowFromBlockedDonor`
  derives `donationOwnerFlowsToHolder`'s conclusion from its sibling plus the
  *receiving* gate — `label owner ⊑ label ep ⊑ label holder` — because a
  `.donated scId owner` binding is minted only through a `Call` rendezvous in which
  the donor is `.blockedOnCall` on that endpoint.  **Transport is weaker than a
  frame, deliberately**: `blockedSenderShrinks` (with `.refl`, `.trans` and
  `blockedSenderShrinks_of_ipcStateFrame`) says a step introduces no blocked sender
  *on the same endpoint* it did not already have — a send rendezvous writes the
  receiver `.ready` and a wake writes a runnable state, so neither frames every
  `ipcState` while both shrink the set, and a step moving a thread from
  `.blockedOnSend ep₁` to `.blockedOnCall ep₂` would satisfy a set-shaped relation
  and break the predicate.  The donation fact's counterpart is
  `donationOwnerFlowsToHolder_of_sameSchedContextBindings`, over the frame family
  the tree already has for every transition that mints no donation.
  **Establishment is stated at the one WRITE, not per transition**: every
  production path that blocks a sender or a caller goes through
  `storeTcbIpcStateAndMessage` with the endpoint as an explicit argument, so
  `storeTcbIpcStateAndMessage_preserves_blockedSenderFlowsToEndpoint` takes the gate
  as an argument (a transition-time check the store records no trace of) and a
  transition inherits the fact by exhibiting its own decomposition.  Landing it
  moved `storeTcbIpcStateAndMessage_tcb_backward_fields` out of
  `IPC/CrossCore/EndpointReplyInvariant.lean` and beside the primitive it frames,
  which is `v0.35.59`'s rule — *when a question has one owner and an asker that
  cannot see it, the owner is in the wrong layer* — and put it next to the two
  siblings RR3.5 had already relocated for the same reason.  And **the boot state
  inhabits both, for every labelling context**
  (`bootFromPlatformCheckedWithIdleThreads_flowGateFacts`): `bootSafeTcbCheck`
  refuses a blocked or bound config TCB and the idle fold installs neither, so both
  antecedents are *empty* rather than their conclusions cheap.  That measurement
  generalised `bootFromPlatformChecked_ok_tcb_inactive` — which concluded two of the
  ten fields its own object-reachability argument establishes, so the other eight
  needed a second copy of that argument — into
  `bootFromPlatformChecked_ok_tcb_bootSafeFields`, with the old name its two-field
  corollary.  **And the per-transition lift landed at `v0.35.191`**
  (`SeLe4n/Kernel/IPC/Invariant/BlockedSenderPreservation.lean`): both
  `endpointSendCrossCoreDispatchChecked` and `endpointCallCrossCoreDispatchChecked`
  carry the fact, each under the `endpointFlowGate` its own branch condition
  supplies.  **The per-TCB dichotomy this paragraph predicted was not needed**, and
  that correction is the cut's own finding: every step of both composites falls
  into one of three classes rather than needing a pullback — it preserves every
  `ipcState` (the queue splice, the capability transfer, the reply link, the
  SchedContext donation, the priority-inheritance walk, the run-queue removal, each
  getting `ipcStateFrame`, the relation `QueueSplicePreservation.lean` already owned
  for this question), it writes `.ready` (`storeTcbReceiveComplete` and the wake's
  `enqueueRunnableOnCore`, which *shrink* the blocked-sender set and are therefore
  `blockedSenderShrinks` rather than a frame — a Tier 3 negative refuses the
  stronger claim, which is false of both), or it **is** the blocking store, which
  the `v0.35.126` establishment already covered.  A donation's frame is read off its
  own `donationReadAgreement`, whose `tcbBwd` clause states the conjunct outright,
  so a widening of the donation inherits it.  Two things new code must respect.
  **The lift is a theorem about the CHECKED arm and is false of the unchecked one**:
  what discharges the blocking store's obligation is the gate the dispatch
  evaluates, so the unchecked composites take it as an argument and only the checked
  ones discharge it.  And **both arms carry `donationOwnerFlowsToHolder` too, by
  two different routes**: the send over its own `sameSchedContextBindings` frame
  (`endpointSendCrossCoreDispatchChecked_preserves_donationOwnerFlowsToHolder`,
  `v0.35.191`), which the `.call` chain has had since RR2 and the send did not,
  and the call — the one transition that **mints** a donation, so no binding frame
  can carry it — over the *receiving* gate, which `v0.35.196` made a state
  predicate.  See the next bullet.
- **...and the RECEIVING side of the endpoint gate is a state predicate too, so
  the arm that mints a donation carries the flow fact** (WS-RR RR8.16,
  `v0.35.196`, closing register row 183).  `blockedSenderFlowsToEndpoint` records
  what the *sending* gate checked; nothing recorded what the *receiving* gate
  checked, so `donationFlowFromBlockedDonor` had to take that half as an argument
  (`hReceiveGate`) and no dispatch could discharge it.  Six things new code must
  respect.  (1) **The direction IS the predicate.**
  `blockedReceiverFlowsFromEndpoint` reads `endpoint ⊑ thread` where its sibling
  reads `thread ⊑ endpoint`, so a spelling that swaps the two arguments is the
  sibling's reading and the transitivity in `donationFlowToBlockedReceiver` stops
  composing; a Tier 3 anchor pins the direction inside the declaration.  (2) **It
  is established at the SAME write**, `storeTcbIpcStateAndMessage`, from the
  receive arm's own `endpointFlowGate` — a second establishment site would be a
  second answer to one question — and transported by a `blockedReceiverShrinks`
  twin, which is weaker than `ipcStateFrame` for the reason its sibling is.  (3)
  **The derivation reads the receive half OFF THE STATE**, which is the whole
  content: `donationFlowToBlockedReceiver` takes
  `blockedReceiverFlowsFromEndpoint` where `donationFlowFromBlockedDonor` takes a
  gate, and a mutation that restores the argument shape keeps every token and
  reopens the row.  (4) **The extra `ipcInvariantFull` conjunct is the RESOLUTION
  of the receiver, not an extra assumption.**  The `.call` lift takes
  `queueHeadBlockedConsistent` where the send's lift takes none, and that
  difference is structural: the sending gate is evaluated on the *invoking*
  thread, whose identity the transition holds, while the receiving gate is
  evaluated on a thread the rendezvous **finds** on a queue — so the conjunct is
  what says *which* thread the receiver is.  `rendezvousReceiverFlow` is where the
  two meet.  (5) **The donation's own step is gated on its own resolver**:
  `applyCallDonationOnCore_preserves_donationOwnerFlowsToHolder` keys its flow
  hypothesis on `callDonationSchedContext?` rather than on the two threads'
  identities, so a widening of the donation guard cannot leave it behind.  (6)
  **The labelled reachable pack is OPT-IN**: `ipcReachableUnder ctx` is
  `ipcReachable` and the three flow facts, `ipcReachable` is unchanged and
  `.reachable` projects out of it, so no existing consumer carries a `ctx` it does
  not read, and `ipcReachableUnder_default` inhabits it for *every* labelling.
  Neither pack is claimed preserved along a trace — that is `ipcReachable`'s own
  shape as a pre-state pack the dispatch payoff consumes, so the labelled
  extension is exactly as strong as the thing it extends.  The witness is
  `tests/SmpInformationFlowSuite.lean` §15 and its decisive case is the one where
  the caller's gate **passes** and the donation **is** minted while the
  receiver-side fact is false; its fixture is built by the **live** receive,
  because a hand-built blocked server carries no Reply object, `donationPushFrame?`
  then refuses, and every outcome assertion passes vacuously.
- **The two cross-subsystem invariant bundles have FRAMES, so a step that writes
  nothing they read costs one application** (WS-RR RR8.16, `v0.35.197`, register
  row 85's first half).  Before this cut neither `schedulerInvariantBase_smp` nor
  `capabilityInvariantBundle` had one: twelve per-conjunct lemmas existed across
  the *scheduler* transitions and **none** for an objects-only step, and the only
  reusable capability shape was one operation's forty-line argument — so each IPC
  step's lift would have been a fresh case analysis over predicates it does not
  touch.  Six things new code must respect.  (1) **The scheduler frame takes TCB
  SURVIVAL, not store equality.**  A step that rewrites the current thread's own
  TCB — the reply leg's `ipcState` write, the donation's binding write, the
  walk's `pipBoost` write — is the common case, and equality would refuse exactly
  the steps the frame exists for; a Tier 3 negative refuses that hypothesis
  coming back.  (2) **The narrower frame is at the fields the invariant reads**:
  `SchedulerState` has nine and the base invariant reads `current` and
  `runQueue`, so a step that writes `replenishQueue` alone (the SM5.H migration)
  satisfies `_of_schedulerFields` and *not* whole-scheduler equality — demanding
  the latter would refuse a step the invariant provably does not see.  (3) **The
  capability frame states the DIRECTION each conjunct transports in**, which is
  its whole content: three conjuncts read CNodes and go **backward** (a post-state
  CNode must be a pre-state CNode — what a store at a TCB key gives), while
  `cdtCompleteness` and the Reply half of `replyCapPointsToValidReply` go
  **forward** (a store removes no key and no Reply).  `cspaceLookupSound` is
  structural and `cdtAcyclicity` reads `st.cdt` alone.  (4) **`cnode` is excluded
  from the pointwise instance, in one direction only**: a CNode *rewrite* keeps
  the key and the kind while changing the slots, and three conjuncts are about
  the **value** — so a genuinely CNode-writing step (`ipcTransferSingleCap`,
  `ipcUnwrapCaps`) takes the general frame and has its own bundle lemma already.
  (5) **`storeObject_preserves_capabilityInvariantBundle_of_kind` is what every
  IPC store chain is built from**: `storeObject` writes no CDT table, so of the
  frame's six hypotheses four are that lemma pair and the `invExt` frame, and
  what is left is the store's own key.  (6) **A lift is not always a frame
  application, and the walk is the example**: `propagatePipChainCrossCore`
  re-buckets, so neither whole-scheduler nor field equality holds of it, and its
  lift composes four facts stated *beside the transition* — the current slot is
  fixed, membership is fixed, the `remove`-then-`insert` keeps `Nodup`, and the
  only object write is a TCB for a TCB.  An instance of a frame lives beside the
  frame; a fact about a transition lives beside the transition; where a
  transition's own module is upstream of the predicate's (which is true of
  `Propagate.lean` and of `Scheduler/Operations/Selection.lean`), the lift goes
  to the predicate's module and says so.
- **...and the relation those frames read has ONE NAME, so the reply chain is
  citations rather than an argument** (WS-RR RR8.16, `v0.35.199`, register row
  85's reply half).  `v0.35.197` stated each frame's pointwise instance as an
  inline condition on the two stores, which is the recognised-set shape one level
  down: a step's lift had to spell it out, and a widening would reach whichever
  consumer a review named.  `kindPreservingWrite st st'` — *at every key the
  object is unchanged, or both sides hold an object of the same non-`cnode` kind*
  — is the one name both bundles' frames take (`_of_kindPreserving` on each), so
  a widening reaches the scheduler bundle and the capability bundle by
  construction.  Five things new code must respect.

  (1) **A store primitive answers this question BESIDE ITSELF.**  The two
  primitives are `storeObject_kindPreservingWrite` and
  `rewriteObject_kindPreservingWrite`, and every composite reaches them through
  `.trans` rather than through a pointwise walk: the consume, the splice, seL4's
  `reply_remove`, the delivery store, the enqueue, the wake and the donation pop
  each carry one, and each is a few lines because the primitive carries the
  content.  A new store-shaped step states its own on the day it is written.

  (2) **The in-place primitive needs NO side condition, and that is not an
  economy.**  A `rewriteObject` carries its own proof that the key holds an
  object of the replacement's kind *and* that the kind is bookkeeping-neutral
  (`rewriteAdmissible`), and `KernelObjectType.rewriteNeutral` is `false` at
  `.cnode` — so **both** of the store lemma's hypotheses are already inside the
  rewrite's proof argument.  A Tier 3 negative refuses a `cnode` side condition
  coming back, because re-adding one reads as caution and is the statement that
  the admissibility argument was not consulted.

  (3) **The two lifts of one transition take DIFFERENT preconditions, and the
  asymmetry is the claim.**  The capability bundle reads the object store and the
  two CDT tables, all of which the reply chain frames or writes
  kind-preservingly, so `endpointReplyOnCore_preserves_capabilityInvariantBundle`
  and the dispatch's are **unconditional**; the scheduler bundle reads
  `currentOnCore`, and the wake's `queueCurrentConsistentOnCore` preservation
  needs the thread it enqueues not to be that core's current thread, so the
  scheduler lifts carry `hNotCur`.  Both directions are pinned — a positive that
  the scheduler lift has it, a negative that the capability lift does not — since
  a mutation either way keeps every other token.

  (4) **`hNotCur` is stated on the PRE-state, which is where a caller can
  discharge it — and it is STATED rather than derived, which is a gap this cut
  names rather than closes.**  The delivery store frames the scheduler and every
  thread's `cpuAffinity`, so the core the wake enqueues on and the slot it reads
  are the pre-state's; a lift that asked for the post-delivery state would be
  asking a caller about a state it does not hold.  What would *derive* it is a
  **per-core** current-thread-IPC-readiness discipline, and this tree states that
  at the boot core only (`currentThreadIpcReady`); `blockedOnReplyNotRunnable` is
  not it, since it says a reply-blocked thread is not in a run **queue**, which
  `queueCurrentConsistentOnCore` makes compatible with being current rather than
  incompatible.  The single-core `endpointReply_preserves_schedulerInvariantBundle`
  has taken the boot-core form since WS-H1 for the same reason.

  (5) **What remained of row 85 was the CALL chain and the fault composition**,
  and `v0.35.200` closed it — see the next bullet.  The scope was a measurement
  rather than an estimate, and the measurement held: `endpointCallOnCore`'s store
  primitives (`endpointQueueEnqueue`, `endpointQueuePopHead`,
  `storeTcbQueueLinks`, `linkCallerReply`, `linkServerStashedReply`, and the
  delivery store this cut already covers) had **no** CDT frames and no
  `kindPreservingWrite` instances, so each owed the pair this cut wrote for the
  reply side; `endpointCallWithCapsOnCore` then takes the *general* capability
  frame, because `ipcUnwrapCaps` writes CNodes and has its own bundle lemma
  (`ipcUnwrapCaps_preserves_capabilityInvariantBundle_grant`).
- **...and the CALL chain and the FAULT composition close it — where the two
  lifts' preconditions come from, and where a frame LIVES** (WS-RR RR8.16,
  `v0.35.200`, register row 85 **CLOSED**).  The row is named for the fault path,
  and the fault path could not compose what its substrate lacked:
  `faultDeliverOnCore` runs the live cross-core `.call` chain and
  `faultReplyOnCore` the live `.reply` chain.  With `v0.35.199`'s relation and
  this cut's call-side instances both transitions carry the base SMP scheduler
  invariant and the capability invariant bundle.  Six things new code must
  respect.

  (1) **The typed read-modify-write is the one owner for "a TCB rewrite keeps
  every key's kind".**  `SystemState.updateTcb_kindPreservingWrite` needs **no**
  side condition, for the reason `rewriteObject`'s does not, and every write on
  the fault path — the fault record, the restart frame, the `.Inactive` store,
  the four register-context writers, the delivered-message staging — is
  `updateTcb`, so each reaches both bundles through it rather than re-deriving
  the rewrite's admissibility at its own site.  Its `_cdt` / `_cdtNodeSlot`
  siblings sit beside it, and a Tier 3 negative refuses a `cnode` side condition
  coming back.

  (2) **The two lifts' preconditions differ for a reason that is a property of
  the CHAIN, not of a level of it.**  The `.reply` chain's capability lift is
  unconditional at every level; the `.call` chain's is unconditional at the bare
  leg and **reduces** to `ipcUnwrapCaps`'s from `endpointCallWithCapsOnCore` up,
  because that is where the one IPC step that writes a CNode *and* mints CDT
  derivations enters, which `kindPreservingWrite` excludes by construction.  So
  **neither** fault transition owes anything: `faultMessage` carries `caps := #[]`
  and the leg short-circuits on `msg.caps.isEmpty` *before* it resolves the
  receiver's CSpace root, so the delivery composes `…_of_no_caps`, and the reply's
  payload is registers.  The scheduler lifts carry `hNotCur` at every level of
  both chains, stated on the pre-state and *stated rather than derived*, for the
  reason `v0.35.199` recorded.

  (3) **A hypothesis you cannot exhibit is a vacuity, so REDUCE rather than
  import.**  The obvious shape here is to take
  `ipcUnwrapCaps_preserves_capabilityInvariantBundle`'s three externalised
  premises.  The first is **refuted**: `hSlotCap` asks that inserting any
  capability at any slot of any CNode of any bundle-satisfying state keep
  `slotCountBounded`, `cspaceSlotCountBounded` is `≤` so a bundle state may hold a
  CNode at capacity, and `CNode.insert` at a fresh slot grows the table.  A lift
  taking it would hold on no state while its name read as coverage — and that
  lemma's having no consumer since it was written is the corroborating
  measurement.  `ipcUnwrapCapsPreservesCapabilityBundle` is the reduction instead:
  a statement about the *operation*, exhibited by `…_of_noGrant`, so the chain's
  content is *everything else is kind-preserving; the bundle reduces to this one
  step*.  **Ask of any hypothesis you add: what discharges it?**  Pulling on that
  question here surfaced a live **High**-severity defect — no CSpace destination
  slot is validated against the target CNode's radix width at *any* of the four
  capability-insert paths, so one `seL4_CNode_Copy` with a raw out-of-range
  `dstSlot` grows a fixed-size kernel object without bound and falsifies
  `cspaceSlotCountBounded` — which is registered with its end-to-end `#eval`
  measurement rather than described.

  (4) **A composition that resolves its own endpoint takes the STATE-level
  `hNotCur`.**  `endpointReceiveHeadsNotCurrent` — *no endpoint's receive-queue
  head is current on the core its own affinity names* — is what the fault
  delivery takes, since its handler endpoint comes from `resolveFaultHandler`;
  `endpointReceiveHeadsNotCurrent_at` projects it at one endpoint, which is the
  form every rendezvous lift keeps, because that is exactly what each lift needs
  and a caller who knows the endpoint can discharge it there.  The per-core
  `currentThreadIpcReady` discipline retires both.

  (5) **A frame that reads no staged surface is PRODUCTION, and eight of them
  were not.**  The four fault-path `_preserves_objects_invExt` frames and the two
  chain-level ones lived in the staged `IPC/Invariant/FaultPreservation.lean`,
  which is staged for the call chain's staged *`ipcInvariantFull`* bundle — so
  each was out of reach of the production consumer that needed it, which is row
  85's own complaint one level up.  They are beside their operations now, and the
  fault path's two cross-subsystem bundles live in the **production**
  `IPC/Invariant/FaultBundlePreservation.lean` rather than beside the staged
  `ipcInvariantFull` surface of the same transitions.  Two more moved for
  `v0.35.59`'s rule: `ipcUnwrapCaps_getTcb?_eq` was `private` in a cross-core
  *reply* module while framing a model-layer primitive the `.call` leg asks the
  same question of, and the two reply-link `invExt` frames sat above the model
  primitives they frame.  A `private` duplicate of `storeTcbIpcStateAndMessage`'s
  CDT frame was **deleted** rather than kept beside the public one.

  (6) **The donation's lifts sit with the call chain, and the asymmetry with the
  reply pop's is the import graph's.**  `returnDonatedSchedContext` is declared in
  `IPC/Operations/Endpoint.lean`, below both bundle modules, so its lifts are
  beside the bundles; `applyCallDonationOnCore` is declared in
  `IPC/Operations/Donation.lean`, which composes the priority-inheritance walk and
  so sits *above* the scheduler-invariant layer — neither bundle module can name
  it.  Its lifts are therefore in `IPC/CrossCore/EndpointCallDispatch.lean` beside
  the chain that composes them, and the docstring says which fact decides that
  rather than leaving a reader to infer a convention.
- **...and `passiveServerIdle` is preserved by `cancelIpcBlocking` on every arm**
  (WS-OD OD1.5, v0.34.105) — the theorem OD1 exists to prove, and one that was
  *false* before the abort prefix: the reply arm's reclaim could leave a holder
  `.unbound` and still `.blockedOnCall`.  Four things new code must respect.
  (1) **The load-bearing fact is the filter, not a pullback**: every thread a
  cancellation rewrites ends in a state `passiveServerIdle` permits, so
  `passiveServerIdleFrame`'s own `¬ passiveServerIdleAllowed` hypothesis
  discharges it and the pullback fires only on threads the transition left
  alone.  That is why the frame primitive
  (`passiveServerIdleFrame_of_backward_of_not_allowed`) hands the backward
  obligation *both* discriminating hypotheses — the donation return needs the
  `.unbound` one for the caller it re-binds and the filter for the holder it
  unbinds.  (2) **`ipcStateQueueMembershipConsistent` is a hypothesis, and a
  substantive one**: it is what makes the abort *succeed*
  (`abortPendingIpcOnEndpoint_ok` — a thread blocked sending or calling names an
  endpoint that exists), and a refused abort leaves the holder exactly where the
  defect left it.  (3) **The footprint gained three members, not one**: the abort
  *splices*, so `lockSet_cancelIpcBlocking` names the holder's endpoint **and its
  two queue neighbours** (`cancelHolderBlockedEndpoint?`,
  `cancelHolderSpliceNeighbors?`, both resolved from `st` because the holder is
  resolved rather than supplied, and both gated on the abort's own guard).
  (4) **The bound is a case analysis, and since WS-OD OD3.5 an arm-selected
  one**: summed, the resolved footprint carries fourteen members (twelve before
  OD3.7's two below-head reads), and it fits because every resolver keys on
  `tcb.ipcState` — including, since OD3.5, the victim's own splice neighbours,
  which were the one member of the family that did not.  The widest arm is the
  reply arm, at **eight** after OD3.5 and **ten** since OD3.7
  (`lockSet_cancelIpcBlockingOnCore_size_le_ten` then; the live bound is
  `lockSet_cancelIpcBlockingOnCore_size_le_thirteen`); the endpoint arm is four and
  the notification arm two.  Before the OD3.5 split the reply arm declared two
  TCB write locks for a splice it does not perform, which also put it at ten —
  the same number for the opposite reason, so read the theorem rather than the
  figure.  New code adding a cancellation member states the arm it belongs to,
  not the sum.
- **The cancellation teardown IS the reply path's consume** (WS-RR RR8.5,
  v0.35.63).  The tree carried two spellings of "tear down the caller↔Reply
  link": the monadic `SystemState.consumeCallerReply` on the reply paths, and a
  pure pair of raw-insert helpers on the cancellation path, written because
  `cancelIpcBlocking` is a pure composition and could not run a `Kernel` step.
  They had parted on write order and on whether the writes went through
  `storeObject`'s bookkeeping, and every fact about one was proved a second time
  about the other.  Five things new code must respect.  (1) **The survivor is the
  monadic step, and its pure form is a projection, not a second body**:
  `SystemState.consumeCallerReplyLink st caller rid` is the one state
  `consumeCallerReply caller rid st` leaves — defined by matching on the step
  with the `.error` arm *eliminated* by `consumeCallerReply_isOk`, never
  defaulted to `st` — and `consumeCallerReply_eq_link` is the bridge.  A pure
  transition that needs the consume calls the projection; one that re-spells the
  two writes is the defect this closed, and Tier 3 refuses the retired names
  (`clearTcbReplyObject`, `clearReplyObjectCaller`) tree-wide.  (2) **Every
  cancellation-side fact is a corollary through the bridge.**
  `consumeReplyLink st tid tcb` is the projection under the victim's own
  `replyObject`, and `consumeReplyLink_preserves_objects_invExt`, `_tcb_lookup`,
  `_other_tcb_eq`, `_preserves_ipcInvariant`, `_sameSchedContextBindings`,
  `_passiveServerIdleFrame`, `_preserves_donationChainWellFormed` and
  `_preserves_projection_high` all keep their statements and are one application
  of the `consumeCallerReply_*` twin each; a new fact about the teardown is proved
  of the monadic step and read across, never of `consumeReplyLink` directly.  The
  two sharp pointwise readings that made this possible are new —
  `consumeCallerReply_tcb_caller` (the caller's key holds the pre-state TCB with
  `replyObject` cleared and nothing else moved) and `consumeCallerReply_tcb_other`
  (every other TCB-holding key is untouched), stated with no `rid`-distinctness
  hypothesis because the distinctness is derived from the store's contents.  (3)
  **The teardown writes through `storeObject` now, so a definitional lifecycle
  frame across the reply arm is false**: `cancelIpcBlocking_lifecycle_eq` and
  `consumeReplyLink_lifecycle_eq` are deleted rather than given a third
  hypothesis, and a caller needing the metadata across a cancellation needs a
  semantic frame, owed once, about `storeObject`.  (4) **The projection theorem
  reads index completeness**, because the reply path's
  `consumeCallerReply_preserves_projection` needs the (already-present) Reply's
  membership — so `consumeReplyLink_preserves_projection_high` takes
  `objectIndexSetComplete` and the reply arm's composite carries it from the
  return through the splice and the restore
  (`restoreToReadyStaging_preserves_objectIndexSetComplete`,
  `spliceThreadReplyFrameOut_preserves_objectIndexSetComplete`).  (5) **The
  census knows both**: `consumeCallerReplyLink` is a `chainWritePrimitives`
  entry — a pure transition reaching for it bare is WS-RM's defect in the other
  calling convention — and `consumeReplyLink` is registered as a site stating its
  chain result.  What the collapse *measured* and did not fix is the drift it is
  one instance of: sixty executable definitions still wrote the object table
  raw beside `storeObject`, registered with the measurement in
  [`docs/REGISTERED_DEBT.md`](docs/REGISTERED_DEBT.md) table C rather than
  absorbed into an M-sized row — and migrated from `v0.35.64` on, see the next
  bullet.
- **A kernel object is rewritten in place through `SystemState.rewriteObject`,
  and stored through `storeObject`** (`v0.35.64`, the raw-write migration's
  first cut).  The register's remedy for the raw writers — a pure `storeObject`
  projection — was the wrong primitive for the sites that matter: `storeObject`
  filters every capability reference and re-inserts into two more tables on
  every write, and an `RHTable` re-insert of an existing key is not structurally
  the identity without a no-resize hypothesis, so a scheduler tick spelled
  through it would pay on every quantum and every definitional field frame would
  become a conditional theorem.  `rewriteObject st id new h` takes a proof that
  the key holds an object of the **same, bookkeeping-neutral kind**
  (`rewriteAdmissible`, over `KernelObjectType.rewriteNeutral` — every kind but
  CNode and VSpace root, whose contents *are* bookkeeping, enumerated
  constructor by constructor) and its body is the bare insert; the proof is
  erased, so the executable is one table insert.  Five things new code must
  respect.  (1) **A lookup-then-write site is `updateTcb` /
  `updateSchedContext`** — a plain match on the **witnessed lookup**
  `getTcbWitnessed?` / `getSchedContextWitnessed?` (`v0.35.65`: `getTcb?`
  carrying its own equation, `Option { t // st.getTcb? tid = some t }`, matched
  on the store and erased to the value; `getEndpointWitnessed?` /
  `getNotificationWitnessed?` are the endpoint and notification twins since
  `v0.35.74`) whose witness is the rewrite's proof —
  or that witnessed lookup around `rewriteObject` with `rewriteAdmissible_tcb`
  (one such lemma per neutral kind) when the looked-up value is used for more
  than the write; never a raw `objects.insert`, and never a dependent
  `match h : st.getTcb? tid with`: a dependent matcher's discriminant occurs in
  its own motive, so no consumer proof can rewrite it, and `v0.35.64`'s
  `updateTcb` was spelled that way for exactly one cut.  A Tier 3 negative holds
  the migrated files to it.  (2) **A key that may hold nothing, or a CNode or VSpace
  root, is a store**: `storeObject` in a `Kernel` step, `withObjectStored` in a
  pure transition — the RR8.5 projection with the error arm eliminated by
  `storeObject_isOk`, bridged by `storeObject_eq_withObjectStored`.  (3) **The
  bookkeeping is unchanged by theorem, once**:
  `rewriteObject_preserves_objectIndexSetComplete`,
  `rewriteObject_preserves_objectIndexLive`,
  `rewriteObject_preserves_objectIndexBounded`,
  `rewriteObject_preserves_objectIndexSetSync`,
  `rewriteObject_preserves_objectTypeMetadataConsistent` in `Model/State.lean`,
  `rewriteObject_preserves_asidTableConsistent` in
  `Architecture/VSpaceInvariant.lean`, `rewriteObject_preservesFieldsOutside`
  against the one-field `rewriteObject_modifiedFields` in
  `Kernel/CrossSubsystem.lean`, and `rewriteObject_eq_objects_update` for any
  field with no named frame — each instantiated on `updateTcb` and
  `updateSchedContext`.  A site proof reaches for these rather than re-deriving
  the fact from `RHTable.insert_preserves_invExt`.  (4) **The proof recipe is
  two equations**: `cases hT : st.getTcb? tid`, then `updateTcb_eq_of_some hT`
  or `updateTcb_eq_self_of_none hT`, and the old proof continues verbatim;
  `updateTcb_getTcb?_self` is the read-back.  A site that matches on the
  witnessed lookup itself reduces under `simp only [site,
  getTcbWitnessed?_eq_some hT]` (or `_eq_none`), and after a `split` its arm
  carries **three** inaccessibles — the value, the witness, the match equation —
  so it is `rename_i tcb hTcb _`, never the two-name `next tcb _` of the old arm,
  which binds the witness to the value's name and fails one line later at the
  record update; `rewriteObject_objects` exposes the insert to a proof that
  reads the table directly.  **The case split precedes the unfold**
  (`v0.35.66`): `cases hT : st.getTcb? tid` over a goal that already holds the
  unfolded witnessed match fails to generalise, because the lookup's *type*
  mentions `st.getTcb? tid` — so a proof cases on the typed lookup first, then
  unfolds the site and rewrites with `getTcbWitnessed?_eq_some hT` /
  `_eq_none hT`; a hypothesis `hStep : site st = .ok …` is rewritten the same
  way and then `dsimp only [SystemState.rewriteObject] at hStep` restores the
  literal the old proof read.  (5) **A twin migrates with its
  original.**  `cancelBoundDonationOnCore` is held to `cancelBoundDonation` by a
  `rfl` bridge, so it moved in the same cut; the private copy of
  `restoreToReadyOnCore`'s prefix that `PriorityInheritance/PerCore.lean` pinned
  by `rfl` was deleted instead, and the operation is now *defined* through the
  public `restoreToReadyMidState` — a pin between two spellings of one prefix is
  the signal to make one of them the definition.  The R5.D shim
  `clearTcbIpcFields` and its theorems went in the same cut, having no consumer.
  The same signal closed the single-thread PIP boost update at `v0.35.66`:
  `updatePipBoost` and `updatePipBoostOnCore` were two copies of one body
  differing in the literal core, held together by an `rfl`, so the single-core
  name is now *defined* as the per-core update at `bootCoreId` and
  `updatePipBoost_eq_updatePipBoostOnCore_bootCore` stays as the equation
  consumers rewrite with — definitional, and still the fact that the two cannot
  diverge.  What is still raw is registered with its measurement (65 sites in 52
  executable declarations across 22 files after `v0.35.64`; 60 in 47 across 22
  after `v0.35.65` moved the scheduler's context-save family —
  `saveOutgoingContext`, `saveOutgoingContextChecked`,
  `saveOutgoingContextOnCore`, `preemptCurrentOnCore` — and
  `setThreadCpuAffinity`; **53 in 41 across 20** after `v0.35.66` moved
  `enqueueRunnableOnCore`, `updatePipBoostOnCore`, `timerTick`,
  `refillSchedContext` and `handleYieldWithBudget`; **43 in 37 across 17** after
  `v0.35.67` moved `timerTickBudget`, `timerTickBudgetOnCore`,
  `enqueueIdleThreadOnCore` and the trace model's `stepPost`; unchanged at
  `v0.35.68`, which migrated no site but *derived* the boot's idle install from
  `enqueueIdleThreadOnCore`, so the boot performs no raw write of its own
  through it; **39 in 33 across 15** after `v0.35.69` made the four
  register-context writers — `writeReturnFrameToTcb`, `writeRestartFrameToTcb`,
  `writeFfiRegistersToTcb`, `writeFaultRegistersToTcb` — the `updateTcb` each
  already had the shape of; **32 in 26 across 13** after `v0.35.70` moved the
  fault path's seven — `recordPendingFault`, `applyFaultRestart`, the four
  fail-closed dispositions over their deschedule, and `installFaultHandler`
  taking the store's witness for the TCB it is handed; **19 in 19 across 10**
  after `v0.35.71` moved the SchedContext operations and the priority
  management — `updatePrioritySource`, `setMCPriorityOp`,
  `setMCPriorityOnCore`, `schedContextConfigureBoundPropagate`,
  `schedContextBind`, `schedContextUnbind`, `schedContextYieldTo`; **16 in 16
  across 8** after `v0.35.72` moved the cross-core suspend's G6, the revoke
  sweep's step and the destroy path's origin scrub — `suspendThreadOnCore`,
  `revokePendingTransfersStep`, `clearDonationOriginReferences`; **9 in 9
  across 6** after `v0.35.73` made the seven inhabitation witnesses the
  store on each fresh key and the rewrite on the bind's two in-place writes
  — `witnessSt1`–`witnessSt4`, `chainWitnessSt1`, `chainWitnessSt2`,
  `donationChainWitness`; **5 in 5 across 4** after `v0.35.74` moved the two
  queue sweeps — `removeFromAllEndpointQueues`,
  `removeFromAllNotificationWaitLists` — onto the witnessed lookup around
  `rewriteObject`, and those five are the primitives that should be raw:
  `storeObject`, `rewriteObject`, `Builder.createObject`, `updateObjectAt`
  and the frozen store, so the executable population outside them is
  **zero**; since `v0.35.75` the trace harness's 61 fixture inserts are
  stores too, so over the whole `SeLe4n/` tree the only raw writes in the
  spellings that census recognises are those five and the reply-stack
  census's planted witness — and since `v0.35.76` that is **enforced**:
  `STORE_WRITE_CODE` is a Tier 0 `ZERO_METRICS` entry, those six bodies are
  `WRITE_PRIMITIVE_BODIES`, reconciled in both directions, and a raw write
  reappearing in an executable position fails on the day it is written.
  **Six executable writes and four reads are outside those spellings** and
  were outside this ledger until `v0.35.117` measured them: a declaration
  that holds the object table through a binding or a parameter is invisible
  to a pattern keyed on the receiver text `.objects`, and three of them do
  — see *both zeros are over the DIRECT spellings* in the key-conventions
  section above for the population, the floor that now reports it, and the
  named architecture for driving it to zero).  At `v0.35.77` (D2)
  `storeObject`'s capability-reference maintenance became an erase over the
  displaced CNode's populated slots rather than a filter over the whole
  table, and the register row was **closed**; what landing it found — the
  table was read by no executable code, and `capabilityRefMetadataConsistent`,
  the invariant named for it, read the object store instead, so it was
  definitionally true and its `storeObject` preservation proof consumed no
  hypothesis — is closed at `v0.35.78` by **retiring the table** (the
  *capability-reference table* bullet below).  (6) **A transition that rewrites a TCB it is
  handed takes the store's witness for it.**  `timerTickBudget` /
  `timerTickBudgetOnCore` (`v0.35.67`) take `(hTcb : st.getTcb? tid = some tcb)`
  beside the TCB — the proof `rewriteAdmissible_tcb` consumes, erased at runtime —
  so a caller cannot charge a TCB the store does not hold (both suites did, with a
  TCB fabricated at an unstored id, and the tick then wrote it into the store);
  every caller resolves the thread through `getTcbWitnessed?` and hands the
  witness on.  A consumer statement carries it as an implicit
  `{hW : st.getTcb? tid = some tcb}` beside its `hStep` — positional applications
  are unchanged, and a pre-state hypothesis of the same type stays revertible,
  the two being interchangeable by proof irrelevance — an arrow-chain hypothesis
  names its binder (`∀ (hTcb : …), timerTickBudgetOnCore … tcb hTcb = .ok … → …`),
  and a `split` on the witnessed SchedContext match yields three inaccessibles,
  `rename_i sc hSc _`, in the bullet form as well as the bare one.  (7) **A
  dependent match lives in a definition whose state is a parameter, never inline
  under a `let`.**  Lean elaborates a `let` whose body's type does not depend on
  it as a `have`, and a dependent match — one whose alternative's type names the
  scrutinised state, which every witnessed lookup is — under a `have` binder, or
  over a stuck projection, is opaque to definitional unification: two spellings
  of one match tree unify only when the state is a variable.  Measured
  (`v0.35.67`, eleven isolated experiments): with the witnessed lookup inline,
  `timerTickOnCore_eq_prepared`'s `rfl` failed on every restatement but a
  verbatim copy of the body, a phase definition over the prepared triple failed
  the same way, and a `split`-based proof splits the two sides independently.
  `timerTickChargeCurrentOnCore` is the shape — the dependent match over a
  parameter, the tick's own match tree non-dependent, the equation `rfl` — a
  consumer reads through `timerTickChargeCurrentOnCore_eq` / `_none` / `_ok`,
  and Tier 3 refuses any lookup coming back into the tick's body.  (8) **A
  transition that rewrites two objects performs the first under the witness
  its own lookup carries and the second through the typed read-modify-write
  over the rewritten state** (`v0.35.71`).  A witness taken at the pre-state
  does not carry across a rewrite without `invExt`, which executable code has
  no proof of — so `schedContextBind` writes the SchedContext through
  `rewriteObject` under `hSc` and then the TCB through `st1.updateTcb`, and
  the lambda's record is the stored one with its fields moved, which is what
  the raw insert wrote from the pre-state lookup on every state the two
  lookups admit.  The proofs reduce the pair once, from the pre-state's
  witness and `invExt` (`updateTcb_after_rewriteObject_schedContext` and its
  three siblings), on the lemma library that makes the reduction a fact
  rather than a case split: a SchedContext rewrite is invisible to every TCB
  lookup at *every* key (`rewriteObject_schedContext_getTcb?` — at the key
  itself the admissibility witness says it held a SchedContext, so no TCB
  lookup read it), the twin, the typed read-modify-writes inheriting both,
  and the keys of two typed witnesses distinct with no invariant consulted
  (`getTcb?_getSchedContext?_keys_distinct`).  Where the second write sits on
  a state that is a scheduler-only update of the pre-state, the stage is
  spelled `{ st with scheduler := … }` so its object table is the pre-state's
  *definitionally* and the witness needs no transport at all
  (`schedContextUnbind`).  Two things that cut measured.  A `_` field in a
  `{ s with x := _ }` pattern is filled from `s`, not left as a hole, so a
  reduction whose base state must be read off the goal is applied with
  `exact` rather than `rw`.  And a hypothesis a raw insert needed can be one
  the typed rewrite makes false to need:
  `updatePrioritySource_donated_preserves_donor_schedContext` lost
  `tid.toObjId ≠ scId.toObjId`, because the rewrite fires only at a key
  holding a TCB and reaches no SchedContext at any key — the one way that
  security statement could have been vacuous is gone with the hypothesis.
- **There is no capability-reference table** (`v0.35.78`, closing the row
  `v0.35.77` registered).  `LifecycleMetadata` is the object-type table alone,
  `lifecycleInvariantBundle` is `objectTypeMetadataConsistent` under two names
  (`lifecycleIdentityTypeExact`, `lifecycleIdentityAliasingInvariant`),
  `IntermediateState.hLifecycleConsistent` is that predicate of the builder
  state, and a slot's target is read through `lookupSlotCap` — the one
  slot-target reader, `O(1)`, which yields the whole capability.  The register
  row's remedy said *wire or retire, and the rule says wire*; the decision was
  **retire, on measurement**.  `lookupCapabilityRefMeta`, the reader the table
  was named for, had been `(lookupSlotCap st ref).map Capability.target` since
  the repository's root, so no executable code had ever read the table; every
  slot-target query in the tree holds or fetches the CNode already; the one
  consumer the remedy proposed — a revocation sweep over a *target* — is a
  target→slots question a table keyed by slot cannot answer; the boot builder
  installed populated CNodes without ever populating it; the frozen mirror
  never maintained it; and every CNode store paid a fold over the CNode's slots
  for it.  A cache nothing reads is not a cache, and *implement the
  improvement* has no improvement to implement when no reader can be named.
  Four things new code must respect.  (1) **A conjunct whose proof consumes
  no hypothesis is deleted, and so is everything stated over it**:
  `capabilityRefMetadataConsistent`, the bundle-of-one
  `lifecycleMetadataConsistent`, the lifecycle capability-reference and
  stale-reference families (`lifecycleCapabilityRefExact` through
  `lifecycleIdentityStaleReferenceInvariant`), the capability layer's
  `lifecycleCapabilityStaleAuthorityInvariant`, the policy surface's
  owner-authority implication (`policyOwnerAuthorityRefRecorded →
  policyOwnerAuthoritySlotPresent`) and the builders' `withLifecycleCapabilityRef`
  — each an instance of `x = x`, of lookup determinism or of
  `objectTypeMetadataConsistent` — with Tier 3 refusing every name tree-wide.
  (2) **`storeObject`'s lifecycle write is the object-type insert alone**, so
  a CNode store is `O(1)` on the lifecycle side rather than a fold over its
  slots, and `allTablesInvExtK` is **sixteen** conjuncts: the positional
  projections in `Builder.lean`, `Boot.lean`, `FreezeProofs.lean` and
  `IdleEnqueue.lean` shifted by one at every position past the sixth, which
  is the fragility their docstrings already record.  (3) **The capability
  operations store once**: `cspaceInsertSlot`, `cspaceRevoke` and
  `cspaceMutate` end in `storeObject`, `cspaceDeleteSlotCore` in the store
  then `detachSlotFromCdt`; the second writer `storeCapabilityRef` and the
  fused `revokeAndClearRefsState` are gone, and a proof over one of these
  operations is one `storeObject_*` frame lemma rather than a composition of
  two.  (4) **The one substantive fact the layer had restated is owned where
  it always was**: a reply cap is backed iff its Reply resolves, which is the
  capability layer's step-preserved `replyCapPointsToValidReply`, exhibited
  by `replyCapPointsToValidReply_distinguishes_backed_and_dangling`.
- **A state-resolved thread is descheduled where the state PLACES it** (WS-RR
  RR8.6, `v0.35.79`).  `descheduleThread`, `cancelIpcBlockingOnCore` and
  `suspendThreadOnCore`'s G4 removed a victim at `determineTargetCore` — its
  *home*, which is where a wake places a thread and not where a removal finds
  it: `preemptCurrentOnCore` re-enqueues a preempted thread on the core that ran
  it, and an unpinned thread may run on any core, so a `.tcbSuspend` on an
  unpinned thread preempted on a secondary core marked it `.Inactive` and left
  it in that core's run queue.  Five things new code must respect.  (1) **One
  primitive, one resolver**: `descheduleAt st tid placed` removes at a
  pre-resolved placement and `descheduleAtPlacement st tid` *is*
  `descheduleAt st tid (placedCoreOf? st tid)`; a transition that must declare
  its footprint before it runs captures `placedCoreOf?` on the pre-state and
  removes through `descheduleAt` (the suspend), one that acts after other steps
  resolves at the state it acts on through `descheduleAtPlacement` (the reply
  path, the cancellation composite).  Tier 3 refuses `determineTargetCore` and a
  bare `removeRunnableOnCore` inside each of the three declarations.  (2) **The
  poke reads the same placement** (`descheduleSgi?`): the placed core, when the
  thread is current there and it is not the executing core — and no object.
  The wake's ghost-guard is not mirrored, because a removal takes a placed thread
  off its core whether or not a TCB backs it, so a guard on the TCB would clear a
  slot and poke nobody.  (3) **The composite is `descheduleThread` on the
  reclaim's post-state by `rfl`**, and the footprint is declared on the
  pre-state; `cancelIpcBlockingReclaimed_placedCoreOf?_victim` is the relation
  (the victim's post-reclaim placement *is* the pre-state's — an equation since
  `v0.35.158`, where the wake's degenerate self-insert had left it a
  disjunction) and `cancelIpcBlockingOnCoreSchedLockSet_covers_deschedule` is
  its payoff.  (4) **The scheduler footprints take the placement**:
  `descheduleThreadLockSet (placed : Option CoreId)`,
  `cancelIpcBlockingOnCoreSchedLockSet (placed holderPlaced : Option CoreId)`,
  and `suspendThreadOnCoreSchedLockSet (home
  executingCore ownerHome outerHome : CoreId) (placed : Option CoreId)`, whose
  run-queue segment is a *pair* over the placed and executing cores — the home
  stays a replenish member, since the `.bound` arm's purge is keyed on it, and
  the running core needs no member of its own.  (5) **A theorem about a
  deschedule is stated at the placement, never at the home**:
  `descheduleThread_fully_descheduled` takes single placement (which the
  scheduler maintains by construction) where it took the home-placement
  discipline (false of exactly the thread the defect is about), and
  `suspendThreadOnCore_sgi_remote_reschedule` concludes `runningCoreOf? = some c`
  because a victim current nowhere now falls back to the executing core, where
  no SGI can arise.  The retired reading survives in one place,
  `tests/SmpCancellationSuite.lean` §3.24's `retiredHomeAndRunningDeschedule`,
  computed beside the live one on the queued-off-home shape.
- **A donation pop's deschedule names the thread the pop UNBOUND** (PR #897
  review, `v0.35.149`).  Every production pop makes the answered frame's head
  context's own `boundThread` `.unbound`, and the step that follows must be about
  *that* thread: `applyReplyDonation` and `applyReplyDonationOnCore` always were,
  and `replyRecvPostReceiveDonation` was not — it descheduled
  `recordedReplyServer?`, the server the answered caller recorded when it
  *Called*.  WS-HP HP4 (`v0.35.38`) repointed the **trigger** onto the frame and
  left the **deschedule** on the binding-era proxy; HP6.8 (`v0.35.45`) is what
  makes the two disagree, because a spliced middle caller leaves an **orphan
  head** whose context is bound to a thread the caller never recorded.  Measured
  on the live `replyRecvBody`: the holder ended `.unbound` and still queued
  (`hasSufficientBudget` is unconditionally `true` for an unbound thread, so it
  runs at its legacy TCB band charged to no reservation — PR #895 round 8's
  defect on the sibling site that round did not sweep), while a bystander still
  holding its own reservation was taken off its run queue and left `.ready`,
  which WS-OD OD1.7 enumerates as unrecoverable.  Four things new code must
  respect.  (1) **The holder travels inside the arm selector**:
  `replyRecvPopDonation` answers `Option (SchedContextId × ThreadId)`, so a
  consumer cannot hold the context and the holder apart and hand the deschedule a
  different thread; `replyRecvPopDonation_holder_eq_frameHead` is the relation,
  and `replyRecvServerDeschedule` / `replyRecvPoppedContext` are refused
  tree-wide.  (2) **Two threads, two questions**: both deschedule arms name the
  holder and both chain walks keep `recordedServer`, because the walk keys on
  waiters rather than on donations (WS-HP HP7's reason for keeping that
  resolver).  (3) **The idle-state obligation moved with the thread** —
  `hHolderIdleAllowed`, conditioned on the pair the pop returned rather than
  stated unconditionally at a proxy, in the transition's own theorem and in both
  dispatch packs.  (4) **The cancellation reclaim deschedules too, since
  `v0.35.158`** — it was the one pop that ENQUEUED (WS-OD OD1.7), on the
  reasoning that `abortPendingIpcOnEndpoint` stages `Architecture.timeoutFrame`
  into the holder's register context (WS-RR RR7.14) and the kernel owes it a
  delivery it can only observe by running.  It still owes it, and the frame still
  waits in the register context; what changed is *who* pays for the run — the
  holder's next reservation, through its manager's resume or a bind, rather than
  nobody's budget.  All four production pops now take the thread they unbind off
  its placement (`descheduleUnboundHolder`); see the bullet below for what is
  left.
- **A reclaimed holder no longer runs unbudgeted — the reclaim parks it**
  (PR #897 review, `v0.35.149`; the reclaim half **closed at `v0.35.158`**, the
  bind half WS-CB's).  `.unbound` in this kernel means *both* "MCS-passive" and
  "legacy time-sliced at `tcb.priority`": `hasSufficientBudget`'s `.unbound` arm
  is `true` by design, `timerTickBudgetOnCore`'s refills `configDefaultTimeSlice`
  forever, and `schedContextUnbind` deliberately re-buckets an unbound thread.
  So a reclaim that returned the reservation *and* left the holder placed handed
  it the CPU on nobody's budget — measured on the live `suspendThreadOnCore`
  at `v0.35.149`: after a `.tcbSuspend` of a reply-blocked client whose donated
  context was held by a server blocked on a nested call, the server ended
  `.unbound`, `.ready`, **on its home core's run queue**, `hasSufficientBudget =
  true`, at its own TCB band, selected by `chooseThreadOnCore`; and a server
  merely *queued* on the donated context stayed queued, unbound, because OD1.7's
  wake declined a placed thread.  `passiveServerIdle`'s antecedent is *not
  queued*, so a runnable unbound thread satisfied it vacuously — PR #895 round
  8's rule, on the conjunct that rule was written about.  Since `v0.35.158` the
  reclaim takes the holder it unbinds off the scheduler
  (`descheduleUnboundHolder`, the bullet on the reclaim above) and
  `suspendThreadOnCore_holder_unplaced` carries that to the end of the live
  pipeline, so a suspension of the *client* — authority over the client, none
  over the server — no longer puts the server outside CBS admission.  What it
  costs is stated: a passive server whose client is suspended while it services
  the request is parked `.ready`, `.unbound` and unplaced until its own manager
  resumes it or a reservation is bound to it, which is the MCS-passive reading
  and the one every other pop takes.  **And since `v0.35.182` (Cut B2) the bind
  is that manager's recovery**: `schedContextBind` places a parked runnable
  thread on its home core, which is seL4-MCS's `schedContext_bindTCB` tail
  (`if (isSchedulable(tcb)) { SCHED_ENQUEUE(tcb); rescheduleRequired(); }`, read
  at `13.0.0`) and which this kernel did not do — it re-bucketed only a thread
  already queued, so what the reclaim parked stayed parked.  Four things new
  code must respect.  (a) **The guard is `bindPlacesParkedThread`**, four
  conjuncts excluding a placed thread, a thread blocked in IPC, a suspended one
  and — since `v0.36.1`, (d) below — a reservation with no budget left, and its
  third reads the **stored** `threadState` rather than `inferThreadState` —
  which answers `.Inactive` for *any* unplaced, unblocked thread, so the
  inferred reading would refuse exactly the parked shape the guard exists to
  admit.  (b) **The declared footprint did not move**: its run
  segment was already the bound thread's home core, which is the core the
  placement inserts on — a declaration written for the *operation* rather than
  for the branch it happened to take is what makes a behavioural widening free,
  and both that footprint's docstring and its coverage theorem's, which
  predicted a widening, are corrected rather than left standing.  (c) **The
  frozen mirror is swept through a bind-specific writer**
  (`frozenWriteTcbBoundPlaced`), never by widening `frozenWriteTcbRebucketed`:
  that one's other callers are priority writes, and a priority write must not
  make a parked thread schedulable — only a bind, which hands the thread a
  reservation, may.  (d) **A bind places a thread only on a reservation that can
  run it** (PR #900 review, `v0.36.1`).  The fourth conjunct is
  `sc.budgetRemaining.isPositive` of the reservation being bound, which is the
  selector's own reading — `hasSufficientBudget` of a bound thread *is* that
  (`bindPlacesParkedThread_budget_eq_hasSufficientBudget`) — and seL4-MCS's:
  `isSchedulable` requires an active context and `schedContext_resume` postpones
  a thread whose refill is not ready, both read at `13.0.0`.  Without it a
  reservation exhausted mid-period, then unbound — which keeps `budgetRemaining`
  and purges the per-core replenish entry — and rebound to a parked thread put
  that thread on a run queue the selector skips forever, since nothing is left
  to refill it; `budgetPositiveOnCore` was false on the bind's post-state and
  the bind reported success.  With it the thread stays parked
  (`schedContextBind_leaves_unplaced_of_exhausted`), and the frozen mirror
  (`frozenBindPlacesParkedThread`) carries the same conjunct.  **What it does
  not do is postpone**: seL4 re-derives the refill trigger at every
  `schedContext_resume`, and this kernel re-derives it nowhere, so the parked
  thread waits for its manager (unbind, configure, rebind), and the same
  trigger-less state is reachable through the re-bucket arm, a resume of a
  bound thread and a configure that places nothing — all inherited from `main`,
  registered in `docs/REGISTERED_DEBT.md` table C, owner WS-CB.  New code must
  not read a successful bind as evidence that the thread will run.

  **One instance of the class remains**, measured by the post-merge audit
  (`v0.35.156`): a plain-`Send` rendezvous is decided by the two readings on two
  arms — `.replyRecv`'s non-`Call` arm deschedules the holder the pop unbound
  (the MCS-passive reading, so a passive server handed a plain `Send` is parked
  `.ready`, `.unbound` and unplaced), while a `.receive` by an already-unbound
  running thread leaves it current on a plain `Send` (the legacy reading).  That
  is the WS-CB row in `docs/REGISTERED_DEBT.md` table C; it is not a soundness
  gap, and it is not fixed here because it is the passive/legacy split that row
  names rather than a footprint or a placement.  **v1.0.0 may claim, since
  `v0.35.158`, that no client suspension hands a server the CPU on nobody's
  budget, and since `v0.35.182` that a parked passive server is recovered by
  binding it a reservation.**
- **A bare reply's post-state does not satisfy `donationOwnerValid`.**
  `endpointReply` wakes the answered caller `.ready` while the recorded server
  still holds `.donated _ caller`; the donated SchedContext comes back only at
  the next stage, because the server needs that budget *while* it replies (the
  AUD-3 ordering).  The honest statement about that state is
  `ipcInvariantFullExceptDonationOwner st target` — the bundle with
  `donationOwnerValid` relaxed at the woken caller — which
  `endpointReply{,OnCore}_preserves_ipcInvariantFullExceptDonationOwner`
  establishes unconditionally, and which the donation return upgrades back
  (`returnDonatedSchedContext_establishes_donationOwnerValid_of_except`).  The
  composite that covers the whole chain is
  `endpointReplyCrossCoreDispatch_establishes_ipcInvariantFull`.  New code must
  not assume `ipcInvariantFull` of a state between a reply and its donation
  return, and must not add a bundle theorem that threads `donationOwnerValid` on
  such a state: it would be vacuous rather than conditional, which is how the
  nine pre-RR3.12 reply bundles asserted nothing on the ordinary seL4-MCS path.
- **...and the bare reply and the leg the kernel dispatches disagree about
  delegated authority** (PR #895 review round 22).  `endpointReplyOnCore` dropped
  the `replier == expected` gate at PR #822 review 6J-lYm — authority is the
  presented reply capability, which the dispatch resolves, and seL4-MCS reply
  caps are delegatable — while the **bare** `endpointReply`, `endpointReplyRecv`
  and the single-core `endpointReplyWithDonation` that composes the first still
  carry it.  The live `.reply` arm routes through
  `replyTransferOnCoreChecked` → `endpointReplyCrossCoreDispatch`, so **the
  kernel admits a delegated reply-cap holder and the single-core composites
  refuse one**, whatever `endpointReplyOnCore`'s "mirrors the single-core
  `endpointReply`" wording suggests.  Two things new code must respect.  (1) The
  divergence is pinned in both directions —
  `endpointReplyCrossCoreDispatch_independent_of_replier` (every use of `replier`
  is the unused `_replier`, so a delegate gets the non-delegated behaviour) and
  `endpointReplyWithDonation_refuses_delegated_replier` — so a coverage claim, a
  refinement or a mirror must name *which* spelling it is about; `frozenBranchLiveLeg`
  and `frozenBranchLiveOperation` carry the frozen surface's counterparts as data
  for exactly that reason.  (2) The direction is fail-**closed** (legitimate
  authority declined, never illegitimate authority admitted) and the single-core
  composite has no production caller, so this is a divergence to respect rather
  than a hole; giving the question one answer is registered debt.
- **A bare endpoint splice's post-state does not satisfy
  `ipcStateQueueMembershipConsistent`.**  `endpointQueueRemoveDual` takes a
  thread out of its endpoint queue and deliberately does **not** touch that
  thread's `ipcState`; the composites that use it write it in their very next
  step (the bound delivery makes it `.ready`).  So the honest statement about
  that state is `ipcInvariantFullExceptMembership st' tid` — the bundle with the
  membership conjunct relaxed exactly at the removed thread — which
  `endpointQueueRemoveDual_establishes_ipcInvariantFullExceptMembership`
  (`IPC/Invariant/QueueSplicePreservation.lean`) establishes from
  `ipcInvariantFull`.  It stands to the splice as
  `ipcInvariantFullExceptDonationOwner` stands to the bare reply, and new code
  must not state a splice bundle threading the **full** membership conjunct on
  the post-state: that would be vacuous rather than conditional.  Three further
  things the module fixes in place.  (1) **The four-branch case analysis is
  derived once**, as `SpliceShape`: which program `endpointQueueRemoveDual` is
  depends on whether the removed thread is the queue head and whether it has a
  successor, and that is a property of the *operation*, not of the conjunct — a
  new conjunct proof consumes the four branches rather than re-running `unfold`.
  (2) **One conjunct genuinely does not follow from the bundle**:
  `splicePredecessorBlocked`, the fact that a predecessor promoted to tail is
  blocked on that endpoint.  `queueNextTargetBlocked` propagates blockedness
  *forwards*, the head conjunct constrains only the head, and link integrity
  says nothing about `ipcState` — so it is stated, vacuous when the removed
  thread is the head, and discharged from a reachability witness through
  `spliceSideBlocked_along_path` (*every thread reachable from a queue head is
  blocked on that endpoint* — the fact `queueNextTargetBlocked`'s own docstring
  promised and nothing stated).  (3) **`endpointQueueNoDup` is a consequence,
  not an obligation**: `endpointQueueNoDup_of_dualQueue_of_headBlocked` derives
  it from the dual-queue invariant and the head conjunct, so a transition need
  not re-establish it separately.
- **A woken caller's post-state does not satisfy `replyCallerLinkage`, and
  asking for the full bundle *and* the wake is asking for nothing** (WS-RR
  RR8.7, `v0.35.80`).  The third relaxed view, and the one whose absence had
  produced two **vacuous** production theorems.
  `consumeCallerReply_preserves_ipcInvariantFull` and
  `removeCallerReplyFrame_preserves_ipcInvariantFull` each took
  `ipcInvariantFull st` together with "st's answered caller is not
  `.blockedOnReply`", and `replyCallerLinkage`'s second direction refutes that
  pairing outright — a stored Reply naming a caller obliges that caller to be
  reply-blocked, so the bundle *entails* that no woken thread is still named.
  Their premises held on **no state**; they asserted nothing while their names
  read, in a bundle search, exactly like coverage.  Six things new code must
  respect.  (1) **The refutation is pinned, permanently**:
  `replyCallerLinkage_refutes_woken_linked_caller` derives `False` from the two
  premises, is consumed by nothing, and is anchored in Tier 3 for that reason —
  a refutation nothing states is one the next cut re-discovers by shipping the
  defect again.  Two Tier 3 negatives refuse both retired spellings tree-wide,
  each mutation-tested by reintroducing the name as **code** (the tombstones
  mention them in prose, which the code view strips, so the clean tree
  exercises the other direction).  (2) **The relaxation is the narrowest one
  that admits the state.**  `replyCallerLinkageExcept st woken` still requires
  the reciprocal pair to *exist* at the woken thread — the Reply resolves and
  the thread names it back — and drops only the blocking clause, written as a
  **disjunct** (`tid = woken ∨ ∃ ep rt, …`) rather than by excusing the thread
  from the clause.  Excusing it would drop the pair too, and the pair is
  precisely what the teardown reads.  (3) **The unit is the pair, not either
  half.**  `restoreToReadyStaging` wakes the victim and so *breaks*
  reciprocity, leaving `ipcInvariantFullExceptReplyLinkage` and nothing
  stronger; the teardown alone would break the third clause, since it clears
  `replyObject` without unblocking.  Each is the other's repair, so
  `restoredAndConsumed` — the composition the reply arm performs — is what
  carries the full bundle (`restoredAndConsumed_preserves_ipcInvariantFull`), and
  a claim taken at either half is a claim about a state the arm does not rest
  at.  (4) **A relaxed view is registered with the de-threading gate**, in
  `PRE_STATE_PREDICATES`, longest-prefix-first — otherwise the gate reads the
  relaxed bundle's own hypothesis as a threaded post-state conjunct.  (5) **The
  removal's own bundle statement is the *relaxed* one, and since `v0.35.188` it
  exists** (`removeCallerReplyFrame_establishes_ipcInvariantFull_of_exceptReplyLinkage`).
  What it needed was a **unit** at which the relaxation could be transported:
  `replyCallerLinkageExcept` was a flat triple, so no `replyLinkageFrame` could
  carry it and the splice would have had to re-run the full store's case
  analysis.  It is now split exactly as `replyCallerLinkage` is — the reciprocal
  pair (`replyCallerLinkageReciprocalExcept`) and `blockedOnReplyHasReplyObject`
  — so `replyCallerLinkageReciprocalExcept_of_frame` is its full sibling one
  strength down, and the store's own frame member
  (`storeObject_reply_caller_replyLinkageFrame`, which the family lacked because
  its neighbour excludes a Reply on purpose) carries it.  Three things new code
  must respect.  **Everything but the reciprocal pair is proved once**
  (`storeObject_reply_stackLinks_preserves_nonReciprocal`) and assembled twice,
  because the two bundles differ in the pair and nowhere else.  **The splice's
  store chain has one owner** (`spliceReplyFrameOut_transport`, over any
  predicate a caller-preserving Reply store carries): which stores run, in what
  order, with which lookups surviving between them is a fact about the
  *operation*, and a second copy per bundle is how the two would come to disagree
  about it.  And **the composite's hypotheses are all about the state the removal
  runs on** — the answered Reply's survival and the woken caller's TCB's are
  discharged inside it, not pushed onto a caller reasoning about a state the
  operation does not rest at.  Its premises are jointly satisfiable and that is
  *exhibited*: `restoredAndConsumed_preserves_ipcInvariantFull` already supplies
  the relaxed bundle and the caller's non-`.blockedOnReply`-ness at one state,
  which is exactly the pairing the deleted theorem could not have.
  (6) **The class was named at `v0.31.154` and not swept.**
  `REPLY_OBJECTS_COMPLETION_PLAN.md`'s own landed note re-based
  `linkCallerReply_preserves_ipcInvariantFull` because "full `ipcInvariantFull
  st` would be *vacuous* at a link site" — and left the sibling `consumeCallerReply`
  threading the post-state, one clause away, with the same contradiction
  available.  RR8.5 then turned that post-state threading into a *pre*-state
  hypothesis, which moved the vacuity from the conclusion into the premises
  rather than removing it.  **When a cut records that a bundle would be vacuous
  at one site, ask the same question of every operation that writes the same
  field** — and note that de-threading a conjunct can *preserve* a vacuity by
  relocating it.
- **The `.call` chain's IPC bundle is staged; every other live-arm bundle is
  production.**  RR2 (v0.34.42) gave the transitions behind `Kernel/API.lean`'s
  SMP dispatch `_preserves_ipcInvariantFull` theorems, and the RR2 closure audit
  split them by what they actually read: only
  `endpointCallCrossCoreDispatch`'s bundle
  (`SeLe4n/Kernel/IPC/CrossCore/DispatchInvariant.lean`) composes the staged
  `EndpointCallInvariant` surface and is staged with it — CI builds it on every
  PR through `Platform.Staged`; a linked kernel image does not.  The `.reply`
  chain's (`IPC/CrossCore/EndpointReplyDispatchInvariant.lean`), the
  priority-inheritance walk's (`IPC/Invariant/DonationPreservation.lean` §8),
  the send/receive/stash/wait and `replyRecvReturnDonation` bundles are all
  production (`EndpointReplyInvariant` always was — the first staging rationale
  misnamed it).  Production code must not cite the call chain's bundle.  RR3.22 (v0.34.43)
  closed two of the four gaps this bullet used to list: the `replyRecvBody`
  three-stage composite (`replyRecvBody_preserves_ipcInvariantFull`,
  `IPC/Invariant/DispatchPayoff.lean`, staged with the payoff tier) and the
  `Architecture.stage*` return-frame writes
  (`IPC/Invariant/DispatchArmPreservation.lean`, production).  **All three
  `cancelIpcBlocking` arms are covered since RR8.7 (`v0.35.82`)**, each in its own
  production module: the **blocked-on-endpoint** arm at v0.34.95
  (`cancelIpcBlocking_endpointArm_preserves_ipcInvariantFull`,
  `SeLe4n/Kernel/Lifecycle/Invariant/CancellationQueueShape.lean`), the
  **notification** arm at v0.34.96
  (`cancelIpcBlocking_notificationArm_preserves_ipcInvariantFull`,
  `…/CancellationNotificationShape.lean`), and the **reply** arm at `v0.35.82`
  (`cancelIpcBlocking_replyArm_preserves_ipcInvariantFull`,
  `…/CancellationReplyShape.lean`).  **The arm-complete composite and its
  cross-core lift landed at `v0.35.85`** (WS-RR RR8.10,
  `SeLe4n/Kernel/IPC/Invariant/CancellationBundle.lean`, production and in the
  library root): `cancelIpcBlocking_preserves_ipcInvariantFull` over the four
  bodies the six `ipcState` constructors are serviced by, and
  `cancelIpcBlockingOnCore_preserves_ipcInvariantFull` over the transition the
  live `.tcbSuspend` dispatch runs.  Three things new code must respect.  (1)
  **The premises are per-arm**: `cancelIpcBlockingArmPremises` gates each group
  on that arm's own `ipcState` equation — which is the equation each arm theorem
  already takes, so no second reading of "which arm is this" enters the tree —
  and the `.ready` arm owes nothing, because it commits no write.  (2) **The
  cross-core form's premises are the teardown's and nothing more**: the
  migration, the holder wake and the victim's placement removal each frame
  `passiveServerIdle` for a reason that is a property of the *step* — the
  migration writes no run queue and no current slot, an *insert* cannot break a
  conjunct whose antecedent is "not queued", and the removal's one obligation is
  discharged from `cancelIpcBlocking_victim_ready`, the fact that a cancelled
  victim ends `.ready` on every arm.  A hypothesis about any of the three here
  would retract that claim, and a Tier 3 negative refuses one.  (3) **Only
  `passiveServerIdle` reads the scheduler**, which is why the lift is
  `ipcInvariantFull_of_descheduleFrame` and not a second twenty-conjunct
  argument; a proof that unfolds the bundle instead is doing the work RR2.5
  factored away.  "All five arms" is how the register named this row and the
  count is **four bodies over six constructors** — the three endpoint states
  share one.  The sentence here named the notification arm as
  uncovered for eighteen cuts after v0.34.96 covered it, two sentences below its
  own retraction, which is the *status claim a later cut must sweep* shape — so
  read this list as of its stated versions and sweep it, not around it.  Each arm
  needed its own engine, because the first two run a whole-store fold rather than
  RR7.22's splice, and the third is a **four-step composition** — reclaim, splice,
  restore, teardown — in which no two steps carry the bundle for the same reason
  (`cancelIpcBlocking_reply_arm_eq` pins the arm to that composition by `rfl`).
  Two hypotheses beyond the bundle are common to the first two: the
  timeout-budget discipline
  `allTimeoutBudgetsNone` (unavoidable — the conjunct says a budget-carrying
  thread is *blocked*, and both operations make one `.ready`), and a
  queue-coherence fact `ipcInvariantFull` does not entail, because it constrains
  queues only at their boundaries and carries no connectivity:
  `sweptThreadQueueCoherent`'s three clauses for the endpoint arm, and
  `sweptThreadOffQueueChains` for the notification arm, which has no splice to
  repair the swept thread's neighbours.  New code must state those rather than
  assume them.  **The reply arm's set is larger, because its steps are** — read it
  off `cancelIpcBlocking_replyArm_preserves_ipcInvariantFull` rather than off a
  count here.  Those two, and: `donationChainWellFormed`, which is what makes the
  pop's fail-closed head validation *resolve*; `cancelDonationStackValid` for the
  pop's outer caller; `abortHolderQueueCoherent`, the endpoint arm's three clauses
  again but for the *holder* the reclaim aborts and under the arm gate, since a
  caller cannot name that thread to state them of it; and **both directions of one
  local coherence fact** — `replyFrameHeadHolderDonation` at the victim's reply
  object (head → binding, which the pop's carriage is stated over) and
  `donatedContextIsOwnerFrameHead` (binding → head, which the no-donation payoff
  quantifies over).  Neither direction entails the other — a frame head whose
  context is `.bound` to its holder satisfies the second and refutes the first, and
  a binding with no frame satisfies the first vacuously — and `ipcInvariantFull`
  entails neither, which is WS-HP HP7's own reason for keeping the first stated.
  `sweptThreadOffQueueChains` does double duty here: it is also what rules the
  victim out as a queue neighbour of that holder, which is what carries the
  victim's own TCB across the reclaim with only its binding rewritten.  What is **not** a hypothesis is anything the bundle entails:
  `replyObject_none_of_not_blockedOnReply` derives "holds no Reply object" from
  the bundle's own reciprocity, and
  `purgedAndRestored_victim_off_endpoint_boundaries` derives that a
  notification-blocked thread bounds no endpoint queue.  Tier 3 negatives refuse
  either as a premise.  The flow-`Checked` dispatch
  wrappers gained their own payoff tier
  (`dispatchWithCapChecked_preserves_ipcInvariantFull` /
  `dispatchSyscallChecked_preserves_ipcInvariantFull`, staged) in the same
  cut.
- **Every SchedContext hand-off must migrate the replenish queue, and the
  migration's DESTINATION is the bound thread's home rather than the thread the
  hand-off expects to bind** (SM5.H; the destination half is WS-RR RR8.11,
  `v0.35.86`).  The CBS replenishments of a SchedContext live on its *bound
  thread's* home core (`replenishQueueAffinityConsistentOnCore`), so any transition
  that rebinds `boundThread` across cores must call
  `migrateSchedContextReplenishment` or the invariant is false from the instant it
  commits.  Four live paths do (`applyCallDonationOnCore`,
  `applyReplyDonationOnCore`, `.replyRecv`'s pop — `replyRecvPopDonation` since
  WS-RM split the fused `replyRecvReturnDonation`; the paths landed at v0.34.42 —
  and, since `v0.35.161`, the pre-receive donation return
  `cleanupPreReceiveDonationMigrated`), each with a
  `replenishQueueAffinityConsistent_smp` preservation theorem, and
  `PerCoreDonationStep` (`API.lean`) is the relation that names them all.  The
  pre-SM10 audit found only two of the first three, because it enumerated the
  donation *primitives* and `.replyRecv` composes them from the API layer — the
  enumeration-versus-derivation shape the key-conventions section above warns
  about — and this sentence then said **three** from v0.34.42 until `v0.35.160`,
  while the fourth rebound a context across cores and migrated nothing (register
  row 57, found by reading the arm for RR8.12 Cut C2 and closed one cut later).
  Twice is the measurement that a hand-kept list of hand-offs is not a derivation;
  the bullet after this one says what pins the fourth.
  And **one more** migrates with no constructor here and, until `v0.35.164`, no
  theorem anywhere: the suspend pipeline's own G3 donated arm
  (`cancelDonatedDonationOnCore`), which the destroy path runs too since that
  version.  Its theorem is beside the arm
  (`cancelDonatedDonationOnCore_preserves_replenishQueueAffinityConsistent_smp`),
  composed from the same general `_to_home` migration lemma the pre-receive
  return's is, and this relation's docstring names it as the second hand-off of
  the reclaim's shape — one that carries its own theorem rather than a
  constructor.  See the standing constraint on the retype's cleanup below.
  A same-core hand-off is a definitional no-op
  (`migrateSchedContextReplenishment_noop`), so the migration costs nothing where it
  is not needed and there is no reason to omit it.

  **And a caller that can refuse must read the destination off the post-rebind
  state.**  `cancelIpcBlockingMigrated` aimed its migration at
  `determineTargetCore st victim` — the home of the thread the reclaim is *about to*
  bind the context to — and the reclaim's guards are fail-closed (the outer-caller
  check, HP4.6's recipient guard, the head validation), so on a refusal it moved
  `scId`'s replenishments to a core no thread bound to `scId` is homed on, which is
  the invariant's own negation.  Latent rather than live — the refusal needs a state
  violating one of the two *stated* coherence facts, which hold on every reachable
  state — but the migration's soundness rested on an unstated hypothesis, and the
  reply path never had the defect because *its* migration sits in the `.ok`
  continuation of its return: one question, two spellings, and the pure one had it
  wrong.  `replenishHomeOfSchedContext` (`SchedContext/ReplenishAffinity.lean`) is
  the destination now — the home of the thread the context is bound to, read on the
  state the migration runs against — so a refused rebind is a *self*-migration that
  `_noop` collapses to the identity, and
  `migrateSchedContextReplenishment_to_home_preserves_affinityConsistent_smp` gets
  its destination obligation free from `replenishHomeOfSchedContext_spec`.  Three
  things new code must respect.  (1) **Every caller passes the migration's own
  source as the fallback**, so a context that resolves to nothing or is bound to no
  thread is a no-op rather than a pointless move.  (2) **The general lemma requires
  the source to be where the invariant currently puts the context** — spelled as the
  pre-state binding and its home, not as an implication, because a context bound to
  no thread locates no entries a migration could move.  (3) **The footprint does not
  grow**: both cores the destination can name were already declared, and
  `maxLockSetSize` is unmoved.
- **...and the pre-receive donation return migrates too, on the cross-core leg,
  keyed on the pop's own guard** (`v0.35.161`, register row 57).  The block arm
  of `endpointReceiveDualOnCore` — so `.receive`, and `.replyRecv`'s receive leg —
  returns a `.donated` receiver's context to its owner before the receiver parks,
  and it ran that pop bare until this cut: `boundThread` moved to the owner, the
  reservation's replenishments stayed on the receiver's home core, and
  `replenishQueueAffinityConsistent_smp` was false on a state three ordinary
  operations reach (a client `Call`s a passive server homed elsewhere, the
  server's `Recv` takes it and the hand-off migrates, the server abandons the call
  with a plain `Recv`).  No theorem claimed the leg preserved the invariant, so the
  surface was silent rather than wrong.  Five things new code must respect.  (1)
  **The arm runs `cleanupPreReceiveDonationMigrated`** — the checked pop, then
  `preReceiveReturnMigration` — and never the bare
  `cleanupPreReceiveDonationChecked`; a Tier 3 negative refuses the bare match
  inside the definition.  The order is the content: the migration reads the
  *post-pop* binding for its destination (`replenishHomeOfSchedContext`, RR8.11's
  rule above), so a refused pop self-migrates to the identity; and its guard is
  the pop's own — `preReceiveDonation?`, resolved through `lookupTcb` exactly as
  the pop resolves it — never the footprint's `getTcb?` resolver
  `endpointReplyDonation?`, which differs from it only on a reserved id, where the
  footprint over-declares and the transition is inert
  (`preReceiveDonation?_eq_endpointReplyDonation?_of_lookup`).  (2) **The
  single-core `endpointReceiveDual` keeps the bare pop**, because on one core the
  migration is the identity; what that costs is the agreement dichotomy
  `endpointReceiveDualOnCore_post_agrees`, whose block path now runs the two
  spines on two states that agree off the scheduler rather than on one, carried
  by three step congruences the dichotomy lacked
  (`endpointQueueEnqueue_offSchedulerAgrees`,
  `storeTcbQueueLinks_offSchedulerAgrees`,
  `migrateSchedContextReplenishment_offSchedulerAgrees`) — a new object-level step
  in that leg needs its congruence on the day it is written.  (3) **The leg has
  its affinity theorems** (`cleanupPreReceiveDonationMigrated_preserves_…`,
  `endpointReceiveDualOnCore_preserves_…`, `…WithCapsOnCore_preserves_…`), stated
  over every path, and `PerCoreDonationStep.preReceiveReturn` is the catalogue's
  fifth constructor; the whole-leg frame
  `endpointReceiveDualOnCore_replenishQueueOnCore` is retired for per-path ones
  (`_of_rendezvous`, `_of_blocked`, `_of_no_donation`) and refused tree-wide,
  because it was true of the transition only because the transition omitted the
  write.  (4) **The `.receive` footprint's block-path replenish segment is the
  pair `[receiver's home, owner's home]`**, read through `receivePreReturn?` — the
  resolver the object domain already reads this return through, so the two
  domains cannot name different owners — with
  `endpointReceiveHandoffReplenishCores_of_blocked_returning_eq_migration` the
  licence that the pre-state pair **is** the migration's and
  `schedLockSet_endpointReceiveOnCore_covers_preReturnMigration` the coverage;
  `endpointReceiveHandoffReplenishCores_of_blocked` and
  `schedLockSet_endpointReceiveOnCore_no_replenishQueue_of_blocked` are
  conditioned on no loan now, and the `.replyRecv` footprint inherits the pair
  when Cut C2 declares it over the same leg.  (5) **The witness computes the bare
  pop beside the migrated return** on the same reachable state
  (`tests/SmpIpcSuite.lean` §3.28) and asserts the bare one *falsifies* the
  invariant — the bare pop is still a live definition, the migrated return's own
  first half, so the retired reading needs no private copy — with a no-loan
  control and a same-core control, where the two returns agree.
- **A destroyed thread's reservation is ended the way a suspended thread's is**
  (`v0.35.164`, register row 62).  `lifecyclePreRetypeCleanup`'s TCB arm runs
  `cancelDonationArmOnCore` (`Lifecycle/Operations/Cleanup.lean`) — the suspend
  pipeline's G3 three-way binding match, named: `.unbound` is the identity,
  `.bound` is the in-place unbind with the replenish purge on the thread's home
  core (seL4's `finaliseCap` → `unbindFromSc`), `.donated` the return **and** the
  replenishment migration to the owner's home.  Until then the arm was the bare
  `cleanupDonatedSchedContext` — a return that migrates nothing, register row 57's
  class on the destroy path — and a `.bound` thread had only its `scThreadIndex`
  entry removed, leaving the SchedContext bound to a destroyed thread with its
  replenishment stranded on that thread's home core: `schedContextBindingConsistent`
  and `replenishQueueAffinityConsistent_smp` were both false after a successful
  retype, and no theorem claimed either across it.  Five things new code must
  respect.  (1) **The two per-core arms live beside the cleanup they complete**:
  `cancelBoundDonationOnCore` and `cancelDonatedDonationOnCore` moved from
  `IPC/CrossCore/Cancellation.lean` to `Cleanup.lean`, definitions only, keeping
  their namespace — the destroy path's module cannot import the cancellation
  layer, so *when a question has one owner and an asker that cannot see it, the
  owner is in the wrong layer* (`v0.35.59`).  Their `ipcInvariant` theorems, the
  single-core bridges and the suspend footprint stay where they were; the frames
  the destroy path reads are in `CleanupPreservation.lean`.  (2) **One owner, two
  spellings, one of them defined through the other**: `cancelDonationOnCore` (the
  `withLockSet` bracket convention) is one `match` over the arm, and the suspend's
  G3 is pinned to the arm by `rfl` (`suspendDonationArm_eq_cancelDonationArmOnCore`)
  rather than defined through it, because its `home` is read on the **pre**-G2
  state and calling the arm there would owe an affinity frame at the eight proof
  sites that open the pipeline — RR8.12's recorded reason stands.  A step added to
  the arm reaches the destroy path by construction and fails the G3 pin on the
  day it is written.  (3) **The arm has the affinity theorem neither caller had**:
  `cancelDonationArmOnCore_preserves_replenishQueueAffinityConsistent_smp`, over
  `cancelBoundDonationOnCore_preserves_…` (no hypothesis on the purge core — the
  unbound context's obligations are vacuous wherever its entries survive, which is
  the unbind's own argument) and `cancelDonatedDonationOnCore_preserves_…`
  (through the general `migrateSchedContextReplenishment_to_home_preserves_affinityConsistent_smp`,
  the one owner `v0.35.161`'s pre-receive return composes).  The suspend pipeline
  had run both arms since SM6.E.3 with the invariant stated of its G2 teardown and
  of nothing after it.  (4) **`retypeTargetDetached` has `tcbNotBound`**: revoke,
  suspend, cancel *and unbind* before retype, so the dispatch payoff's retype arm
  is stated where the arm is the identity, and the runtime arm is what makes a
  violation safe.  (5) **What is measured, and what is proved**: `tests/SmpIpcSuite.lean`
  §3.31 drives the live wrapper on both binding shapes with the retired cleanup
  computed beside it and an unbound control; the **cleanup**'s own preservation of
  `replenishQueueAffinityConsistent_smp` is proved at `v0.35.166`
  (`lifecyclePreRetypeCleanup_preserves_replenishQueueAffinityConsistent_smp`,
  `Lifecycle/Invariant/RetypeReservation.lean` — see the bullet below for where
  the frames it composes went), and what register row 63 still carries is
  `schedContextBindingConsistent` across either program, plus the retype
  *composite*'s affinity theorem, which is gated on it.

- **...and a destroyed SCHEDULING CONTEXT releases the binding it holds**
  (`v0.35.165`, register row 63's arm half).  `lifecyclePreRetypeCleanup`'s
  `.schedContext` arm refused a context that heads a reply stack
  (`sc.scReply.isSome`) and nothing else, so a context **bound** to a thread
  passed: the retype left that thread `.bound scId` — or `.donated scId owner`,
  the binding a donee holds — naming an object the slot no longer carries, its
  `scThreadIndex` entry in place, and `scId`'s replenish entries queued on its
  home core under an id the slot's next occupant inherits.  `releaseSchedContextBinding`
  (`Lifecycle/Operations/Cleanup.lean`) is seL4's `schedContext_unbindAllTCBs`
  per core.  Four things new code must respect.  (1) **Its three writes are
  `schedContextUnbind`'s own**, composed from the same primitives in the same
  order — the binding cleared through `updateTcb`, the replenishments purged with
  `purgeReplenishmentOnCore` on the bound thread's home core, the index entry
  removed — rather than a second spelling of the queue write; the TCB-absent arm
  sweeps **every** core, for the unbind's own stated reason (a thread gone from
  the store has no `cpuAffinity` left to read).  (2) **It does not rewrite the
  SchedContext record**, because the retype replaces the object, and it writes no
  run queue and no current slot — which is what keeps the destroy path's write
  set empty and its confinement result unchanged
  (`releaseSchedContextBinding_confinedToCores`, over the six slots a replenish
  queue is deliberately not among).  (3) **A donee's context is not
  returned to its owner**: the owner is already `.unbound` and the object it
  would receive no longer exists.  (4) **Its affinity theorem is unconditional,
  and not for the unbind's reason**: the release only ever *removes* replenish
  entries and frames both readings the invariant makes, so an invariant
  quantified over the entries that are present descends to a state with fewer of
  them — where the unbind needs more precisely because it rewrites its context to
  `boundThread := none`.  One consequence for proofs: the arm is **unreachable**
  under `retypeTargetDetached`, whose `notSc` excludes SchedContext targets
  outright, so `lifecyclePreRetypeCleanup_detached_frame` discharges it by
  contradiction rather than by the arm being the identity.
- **...and the CLEANUP has its reservation theorem, because a frame it composes
  moved to the layer that can state it** (`v0.35.166`, register row 63's layering
  half).  `v0.35.164` and `v0.35.165` each gave an *arm* of
  `lifecyclePreRetypeCleanup` its own `replenishQueueAffinityConsistent_smp`
  theorem and neither could state one about the **program** that runs them: the
  `.tcb` arm's reference sweep runs two whole-store folds whose
  `getSchedContext?` and `cpuAffinity` frames WS-RR RR8.11 wrote `private` in
  `IPC/Invariant/CancellationBundle.lean`, which is downstream of both the
  cleanup and the retype wrapper.  So the theorem was **unstateable** rather than
  unproved — `v0.35.59`'s rule (*when a question has one owner and an asker that
  cannot see it, the owner is in the wrong layer*) at the scale of a composite.
  Six things new code must respect.  (1) **Each frame is beside the fact its
  proof rests on, not in one convenience module**: the two generic accessor
  bridges (`SystemState.getSchedContext?_eq_of_kind_iff`,
  `SystemState.map_cpuAffinity_eq_of_refines`) in `Model/State.lean` beside
  `getSchedContext?_eq_some_iff` / `getTcb?_eq_some_iff`; the splice's affinity
  frame in `CleanupPreservation.lean`; each sweep's pair in its own
  `Cancellation*Shape.lean` beside that sweep's `non…` biconditional.  A new
  frame over one of those sweeps goes to the same place.  (2) **The composite
  lives in `Lifecycle/Invariant/RetypeReservation.lean`**, which imports
  `CancellationNotificationShape` — the only layer that sees every frame it
  composes, and imported by nothing that would close a cycle — and which the
  library root imports, since a module outside every root is outside every
  census's derived domain.  (3) **The sweep frames `boundThread`, not
  `getSchedContext?`**: its last step (`clearDonationOriginReferences`) genuinely
  rewrites scheduling contexts, and the invariant reads only the field it leaves
  alone, so `cleanupTcbReferences_boundThread_frame` is the projection and
  `replenishQueueAffinityConsistentOnCore_transfer` is what consumes it.  (4)
  **The composite takes no detachment pack**, so it covers exactly the states on
  which the runtime arms do the work — under `retypeTargetDetached` the whole
  cleanup is the identity (`lifecyclePreRetypeCleanup_detached_frame`), which is
  the posture that pack's own clauses record and the reason a theorem stated
  under it would exercise neither arm.  `hTcb` is the arm's own soundness
  condition, stated where it binds.  (5) **`replenishQueueAffinityConsistent_smp_frame`
  is the shape a step writing no object at all reaches for** — the per-core
  `_frame` at every core, beside `_smp_congr` in `ReplenishAffinity.lean` — and
  the CDT detach, the service-registry revoke and the memory scrub all take it.
  (6) **What row 63 then carried was an effort fact, measured**: there was no
  `preserves_schedContextBindingConsistent` theorem anywhere in the tree, so that
  reciprocity had to be built for eight operations before either program could
  claim it — `v0.35.183` built it, see the bullet below — and the retype
  *composite*'s affinity theorem is gated on the same work rather than on a
  second layering fact, because its `storeObject` at `target` rewrites
  `getSchedContext?` and `determineTargetCore` there and so preserves the
  invariant exactly when no surviving context is bound to the destroyed thread.
  Stating *that* as a hypothesis would be a predicate no transition establishes
  (`v0.35.126`).
- **...and Z4-O crosses that cleanup too — with the SchedContext arm REFUTED
  rather than proved** (`v0.35.183`, register row 63's remaining half).
  `schedContextBindingConsistent` is bidirectional reciprocity between
  `TCB.schedContextBinding` and `SchedContext.boundThread`, and it reads nothing
  else, so `schedContextBindingConsistent_transfer` (beside the predicate) takes
  both projections as `Option.map` frames and carries the invariant whole, with
  `schedContextBindingConsistent_of_objects_eq` the degenerate case.  Five things
  new code must respect.

  (1) **Both frames, never one.**  Framing the binding alone leaves the backward
  clause unsupported — a step that rewrites a `boundThread` and no binding would
  pass it — which is *a presence check is not a relation check* at the level of a
  transfer lemma's own hypotheses.

  (2) **The splice's field frame has one owner.**  `spliceOutMidQueueNode`
  rewrites its neighbours' three link fields and nothing else (WS-OD OD1.1 /
  OD3.9's own subject), so `tcbQueueLinkRewrite` states that as a relation,
  `spliceOutMidQueueNode_tcbField_frame` proves the frame once over an arbitrary
  projection, and `_affinity_frame` and `_binding_frame` are instances.  A new
  projection over the splice is a one-line instance, never a second induction —
  and a whole-record `getTcb?` equality for the splice, or for the sweep built
  over it, is **false** and refused tree-wide.

  (3) **The pop moves one whole reciprocal pair.**
  `returnDonatedSchedContext_preserves_schedContextBindingConsistent` is the
  substantive theorem of the family: the pop clears the holder's binding,
  installs the recipient's and rewrites the context's `boundThread` to name the
  recipient, so both clauses are re-established at the moved pair and transported
  everywhere else — and its uniqueness obligations come from Z4-O itself rather
  than from a fresh argument.  `cancelBoundDonationOnCore`'s unbind *clears* both
  sides of one pair; `cancelDonationArmOnCore` covers all three bindings, so the
  suspend pipeline's G3 inherits it through
  `suspendDonationArm_eq_cancelDonationArmOnCore`.

  (4) **`releaseSchedContextBinding` does NOT preserve it, deliberately**, and
  `releaseSchedContextBinding_refutes_schedContextBindingConsistent` says so: the
  arm clears the bound thread's binding and leaves the destroyed context's
  `boundThread` naming it for the retype's own `storeObject` at that key to
  replace, so the backward clause is false on the arm's post-state and repaired
  one step later.  Writing `boundThread := none` there would add a store to an
  object the very next step replaces, for no property that is not already had.
  `lifecyclePreRetypeCleanup_preserves_schedContextBindingConsistent` therefore
  takes `hNotSc` — free at the live call site, where `retypeTargetDetached`'s
  `notSc` excludes a SchedContext target outright — and the refutation is what
  shows that hypothesis *necessary* rather than convenient, the standing pattern
  WS-RR RR8.7 set with `replyCallerLinkage_refutes_woken_linked_caller`.  A proof
  that wants the preservation is asking for a premise the arm refutes.

  (5) **A retyped SchedContext starts bound to nobody, and that is a runtime
  refusal** (`v0.35.184`).  `KernelObject.wellFormed`'s `.schedContext` arm is
  `sc.boundThread = none`, following the `Reply` clause SM6.D added one field over
  and for the reason SM6.D states in terms: the two retype wrappers check
  `wellFormed` and **nothing else** of the replacement, so an arm reading `True`
  admits a retype installing a context that claims a thread which does not name it
  back — exactly what Z4-O forbids, and a disagreement no operation reconciles.
  Three things new code must respect.  The clause **is** the refusal, because both
  wrappers answer `.illegalState` and commit nothing when `wellFormed` fails; a
  Tier 3 anchor is scoped to **each** wrapper's declaration, since one tree-wide
  pattern is satisfied by whichever of the two still carries the guard.  It costs
  the tree nothing — nothing depended on the arm being `True`, and the live
  dispatch's builder is `objectOfKernelType`, whose `.schedContext` arm is
  `SchedContext.empty` — which is what makes it the difference between an invariant
  maintained by convention and one enforced structurally, true of every *future*
  replacement builder rather than of the one that exists.  And the witness's
  negative is the falsification: `tests/SmpIpcSuite.lean` §3.34 computes the
  retired guard beside the live one, stores the claiming replacement through it and
  asserts Z4-O **false**, against a CONTROL on the pristine replacement where it
  holds — so the claim is about `boundThread` rather than about the retype.

  Register row 63's last half — the retype **composite**'s two theorems — is
  `v0.35.185`, the bullet below.
- **...and the COMPOSITE crosses through one intermediate, carved out of BOTH
  sides, and it is the intermediate BOTH invariants need** (`v0.35.185`,
  register row 63 CLOSED).  `lifecycleRetypeDirectWithCleanup` is the cleanup,
  then `scrubObjectMemory`, then a `storeObject` at `target`, and a composite
  stated as *"Z4-O of the post-cleanup state carries to the post-store state"* is
  a statement about a state the pipeline does not rest at — the `.schedContext`
  arm refutes Z4-O on its own post-state by design (the item above).  Six things
  new code must respect.

  (1) **`schedContextBindingRetypeReady st target` is Z4-O with `target` carved
  out of the SUBJECT and of the OBJECT of both clauses**, and all four carve-outs
  earn their place at the store: the forward clause's `scId.toObjId ≠ target`
  rules out a thread still bound to the *destroyed context* (after the store the
  target holds `newObj`, so it would have no witness), the backward clause's
  `tid.toObjId ≠ target` a surviving context still naming the *destroyed thread*
  (after the store its record is `newObj`'s).  Neither follows from the other, and
  dropping either makes
  `storeObject_establishes_schedContextBindingConsistent` **false** rather than
  unprovable.  It stands to the retype as
  `ipcInvariantFullExceptDonationOwner` stands to the bare reply and
  `replyCallerLinkageExcept` to the woken caller.

  (2) **The SAME predicate carries the replenish half**, which is the measurement
  that it is the destroy path's own fact rather than one proof's scaffolding:
  `storeObject_preserves_replenishQueueAffinityConsistent_smp` consumes it because
  the backward carve-out is exactly what keeps the store from moving a replenish
  entry's home core — the replacement TCB's `cpuAffinity` is its own.  A second,
  private readiness predicate for that half would be *one question, two answers*
  inside the remedy for it.

  (3) **`retypeTargetUnpaired` is the fact each cleanup arm establishes**, stated
  once, and `lifecyclePreRetypeCleanup_targetUnpaired` proves it for five of the
  six arms; `hNotSc` is the sixth, free at the live call site.  The store's two
  remaining conditions are the replacement's: `hScFresh` is a **runtime refusal**
  (`v0.35.184`) read off the wrapper's own guard, and `hTcbFresh` the
  `retypeReplacementFresh` pack the live dispatch already supplies.

  (4) **`hIdentity` — a TCB is stored under its own thread id — is a hypothesis,
  and the reason it is one is a registered gap** (its runtime half closed at
  `v0.35.187`, the item below; the store-level invariant that would retire the
  hypothesis is open).  The `.tcb` arm is handed `tcb`
  and operates on `tcb.tid` while the store is at `target`, so without their
  agreement the cleanup can clear a binding at one key and leave the retype's own
  key paired.  Four measurements place it: `PlatformConfig.wellFormed`'s
  `embeddedIdentitiesMatchSlots` establishes it for every boot object,
  `enqueueIdleThreadOnCore` stores `queuedIdleThread c` at
  `(idleThreadId c).toObjId` carrying that very id, **no transition writes
  `TCB.tid`**, and the one remaining builder (`objectOfKernelType`) sets it to
  `ThreadId.sentinel` but is refused by `KernelObject.wellFormed`, whose `.tcb`
  arm requires the replacement's `cspaceRoot` and `vspaceRoot` to resolve while
  that builder sets both to `ObjId.sentinel`.  **That last refusal is a
  convention, not an invariant** — the H-06/WS-E3 reservation of id 0 is enforced
  at boot for the *boot VSpace root alone* and by no store-level invariant, and no
  conjunct of `PlatformConfig.wellFormed` refuses an `initialObjects` entry at
  slot 0 — so the agreement holds of every reachable state and is stated by
  nothing, a latent false-assurance gap with its own register row whose remedy is
  to **stamp the slot's identity** rather than to weaken the claim.

  (5) **The claim's unit is the PROGRAM THE ARM RUNS.**  The live
  `.lifecycleRetype` dispatch runs
  `lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache`, so both theorems are
  lifted through the three cached-structure layers — Cut C6g's rule, and the lift
  is a citation rather than a second argument because each layer frames `objects`
  and `scheduler` outright.  One shared frame
  (`lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_ok_frame`) says it for
  both, so a fourth layer costs one proof rather than one per consumer.

  (6) **What the composite DID has one owner**, and a `private` frame has none.
  `lifecycleRetypeDirectWithCleanup_ok_decompose` replaced the same twenty-line
  decomposition inlined in both proofs, which were free to disagree about which
  state the cleanup left; and `retypeInitiatorDrain_objects` is public beside its
  `_scheduler` and `_machine` siblings, where it was the `.1` of a `private`
  conjunction whose `.2` duplicated the public `_scheduler` two lines from the
  step it frames — half a second answer, half unreachable from every asker
  upstream.  Both are refused in their retired spellings by Tier 3 negatives.
- **...and a retyped object carries the SLOT's identity, because the runtime now
  refuses one that does not** (`v0.35.187`).  A TCB, a SchedContext and a Reply
  each carry their own id in a field while the object store is keyed by `ObjId`,
  so the two can disagree; `PlatformConfig.wellFormed`'s
  `embeddedIdentitiesMatchSlots` has refused that at **boot** since PR #889
  review round 8 and **nothing refused it at the runtime**, while
  `objectOfKernelType` — the one builder the live retype installs through —
  stamped the reserved **sentinel** into all three.  Four things new code must
  respect.

  (1) **`KernelObject.embeddedIdentityMatches` is the question, with no
  wildcard**: a kernel object that starts carrying its own id must be classified
  there rather than silently answering `true`, which is the closed-inductive rule
  this file states for `ConstantInfo` applied to a kernel record.

  (2) **A refusal needs an answer, and `KernelObject.withIdentity` is it** — it
  writes the identity field and nothing else, so `withIdentity_wellFormed`,
  `_objectType` and `withIdentity_replacementFresh` carry every property the
  retype's other guards and the dispatch payoff's pack read.  A builder that
  installs a TCB, SchedContext or Reply stamps.

  (3) **Both retype wrappers read ONE named predicate**,
  `retypeReplacementAdmissible`, rather than a second `if` beside the T5-D one:
  *a named condition beside unnamed ones is a subset*, and a condition added to
  the predicate reaches both wrappers by construction.

  (4) **The boot's check and the runtime's guard are one question by theorem**
  (`embeddedIdentitiesMatchSlots_iff`), not by a shared spelling.  What the cut
  does **not** do is retire `hIdentity`, which is about the object being
  *destroyed*: that needs the store-level invariant *every stored object's
  embedded id is its key*, which the boot, the idle enqueue and now the retype
  all establish and which no transition falsifies — a preservation theorem per
  transition, registered rather than implied.
- **...and the `.replyRecv` arm declares one, by re-running its own spine** (WS-RR
  RR8.12 Cut C2, `v0.35.162`).  `schedLockSet_endpointReplyRecvOnCore` is
  `schedFootprintOfCores` of `replyRecvBodyWriteSet` — the arm's own SM8.B write
  set, which `replyRecvBody_confinedToCores` is stated at — and of
  `replyRecvHandoffReplenishCores`, the cores its **three** SchedContext hand-offs
  migrate between: the pop between the legs (`replyRecvPopDonation`, WS-RM), the
  receive leg's block-path return (`cleanupPreReceiveDonationMigrated`,
  `v0.35.161`) and the re-donation to the receiver on a dequeued `Call`
  (`replyRecvPostReceiveDonation`, WS-RR RR2.20).  **Inert** until the bracket
  cut.  Six things new code must respect.  (1) **Each hand-off is read at the
  state it runs on, through its own arm selector** — the pop's frame trigger
  `replyFrameHeadHolder?` at the reply leg's post-state
  (`replyDonationReturnReplenishCores`, the pair the `.reply` dispatch reads too
  since Cut C3a; the pop's `returned?` is that trigger's answer), the block path's
  `receivePreReturn?` at the pop's post-state (`receivePreReturnReplenishCores`),
  the re-donation's `callDonationSchedContext?` at the post-deschedule state
  (`replyRecvPostReceiveReplenishCores`, over the post-state form
  `rendezvousCallDonationReplenishCores`) — which is the discipline
  `replyRecvBodyWriteSet` established for the run segment, and the reason this arm
  could not take `.receive`'s pre-state form: the pop rewrites the receiver's
  binding between the legs, so a pre-state reading of the receive leg's donation
  guard would be a proxy for the guard the transition reads two legs later.  The
  footprint's resolution and the transition's are the same computation, so the
  asymmetry WS-HP HP10.8 registered for the reply arm's origin member has no
  instance here.  (2) **The block-path pair has one owner for both receiving
  arms**: `receivePreReturnReplenishCores` is what
  `endpointReceiveHandoffReplenishCores` reads on its block branch too, and
  `receivePreReturnReplenishCores_eq_migration` is the licence — stated once,
  consumed by both — that the pair **is** the migration's.  (3) **Every hand-off
  is covered by theorem at the cores its migration actually resolves**:
  `schedLockSet_endpointReplyRecvOnCore_covers_pop` (through
  `replyRecvPopDonation_ok_some_decompose`), `…_covers_preReturnMigration`, and
  `…_covers_postReceiveDonation` (through `applyRendezvousCallDonation_ok_migrates`).
  (4) **The empty segment is exact in both directions**: where the pop hands
  nothing back and the block path returns no loan, the footprint names no
  replenish lock (`…_no_replenishQueue_of_no_donation`) and the live transition
  writes none (`replyRecvBody_replenishQueueOnCore_of_no_donation`, composed from
  the reply leg's new frame `endpointReplyOnCore_replenishQueueOnCore`, the pop's
  `none` arm being the identity, the receive leg's `…_of_no_preReturn` frame and
  the two walks' frames).  (5) **That licence pins a divergence, deliberately.**
  On a `.replyRecv` whose pop returned nothing, a dequeued `Call` caller's context
  is **not** donated to an `.unbound` receiver — `replyRecvPostReceiveDonation`'s
  never-donated arm walks only — where this kernel's own `.receive` arm
  (`applyReceiveRendezvousHandoff`, unconditional) and seL4-MCS's `receiveIPC`
  would donate.  Reachable with one legacy `.unbound` client, measured in
  `tests/SmpIpcSuite.lean` §3.29 (b) beside the `.receive` step on the same
  state, and recorded in the register's WS-CB row as the third instance of the
  passive/legacy split; a cut that makes the arm donate widens
  `replyRecvPostReceiveReplenishCores`'s `none` arm and breaks the licence, so the
  footprint and the transition move together or not at all.  (6) **The two chain
  walks are in the run segment**: `replyRecvBodyWriteSet` re-runs the spine to the
  state each walk starts from and appends `pipChainWriteSet` there, so the walked
  members' run queues are static members, and the `pipChainStart_replyRecv*`
  obligations add the object domain's per-member TCB locks through
  `pipChainSchedFootprint` (`v0.35.162` said "declared dynamically"; corrected at
  Cut C3a).  `maxLockSetSize` is unmoved.  §3.29 drives all three shapes through the live
  operations — the steady state with a second client on a third core (three cores
  named), the legacy client (none), and a delegated invoker that blocks holding a
  loan (all four) — asserting the segment, the footprint and the post-state
  replenish queues.
- **...and the `.call` and `.reply` arms declare theirs, over write sets that now
  live in production** (WS-RR RR8.12 Cut C3a, `v0.35.163`).
  `schedLockSet_endpointCallOnCore` (`IPC/CrossCore/EndpointCallDispatch.lean` §3)
  is `schedFootprintOfCores` of `endpointCallDispatchWriteSet` — the arm's SM8.B
  write set, which `endpointCallCrossCoreDispatch_confinedToCores` is stated at —
  and of `endpointCallDispatchReplenishCores`, the donation's pair;
  `schedLockSet_endpointReplyOnCore` (`EndpointReplyDispatch.lean` §6) is the same
  over `endpointReplyDispatchWriteSet` and `endpointReplyDispatchReplenishCores`,
  the return's pair; and `schedLockSet_replyTransferOnCore` (`Fault.lean` §6) is
  the **arm's** — seL4's `doReplyTransfer` branch — over the dispatch's at the
  message each branch hands it, plus on an abandon the faulted thread's home core.
  **Inert** until the bracket cut.  Six things new code must respect.  (1) **A
  replenish segment mirrors the dispatch's own guard at the state the dispatch
  asks it**: the `.call` segment asks `callDonationSchedContext?` at the WithCaps
  post-state and reads the two homes off the pre-state, exactly as
  `applyCallDonationOnCore` is handed them, so the pair and the migration's
  endpoints are the same two expressions and no home-core frame stands between
  them; the `.reply` segment re-runs the leg and reads the return's pair at that
  leg's post-state through `replyFrameHeadHolder?`, because the recipient is
  decided there (WS-HP HP10.8's asymmetry is what a pre-state reading would
  reintroduce).  (2) **The pop's pair has ONE owner**,
  `replyDonationReturnReplenishCores` — spelled through the two named home
  resolvers the dispatch passes — and `.replyRecv`'s pop component reads it too;
  `replyRecvPopReplenishCores` is retired, since the pop's `returned?` *is* the
  trigger's answer (`replyRecvPopDonation_holder_eq_frameHead`,
  `…_ok_none_frameHead`).  (3) **The `.reply` footprint is the DISPATCH's; the
  ARM's sits over it**, and only the arm's is complete: `faultAbandonOnCore`
  deschedules the answered thread on its home core, a write the dispatch never
  performs, so `schedLockSet_replyTransferOnCore_contains_abandon_runQueue_write`
  is the member a dispatch-level footprint would have missed, and
  `…_covers_dispatch_of_no_fault` / `…_of_fault` is the relation between the two.
  (4) **Coverage is at the resolved cores, and the RR2.4 shape is covered while
  the RR2.10 shape is not**: `schedLockSet_endpointCallOnCore_covers_parametric`
  holds because every core the parametric `.call` footprint declares is written;
  the parametric `.reply` footprint declares the executing core's run queue on the
  ground that the reversion re-buckets "locally", which is false — it re-buckets
  each member on its *home* core, and nothing in the dispatch writes the
  replier's own core — so that member is an over-declaration the derived form
  drops, and what is covered is the donation-return footprint the parametric form
  declares correctly (`…_covers_donation`, `…_covers_migration`,
  `…_covers_deschedule`).  (5) **The empty segments are exact in both
  directions** (`…_no_replenishQueue_of_no_donation` / `_of_no_receiver` /
  `_of_no_head` against `endpointCallCrossCoreDispatch_replenishQueueOnCore_of_no_donation`
  / `_of_no_receiver`, `endpointReplyCrossCoreDispatch_replenishQueueOnCore_of_no_head`
  and the arm's `replyTransferOnCore_replenishQueueOnCore_of_dispatch`), over four
  new frames — the bare and WithCaps call legs', the declined donation's, and the
  walk's `propagatePipChainCrossCore_replenishQueueOnCore`, which needs **no**
  object-store hypothesis: a claim about what a transition writes should not have
  to assume the invariant it preserves.  (6) **The chain walks are in the run
  segments**, for `.call`, `.reply` and `.replyRecv` alike: each write set re-runs
  the spine to the state its walk starts from and appends `pipChainWriteSet`
  there, so the walked members' run queues are static members, bounded by the
  object count (a `SchedLockSet` carries no cardinality bound); what the
  `pipChainStart_*` obligations still add through `pipChainSchedFootprint` is the
  object domain's per-member TCB write lock, which no scheduler footprint can
  name.  `.receive` (Cut 8a-ii) is the one declared arm whose walk is not in its
  run segment.  Five write sets and one frame moved here from the staged
  `InformationFlow/NonInterferenceCrossCore.lean` (`endpointCallWriteSet`,
  `endpointCallDispatchChainWriteSet`, `endpointCallDispatchWriteSet`,
  `replyDonationDescheduleCores`, `endpointReplyDispatchWriteSet`,
  `endpointCallWithCapsOnCore_scheduler_eq`), each with a tombstone, the
  confinement theorems staying staged — the layering rule Cuts 5, 7, 8a-ii and C2
  applied.  `tests/SmpIpcSuite.lean` §3.30 drives five shapes through the live
  operations and `tests/FaultHandlingSuite.lean` §7c the abandon;
  `maxLockSetSize` is unmoved.
- **...and the three TCB-control arms declare theirs, in a module of their own,
  because their own modules cannot name a `SchedLockId`** (WS-RR RR8.12 Cut
  C3b-i, `v0.35.167`).  `schedLockSet_resumeThreadOnCore`,
  `schedLockSet_priorityControlOnCore` and
  `schedLockSet_setThreadCpuAffinityOnCore` (`SeLe4n/Kernel/SyscallSchedFootprint.lean`)
  are the live `.tcbResume`, `.tcbSetPriority` / `.tcbSetMCPriority` and
  `.tcbSetAffinity` arms' scheduler-domain footprints — **inert** until the
  bracket cut.  Six things new code must respect.  (1) **Placement is a fact
  about the import graph, not a convention this module abandons.**  `SchedLockId`
  is declared in `Scheduler/Operations/PerCoreChooseThread.lean`, which imports
  `Lifecycle/Suspend.lean` and `IPC/Operations/Endpoint.lean`; measured,
  `Lifecycle/Suspend.lean`, `SchedContext/Operations.lean`,
  `SchedContext/PriorityManagementPerCore.lean`, `Scheduler/Operations/Core.lean`
  and `Lifecycle/Operations/RetypeWrappers.lean` are all outside its reverse
  closure, so none of them can name a `SchedLockId` at all.  Moving the
  identifier down was rejected — it is declared with `RunQueueLockId`,
  `ReplenishQueueLockId` and the cross-domain order over them, which is what
  `schedFootprintOfCores` is *about*.  The rule is therefore stated once, in that
  module's header: **a resolved scheduler footprint lives beside its transition
  where that module can name a `SchedLockId`, and here where it cannot** — the
  shape the object domain reached at `Concurrency/Locks/LockSetTransitions.lean`.
  (2) **Each footprint IS `schedFootprintOfCores` of its arm's own SM8.B write
  set**, which is Cut 7's rule, and that is what forced the three write sets out
  of the staged `InformationFlow/NonInterferenceCrossCore.lean` — a production
  footprint cannot read a write set declared in a staged module.  The confinement
  theorems stay staged.  (3) **The priority pair shares one footprint**, because
  SM8.B gives the two arms one write set; `.tcbResume`'s fault retire
  (`retirePendingFaultForResume`) needs no member of its own, writing one TCB's
  `pendingFault` and no scheduler state.  (4) **The affinity arm's replenish
  segment follows the thread's BINDING**, not the arm: a migration of a thread on
  no reservation moves no entry, and over-declaring is not free — lock contention
  is an observable channel (SM8.D's CC-5), which is WS-OD OD3.5's own reason for
  narrowing a footprint.  Every empty segment is a **theorem**
  (`resumeThreadOnCoreLive_replenishQueueOnCore`,
  `setPriorityOnCore_replenishQueueOnCore`,
  `setMCPriorityOnCore_replenishQueueOnCore`,
  `setThreadCpuAffinityWithMigration_replenishQueueOnCore_of_no_context`) against
  the declaration's own half, so each narrowing is exact in both directions.
  Coverage against the *transition* is its own statement
  (`schedLockSet_setThreadCpuAffinityOnCore_covers_migration`), because the
  transition resolves its destination as `determineTargetCore stSet tid` at the
  post-affinity-write state where the footprint resolves it from the argument:
  the two are one value only through `setThreadCpuAffinity_determineTargetCore_eq`,
  and a coverage claim read off `_contains_replenishQueue_writes` alone is about
  the argument rather than about the migration.
  (5) **The parametric SM5.H.4 family is production now**, and asking for the
  coverage relation is what found it: `setThreadCpuAffinityWithMigrationLockSet`
  and `migrateRunQueueOnAffinityChangeLockSet` sat in the staged
  `Scheduler/Operations/PerCoreCbs.lean` **twenty lines below the tombstone WS-RR
  RR2.4 left when it relocated `migrateSchedContextReplenishmentLockSet` out of
  that same file for that same reason** — *a fix applied at one site and not at
  its sibling*, invisible until a production footprint had to state
  `schedLockSet_setThreadCpuAffinityOnCore_covers_parametric`.  They are beside
  that family now, in `PerCoreChooseThread.lean`, and every consumer keeps working
  with no import edit.  (6) **A write set's content needs no anchor and must not
  get one**: each footprint's `_contains_*_runQueue_write` theorem is
  `simp [<the write set>]`, so a mutation dropping a core fails to *elaborate* —
  measured, rather than asserted, at
  `schedLockSet_resumeThreadOnCore_contains_home_runQueue_write`.  *Prefer making
  the property structural over checking it at all.*  Four frames moved to
  production beside the definitions they frame in the same cut
  (`migrateRunQueueOnAffinityChange_replenishQueueOnCore` →
  `Scheduler/Operations/Core.lean`; `enqueueRunnableOnCore_replenishQueueOnCore`
  and `setThreadCpuAffinity_determineTargetCore_eq` →
  `Scheduler/Operations/Selection.lean`; the new
  `migrateRunQueueBucketOnCore_replenishQueueOnCore` →
  `SchedContext/PriorityManagement.lean`).  `tests/SmpCbsSuite.lean` §4.5 is the
  decisive witness — one state, a thread on a reservation and a thread on none,
  the same migration, opposite segments, with the **parametric** footprint
  computed beside the resolved one so the assertions are known to discriminate —
  and `tests/SuspendResumeSuite.lean` SR-035 and
  `tests/PriorityManagementSuite.lean` PM-FP-01 drive the other two arms with the
  target's home core and the executing core distinct.  `maxLockSetSize` is
  unmoved.
- **...and the three SchedContext arms declare theirs, which found a duplicate
  resolver under a docstring claiming there was none** (WS-RR RR8.12 Cut C3b-ii,
  `v0.35.168`).  `schedLockSet_schedContextConfigureOnCore`,
  `schedLockSet_schedContextBindOnCore` and
  `schedLockSet_schedContextUnbindOnCore` join the three above, in the same
  module and for the same reason — **inert** until the bracket cut.  Five things
  new code must respect.  (1) **The thread a SchedContext operation acts on has
  one resolver, `SchedContextOps.schedContextBoundThread?`**, whose own docstring
  has said since SM8.B that it is *"single-sourced here in production because two
  consumers need it and a second copy would drift"* — while the staged
  `InformationFlow/NonInterferenceCrossCore.lean` carried `schedContextSubject?`,
  clause for clause the same function, and the write set the docstring names read
  *that* one.  The copy is **deleted** and refused tree-wide; a reader asks the
  owner by its own name, never through an alias, because an alias is the second
  spelling this cut retires.  *A docstring naming a drift hazard is not a check
  that the hazard is closed.*  (2) **The configure's replenish segment keys on
  the SCHEDCONTEXT resolving, not on its being bound**: an unbound SC has no
  home, `schedContextReplenishHome` answers the boot core, and the purge still
  runs there — a stale entry left by an earlier binding is exactly what it drops,
  so a segment keyed on the binding would omit a lock the transition takes.  When
  the SC *is* bound the purge and the re-bucket land on one core
  (`schedContextConfigureReplenishCores_eq_writeSet_of_bound`), so one lock covers
  both effects.  (3) **The unbind's replenish segment is the first in this family
  that is EVERY core.**  Its sweep arm — reached when the bound TCB is already
  gone from the store — runs `purgeReplenishmentFromAllCores`, because with no
  `cpuAffinity` left to read there is no home core to name; both arms are decided
  on the pre-state, so the declaration is exact rather than a conservative union,
  and a footprint naming only the home core would be **false** there.  (4) **The
  bind declares no replenish lock**, and `schedContextBind_replenishQueueOnCore`
  is the absence; the run segment is where seL4-MCS's `SCHED_ENQUEUE` divergence
  would widen it, not this one.  (5) **Every narrowing is a theorem in both
  directions**: `schedContextConfigure_replenishQueueOnCore_ne` and
  `schedContextUnbind_replenishQueueOnCore_ne_of_tcb` say each arm writes the one
  replenish queue its own resolver names, with
  `schedContextUnbindOnCore_replenishQueueOnCore_ne_of_tcb` lifting the second
  through the wrapper's scheduling point — and the **sweep** arm needs no such
  statement and can have none, writing every core being precisely what it
  declares.  The four SM8.B write sets moved to production with tombstones, and a
  Tier 3 anchor that pinned one at its old home is repointed rather than deleted,
  the SM8.B claim it carries being unchanged.  `tests/SmpCbsSuite.lean` §4.6 is
  the witness: the sweep fixture's entries sit on two cores, the live unbind
  purges both, and the retired home-only reading — a `private def` in the suite
  and nowhere else — declares neither.  `maxLockSetSize` is unmoved.
- **...and the destroy path declares its own, over a write set that is silent
  about the thing it moves** (WS-RR RR8.12 Cut C3b-iii, `v0.35.169`).
  `schedLockSet_lifecycleRetypeOnCore` is the live `.lifecycleRetype` arm's
  scheduler-domain footprint — **inert** until the bracket cut.  Five things new
  code must respect.  (1) **SM8.B's write set is a RUN-QUEUE write set**:
  `observableSlotsConfinedToCores` covers six per-core slots and the replenish
  queue is not one of them, so `lifecycleRetypeWriteSet` says nothing about the
  two reservation steps `v0.35.164` and `v0.35.165` put on the destroy path, and
  a footprint built from it alone is **false** of the operation.  That is what
  `tests/SmpIpcSuite.lean` §3.33 measures, computing the run-only reading beside
  the live footprint on both target shapes.  (2) **The replenish segment is keyed
  on the OBJECT KIND**, with exactly two kinds naming a core because the cleanup
  has exactly two reservation steps: a `.tcb` target's is the donation arm's
  (nothing for `.unbound`, the thread's home for `.bound`, the return's two
  migration endpoints for `.donated`, the destination read at the post-return
  state), a `.schedContext` target's is the release's, and every other kind's is
  empty — with `schedLockSet_lifecycleRetypeOnCore_empty_of_other` the
  declaration's own half, so a kind that acquires a scheduling effect has to move
  a definition rather than a proof.  (3) **The release's segment is `allCores`
  where the bound TCB is gone**, for the reason `v0.35.168`'s unbind gives on the
  same shape: with no `cpuAffinity` left to read there is no home core to name.
  (4) **Both resolvers read the PRE-state, and that is a fact rather than a
  convenience**: for a SchedContext target every earlier step of the cleanup is
  the identity, and for a TCB target the donation arm *is* the first step — so
  this whole footprint is pre-state computable with no mid-state bridge, which is
  what `.replyRecv` and `.tcbSuspend` do not get.  (5) **Exactness is composed
  over all six kinds**: two step frames, two arm frames stated against their own
  resolvers, and `lifecyclePreRetypeCleanup_replenishQueueOnCore_ne` over the
  whole cleanup, every other step of it framing the scheduler outright.
  `threadOccupiedCores` and the two retype write sets moved to production with
  tombstones — their lemma family and the confinement theorems stay staged, being
  about the destroy sweep's confinement, which is that module's question — and
  `SyscallSchedFootprint.lean` imports `Lifecycle/Invariant/RetypeReservation.lean`
  for the reference sweep's frame.  `maxLockSetSize` is unmoved.  **`.tcbSuspend`
  is the one arm left**, and it is a cut of its own: its run segment re-runs a
  seven-stage pipeline and its replenish segment two migrations read at
  intermediate states.
- **...and the last arm declares one — and the two parametric footprints it
  replaces were FALSE** (WS-RR RR8.12 Cut C3b-iv, `v0.35.170`).
  `schedLockSet_suspendThreadOnCore` is the live `.tcbSuspend` arm's
  scheduler-domain footprint — **inert** until the bracket cut, and the
  sixteenth and last of the arms RR8.12's sequence enumerated (which of the
  remaining nineteen write a scheduler slot at all is
  `declaredSchedFootprintSyscall`'s question, and the next cut's).  Six things
  new code must respect.

  (1) **The finding, which is what declaring a resolved form is for.**  Since
  WS-RR RR8.11 (`v0.35.86`) the suspend's G2 teardown is
  `cancelIpcBlockingMigrated`, and since RR8.12's second cut (`v0.35.90`) the
  live pipeline runs it: it moves the reclaimed reservation's replenishments
  from the **holder's** home core to the home the context is bound to at the
  torn state, writing the replenish queue of *both*.
  `cancelIpcBlockingOnCoreSchedLockSet`'s replenish segment was `[]` and
  `suspendThreadOnCoreSchedLockSet`'s was `[home, ownerHome, outerHome]`, which
  is G3's migration read off the **victim's** binding — a different thread and a
  different state — so neither endpoint was named by either.  RR8.12's second
  cut widened the *run* segment by the holder's placed core and did not ask the
  same question of the replenish segment: *a fix applied at one site and not at
  its sibling*.  Latent rather than live (the syscall seam does not yet bracket
  the scheduler domain), so everything stated over those footprints was
  **silent** about the two queues rather than conservative — RR8.11's and
  OD3.9's own posture.  Both are fixed here, each taking a
  `reclaimReplenish : List CoreId`.

  (2) **The resolver lives beside the transition, not beside the footprints.**
  `cancelIpcBlockingReplenishCores` is in `Lifecycle/Suspend.lean` next to
  `cancelIpcBlockingMigrated`, reading the same `let`s, because both parametric
  footprints must name it and neither can see the resolved-footprint module —
  *when a question has one owner and an asker that cannot see it, the owner is
  in the wrong layer* (`v0.35.59`).  It mentions no `SchedLockId`, so nothing
  about it belonged above that layer.  A Tier 3 negative refuses it coming back
  upstream, and the positive pins its name **followed by its parameter list**,
  because `^def X` matches a suffix-renamed `X_Moved` — the presence-check one
  character down that Cut 7 recorded for theorems.

  (3) **Neither half of the replenish segment is pre-state computable**, which
  is why this arm is a cut of its own.  G2's reclaim resolver is read at the
  pre-state (it resolves the torn state itself); G3's arm resolver is read at
  the **post-revert** state, because the reclaim rebinds the victim and WS-OD
  OD5.3's second pop then migrates to the *outer caller's* home — a core the
  pre-state cannot name, the victim holding no binding there.  So the segment
  re-runs the spine, exactly as `replyRecvBodyWriteSet` does, and a Tier 3
  negative refuses a pre-state reading of G3's arm.

  (4) **The donation-arm frame has ONE owner, at an explicit purge core.**
  `donationArmAt_replenishQueueOnCore_ne` is stated over the three-way match at
  a `home` argument, because the two askers hand it different cores — the
  destroy path reads it off the state it runs on, the suspend's G3 was handed it
  from the pre-G2 state — and a frame at `determineTargetCore st tid` covers the
  first and not the second.  `cancelDonationArmOnCore_replenishQueueOnCore_ne`
  is its instance rather than a second proof.

  (5) **Exactness is over the whole arm**:
  `suspendThreadOnCore_replenishQueueOnCore_ne`, all seven stages, of which two
  move a reservation and five frame every replenish queue, with
  `cancelIpcBlockingOnCore_replenishQueueOnCore_ne` the same pair for the
  cancellation composite — a footprint owes both halves, and the fixed one had
  gained only *names what is written*.  A claim stated over
  `cancelIpcBlockingReclaimed` alone would be a claim about a prefix of the
  transition the live `.tcbSuspend` runs, and a Tier 3 relation anchor refuses
  that shape.  Coverage against the parametric form
  (`…_covers_parametric_runQueue`) is stated over the **run-queue half alone**,
  which is the honest scope: the parametric replenish segment is four free
  parameters, so a coverage claim over it would have to hypothesise that a
  caller passed what the transition writes — which is the conclusion.

  (6) **The witness computes both retired readings beside the live ones.**
  `tests/SmpCancellationSuite.lean` §3.27 drives the live reclaim and the live
  suspend on a state the kernel reaches — the reservation queued on the holder's
  home core, the victim homed elsewhere — with core 3 as the control, in neither
  footprint and written by neither transition, so the membership assertions are
  about the migration rather than about width.  `maxLockSetSize` is unmoved and
  the golden trace is byte-identical.
- **...and the sixteen declared arms have ONE resolver, whose undeclared
  direction is the load-bearing one** (WS-RR RR8.12 Cut C4, `v0.35.171`).
  `schedLockSetForSyscall` is the scheduler domain's `lockSetForSyscall`, in the
  same module as the arms it dispatches to and for the same layering reason, and
  **inert** until the bracket cut.  Four things new code must respect.

  (1) **Adding a declared arm changes `declaredSchedFootprintSyscall`**, or
  `schedLockSetForSyscall_undeclared_none` stops elaborating.  That negative is
  what the object domain's own is: a caller reading `some S` treats `S` as the
  complete set of **cores** the transition writes, so an arm that returned a
  footprint before its coverage proof existed would hand out exclusion the
  runtime never established.  The other drift direction — an arm listed as
  declared that became unconditionally `none` — is closed by the per-arm
  `_isSome_iff` family, each stating the exact operands its arm needs.

  (2) **One operand record, because they are one syscall's operands.**
  `SyscallLockOperands` carries the scheduler domain's five extra fields beside
  the object domain's, defaulted absent, because the two domains ask *different
  questions of the same arm*: an object footprint names the objects a transition
  writes, resolved from the capability it was invoked through, while a scheduler
  footprint names the cores it writes, resolved by re-running the transition's
  own control flow — which needs the transition's own arguments.  `affinity` is
  **doubly** optional and must stay so: the inner `Option` is the unpin request,
  the outer says whether the operand was supplied, and collapsing them makes an
  unsupplied operand read as an unpin.

  (3) **Two arms route to a footprint that is not the obvious one.**
  `.notificationSignal` takes the **bound** arm's, which is the one the live
  dispatch reaches; `.reply` takes the **arm's** rather than the dispatch's,
  because `v0.35.163` proved the abandon's home-core member is one the dispatch
  never writes.  Both are pinned as relations, with the wrong resolver refused.

  (4) **The ABI seam reaches it since Cut C4b** (`v0.35.172`, the bullet below).
  Cut C4 shipped the resolver with nothing calling it, because
  `abiEntryLockOperands` supplied none of the five new fields — so wiring it that
  day would have made `.call`, `.reply`, `.replyRecv` and `.tcbSetAffinity`
  answer `none`: sound, since an undeclared arm establishes no exclusion, and it
  would have silently dropped four arms out of the coverage this workstream is
  building.  The resolver's docstring said so rather than leaving a reader to
  discover it by wiring it up, and C4b closed it by extending that one builder.
- **...and the ABI seam resolves ONE decode for BOTH domains** (WS-RR RR8.12
  Cut C4b, `v0.35.172`).  `declaredSchedLockSetForAbiEntry` is
  `declaredLockSetForAbiEntry`'s twin clause for clause — `abiEntryPlan`, then
  `abiEntryLockOperands` on that plan's answer, then the domain's own resolver —
  and it is still **inert** until the bracket cut.  Five things new code must
  respect.

  (1) **One builder, not two, and that is the whole of the cut.**  The obvious
  shape is a second operand builder for the scheduler domain; it is the shape
  that lets one domain's footprint be acquired around the other domain's
  transition, because two builders may resolve a capability differently, decode
  a different argument, or read a different state.
  `declaredSchedLockSetForAbiEntry_shares_decode` states the alternative as a
  fact: both footprints are functions of the *same* `(tid, decoded, stFilled)`
  and the *same* `ops`.  A Tier 3 negative refuses the resolver re-deriving the
  gate or the capability lookup.

  (2) **What that costs is a congruence the object domain must satisfy.**  One
  record for two domains means a field added for one could move the other's
  answer, so `lockSetForSyscall_ignores_sched_operands` says it cannot — stated
  over all five fields at once, so a sixth added without extending it is a field
  nothing has checked, and measured at the seam's own operands in the witness.
  That is what makes "the object domain is byte-identical to Cut C4's" a theorem
  rather than a reading of two definitions.

  (3) **Four arms grew the operands their scheduler footprint refuses without,
  and each names what its own live dispatch arm names.**  `.call` the invoked
  capability's rights and the receiver's slot base; `.reply` the `MessageInfo`
  and register payload `decodeFaultReply` reads to tell a restart from an
  abandon; `.replyRecv` the reply *payload* — MR0 stripped, badged with the
  **reply** capability's badge rather than the endpoint receive cap's, which is
  SM6.D's own distinction and is refused in the wrong spelling by a negative;
  `.tcbSetAffinity` the destination core through both decoders, since its inner
  `Option` is the unpin request.

  (4) **Eight arms are here because the SCHEDULER domain declares for them** —
  the five TCB-directed ones, the three SchedContext ones and the retype — and
  `lockSetForSyscall` answers `none` at every one of them whatever these fields
  hold.  `.schedContextBind` names the **decoded `threadId` argument** rather
  than the capability's object, because that is the thread its own live arm
  binds, and its raw operand is validated at its own lift.

  (5) **The `.replyRecv` footprint's CSpace root is the gate's own.**  The live
  arm passes `gate.cspaceRoot`; the scheduler resolver has no gate, so it reads
  the caller's TCB at the same state.  `abiEntryGate_cspaceRoot` and
  `abiEntrySchedReceiverCspaceRoot` are what make those one lookup rather than
  two readings of one question — the shape that would let a footprint name a
  root the transition does not walk.  The witness is state-dependent by
  construction: an `.Inactive` victim declares the object-store lock alone and an
  **active** one, one field apart, additionally declares the executing core's run
  queue, which a resolver ignoring the state could not do.
- **...and the family that resolver dispatches to is derived and reconciled**
  (WS-RR RR8.12 Cut C5, `v0.35.173`).
  `SeLe4n/Testing/SchedFootprintCensus.lean` (Tier 1) is the object domain's
  `LockFootprintBoundCensus` for the scheduler domain, and it exists because Cut
  8a-ii measured the gap: **thirty-three of the family's forty-seven theorems
  had neither a consumer nor a Tier 3 anchor**, every one silently deletable,
  because their consumer is the bracket cut and the bracket cut has not landed.
  Eight hand anchors were the stopgap; a hand-written list is what a census
  retires.  It asks two questions, and reports **17 footprints, all canonical,
  15 consumed, 2 registered as superseded**.

  (1) **Every footprint is the canonical `schedFootprintOfCores` ladder, at its
  full arity** — and that is not a style rule, it is the premise every generic
  lemma is consumed under.  The scheduler domain restates none of
  `_write_only` / `_pairwise_le` / `_keys_nodup` / `_subset` / `mem_…_iff` per
  footprint, because they are stated once of `schedFootprintOfCores` and
  inherited *by being that function applied to two core lists*; a footprint
  written any other way loses all five **silently**.  `_keys_nodup` is
  `SchedLockSet.ofList?`'s own obligation, so such a footprint can make the
  constructor refuse and the arm then answers `none` — an *undeclared* arm,
  which the bracket treats as no exclusion established, so it is sound and it
  drops the arm out of the coverage this workstream is building.  `_pairwise_le`
  is the ladder's acquisition order, and there is no other proof of it.  The
  question is put to the elaborator by reducing **towards** the constant
  (`Meta.whnfUntil`), since `whnf` would run past it into the `List.cons` the
  body builds and the question would be unaskable.

  (2) **Every footprint is NAMED by `schedLockSetForSyscall`, or registered with
  a reason** — and *named*, not *reached*: a transitive closure would count a
  footprint as consumed because some reachable helper mentions it, which is the
  presence-for-relation substitution one level down and would silence the census
  exactly where it fires.  The register holds two supersessions — the **bare**
  notification signal (the live dispatch routes through the bound arm) and the
  **dispatch**-level reply footprint (the arm's sits over it, and `v0.35.163`
  proved the abandon's home-core member is one the dispatch never writes) —
  reconciled in both directions, so a stale exemption fails as loudly as an
  orphan footprint.

  (3) **Neither failing branch can fire on the live tree, so the plants are the
  measurement.**  A canonical footprint and a hand-written ladder carrying a
  member the canonical form also carries; a constant with the family's **name**
  and not its **type**, which must stay outside the derived family permanently
  rather than for the length of one mutation run; and a namer pair whose
  indirect half is what separates *named* from *reached*.  The pair alone is not
  enough — it decides `namedBy`, and a `resolverConsumed` that closed over it
  transitively would pass every plant — so the self-test carries a **wiring
  case** drawn from the live tree: a write-set helper is named by a footprint and
  by no arm, so it is reached at depth two and named at depth one by nothing.

  (4) **The shape check carries no arity test, deliberately.**  The applied term
  is the definition at its full telescope and its type is
  `List (SchedLockId × AccessMode)`, so a reduction stopping with
  `schedFootprintOfCores` as head has it fully applied by type-correctness: the
  condition could only ever be true, and *a condition no input can decide is
  indistinguishable from a wrong one*.  A Tier 3 negative refuses it coming back.
- **...and the first eight arms' footprints are proved not to be false** (WS-RR
  RR8.12 Cut C6a, `v0.35.174`).  A footprint that omits a slot the transition
  writes is **false**, and the 2PL serialisation results,
  `boundedWait_under_2pl` and the CC-5 contention bound are then *silent* about
  that slot rather than conservative —
  `UncoveredLockDomain.syscallSeamSchedulerDomain` was the register entry saying
  the scheduler domain had not met that standard at the syscall seam (retired at
  Cut C6h, `v0.35.181`, once it had).  Cut C4
  gave every declared arm a footprint and C4b wired the seam's resolver to it;
  **the coverage lands before the bracket**, which is the numbering rule's
  semantic half: a bracket acquiring a footprint nobody proved covers the writes
  hands out exclusion the runtime never established.
  `SeLe4n/Kernel/SyscallSchedContainment.lean` is staged, for the reason
  `SchedLockTimerContainment` is — every proof consumes an SM8.B confinement
  theorem, and those are staged.  Four things new code must respect.

  (1) **One bridge, and the three clauses are discharged three different ways.**
  `schedFootprintCoversWrites_of_cores` (production, beside the obligation) makes
  the **object** clause structural — `schedFootprintOfCores` always names the
  object-store table write lock, a scheduler footprint being a footprint of an
  operation that stores — and reduces the rest to two hypotheses;
  `schedFootprintCoversWrites_of_confined` (staged) supplies the **run-queue**
  clause from the arm's own `observableSlotsConfinedToCores`.  The **replenish**
  clause has no such bridge and cannot: confinement covers six per-core slots and
  the replenish queue is not one of them, which is exactly why every donating arm
  carries a frame of its own.  A new arm's coverage is one application, not a new
  argument.

  (2) **The split between this cut and the next is semantic, not convenient.**
  Where an arm's replenish segment is `[]` the clause is a **whole-state frame**
  (the transition writes no core's replenishment at all); where the segment names
  cores it is an **exactness** claim (unchanged outside exactly those).  Those are
  different propositions with different frames, so the empty-segment arms —
  `.notificationWait`, `.notificationSignal`, `.send`, `.tcbResume`,
  `.tcbSetPriority`, `.tcbSetMCPriority`, `.schedContextBind` — are here, and
  `.tcbSuspend` joins them because RR8.12's fourth cut already built its `_ne`
  frame.  The remaining eight are Cut C6b's, with the frames they need.

  (3) **Eight proved theorems cannot be wrong; they can be VACUOUS**, so the
  module carries the refutations that say the obligation is not held by every
  footprint — one per clause, and the replenish one is the sharper because it is
  the clause no confinement result can reach.  A Tier 3 negative refuses
  `schedFootprintCoversWrites_refl` anywhere in the module: discharging an arm
  with the no-op lemma is the token-preserving weakening this family admits, and
  it would turn eight measurements into eight tautologies.

  (4) **A coverage claim names the arm the live dispatch reaches.**
  `.notificationSignal`'s is stated of the **bound** arm, which is what the
  resolver names and what `API.dispatchWithCap{,Checked}` routes to; the bare
  signal's footprint is registered as superseded in `SchedFootprintCensus`, and a
  coverage theorem for it would be a claim about a transition no syscall reaches.
- **...and the first three core-naming segments are covered, with the `_ne`
  frames keyed on the FOOTPRINT rather than on a resolution** (WS-RR RR8.12 Cut
  C6b, `v0.35.175`).  `.schedContextConfigure`, `.schedContextUnbind` and
  `.tcbSetAffinity` are the first arms whose replenish segment names cores, so
  their clause is an **exactness** claim rather than a whole-state frame.  Three
  things new code must respect.

  (1) **An arm's `_ne` frame is keyed on its own replenish segment.**
  `schedFootprintCoversWrites`'s clause asks *unchanged at every core the
  footprint does not name*; a frame keyed on a resolution — "`c` is not this
  SchedContext's replenish home", "`c` is not this thread's target core" —
  answers a different question that every consumer must then case-split to reach,
  which is the duplication this family exists to avoid.  So the footprint-keyed
  form carries the plain `_ne` name and the resolution-keyed one is `_ne_of_sc` /
  `_ne_of_tcb`; a Tier 3 negative refuses the plain name re-acquiring the narrower
  hypothesis, because a family where `_ne` means two things at two arms is exactly
  what a coverage proof gets wrong without noticing.

  (2) **An unresolved segment is a refusal, not a gap.**  A
  `.schedContextConfigure` whose SchedContext does not resolve, and a
  `.schedContextUnbind` whose SchedContext has no bound thread, both make the
  *transition* fail — so the empty segment costs the claim nothing, and the proof
  says so by deriving the contradiction rather than by assuming resolution.

  (3) **`allCores` is a segment, and the clause is then vacuous — correctly.**  A
  SchedContext bound to a thread the store no longer holds has no `cpuAffinity`
  left to read, so the unbind sweeps every core's replenishment and the footprint
  declares every core's lock; there is no core outside it, which is the honest
  reading rather than a hole.
- **...and the two IPC spines get their exactness frames, with `.call` covered**
  (WS-RR RR8.12 Cut C6c, `v0.35.176`).  The IPC arms' replenish segments are
  *computed by running the transition*, so their exactness frames are the one
  place a footprint and its operation could describe different migrations.  Four
  things new code must respect.

  (1) **The segment's branch structure and the transition's are the same
  structure, by construction** (Cut C3a), so each frame is one case split that
  visits both at once rather than a second reading of the transition.  Every arm
  short of a resolving donation leaves the segment empty and the step's own frame
  applies; the resolving arm is the SM5.H migration's `_other` frame at exactly
  the pair the segment names.

  (2) **Each donation step gets its own `_ne` beside its `_of_no_donation`.**  The
  existing frames say the hand-off moves *nothing* when the resolver declines;
  the new ones say *where* it moves when it answers, which is what the replenish
  clause needs.  Both directions matter and neither implies the other.

  (3) **The `.reply` arm's frame cannot be the hypothesis-parameterised one.**
  `replyTransferOnCore_replenishQueueOnCore_of_dispatch` asks for the dispatch's
  frame at *every* message, and the segment is message-dependent — the fault
  branch composes the dispatch at `IpcMessage.empty` and the ordinary branch at
  `msg`.  So the footprint-keyed frame is stated per branch, through
  `faultReplyOnCore_replenishQueueOnCore_ne`, and `faultReplyApplyOnCore` frames
  every replenish queue on both its outcomes.

  (4) **`.call`'s coverage is stated of the UNCHECKED dispatch** — what the write
  set and the confinement result are stated at, and what the checked arm equals
  wherever its flow gate admits; a denied flow commits nothing, so the covered set
  is the same either way.  `.reply`'s coverage waits on a confinement theorem at
  `replyTransferWriteSet` that does not exist yet, which is Cut C6d's first row
  rather than an omission here.
- **...and a coverage claim names the ARM, not the dispatch beneath it** (WS-RR
  RR8.12 Cut C6d, `v0.35.177`).  `schedLockSet_replyTransferOnCore` had nothing
  behind it because the confinement surface stopped at
  `endpointReplyCrossCoreDispatch`, and the arm `API.dispatchWithCap` runs is
  `replyTransferOnCore` — seL4's `doReplyTransfer` branch — whose **post-state is
  not the dispatch's**: it adds the delivered-message staging on an unfaulted
  caller and the decoded outcome on a faulted one, the latter either installing a
  restart frame or *descheduling* the faulted thread.  A coverage claim proved at
  the dispatch is a claim about a different state, however closely the two write
  sets agree.  Three things new code must respect.

  (1) **Each member of the chain is stated at the write set its OWN definition
  derives** — `applyFaultRestart_confinedToCores` at `[]`, the abandon's at
  `[cc]`, `faultReplyApplyOnCore_confinedToCores` at `faultReplyApplyCores`,
  `faultReplyOnCore_confinedToCores` at `faultReplyWriteSet`, and the arm's at
  `replyTransferWriteSet` — so the coverage theorem is one application of
  `schedFootprintCoversWrites_of_confined` and not a second reading of the seam.
  The `regs` conjunct is what made two machine frames load-bearing and missing
  (`applyFaultRestart_machine_eq`, `faultAbandonOnCore_machine_eq`): a fault
  outcome writes the *thread's* saved context, never the executing core's bank.

  (2) **A claim about what a transition writes is read off a measurement, not off
  the shape of the definition that declares it.**  This cut's own first draft said
  the abandon "deschedules on a core the dispatch never names".  It does not:
  every arm on which the dispatch succeeds opens its write set with
  `[determineTargetCore st target]` and no step of it writes a `cpuAffinity`, so
  the appended `determineTargetCore st' faulted` is a **duplicate** — and
  `tests/FaultHandlingSuite.lean` §7c had been measuring exactly that since Cut
  C3a.  The draft was written from the definition's shape with the measurement
  sitting beside it unread.  When a cut's finding is about what a program writes,
  find the assertion the tree already makes about it *before* writing the
  sentence; where there is none, the sentence is what the cut owes.

  (3) **The declaration stays derived from the arm, and the measurement becomes an
  assertion.**  Tightening the segment to today's coincidence would make it false
  the moment either side moved, so the write set is still the arm's own; what
  changed is that the duplicate is now asserted, with the restart's *empty* append
  as its control — a write set naming every core satisfies neither.
- **...and a coverage claim's UNIT is what the footprint bounds, which may be a
  sub-composition** (WS-RR RR8.12 Cut C6f, `v0.35.179`).  `.receive` is the one
  declared arm whose chain walk sits **outside** its run segment — the walk's
  cores are state-discovered and are declared dynamically through
  `pipChainSchedFootprint` — so `schedLockSet_endpointReceiveOnCore_coversWrites`
  is stated at the leg composed with WS-OD OD3.6's donation, and a claim at the
  whole hand-off would be *false* of that footprint.  A Tier 3 negative refuses
  that spelling, because a coverage theorem naming the wrong unit reads exactly
  like one naming the right one.  Three things new code must respect.

  (1) **A footprint resolved BEFORE a transition and a resolver read AFTER it
  must be shown to name the same thing.**  The arm hands the hand-off the thread
  the *leg* reports; the segment is read off the *pre-state* send queue.
  `endpointReceiveDualWithCapsOnCore_ok_dequeued_eq_head` and its block-path
  sibling are what close that, and they did not exist: every other rendezvous
  frame did, because until a coverage proof nothing had to relate the leg's
  **output** to the resolver.  A new arm whose footprint and transition resolve at
  different states owes the same lemma.

  (2) **Look for the degenerate case before reaching for an invariant.**  The
  block path hands the hand-off the *receiver's own id*, and
  `callDonationSchedContext?_self` — a thread donates nothing to itself, because
  the resolver reads an `.unbound` binding twice — is that path's whole donation
  story.  No reasoning about the post-state `ipcState` is needed there at all.
  `queueHeadBlockedConsistent` is then taken for exactly one corner and named at
  the point of use rather than carried by the family.

  (3) **Write the helper and let the build tell you it exists.**  Two confinement
  theorems this cut needed were written, compiled, and rejected as *already
  declared* — the tree has had both since WS-OD OD3.6.  That is a cheaper search
  than grepping for a name you would have had to guess.

  One mechanical note, the same hazard as Cut C6e's at a smaller unit: an anchor
  pattern written against a witness label containing a **backtick** must count the
  characters, because `.` matches one — `the .receive. segment` misses
  ``the `.receive` segment`` by exactly one.  The sweep reported it as a failing
  command rather than as a silent pass, which is the direction that class must
  fail in.
- **...and two lock DOMAINS that write the same word are one footprint, never
  two brackets** (WS-RR RR8.12 Cut C6h, `v0.35.181`).  The syscall seam brackets
  on the scheduler domain now, which deletes
  `UncoveredLockDomain.syscallSeamSchedulerDomain` — and the design was decided
  by a measurement that **contradicted the retired constructor's own stated
  reason**.  It said the object-domain footprints hold `stateLevelLock` and
  per-object locks *"**not** the object-store table lock"*; they are the same
  lock, because `acquireLockOnObject`'s `.objStore` arm writes
  `SystemState.objStoreLock` and reads nothing else of the `LockId`.
  `schedObjStoreLockId`'s docstring had said so since SM5.A.2 and **nothing
  stated it**, which is why a claim built on the opposite could stand for
  fourteen minor versions.  Four things new code must respect.

  (1) **Nesting two brackets over one set of lock words is a ladder violation,
  not a double-acquire nuisance.**  `lockAcquireSequence` orders *one* list, so
  an inner bracket's level-0 table lock taken after an outer bracket's levels
  1..9 is a sequence the SM0.I ordering theorem says nothing about — and
  deadlock freedom in this tree rests on that ordering.  The seam therefore
  acquires one unified `SchedLockSet`, which is what `SchedLockId` was
  introduced for: *a cross-domain order exists precisely so a cross-domain
  acquisition is one ladder.*

  (2) **A canonicalisation is sound only if EVERY operation on the two keys
  agrees**, so it is pinned at all four primitives — acquire, release, withdraw
  and held.  Pinning the acquire alone would leave a release that read the
  `ObjId` free to disagree, and the two keys would then be one word for taking
  and two for giving back.

  (3) **A claim travels to a superset rather than being restated at it.**
  `schedFootprintCoversWrites_mono` is why the sixteen per-arm coverage theorems
  are not re-proved over the unified footprint: every clause of the predicate is
  of the form *"a lock the footprint does **not** name"*, so a superset only
  discharges more antecedents.  Read the direction carefully — it is about the
  *obligation*, not about footprint quality: lock contention is an observable
  channel (SM8.D's CC-5), which is why the footprints themselves stay narrowed
  per arm.

  (4) **Acquiring is not covering, and that asymmetry is what makes a bracket
  landable early.**  An arm declared in one domain and not the other acquires
  what that domain declared; the other domain's writes stay outside a footprint
  until it declares one.  An arm neither declares is the bare step, bit-identical
  to the pre-bracket seam.  That is RR7.12's posture, and it is the reason a
  bracket may precede the declarations it does not yet have while a *coverage*
  claim may not.
- **...and a claim's unit is the PROGRAM the arm runs, wrappers included** (WS-RR
  RR8.12 Cut C6g, `v0.35.180`).  The sixteenth and last declared arm, and the one
  whose transition is three wrappers deep: `.lifecycleRetype` dispatches
  `lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache` — the retype with its
  cleanup, the `.aside1` shootdown round for the destroyed and rebound ASIDs, the
  initiator's own per-core TLB drain, and the domain-wide `IC IALLUIS`.  Each of
  those two cached-structure layers writes kernel state, so a coverage claim taken
  at the retype core is a claim about a program the arm does not run, and a Tier 3
  negative refuses that spelling.  They are both scheduler-silent *by theorem*
  (`retypeInitiatorDrain_scheduler`, `Architecture.withIcacheBroadcast_frame`'s
  third conjunct), which is what lets the exactness frame descend through them by
  citation rather than by a second case analysis of the arm — the difference
  between a claim that inherits its wrappers' frames and one that re-derives them.
  Three things new code must respect.

  (1) **A segment over a destroyed object is read at the PRE-state, and that is
  not a convenience.**  The object a retype destroys is gone from the post-state,
  so a post-state reading of `lifecycleRetypeWriteSet` or
  `lifecycleRetypeReplenishCores` would name the empty set on exactly the
  transition the segments exist for.  Both take `st`, which is also what a bracket
  needs — it resolves a footprint *before* the transition runs — so this arm has
  no instance of WS-HP HP10.8's footprint/transition resolution asymmetry.

  (2) **The layering rule is a convention, not an accident, and this is its
  fourth instance in one sequence.**  `retypeInitiatorDrain_scheduler`,
  `retypeInitiatorDrain_machine` and a private `lifecycleRetypeDirect_framed` were
  declared in the **staged** `InformationFlow/NonInterferenceCrossCore.lean`, so
  the production replenish frame could not read the two frames it needs and the
  third was a private duplicate of a fact the production wrapper module can state
  outright.  They live beside the wrappers they frame now.  Cuts 5, 7, 8a-ii and
  C3a each paid the same rule; when a sequence pays it four times, a new frame
  over a production transition goes beside that transition on the day it is
  written rather than in whichever module first needed it.

  (3) **Where every mutation breaks ELABORATION, the witness is a differential
  inside the suite.**  Dropping either of this footprint's segments, or widening
  both to `allCores`, fails to elaborate — the definition's own membership
  theorems unfold it — so a coverage assertion in `tests/SmpIpcSuite.lean` cannot
  be shown decisive against the production code by mutation.  That is §3.23's
  situation for the splice's store shape, and the answer is §3.20's: §3.33 (d)
  takes the *same measurement* over `runOnlyRetypeFootprint` — the retired reading
  with no replenish segment, spelled in the suite and nowhere else — and asserts
  it **fails**.  A coverage assertion with no failing counterpart beside it is
  indistinguishable from one the fixture satisfies by accident.
- **...and a NEGATIVE anchor over prose is a prose check, which only a mutation
  tells you** (WS-RR RR8.12 Cut C6e, `v0.35.178`).  The cut retired a hand-kept
  figure — `SyscallSchedContainment.lean`'s §7 said *"Eight coverage theorems
  above"* at fourteen — and wrote a `run_negative_check` refusing its return.  It
  passed on the clean tree and **passed on the mutation that restored the
  sentence**, because the sentence lives in a `--` comment and `run_negative_check`
  reads the code view, which blanks it.  That is this file's own *gates read code,
  prose reads prose* rule at the one case it exists for — the subject genuinely
  **is** the text — and the anchor is `run_prose_negative_check` now.  What is worth
  keeping is not the instance but how it surfaced: a negative that cannot match is
  indistinguishable from a tree that is clean, so the only thing that separates them
  is breaking the relation it forbids.  Ask of every new negative whether its
  subject survives the view the helper routes through.

  Two further things that cut recorded.  **The composite's frames are keyed on the
  SUB-SEGMENT each stage appends**, not on which path the stage took: a four-stage
  arm whose frame took four path hypotheses would be a claim a bracket cannot
  discharge, since a bracket resolves the footprint before the transition runs.  And
  **a sweep's own input can be malformed, which the row accounting catches**: the
  first run reported *"accounted for 473 of 474 selected rows"* because
  `select_changed_anchors.py` writes its `# derivation:` line to stderr and the
  invocation had merged it in with `2>&1`.  The gate was right; read a shortfall as
  a question about the selection before reading it as a question about the anchors.
- **A thread's base priority has ONE home: `TCB.priority`** (`v0.35.133`).  It had
  **two** until this cut — the TCB field and, mirrored onto it by the AK2-B
  propagation convention, its reservation's `SchedContext.priority` — with
  `SystemState.threadBasePriority` choosing between them by
  `SchedContextBinding.ownScId?` and `boundThreadPriorityConsistent` keeping the
  pair in step.  The pair is what `v0.35.98` found `.tcbSetPriority` not
  maintaining: a demotion re-bucketed the thread at its new band while every
  later wake re-inserted it at the old one, permanently, because the run queue is
  keyed by `TCB.boostedPriority` (the thread's field) and the resolver read the
  reservation's.  A demotion that does not stick is a temporal-isolation break in
  exactly the mixed-criticality deployments MCS exists for, and it needed no
  authority beyond what the syscall already requires.

  **The remedy is structural rather than another writer** — for *reads*, and
  `v0.35.136` is where that qualification stops being implied and starts being
  printed.  This paragraph said "with one home the pair is unfalsifiable by
  construction, so a stale mirror is not a defect that was fixed but a state no
  writer can reach", and PR #897's review found the writer: the collapse gave the
  band one **reading** home and left it two **writing** homes, so a stale mirror
  is still reachable and `boundThreadPriorityConsistent` is still falsifiable —
  it just no longer mis-schedules anything, which is the whole of what the
  collapse bought.  See the standing constraint *a `bound*Consistent` predicate
  is a writer fact* below for the two routes and the register row.  Six things
  new code must respect.

  (1) **Every reader reads `TCB.priority`, at every binding.**  Five did the
  classification and all five are collapsed: `SystemState.threadBasePriority`,
  `resolveEffectivePrioDeadline`, `effectiveSchedParams`,
  `getCurrentPriorityChecked` and the frozen
  `FrozenSystemState.threadBasePriority`.  `threadBasePriority_eq`,
  `effectiveBucketPriority_eq` and `FrozenSystemState.threadBasePriority_eq` are
  the `rfl` statements of that, and `FrozenSystemState.threadBasePriority_eq_live`
  is the live/frozen agreement — which under two homes could only be stated per
  binding and under a consistency hypothesis, and is now the strongest form such
  an agreement can take.

  (2) **`effectiveBucketPriority` was the THIRD copy of the resolver and its body
  is gone.**  It mirrored `resolveEffectivePrioDeadline` because
  `Scheduler/Invariant.lean` sits below `Selection.lean` and could not call it —
  a second implementation held in step by a pin, which is the shape this project
  spends its length retiring and which existed only because there were two bases
  to choose between.  It is `TCB.boostedPriority` now and the pin is `rfl`.

  (3) **The run-queue invariants moved with the readers, and then COLLAPSED.**
  `effectiveParamsMatchRunQueue` and `effectiveParamsMatchRunQueueOnCore` asserted
  on their `.bound` arm that the recorded bucket equals the RESERVATION's
  `priority`.  That was over-strong the moment the base had one home — the queue
  is keyed by `TCB.boostedPriority` — and under two homes it was precisely the
  conjunct that had to hold for the `v0.35.98` defect not to strand a demoted
  thread.  With all three arms saying the same thing the binding case analysis is
  **deleted**, and auditing this cut's own diff is what showed that keeping it was
  wrong rather than merely untidy.  Its `.bound` arm ended `| _ => True`, so a
  bound thread whose reservation did not resolve was silently excused from the
  bucket claim: *a scanner's default branch is a decision* one artefact over — a
  **predicate's** default arm is one too, and that one excused a case nobody chose
  to excuse.  And under two homes this predicate and `schedulerPriorityMatch` were
  **jointly unsatisfiable** for any bound thread whose mirror had drifted, which is
  the S-H04 over-constraint `Scheduler/Operations/Core.lean`'s own header records
  — so the collapse is what makes the pair satisfiable rather than merely shorter.

  (4) **Three theorems retire into one, and the HYPOTHESES are the point.**
  `boostedPriority_eq_resolve_unbound` (AI3-A) related the selector's base
  component to `TCB.boostedPriority` at `.unbound`;
  `resolveEffectivePrioDeadline_fst_eq_boostedPriority_of_agree` (SM5.I) extended
  it to `.bound` **under the `boundThreadPriorityConsistent` agreement specialised
  to the thread**; `resolveEffectivePrioDeadline_fst_of_donated` (WS-OD) was the
  `.donated` payoff.  With one home the `.bound` arm reads the TCB field like the
  other two, so that agreement hypothesis is discharged by nothing at all — and a
  name like `_of_agree` kept past its hypothesis is not merely redundant, it
  *teaches a false dependency*: a reader would go on believing that weakening the
  bind/configure propagation costs the selector its priority ordering.  It does
  not.  The three are deleted for the one unconditional
  `resolveEffectivePrioDeadline_fst_eq_boostedPriority`, with a tombstone and
  three Tier 3 negatives.  **Deadlines have no counterpart and must not be read as
  having one**: bind copies only the priority, so a TCB-*deadline* comparison still
  diverges from the selector for exactly the bound threads CBS exists for, which is
  what the `chooseThreadEffectiveOnCore` gate says.

  (5) **`SchedContext.priority` survives as what it always was on the WRITE side**
  — the band a reservation *configures* its bound thread to, propagated into the
  TCB by `schedContextBind` and `schedContextConfigureBoundPropagate` — and no
  scheduling decision reads it.  `boundThreadPriorityConsistent` is therefore no
  longer load-bearing for any read; it is **kept, not retired**, as the only
  artefact stating that the propagation happened, which is a real property of those
  two writers and not a tautology.  A new *reader* of `SchedContext.priority` as a
  thread's band is the defect this cut closed; a new *writer* still propagates.
  **And a justification that names a constraint the cut removed invites deleting a
  live write**: `schedContextBind`'s propagation comment said the two run-queue
  invariants *jointly force* `tcb.priority = sc.priority` with no operation
  establishing it — its whole stated reason, and false the moment neither predicate
  read a reservation.  When a cut retires a constraint, sweep the comments that
  cite it as a *reason*, not only the ones that cite it as a fact.

  (6) **A witness for a collapsed mirror lives on the state the collapse makes
  UNREACHABLE.**  The soundness argument and the testability problem are the same
  sentence: on a state satisfying `boundThreadPriorityConsistent` the two readings
  agree *by construction*, so a fixture built there asserts nothing about which one
  is live and passes either way.  What discriminates is a **drifted** state — the
  shape `v0.35.98` produced — and four fixtures in this tree were already sitting
  on one, which is why all four failed when the readers collapsed.  The instinct on
  such a failure is to make the fixture consistent; that is right for a fixture
  whose subject is the *operation* and wrong for one whose subject is *which field
  the operation reads*, and doing it everywhere would have left the cut with no
  decisive witness at all.  So `AK8-E.2` and `AN10-D.6` keep their drifted states
  and flip their expectations; `PM-010b` becomes consistent because its subject is
  the cap firing, with `PM-010c` added to carry the drifted half; and the
  `v0.35.99` frozen-ceiling witness is restated over **both** branches of the cap,
  since the divergence it was written for has no state left to arise on and what
  survives is that the two surfaces fire *and decline* together.  Generalising:
  when a cut makes two readings agree everywhere, the only witness that can fail on
  a revert is one standing on the disagreement the cut abolished — keep it, name it
  as such, and say in the fixture why the state is one the kernel no longer
  reaches.

  The collapse is behaviour-preserving on every reachable state, and that is
  measured rather than argued: `schedContextConfigurePropagates` is
  `ownScId? = some scId`, which is exactly the condition the retired resolver
  classified on, so the two readings differ only where the mirror had already gone
  stale — and the golden trace is byte-identical at 239/239 with the whole library
  building.

  The **frozen** surface writes the configured band too (`v0.35.99`):

  `FrozenSystemState.threadBasePriority` is its reader and
  `frozenWriteBasePriority` the one writer both `frozenSetPriority` and
  `frozenSetMCPriority`'s ceiling call, so a new frozen priority operation reads
  and writes the pair the way the live one does rather than growing a second
  answer.

  **And a priority write moves the thread's run-queue BUCKET, on both surfaces**
  (`v0.35.101`, reported on PR #897).  `TCB.boostedPriority` is
  `priority.raisedBy pipBoost`, so a **base** write moves the run-queue key exactly
  as an inherited-**boost** write does, and every live writer of either re-buckets:
  `updatePipBoostOnCore`, `migrateRunQueueBucketOnCore` (which
  `applyPriorityChangeOnCore` composes) and `schedContextBind`'s Z5-G3 step.  On the
  frozen surface the mechanics were spelled *inline* in `frozenUpdatePipBoost`, so
  only the boost half was answered and three base writers moved nothing.  They are
  one definition now — `frozenQueuedAnywhere`, `frozenRebucketRunnable` and
  `frozenWriteTcbRebucketed` (`FrozenOps/Core.lean`, beside `frozenEnsureRunnable`)
  — and a new frozen writer of either field calls them.  Two things new code must
  respect.  (1) **The guard is per-operation and the mechanics are shared**, because
  the live writers disagree about the guard and faithfully: `updatePipBoostOnCore`
  migrates only `if oldPrio != newPrio` while the base writers migrate whenever the
  thread is queued, and the difference is observable — `RunQueue.insert` appends, so
  a remove-and-reinsert at an unchanged key moves the thread to its bucket's tail,
  and `frozenRunAgrees` compares buckets as **lists**.  (2) **The key is the live
  accessor**, read off the record being written: `frozenEnsureRunnable` and
  `frozenChooseThread` already read `TCB.boostedPriority`, so "which bucket does this
  thread belong in" has no frozen-specific answer and must not acquire one.  The
  third site was found by sweeping the *question* rather than the two the review
  named: `frozenSchedContextConfigure` propagated **neither** thread-owned parameter
  and re-bucketed nothing, so every frozen post-configure state with a bound owner
  falsified `boundThreadPriorityConsistent` **and** `boundThreadDomainConsistent`.

  What `v0.35.98` measured, on the live per-core dispatch path: a
  `seL4_TCB_SetPriority` demotion of a bound thread from 50 to 10 re-bucketed it
  at 10 and its first wake re-inserted it at **50**, the band the demotion had
  removed — permanently, since every later wake reads the same stale field.  A
  demotion that does not stick is a temporal-isolation break in the
  mixed-criticality deployments MCS exists for, and it needed no authority
  beyond what the syscall already requires.

  **And the frozen surface reads the same field because the live resolvers read
  it, which is now a theorem rather than a coincidence** (`v0.35.134`).
  `effectiveSchedParams_fst_eq_boostedPriority` states that the triple-valued
  resolver's priority component **is** `TCB.boostedPriority`, unconditionally and
  derived from the existing pair bridge; `FrozenOps.Agreement`'s
  `frozenComputeMaxWaiterPriority_eq_live_reading` carries that across to the
  frozen waiter fold, quantified over *every* live state because the reading
  turns out to read none of it.  PR #897's review reported the two as diverging,
  correctly against `v0.35.132`; `v0.35.133` closed it and swept neither the
  prose nor the missing pin, which is this file's own *sweep the forward-looking
  prose* rule unrun at the cut that made it stale.

  **Sweeping that question found `frozenResumeThread` reading the wrong priority
  in three places**, and the three are what a mirror looks like when nothing
  compares it.  It cleared `ipcState` alone where the live `restoreToReady`
  clears five fields — the fifth, `pendingReceiveReply`, keeps `replyIsStashed`
  true and so makes lifecycle cleanup of that Reply answer `revocationRequired`
  with no receive pending; it carried the pre-suspend `pipBoost` where the live
  resume re-derives it from the post-restore blocking graph; and it compared the
  two **base** priorities where the live test compares the effective ones, so the
  surfaces disagreed in both directions whenever either thread carried a boost.
  Three things new code must respect.  (1) **The field clear is
  `TCB.restoredToReady`** (`Model/Object/Types.lean`, beside `TCB.boostedPriority`
  and `TCB.blockingServer?`), because it had *no name to call* — it was spelled
  inline inside `updateTcb`'s lambda, which is why the mirror carried four fewer
  fields; both surfaces call it now, so a field added to the restore reaches both
  by construction.  (2) **A frozen scheduling decision reads
  `TCB.boostedPriority`**, never `TCB.priority`, and the live counterpart to cite
  is `resolveEffectivePrioDeadline_fst_eq_boostedPriority`.  (3) **Clearing
  `current` is the frozen spelling of the live re-enqueue-then-schedule** —
  dispatch here is `current := some tid` with the thread left in its bucket — so
  that one is *not* a divergence, which was checked rather than assumed.

  What made all three invisible is worth more than the instances: none of the
  three frozen-resume scenarios sets `scheduler.current`, so the preemption
  branch was unexecuted, and `.tcbResume` is outside `FrozenOpBranch.all`, so no
  differential reached it — while the live side has had four scenarios for the
  same two steps since R5.B and PR #811.  `frozenOpUncheckedReason` had recorded
  the gap as *"adapter owed"* the whole time.  **A stated reason bounds nothing**;
  it says who owes the work, and until it is paid a cut that touches a live
  transition with a frozen mirror sweeps the mirror by reading both bodies.

  **And the collapse had a SIXTH reader and an unswept theorem family**
  (`v0.35.134`, PR #897's review against `v0.35.133` itself).
  `threadSchedulingParams` (`Model/Object/Structures.lean`) — the Z1-N migration
  bridge, reachable from the root-imported model API — still took a `.bound` or
  `.donated` thread's band from `sc.priority`.  It is **deleted**, not
  collapsed, and on measurement: zero consumers anywhere in the tree, so
  collapsing it would have produced a fourth reading nobody asks.  New code
  reads `effectiveSchedParams`.

  The family is the same rule one file over.  `v0.35.133` deleted
  `resolveEffectivePrioDeadline`'s three arm-specific readings *because a name
  kept past its hypothesis teaches a false dependency*, and left
  `effectiveBucketPriority`'s six standing with hypotheses the same collapse had
  made dead — three binding-arm instances of the unconditional lemma, one about
  an expression shape the accessor no longer contains, and two frames demanding
  that SchedContext lookups agree of an accessor that reads no store.  All six
  are gone for the unconditional `effectiveBucketPriority_congr`, and the one
  consumer lost seventy lines of case analysis for one citation.  **When a cut
  collapses a definition, the theorems whose hypotheses that definition supplied
  are part of the collapse** — the sweep is the family, not the body.

- **A `bound*Consistent` predicate is a WRITER fact, not an invariant — and the
  domain mirror had the same hole** (`v0.35.136`, PR #897's review, reported for
  the priority half).  `returnDonatedSchedContext`'s bottom arm installs a
  `.bound` binding and writes neither the recipient's `priority` / `domain` nor
  the reservation's, so whichever home moved while the reservation was on loan
  comes back disagreeing: `boundThreadPriorityConsistent` and
  `boundThreadDomainConsistent` are both **false** on a state the kernel reaches.
  Five things new code must respect.

  (1) **Two routes, both ordinary syscalls, and the second breaks both predicates
  at once.**  `.tcbSetPriority` on the **unbound** donor writes its TCB alone —
  correctly, since it owns no reservation to mirror to — and
  `schedContextConfigure` of the **donated** reservation writes `sc.priority` and
  `sc.domain` alone, also correctly, the propagation being gated on the donee's
  `ownScId?`, which is `none` (WS-OD `v0.35.3`, and the whole point of that gate).
  Either way the pop then rebinds the origin under the disagreement.

  (2) **Neither reconciliation is available to the pop**, which is what makes this
  a fact about the *writers* rather than a defect in the pop.  `tcb.* := sc.*`
  would undo a demotion, or **migrate a thread's partition**, on an IPC reply — at
  the instance of a holder of a capability on the *reservation*, which says
  nothing about the thread, and which is the crossing WS-OD closed from the other
  side.  `sc.* := tcb.*` would silently retune what that capability's holder had
  just set, and is projection-**visible** besides, since `SchedContext.priority`
  survives `projectKernelObject`.  A cut that decides otherwise must change
  `donationReturnSchedContext_priority` / `…_domain`, which exist so that it has
  to.

  (3) **The domain now has one reading home too.**  `v0.35.133` collapsed the
  *band*'s readers and left `effectiveSchedParams`'s `.bound` arm reporting
  `sc.domain`, on the stated ground that the domain mirror had *"no writer known
  to break it"* — and this finding is that writer.  `effectiveSchedParams_domain_eq`
  is the unconditional pin that every arm reports `tcb.domain`, the sibling of
  `effectiveSchedParams_fst_eq_boostedPriority`; it was **free**, the component
  having no live consumer (every domain filter reads `tcb.domain` directly through
  `chooseBestRunnableInDomainEffective`) and the golden trace staying
  byte-identical.  *A stated reason that no writer exists is a claim about every
  writer, and it is the kind that ages.*

  (4) **So the residue is a verification gap and not a scheduling one**, and that
  distinction is measured rather than asserted: the origin resumes at its own band
  in its own partition.  `boundThreadPriorityConsistent` is consumed by nothing at
  all; `boundThreadDomainConsistent` is a conjunct of
  `schedulerInvariantBundleExtended`, whose scope is the boot and scheduler
  surface, and no IPC transition claims that bundle — so no theorem in the tree is
  false.  A proof that takes either predicate of a post-pop state is asking for a
  premise the kernel refutes.

  (5) **The refutation is executed, and it has a control.**
  `tests/PriorityManagementSuite.lean`'s WS-RR-PRIO-09 drives the configure and
  the pop as **live operations** and asserts both pairs disagree; WS-RR-PRIO-10 is
  the same fixture and the same pop with the reconfiguration omitted, where both
  pairs agree — which is what makes the witness a statement about the
  reconfiguration rather than about the pop, and what shows the pop is not what
  breaks the agreement but what *installs the binding under which it is asserted*.
  The closure is the model change `v0.35.133`'s register row named and deferred —
  retire `SchedContext.priority` and `SchedContext.domain` as thread-band homes,
  which is what seL4-MCS does, its `sched_context` carrying neither — and it is
  **WS-CB**'s, whose plan already reshapes this surface.

- **The scheduler liveness trace model is boot-core-pinned** (SM4.C.11's
  residual).  SM5.J lifted the per-core Liveness *predicates* at v0.31.64 —
  `eventuallyExitsOnCore`, `higherBandExhaustedOnCore`,
  `CanonicalDeploymentProgressOnCore`, `WCRTHypothesesOnCore`,
  `selectedAtOnCore` and siblings all read `currentOnCore c` / `runQueueOnCore
  c` — but `stepPrecondition`, `stepPost` and `ValidTrace`
  (`Scheduler/Liveness/TraceModel.lean`) still read `bootCoreId`, so no
  `ValidTrace` exhibits a step taken on a secondary core.  New code must not
  read an SMP liveness result off a trace: the predicates are per-core, the
  traces are not.  Owned by **WS-SL** (`docs/REGISTERED_DEBT.md`), closure
  target post-v1.0.0; the old target was a sub-task inside a plan marked
  LANDED, so no open phase owned it.
- **The WCRT liveness theorems are hypothesis-conditional**: the band-progress
  obligation `hBandProgress` consumed by `thread_eventually_scheduled_onCore` /
  `no_starvation_under_smp` is an externalized deployment hypothesis whose
  conclusion carries the substantive progress content; only its
  `eventuallyExits` sub-piece has an RPi5 discharge, and the
  FIFO/bucket-rotation composition that would construct it outright is an open
  Scheduler-subsystem follow-up (`Liveness/Yield.lean` scope — AN5-E.4
  honest-framing note, `Scheduler/Liveness/RPi5CanonicalConfig.lean`). Docs
  citing these theorems must state the hypothesis.
- **No core is marked ready anywhere in the tree**, so every seam behind the
  per-core `lean_ready` gate (`rust/sele4n-hal/src/lean_ready.rs`) degrades to
  its Rust-only half on hardware: the IRQ vector redirect, the `.reschedule`
  SGI receiver and the secondary bring-up entry are all wired end to end and
  all dormant until SM10.1's per-core Lean runtime initialization flips them.
  New code must not assume a Lean seam executes on hardware merely because it
  is wired.  **The gated set is derived, not listed** (PR #887 review round
  2): `build.rs`'s `scan_lean_upcalls_readiness_gated` collects every Lean
  upcall from the Lean tree's `@[export]`s — read over a comment-free,
  string-free Lean view with attribute lists split (`lean_code_view`,
  `lean_exports_in`; PR #889 review round 2: a commented-out `@[export …]`
  had counted as live; round 9: the tree including the library root
  `SeLe4n.lean`, which compiles into the static library like any module) —
  and the HAL's `lean_`-prefixed
  externs, attributes each call to its enclosing function, and fails the
  build unless the readiness guard *dominates* it in that body
  (`readiness_guard_dominates`, PR #887 review round 3: the call sits inside
  the guard's true branch with no `||` in the condition, or after a negated
  bare guard whose block diverges — a stored `lean_ready(..)` result, a guard
  block closed above the call, or an `||` no longer satisfy it; and, since
  round 6, the guard's argument must name the **executing** PE —
  `current_core_id_from_tpidr()` inline, or an identifier a dominating
  statement binds from it or validates against it with `assert_eq!`, the
  last binding winning (`ready_argument_is_executing_core`) — so a literal,
  a parameter, a shadowed binding or a `debug_assert_eq!` reads as ungated) —
  `LEAN_READY_GATED_SEAMS`
  is the pin the derivation must reproduce.  The guard must also **resolve**
  to the gate (round 9): an unqualified `lean_ready(..)` counts only where the
  file imports `crate::lean_ready::lean_ready` and defines no `fn lean_ready`
  of its own (`bare_ready_call_resolves`, threaded through every scanner that
  asks — the condition parsers, the classifier, the SVC arm and the
  site-table's `gate_call_offset`), since a same-scope helper of that name
  satisfied every other readiness question while being a different predicate, and the **two** upcalls that run
  ungated — the Lean library initializer `initialize_seLe4n_SeLe4n`, which must
  run before any Lean definition is used, and the primary's `lean_kernel_main`
  boot install, which writes the state every gated seam reads and so precedes
  every core's readiness — are `LEAN_UPCALLS_OUTSIDE_THE_GATE`, each with its occurrence count
  and reason, reconciled in both directions
  (`reconcile_upcall_exemptions`, round 6: a second call in an exempt
  function is a count mismatch, not a free pass).  A reference to a Lean
  symbol that is not a call — an alias, a function pointer, a cast — fails
  the build outright, since no gate can be attributed to a value that
  escapes.  The classifier upcall
  (`lean_classify_synchronous_exception`) is gated too; a not-ready core
  classifies through the Rust mirror pinned to the Lean table —
  `classifier_status` (round 6) holds the hardware classifier's terminal
  `if … else …` to that shape branch by branch, the ready branch's value
  being the Lean call and the not-ready branch's only statement the mirror
  call.

  **WS-RR RR5.6–RR5.9 closed the two seams that consulted no gate**, so the
  sentence `kernel_entry.rs` had always written over its five-entry table —
  "every hardware seam above therefore also consults the per-core readiness
  gate" — is true rather than aspirational.  What a not-ready core does now
  differs by seam, because what it can safely do differs.  The three ISR seams
  degrade to their Rust-only halves.  `sele4n_suspend_thread` returns
  `KernelError::IllegalState`: a C-callable API with an error channel and no
  trapped thread waiting on it.  `dispatch_svc` **halts the core**
  (`halt_syscall_before_lean_ready`) — an `SVC` advanced the PC, so a fail-closed
  frame *would* be architecturally coherent, but the timer seam consults the same
  mask, so a thread on a not-ready core would never be preempted, charged budget
  or rescheduled again; returning an error hands it the CPU forever.  New code
  must not read the SVC seam's not-ready arm as recoverable.

  The gate precedes **every** SVC outcome (PR #889 review): `dispatch_svc`
  consults it before its id and argument-count prefilters, and the trap's SVC
  arm consults it before the full-width `x7` narrowing and the unknown-syscall
  delivery — the halt's reason is the resume (a thread on a not-ready core is
  never preempted again), which no prefilter rejection escapes.  `build.rs`'s
  `svc_arm_readiness_gate_status` pins the order structurally, because a halt
  inside an `extern "C"` handler aborts a host test rather than unwinding into
  it; the behaviour is pinned at the plain-Rust seam in the two readiness
  integration binaries, and no test in the library binary may assume core 0's
  readiness in either direction — the timer suite there marks it mid-run.

  RR5.8/RR5.9 close the compile-time half: a Lean `extern` may be **declared,
  defined or exported only under `feature = "hw_target"`**, and a host-lane
  stand-in of the same name only under its negation
  (`lean_extern_gating_status`).  Both seams used `cfg(not(test))`, so the
  default host profile compiled a call path to a bare-metal symbol nothing on
  the host provides, and `cargo test` linked one into every test binary through
  a `#[no_mangle]` stub.  The readiness gate could not close that: it decides
  whether a call *executes*, not whether it is *compiled*.  The gate's
  `hw_target` verdict is **computed, not matched**: `cfg_predicate_entailment`
  evaluates what a `cfg` predicate entails about the feature through `not` /
  `all` / `any`, under-approximating so it fails closed — a `cfg_attr` or an
  `any(…)` carrying the token satisfies nothing — and linker visibility is read
  as whole words: `extern`, `no_mangle` in both spellings, and
  `#[export_name = "…"]`, which exports a Lean name from an item of any name.
- **A hardware boot without a verified deployment labeling context fails
  closed** (WS-RR RR5.1–RR5.5).  `bootAndInitialiseFromPlatform`'s
  `LabelingContext` argument is **mandatory** — it defaulted to `none`, and on
  that path the wrapper installed the boot state and left whatever the labeling
  reference held, which was `testLabelingContext`: every entity but the reserved
  sentinel `publicLabel`, so every flow between things that can run was
  permitted and SM8/SM9's results held vacuously.  The wrapper now runs the same
  guard `syscallEntryChecked` runs **before** committing anything, so a refused
  boot leaves both references untouched, and the pre-boot labeling reference is
  `defaultLabelingContext`, which that guard rejects — no syscall can be served
  before a deployment context is installed.

  The guard itself stopped being a heuristic.  `isInsecureDefaultContext` was a
  three-sentinel *sample* (ids 0, 1, 42 across four classes) that reported
  "insecure" only when all twelve lookups came back public, which
  `testLabelingContext` evaded by labeling id `0` alone.  It is now an **exact**
  check of a **declared** witness: `LabelingContext.separatedThreads` names two
  *admissible* threads the labeling separates — neither the reserved sentinel
  nor a per-core idle thread (`separationWitnessAdmissible`), since an idle
  thread runs but never originates or receives a flow, so a labeling that
  differs only on the idle range separates nothing observable — and the kernel
  evaluates that inequality — so `isInsecureDefaultContext ctx = false` *entails*
  `LabelingContextValid.labelNonTriviality`
  (`isInsecureDefaultContext_false_implies_labelNonTriviality`), and the runtime
  guard discharges a deployment obligation instead of approximating it.  New
  contexts are built with `deploymentLabelingContext`, whose output is
  `LabelingContextValid` unconditionally (`deploymentLabelingContext_valid`),
  and whose source carries the four policy fields — `memoryOwnership`,
  `endpointPolicy`, `declassificationPolicy`, `auditMonitorClearance` — with
  their fail-closed defaults (PR #889 review round 2), so a binding configures
  them where it declares its labeling rather than every hardware boot being
  forced to the defaults;
  `confinedLabelingContext` is the production two-domain instance (the two
  *incomparable* lattice corners, so neither domain reaches the other in either
  direction — unlike `publicLabel`/`kernelTrusted`, which confine one way),
  and `harnessLabelingContext` is the fixtures'.  A constant labeling function
  is refused, so a fixture that wants one label everywhere uses
  `uniformFixtureLabelingContext`.  What the guard does **not** decide is
  whether the declared partition is the right one for the deployment's threads;
  that stays the integrator's, stated by `LabelingContextValid`'s other two
  conjuncts and discharged structurally by the constructor.  **Which labeling a
  hardware boot installs is bound, not described**: `PlatformBinding` carries
  the **`DeploymentLabeling` source** (`deploymentLabeling`), and
  `PlatformBinding.labeling` is the constructor's output on it — so admission
  (`PlatformBinding.labeling_admitted`) and the whole of `LabelingContextValid`
  (`PlatformBinding.labeling_valid`) are theorems of every binding rather than
  obligations each one carries (PR #889 review: the guard decides
  non-triviality alone, and a stored bare context it admits could still label
  a thread and its own TCB object incompatibly).  The RPi5 binding's is
  `confinedDeploymentLabeling rpi5UpperDomainBase rpi5LowerWitnessIndex …`, so
  its labeling is
  `confinedLabelingContext rpi5UpperDomainBase rpi5LowerWitnessIndex …`
  (`rpi5_deploymentLabeling`, by `rfl`; the boundary clears the boot VSpace
  root and the idle range), the simulation bindings' is
  `harnessDeploymentLabeling`, and
  `Platform.FFI.bootAndInitialisePlatform` boots under the binding's labeling —
  provably the checked idle boot on the binding's declared cores, then the
  witness check, then the two installs, with the labeling-refusal arm
  unreachable (`bootAndInitialisePlatform_eq_checked_boot`) — of the
  **bound** config (round 7): `bindPlatformConfig` puts the caller's IRQ
  table and objects under the binding's `bootVSpaceRoot` and the machine
  configuration the binding **binds for the caller's account**
  (`PlatformBinding.bindMachineConfig`, PR #892 review round 2), so a caller
  cannot omit the canonical root or describe other hardware.  The account
  selects *among* the binding's declared configurations and never becomes
  one: on the RPi5 it is the largest of the five shipped RAM variants
  (`rpi5Variants`, 1–16 GiB) the account covers, and the **smallest** when it
  covers none (`rpi5VariantFor`) — the only member that claims no RAM a
  Raspberry Pi 5 lacks, where the old unconditional 4 GiB map declared RAM
  the 1 and 2 GiB boards do not have.  The DTB bridge validates the board
  against that same function (`rpi5PlatformConfigFromDtb_ok_binds_detected_variant`),
  so the variant checked and the variant booted are one value, and every
  member declares the binding's PE count
  (`bindMachineConfig_declaredCoreCount`, consumed by
  `bootAndInitialisePlatform_checked_declaredCoreCount`).  The coverage
  predicate the two share sits upstream of the bindings in
  `Platform/Boot/MemoryCoverage.lean`.
  The hardware entry is `bootAndInitialiseRPi5`, the generic entry fixed at
  `RPi5Platform`; `lean_kernel_main` (`SeLe4n.Platform.RPi5.kernelMain`, WS-BP
  BP4.1) calls it, through `bootAndInitialiseRPi5OrHalt`, and nothing else.
  **The declared
  separation witnesses must be installed threads of the boot state** (PR #889
  review round 3): the guard decides that the labeling separates two
  admissible *ids*, and only the boot state can say whether those ids are
  threads the deployment creates, so a boot whose labeling's witnesses do not
  resolve to TCBs — the empty config's, whose only TCBs are the idle threads —
  is refused before anything is committed (`declaredWitnessesInstalled`,
  `uninstalledSeparationWitnessBootError`).  A deployment therefore installs
  the two threads its labeling names as separated, or does not boot.
  **The lower witness is the deployment's parameter, held off the boot VSpace
  root by the binding** (PR #889 review round 5): the family fixed it at
  thread `1`, which is the boot VSpace root's object id on every binding
  (`rpi5BootVSpaceRootObjId`, `simBootVSpaceRootObjId`), so a witness there
  could never be installed and every boot carrying the binding's own root was
  refused.  `indexPartitionedDeploymentLabeling` / `confinedLabelingContext`
  take `lowerWitness` with its admissibility and its position below the
  boundary as obligations; the RPi5 binding declares `rpi5LowerWitnessIndex`
  (`2`) and the harness `harnessLowerWitnessIndex` (`2`); and
  `PlatformBinding.witnessesOffBootVSpaceRoot` — neither declared witness is
  the binding's root's id — is a class obligation every binding discharges by
  evaluation, because the root is not visible where the labeling is built
  (`witnesses_ne_bootVSpaceRoot` is its Prop form).  A new binding chooses its
  witness against its own reserved ids; new code must not assume thread `1`
  is a witness.

- **The boot state enqueues each core's idle thread; it does not dispatch it**
  (WS-RR RR5.11–RR5.14).  `bootAndInitialiseFromPlatform` runs
  `bootFromPlatformCheckedWithIdleThreads`, a thin composition over
  `bootFromPlatformChecked` (same validation, same rejections, the seven results
  characterizing it unchanged) that folds a per-core idle enqueue over
  `allCores`.  **That enqueue is the kernel model's own** (`v0.35.68`):
  `Platform.Boot.enqueueIdleThread ist c` has `state := enqueueIdleThreadOnCore
  ist.state c` (`enqueueIdleThread_state`, by `rfl`), with the four
  `IntermediateState` witnesses the operation's own preservation theorems and
  every boot-level frame an instance of the kernel model's — it was a second
  body (`Builder.createObject` plus a hand-written run-queue write) held to the
  first by a docstring sentence, differing in the bookkeeping the store
  maintains and the builder skips.  The operation therefore lives in the
  production module `Scheduler/Operations/IdleEnqueue.lean`, upstream of the
  boot, and the idle TCB (`createIdleThread`, `queuedIdleThread`) in
  `Scheduler/IdleThread.lean` beside its identities; `PerCoreIdle.lean` (staged)
  keeps the per-core-invariant theorems and consumes both.  New code adding a
  boot-time write of an object the kernel model can already write runs the
  kernel model's operation on `ist.state` and carries the witnesses through its
  theorems, never a builder-side copy of its body.  So `∀ c, idleThreadEnqueuedOnCore st c` holds of the live boot
  state (`bootFromPlatformCheckedWithIdleThreads_idleThreadEnqueuedOnCore`),
  discharging the premise `chooseThreadOnCore_always_succeeds` consumes and
  `schedulerNoStall_smp`'s `hIdle` took by hypothesis — which no reachable state
  discharged before: the checked boot installed no idle threads at all, and
  `bootFromPlatformWithIdleThreads` set current slots *without* enqueuing, so
  the predicate was false on it too.  New code must respect the shape: every
  core's current slot is still `none` after boot
  (`bootFromPlatformCheckedWithIdleThreads_currentAllNone`), because a current
  slot pointing at a queued thread violates `queueCurrentConsistent` from the
  first instruction; each core's first scheduling point dispatches idle out of
  its own queue.  The enqueue stores the **queued** idle form
  (`queuedIdleThread`, `threadState := .Ready`; PR #889 review): storing the
  dispatched form `createIdleThread` (`.Running`) while queuing it made every
  successful production boot violate `threadStateConsistent` on every core,
  which the harness hid by syncing the field before checking it.  With that,
  and with `bootSafeObjectCheck` requiring every config TCB `.Inactive`, the
  production boot state is `threadStateConsistent` with no hypothesis beyond
  the boot (`bootFromPlatformCheckedWithIdleThreads_threadStateConsistent`).
  **That is a boot-state theorem, not a preserved invariant** (PR #889 review
  round 2): no scheduler dispatch writes `.Running` and no rendezvous writes a
  `.Blocked*`, so `threadStateConsistent` is false after any core's first
  dispatch, and the harness re-establishes it with `syncThreadStates` before
  it checks.  What the live decisions read is the inactive flag — `tcbSuspend`
  / `tcbResume` / the cancellation and fault suspends test the field against
  `.Inactive` only — stated as `threadInactiveFlagConsistent` and proved of the
  boot state (`…_threadInactiveFlagConsistent`).  **The per-core context switch
  preserves it** (WS-RR RR7.36,
  `switchToThreadOnCore_preserves_threadInactiveFlagConsistent`, with
  `preemptCurrentOnCore_preserves_…` for the primitive it composes), under two
  side conditions that are the two ways it genuinely breaks: a displaced thread
  stranded off every queue, and a dispatch of a thread the state classifies
  `.Inactive`.  The reusable machinery is
  `threadInactiveFlagConsistent_of_frame` / `…_of_frame_placing` over
  `threadPlacedOnSomeCore`, with `inferThreadState_eq_inactive_iff` the
  characterisation — a thread is `.Inactive` exactly when it is unplaced and
  not blocked — so a further surface is a per-transition application rather
  than a fresh argument.  The wake and idle-enqueue paths (which change the
  stored flag *and* the placement), the lifecycle pair and the IPC writers
  remain registered debt.  New code must not cite `threadStateConsistent` of a
  post-dispatch state.

  **And the classification's placement tests are the cross-core wake's
  single-placement tests** (RR7.36): `threadRunningOnSomeCore` /
  `threadQueuedOnSomeCore` are *defined as* `runningOnSomeCore` /
  `runnableOnSomeCore`, not stated to equal them.  RR5.10 wrote a second fold
  over `allCores` in a module that does not import the one where SM5.C.1 and
  SM5.D.4 had already asked the question, and this pair diverging is not
  cosmetic: the wake's guard exists to keep one TCB off two cores, so a
  disagreement would let a thread be enqueued a second time while still
  classifying as running.
  **A successful boot respects the object-capacity invariant** (PR #889
  review round 18): `wellFormed`'s fifth conjunct `objectBudgetRespected`
  requires `initialObjects.length + 1 + numCores ≤ maxObjects` — room for the
  boot VSpace root and one idle thread per *model* core, since the idle slots
  are reserved model-wide — and
  `bootFromPlatformCheckedWithIdleThreadsFor_objectIndexBounded` proves
  `objectIndexBounded` of the boot state from it.  Before, nothing bounded the
  count at all: a config filled to `maxObjects` booted, the idle fold added
  four more entries, and the state violated the invariant
  `retypeFromUntyped` enforces at every later allocation.
  The idle slots are **reserved** by `PlatformConfig.wellFormed`
  (`idleSlotsReserved`: no `initialObjects` entry and no boot VSpace root in
  `[idleThreadIdBase, idleThreadIdBase + numCores)`), so a successful checked
  boot is fresh (`bootFromPlatformChecked_ok_idleSlotsFreshAt`) and the idle
  fold provably overwrites nothing without a freshness hypothesis — before,
  an accepted config object at an idle id was silently replaced by the fold.
  The reservation also covers every object a config entry *references*
  (`bootObjectReferencesReservedIdleSlot`, total over `KernelObject` and over
  every field that can hold an object, thread or scheduling-context id — a
  notification's `boundTCB`, an untyped's `children` and `parent`, a
  TCB's own `tid` and (round 8) its `queuePPrev`, reply references and
  carried capabilities, a Reply's own id and `prev` link and a
  SchedContext's own id included, PR #889 review rounds 2, 4, 6, 7 and 8; a
  VSpace root holds none — and, since round 8, **pinned by constructor
  arity**: each kind's arm destructures its constructor
  (`tcbReferencesReservedIdleSlot` and seven siblings), so a field added to
  any kernel object fails the build until it is classified, where five
  rounds had each extended the same hand-written list), and a config that
  fails it is refused with its own diagnostic rather than as a duplicate
  id.  **A boot TCB is stored under
  its own thread id** (round 7): `PlatformConfig.wellFormed`'s fourth
  conjunct, `tcbIdentitiesMatchSlots`, requires every `.tcb` entry's
  `tid.toObjId` to be its `id` — the object store is keyed by `ObjId`, the
  TCB carries its `ThreadId`, and the lifecycle paths read the latter back
  (`cleanupTcbReferences`), so a TCB stored under a foreign id — an idle
  thread's, in the finding — would have let a retype dequeue a thread the
  config never owned.  New boot fixtures set `tid := ⟨id⟩`.  Round 8 swept
  the relation across the kinds that carry their own id: the fourth conjunct
  is `embeddedIdentitiesMatchSlots` — TCB, SchedContext (`scId`, which
  `replenishScOnCore` keys the replenishment queue by) and Reply
  (`replyId`) — with `tcbIdentitiesMatchSlots` and its two siblings as its
  parts, so a boot SchedContext or Reply is stored under its own id too; and
  `bootSafeObjectCheck` requires all three queue links of a boot TCB empty,
  `queuePPrev` included.  Beyond the config, the idle
  objects are unreachable by user authority at all: `syscallResolveCap` — the
  one resolution every invoked capability passes through — refuses a
  capability naming a reserved idle object (`capTargetsReservedIdleObject`,
  `syscallResolveCap_ok_not_reserved`), so a boot CNode or a transfer that
  carried one yields a slot that resolves like an empty one and no
  `.tcbSuspend` can remove a core's only guaranteed runnable thread.  That
  chokepoint decides on the **resolved capability's target**, so an arm whose
  operand is a raw id from a message register escapes it: until `v0.35.204`
  `.schedContextBind` resolved its capability to the SchedContext and took the
  thread from a raw `args.threadId`, which let an ordinary SchedContext
  capability bind the idle TCB and re-prioritise it (round 11, P1) — and, more
  generally, bind and re-prioritise **any** unbound same-domain thread the
  caller could name, with no TCB authority at all.  Raw operands are refused
  at their lift points — `validateThreadIdArg` and `validateObjIdArg` reject a
  reserved idle id (`validateThreadIdArg_ok_not_reserved`) — so a new arm
  taking a bare id is covered the day it is written; and the bind takes **no
  raw thread operand any more**: MR0 is a TCB capability address
  (`SchedContextBindArgs.tcbCPtr`), resolved through the caller's own CSpace
  with `.write` by `resolveSchedContextBindThread` — one resolver read by the
  live arm and by the scheduler-domain operand builder, the shape
  `.tcbBindNotification` already had — so the thread a bind names is one the
  caller holds a writable capability to
  (`resolveSchedContextBindThread_ok_authorised`) and the idle TCB is refused
  at the chokepoint (`resolveSchedContextBindThread_refuses_idle_capability`,
  `dispatchCapabilityOnly_schedContextBind_idle_capability_refused`).  `.lifecycleRetype`'s
  raw `targetObj` needs no separate guard: `lifecycleRetypeAuthority` binds it
  to the capability.  The
  one live seam that takes a **raw** id, `suspend_thread_cross_core`,
  refuses an idle id itself (round 8): its whole step is the pure
  `suspendThreadCrossCoreStep`, and `suspendThreadCrossCoreStep_idle_refused`
  proves the refusal — the sentinel's `.invalidArgument` — commits nothing,
  where before it ran `suspendThreadOnCore`, which dequeues an idle TCB like
  any other.
  The boot queue is **characterised, not bounded**: on every
  core it is exactly the empty queue with that core's idle thread enqueued
  (`bootFromPlatformCheckedWithIdleThreads_runQueueOnCore_eq`, membership
  `…_mem_runQueueOnCore_iff`), so its well-formedness and its members'
  resolution are proved of the boot state
  (`…_runQueueOnCore_wellFormed`, `…_runnable_resolve`), the staged keystone
  `bootFromPlatformCheckedWithIdleThreads_chooseThreadOnCore_succeeds` takes
  **no hypothesis beyond the boot**, and each core's first selection is pinned
  to its own idle thread (`…_chooseThreadOnCore_idle`).
  **The binding boot installs idle threads on the binding's declared cores**
  (PR #889 review round 3): `bootAndInitialisePlatform` runs
  `bootFromPlatformCheckedWithIdleThreadsFor (PlatformBinding.declaredCores platform)`,
  the first `coreCount` model cores, so a single-core binding boots one idle
  thread rather than four; the RPi5 binding declares every model core
  (`rpi5_cores_eq_allCores`), so its boot is the all-cores form by `rfl`
  (`bootAndInitialisePlatform_rpi5_all_cores`) and every all-cores boot
  theorem is a theorem of the hardware boot.  **No binding declares more cores
  than the model has** (PR #889 review round 5): `PlatformBinding.coreCountLe :
  coreCount ≤ numCores` is a class obligation, so `declaredCores` — the prefix
  `allCores.take coreCount` — has exactly `coreCount` members
  (`declaredCores_length`), membership is `c.val < coreCount`
  (`mem_declaredCores_iff`), and the boot core embeds in the model
  (`bootCoreModelId`).  **The idle-slot reservation is model-wide**: an
  undeclared core's slot is reserved and *absent* after the boot
  (`bootFromPlatformCheckedWithIdleThreadsFor_undeclared_idle_absent`), never
  free — the ids belong to the `numCores`-wide model, and the capability
  chokepoint decides on the kernel state alone, which carries no binding.
  `bootFromPlatformWithIdleThreads` remains as the SM4.G install-and-dispatch
  wrapper and is **not** the production path.

- **A boot TCB is pinned to a core the platform declares, or to none**
  (PR #889 review round 15).  `bootFromPlatformCheckedWithIdleThreadsFor`
  refuses a config whose TCB carries a `cpuAffinity` outside the core list
  it is given (`bootAffinitiesDeclared`, diagnostic
  `undeclaredAffinityBootError`), because `determineTargetCore` reads that
  field on the first resume or wake and would enqueue the thread on a PE
  the binding does not have.  The checked boot cannot decide this — it is
  binding-agnostic by design, one validation path — so the check lives
  where the core list arrives.  On `allCores` it is vacuous
  (`bootAffinitiesDeclared_allCores`), so the all-cores boot and the RPi5
  boot are unchanged; a `coreCount < numCores` binding now rejects a
  config the model would have accepted.

- **...and a running thread is too** (PR #889 review round 20).  The boot check
  above had no live counterpart: `decodeAffinity` accepts any `v < numCores`, so
  `.tcbSetAffinity` could migrate a thread onto a PE the binding does not have
  the instant after a successful boot — queued where nothing runs it, with the
  reschedule SGI sent to a core that cannot take it, and no error returned.  The
  declared count therefore travels with the machine it describes, which is the
  only thing a transition can read: `MachineConfig.declaredCoreCount` →
  `applyMachineConfig` → `MachineState.declaredCoreCount` →
  `setThreadCpuAffinityWithMigration`, which refuses an out-of-range affinity
  with `.invalidArgument` and commits nothing
  (`setThreadCpuAffinityWithMigration_rejects_undeclared_core`); unpinning names
  no core and is never caught by it
  (`setThreadCpuAffinityWithMigration_none_passes_declared_check`).  The count
  reaches the live state proved rather than by convention
  (`bootFromPlatformChecked_ok_declaredCoreCount`,
  `bootFromPlatformCheckedWithIdleThreadsFor_declaredCoreCount`), and
  `PlatformBinding.declaredCoreCountAgrees :
  machineConfig.declaredCoreCount = coreCount` holds the boot's number and the
  transition's number to one fact — `simSingleCoreMachineConfig` exists because
  the single-core binding was sharing the four-PE `simMachineConfig`, which is
  what the gap was.  The field defaults to `numCores`, so the refusal is inert
  on every existing state and fixture; a new binding that declares fewer PEs
  must give its machine config the matching count, or its instance will not
  elaborate.  New code must not read `numCores` as the set of cores a thread may
  be pinned to.  **The unpinned half closed at v0.34.79** (WS-RR RR7.30):
  `determineTargetCore_lt_declaredCoreCount` says an unpinned thread — and a
  `tid` resolving to no TCB — routes to `bootCoreId`, which is core `0` and so
  inside any declared set (`coreCountPos`), so with the two refusals above **no**
  thread of any kind is enqueued on a PE the machine does not have.  `numCores`'s
  own docstring now states this whole relation at the constant, since describing
  only the RPi5 equality there is what made a reader conclude a narrower binding
  could not shape kernel state at all.

- **Thread-state classification is per-core** (WS-RR RR5.10).
  `inferThreadState` read `currentOnCore bootCoreId` / `runQueueOnCore
  bootCoreId` only, so a thread running or queued on a secondary core
  classified `.Inactive`, `threadStateConsistent` was false of any such state,
  and `assertStateInvariantsFor` — which syncs before it checks — would rewrite
  the field rather than report the mismatch.  It now asks every core
  (`threadRunningOnSomeCore` / `threadQueuedOnSomeCore` over `allCores`), and
  the lift is conservative on every state the old definition classified
  (`inferThreadState_eq_bootCore_of_secondaries_quiescent`).  This had to land
  before the boot switch above: the boot state queues idle on all four cores.

- **A device tree is read whole, and what it withholds is not a resource**
  (PR #892 review round 5, v0.34.113).  Five facts new code must respect.  (1)
  `parseFdtNodes` refuses a structure block that does not reach a top-level
  `FDT_END` at depth zero — every partial exit is `.malformedBlob`, fuel
  exhaustion stays `.fuelExhausted` — so a *fixture* blob must carry its
  terminators or the bridge rejects it.  The header is validated first, and the two
  validators are **one question**: `FdtHeader.isValid` and
  `cmdline::validate_fdt_header` both require §5.1's layout — each block offset
  4-byte aligned (8 for the reservation block) and at or beyond the 40-byte
  header — and both require **version ≥ 17**, the version at which
  `size_dt_struct` enters the header, since both read that field
  unconditionally.  Four of those conditions were Rust-only, with Lean the
  permissive side and Lean the side `BP2.6` made the only reader of the blob's
  memory; the
  reservation-block pair and the version floor were missing from both.  A
  strings block over the header is the sharpest of them: a property's `nameoff`
  then resolves into header bytes, and every field there is the blob author's to
  choose, so `reg` or `status` can be spelled inside a `totalsize`.  The walk
  then refuses a property after a
  child (§5.4.2), a repeated property name (§2.2.4) and — since the RR7 audit
  round — **a repeated sibling node name**: §2.2.3 identifies a node by its full
  path, which is unique only if siblings differ, and every selector in the file
  reaches for a node by name and takes the **first** match.  A second
  `reserved-memory` child was therefore never read, so its carve-outs were never
  subtracted; enforcing uniqueness for properties and not for the nodes those
  properties hang on left the selectors' own premise unchecked.  (2) The machine's RAM is selected by
  `memoryNodeReg?` over that parsed tree, with the same three filters the Rust
  walk applies: the node describes memory (`device_type`), it is operational
  (`FdtNode.statusIsOperational` — `okay`/`ok` and nothing else, decided on the
  operational side because that is the side the specification's list is closed
  on), and it sits at the **top level**, so a `memory@…` under
  `/reserved-memory` is a carve-out rather than an aperture.
  `findMemoryRegPropertyChecked` is now a selector over the same tree, not a
  second token walk, and `findMemoryRegPropertyChecked_eq_memoryNodeReg?` is
  what keeps the standalone API and the boot path from disagreeing about a
  blob.  (3) **A reservation set this parser cannot read whole is a refusal**, not a
  shorter list (the RR7 audit round).  Both sources answer `Option`:
  `FdtBlob.reservations` gives `none` when the §5.3 block reaches no zero
  terminator inside its declared bound or holds an unreadable pair, and
  `fdtReservedRanges` gives `none` when a `/reserved-memory` child's `reg` is
  not a whole number of tuples at the declared cell widths — a child with **no**
  `reg` still contributes nothing, because §3.5 says that is what a dynamic
  allocation means.  `fromDtbFull` refuses on either.  The direction is the one
  `CLAUDE.md` states for scanners: this list is a set of *subtractions*, so an
  entry dropped hands back memory the firmware reserved and the map then permits
  `MachineState.addrInRange` over a firmware, DMA or crash-kernel carve-out,
  while one invented merely costs RAM.  The first cut ended the list at the
  bound, at an unreadable pair and at a fixed fuel of 64 and called that
  "fail-closed"; the fuel is now the block's own capacity, so only the
  terminator or the declared bound can end the walk.  A **fixture** blob must
  therefore carry a real reservation block: `offMemRsvmap` pointing at the
  structure block is not "no reservations", it is no room for the terminator,
  and it is refused.  (4) A peripheral's `reg` is a **child-bus** address until it is
  translated: `extractPeripherals` carries an `FdtAddressContext` and composes
  each bus's `ranges` outward, so a node under a bus with no `ranges` is not
  reported at all (Devicetree Specification v0.4 §2.3.8 — nothing maps), an
  empty `ranges` is the identity, and a node whose address falls outside every
  window is refused rather than reported raw.  The tree root is the base case:
  its children's `reg` *are* CPU physical addresses.
- **The scheduler bracket acquires in ladder order because the domain sorts**
  (PR #892 review round 5, v0.34.113).  `schedulerLockBracketDomain.sequence` is
  `SchedLockSet.lockAcquireSequence`, a `mergeSort` on the key — the same answer
  `objectLockBracketDomain` has given since SM3.B.  It was the declared list
  verbatim, which rested on every footprint being declared ascending; that holds
  for the footprints a *transition* declares and not for the one resolved from
  the state, since `pipChainVisited` follows `blockingServer` and a blocking
  chain descends in `ObjId` whenever a higher-numbered thread blocks on a
  lower-numbered one.  Two things new code must respect.  (1) A `SchedLockSet`'s
  `pairs` is **not** an acquisition order — it is whatever order the footprint
  was resolved in; the order is `lockAcquireSequence`, and
  `lockAcquireSequence_ordered` states it with no hypothesis.  (2) The change is
  transparent to every declared footprint, because an ascending list is its own
  sort (`lockAcquireSequence_eq_pairs_of_pairwise_le`), so an SM5 result stated
  over the declared list still holds — but a *new* result about what the bracket
  acquires names the sequence, not the pairs.
- **The outer-shareable TLBI wrappers cannot execute on the first hardware
  target.**  `tlbi_vmalle1os` / `vae1os` / `aside1os` / `vale1os` are
  **FEAT_TLBIOS** (ARMv8.4-A); Cortex-A76 — the core in the RPi5's BCM2712 —
  is ARMv8.2-A and does not implement them.  Each wrapper probes
  `ID_AA64ISAR0_EL1.TLB` and takes `cpu::fatal_halt()` when the feature is
  absent, deliberately **not** falling back to the inner-shareable variant,
  which would service only the inner domain while the caller asked for the
  outer one.  All platform bindings are `.inner` today, so the path is
  unreachable; a new binding that sets `sharingDomain := .outer` must be for
  a PE that implements FEAT_TLBIOS, or the kernel halts at its first TLB
  invalidation.  New code must not treat the `*OS` wrappers as
  drop-in equivalents of the `*IS` ones.  Pinned by a `build.rs` scanner and
  by `scripts/check_tlbi_broadcast_discipline.py` (Tier 0), which also
  confines the `tlbi` mnemonic to `tlb.rs` and holds every local
  (non-broadcast) call site to `scripts/tlbi_local_allowlist.txt`.
- **An `unsafe fn` body is not an unsafe context** (`v0.34.129`).  `sele4n-abi`
  and `sele4n-hal` both deny `unsafe_op_in_unsafe_fn`, so a hardware operation,
  a raw-pointer dereference or a foreign call inside one of the HAL's ten
  `unsafe fn`s must sit in its own `unsafe { … }` block with its own
  `// SAFETY:` comment — which is what makes the HAL's stated discipline
  (*every unsafe block carries a `// SAFETY:` comment*) reach the bodies where
  the hardware access actually happens.  **That discipline is enforced by
  `scripts/check_unsafe_block_justifications.py` (Tier 0) since `v0.35.9`, and
  was enforced by nothing before it**: this file and
  `docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md` row F.3 both named
  `scripts/check_arm_arm_citations.sh`, which the v0.30.11 audit planned as
  R12.C and which no commit on any branch ever contained.  A claimed gate is
  the worst kind of stale claim, because the discharge row it backs reads as
  evidence.  The live gate asks each site kind its own question — a `// SAFETY:`
  comment in the contiguous run above an `unsafe` **block**, a `# Safety` doc
  section on an `unsafe fn` **declaration**, which are Rust's two idioms and not
  interchangeable — and the tree is at **136 of 136 justified** (114 blocks and
  22 declarations, both counts emitted by the gate rather than written down
  here), so its baseline is empty and any new unjustified site fails outright
  rather than raising a floor.

  **The declarations became 22 at `v0.35.18`, and the ten are a domain the gate
  never examined** (PR #895 review round 5).  A foreign item carries no `unsafe`
  token of its own — the block header does, and only in edition 2024 — so every
  `extern "C" { fn … }` in this tree declared a caller-facing unsafe obligation
  that no count, no inventory and no baseline could see.  Ten are live Lean
  upcalls, and each one's precondition existed only as a `//` comment for the
  reviewer: a caller of `lean_handle_fault` had no rustdoc statement that the
  call is sound only on a ready core and only for an EL0-origin exception.  Each
  publishes a `# Safety` section now, so the empty baseline survives; a new
  foreign declaration must carry one on the day it is written.

  **The count was 125 until `v0.35.15`, and the missing site was a domain
  defect** (PR #895 review round 3).  The census globbed `*/src/**/*.rs`, which
  names the crate libraries and silently omits everything else cargo compiles —
  integration tests, `build.rs`, examples, benches.  `rust/sele4n-hal/tests/`
  carries a real `unsafe` block, so the figure described a subset of the tree
  while reading as a measurement of it, and the empty baseline would have stayed
  green over an unjustified site in any omitted file.  The set is derived now:
  every `.rs` file under the workspace that is not build output.

  **And the gate meant that sentence only from `v0.35.12`** (PR #895 review): it
  accepted a `// SAFETY:` comment on a declaration too, as a fallback, under the
  very comment saying the two are not interchangeable.  That is not leniency —
  the idioms publish to different audiences.  A `// SAFETY:` comment is inside
  the file, for the reviewer reading the next line; a `# Safety` section is
  rustdoc, for the **caller** who must discharge the obligation and never opens
  this file.  Taking the first for the second passes an `unsafe fn` that exposes
  no contract at all to the people bound by it.  All twelve declarations already
  carried a `# Safety` section, so removing the fallback failed nothing and
  refuses the next one documented the wrong way; the self-test pins the
  separation in **both** directions, each case keeping the justification and
  writing it in the other kind's idiom.  The ARM ARM citation count is reported beside it and deliberately not
  enforced: deciding which sites touch hardware needs the body, which is the
  analysis-instead-of-a-contract shape this file retires twice above.  It also makes an *absence* checkable: the host
  `raw_syscall` mock is `unsafe fn` for signature parity alone, and its body
  compiling with no block is the compiler's statement of that, where before it
  was a docstring's.  The lint was added because the claim it replaces was
  false in the direction that matters — `sele4n-abi`'s module docs said
  "exactly one `unsafe` block: the inline `svc #0` instruction in
  `trap::raw_syscall`", and under edition 2021 that block did not exist: the
  `asm!` inherited the `unsafe fn`'s implicit context and the crate's only real
  block was in `invoke_syscall`.  New Rust in either crate writes the block.
- **A fault is delivered, never returned.**  RR4 (v0.34.44) wired
  `dispatchSynchronousException`'s non-`SVC` arms and `trap.rs`'s abort arms to
  the fault delivery, which composes the live `.call` chain
  (`endpointCallCrossCoreDispatch`) with a kernel-built fault message.  Four
  facts new code must respect.  (1) The transition is **total**: no handler, an
  unresolvable one, one lacking send-**and**-grant, a flow the policy denies, or
  a Call that cannot link a reply object all converge on the fail-closed suspend
  (descheduled, `.Inactive`, keeping `TCB.pendingFault` as the diagnostic), so
  there is no error arm a caller could ignore and `eret` through — which is what
  makes `faultDeliverOnCore_not_dispatchable` (RR4.19) hold on *both*
  dispositions.  (2) The live entry calls the **flow-checked** arm
  `faultDeliverOnCoreChecked` (production, `IPC/CrossCore/Fault.lean` §5), not
  the bare transition: the live syscall seam gates every endpoint operation
  through `syscallEntryChecked`, and an ungated fault delivery would be the one
  endpoint flow in the kernel no policy can refuse — it would carry a faulting
  thread's fault address, syndrome and register window into a handler's domain
  across a boundary the deployment forbids.  A denied flow takes the same
  suspend, so the gate costs neither the progress theorem
  (`faultDeliverOnCoreChecked_not_dispatchable`) nor the bundle
  (`faultDeliverOnCoreChecked_preserves_ipcInvariantFull`).  A new fault seam
  must call the checked arm; a Tier 0/3 pair pins that relation rather than the
  name, since both names contain `faultDeliverOnCore`.  (3) The faulting
  thread's `pendingFault` is seL4's `tcbFault` and is the **only** channel from a
  delivery to the reply that answers it; a reply to a thread carrying none is
  `.illegalState`, and `applyFaultRestart` retires it, so a second reply cannot
  re-answer.  The reply that reaches it is the **ordinary** one: the live
  `.reply` dispatch arm is seL4's `doReplyTransfer`, branching on the answered
  thread's `pendingFault` (`replyTransferOnCore`, production,
  `IPC/CrossCore/Fault.lean` §4), because a fault handler holds nothing but the
  reply capability the fault Call gave it — without that branch the whole
  reply-based restart is verified and unreachable.  On an unfaulted caller the
  seam is the pre-RR4 body verbatim (`replyTransferOnCore_of_no_fault`), which
  is why every existing `.reply` theorem transfers under one pre-state
  hypothesis.  **Both branches are covered by the staged dispatch payoff since
  `v0.35.195`** (WS-RR RR8.16): RR4.14 confined it to the unfaulted one with the
  pack field `replyNoPendingFault`, because the abandon arm needs the answered
  thread to be `passiveServerIdleAllowed` at the **post**-state and threading a
  post-state hypothesis is what the RR3 de-threading gate forbids.
  `endpointReplyCrossCoreDispatch_ok_target_ready` reads that off the dispatch's
  own **outcome** — a successful reply leaves its target `.ready` — so the
  hypothesis is derived rather than carried, the confinement field is retired for
  `replyFaultStage` (the same five pre-state conditions the ordinary branch
  already carries, at `IpcMessage.empty`), and the fault reply's own bundle
  composes the **donating** form: `faultDeliverOnCore` runs the live `.call`
  chain, so a faulted thread holding a reservation lends it to its handler and
  `hNoDonationOwnedBy` was **false** in exactly the state the handler replies
  from — the premise the path it was named for refutes.
  **`.replyRecv` does not route through the seam yet**
  — `replyRecvBody` fuses a reply leg, a receive leg and a donation return, and
  a fault reply changes what the latter two are handed — so a handler must
  answer a fault with `.reply` and take its next request separately; that is
  registered debt too, and new code must not assume `.replyRecv` retires a
  fault.  (4) `IpcMessage.label` is set by kernel-originated messages only —
  a user send leaves it at `0` — because carrying a user's label would let a
  thread holding a send capability to a fault endpoint mint a message bearing a
  `seL4_Fault_tag`.  Restoring seL4's sender-side label pass-through needs its
  own authority story and is registered debt — **owner WS-CB since v0.34.68**
  (WS-RR RR7.17), with the constraint and two candidate designs stated in the
  WS-RA plan's §9 rather than inside a review narrative.  (5) The handler capability is
  gated by seL4's `sendFaultIPC` predicate — send, and grant **or**
  grant-reply (`faultHandlerCapAuthorized`) — not send-and-grant: the reply
  link is structural in this model, so the disjunct is a policy gate, and the
  idiomatic `seL4_CapRights_new(0, 1, 0, 1)` handler capability must be
  admitted; the predicate is *defined from* its clause inventory
  (`faultHandlerRequiredRights`, PR #887 review round 3), with
  `faultHandlerCapAuthorized_iff` and
  `faultHandlerCapAuthorized_depends_only_on_faultHandlerRights` holding the
  two readings together — a theorem whose conclusion is one of its own
  hypotheses, which is what pinned them before, pins nothing.  (6) The fault entry **spills the trap frame's fault window**
  (`x0`-`x7`, `SP_EL0`, `x30`) into the faulting thread's `registerContext`
  before it builds the fault context (`writeFaultRegistersToTcb`,
  `faultContextOfThread_writeFaultRegistersToTcb`): the mirror is partial and
  between syscalls holds the *last syscall's* arguments, so a context built
  from it alone would report a stale argument window and, on a payload-free
  resume, reinstall it over the thread's live registers.  `lean_handle_fault`
  therefore takes fifteen words, and new code must not build a fault context
  off the mirror without spilling first.  (7) The entry derives its cross-core
  pokes from the pre/post **diff** (`computeCrossCoreSgis`), as the syscall
  seam does, never from the single SGI the Call chain surfaces; and it runs
  the executing core's successor through `scheduleLocalSuccessorLive`, inert
  until SM10.1.  (8) On hardware only `MR0`-`MR3` of a fault message reach
  the handler's registers: no receive path writes `MR4` onward into the IPC
  buffer yet (a WS-RA residual with its first consumer here), so an
  `unknownSyscall` (13 words) or `userException` (5 words) handler sees its
  first four words until that write lands — registered debt with a closure
  target, not a silent truncation.  (9) **A kernel-origin exception is never
  delivered.**  `classifySynchronousException` maps the current-EL aborts
  (EC `0x25`, `0x21`) to `.kernelAbort`, `faultOfExceptionContext` yields no
  fault for it, and `faultEntryStep` / `unknownSyscallEntryStep` are inert
  unless `SPSR_EL1.M[3:2] = 0` (`ExceptionContext.takenFromEl0`); on the Rust
  side `halt_if_kernel_origin` runs before classification in
  `handle_synchronous_exception` and the `KERNEL_ABORT` arm halts on the
  syndrome alone (`build.rs` pins both as unconditional top-level statements
  of the handler, whose terminal statement is the routing match — round 6);
  the classification itself is
  Lean's only once the core is ready, and the pinned Rust mirror's before
  that.  Delivering one would hand the
  kernel's own register window to a user-level handler and let its reply
  `eret` into the kernel frame.  (10) **A handler already blocked in receive
  gets the fault message in its return frame**: `faultDeliverOnCore` stages
  it (`stageWokenDelivery`, the `.call` arm's write) — the queued-order path
  (fault first, receive later) was always right; the woken path was not.
  (11) **`.tcbResume` retires a pending fault** (`retirePendingFaultForResume`,
  run before `resumeThreadOnCoreLive`): the thread restarts at the faulting
  instruction with its trap-time window and `pendingFault = none`, so no
  later reply can decode against a stale fault; a thread carrying none is
  untouched (`retirePendingFaultForResume_of_no_fault`).  (12) **An unknown
  syscall number is a fault**, delivered through the same entry
  (`lean_handle_unknown_syscall`, `unknownSyscallEntryStep`;
  `trap.rs::deliver_unknown_syscall` on `DispatchError::InvalidSyscallId`),
  never an error frame returned to the thread — seL4's
  `handleUnknownSyscall`.  (13) **`.tcbSetFaultHandler` (id 34) is the only
  writer of `TCB.faultHandler`** (`setThreadFaultHandlerOp`, capability-only
  under the TCB write right): the CPtr is validated through the *target's*
  CSpace against `faultHandlerCapAuthorized` at set time, so "configured" and
  "usable" are the same thing; before it existed nothing outside the test
  fixtures set the field, and every live fault took the fail-closed suspend.
  (14) **The fault tags are the MCS layout**: `Timeout` is 5 and `VMFault`
  is 6 (`libsel4/arch_include/arm/sel4/arch/shared_types.bf` under
  `CONFIG_KERNEL_MCS`; the non-MCS layout's `VMFault 5` is not this ABI), and
  `faultLabel_ne_timeout` / `faultLabel_ne_debugException` pin the two
  reserved tags as never carried.  (15) **A failed capability lookup is a
  fault, on every syscall the refusal ledger does not record** (PR #887
  review round 3): `syscallDispatchFromAbi` re-runs the dispatcher's prologue
  on the refusal arm (`syscallCapFaultOf`: decode, the gate, the *resolution*
  half of the lookup, `syscallResolveCap`) and, when the resolution fails with
  the very error the dispatcher returned, delivers a `capFault` through the
  flow-checked delivery the abort entry uses (`deliverSyscallCapFault`) —
  seL4's `handleInvocation` / `handleRecv`, whose rule is the syscall's
  blocking flag, so every `seL4_Call` invocation and `seL4_Signal` fault in
  the send phase and `.receive` / `.notificationWait` / `.replyRecv` in the
  receive phase (`capFaultReceivePhase?`).  A resolved capability refused on
  rights or by its arm is still an error, a refusal raised before the lookup
  is never delivered, and the two declassifying syscalls keep returning theirs
  because SM9.B records them — the partition is pinned against
  `refusalSeamClass` (`capFaultReceivePhase?_none_iff_records`), not listed
  twice.  The context is the trap frame's window with the `SVC` as the restart
  PC (`svcFaultIP`), so a payload-free reply re-issues the syscall, and
  `ELR_EL1`, `SPSR_EL1`, `SP_EL0`, `x30` cross the ABI for it
  (`lean_syscall_dispatch_cross_core` takes fifteen words).  The outcome is
  `.faulted` — outcome tag 2, distinct from a frame (0) and a block (1), on
  which the SVC arm **halts** pending SM10.1 exactly as the unknown-syscall
  delivery does (`halt_after_delivered_syscall_fault`, PR #887 review round
  5), because a block's sentinel frame would `eret` the caller past the
  `SVC` the model has it restart at — and the caller is not dispatchable
  afterwards (`syscallDispatchFromAbi_capFault_faulted`,
  `syscallDispatchFromAbi_capFault_not_dispatchable`); every error-frame
  theorem at the seam is stated on the complementary arm (`hNoCapFault`).  A
  `.replyRecv` whose *reply* capability fails to resolve still returns the
  error (seL4-MCS's `lookupReply` faults) — registered debt.  (16) **The SVC
  arm reads the syscall number at full width**: `u32::try_from(frame.x7())`,
  with the narrowing's failure delivered as the unknown-syscall fault, so a
  wide `x7` cannot alias a valid id.
- **A core that takes an EL0 abort halts, until SM10.1 — delivered or not.**
  The model deschedules the faulting thread, and the hardware cannot honour
  that until the context restore installs a successor — `trap.S` would
  otherwise `eret` through the blocked thread's own frame, back onto the
  instruction that faulted.  So `trap.rs::deliver_fault` calls
  `cpu::fatal_halt()` after a delivered fault, and (PR #887 review round 3)
  its not-ready path calls `halt_abort_before_lean_ready` rather than
  publishing a status frame: an abort leaves `ELR_EL1` on the faulting
  instruction, so a returned frame is `eret`ed straight back into the abort.
  A fault raised at the SVC seam halts too (outcome tag 2, `.faulted`,
  `halt_after_delivered_syscall_fault`, PR #887 review round 5): the model
  restarts that caller *at* the `SVC`, and a `.blocks` sentinel would `eret`
  it past the `SVC` instead.  Round 7 located that arm and the tag-2 decode
  in the handler's and `dispatch_svc`'s own terminal matches
  (`handler_faulted_arm_halts`, `dispatch_decodes_faulted`), not at their
  first textual occurrence.
  **A fallback may publish a return frame only on a seam whose exception
  advanced the PC** — the SVC seam, where the unknown-syscall path keeps its
  not-ready frame and where the not-ready behaviour as a whole is RR5's
  decision.  The host lane keeps the abort fallback frame as the harness
  observable; `scan_trap_rs_abort_fallback_halts` pins that the write is
  host-only and the halt sits on the not-ready path.  Both halts are
  unreachable at v0.34.44 (no core sets `lean_ready`) and SM10.1 replaces the
  delivered one with the successor install; new code must not read either as
  the fault path's contract.  A kernel-origin exception halts the core too,
  and that one *is* the contract: `halt_if_kernel_origin` (an EL1-origin
  frame) and the `KERNEL_ABORT` arm (a current-EL abort syndrome) are
  fail-closed by design, not SM10.1 placeholders.
- **The deployed reader-writer lock is the ticket-FIFO one, and each lock has
  its own refinement bridge** (WS-RR RR6, v0.34.50).  `STATIC_RW_LOCK_POOL` is
  `[QueuedRwLock; 4]` — `build.rs` pins the element type, so a revert to the
  CAS-retry `RwLock` fails the build — and the four `rw_lock_*` helpers pass
  the executing PE's id, which the ticket protocol needs.  Four things new code
  must respect.  (1) **Cite the right relation.**  `rwLockSim`
  (`Locks/RwLockRefinement.lean`) relates the writer bit and the reader count
  and says in as many words that the abstract `waiters` field is **not**
  represented — honest for the CAS-retry lock, useless for a FIFO claim.  A
  statement about the deployed lock's admission order goes through `queuedSim`
  (`Locks/QueuedRwLockRefinement.lean`), whose ghost ledger is pinned to the
  machine words by `QueuedTicketWf` and whose capstones are
  `queuedRwLock_refines_rwLockSpec` / `queuedRwLock_admits_in_spec_order`.
  Those were proved **before** RR6.10 repointed the pool, so no released
  version carried an unrefined core lock, and the ordering is the rule for any
  future lock switch: the refinement lands first.  (2) **Cite the premise-free
  capstone.**  `rust_rwLock_refines_lean` and
  `rust_rwLock_refines_lean_via_rustImplementsRwLock` still take
  `ListBlockBisim` — which is their own conclusion, one block at a time — and
  are kept only as the general forms.  The results that assert something are
  the `_honest` ones (`rust_rwLock_refines_lean_honest`,
  `…_via_rustImplementsRwLock_honest`, `rust_rwLock_refines_lean_from_unheld`),
  derived from the trace-shape predicate `honestBlock` through
  `listHonestBlocks_listBlockBisim`.  The same shape rule applies to new
  bridges: `queuedTrace_preserves_queuedSim` and
  `ticketTrace_preserves_ticketLockSim` are both stated so they do not assume
  their own per-block conclusion, and a bridge that does is shipping the defect
  RR6 exists to remove.  (3) **`rw_lock.rs` is retained deliberately**, for
  three reasons recorded in its own module docs: it is the Tier-5 oracle's
  second implementation (the oracle drives *both* real locks and checks them
  against each other, against the ticket interval, the served ticket's
  liveness, the per-core withdrawal slots and the per-core held words, and
  against `encodeRwLock` after every operation — and it *excludes*, counted
  and under a ceiling
  rather than silently, a trace that asks a core to acquire while its own
  withdrawal is unclaimed, which parks on hardware and no single-threaded
  replay can execute), it owns the `WRITER_BIT` / `READER_MASK` layout
  `queued_rw_lock.rs` now imports rather than re-declares, and its D-4
  refinement was *completed* rather than deleted.  It is not a fallback: the
  kernel instantiates it nowhere.  (4) **The lock inventory is 30**, partitioned
  4 memory-model + 6 TicketLock + 16 RwLock + 4 refinement (25 at RR6; WS-LC
  LC1 added the withdrawal's three payoff entries and LC5 the two
  cycle-denominated bounds), and
  `LOCK_THEOREM_COUNT` in `lock_bridge.rs` must equal
  `lockPrimitives_count` (`scripts/check_lock_ffi_symmetry.sh`, Tier 0).  The
  R-10 entry names the *liveness* theorem `rwLock_writer_liveness` — admission
  under `FairTrace`, with WS-LC LC1's explicit no-withdrawal premise — and the
  single-step safety theorem it used to stand in for keeps its own entry under
  its accurate name; RR6.23's release-count bound
  (`rwLock_writer_admitted_within_release_budget`) is the "leaves the queue"
  form and is not the entry (the closure audit found both this file and the
  spec naming it as such).
  The two SM2.C **datatype** extensions RR6 did not absorb are WS-LC's (see
  below), and both are closed: **SM2.C-C** at v0.34.54 (spec, both refinements,
  the deployed lock and both consumers) and **SM2.C-T** at v0.34.55 (the timed
  execution) — see the two bullets below.
- **A queued core may withdraw its request, and a withdrawn head hands its
  turn on.**  `RwLockOp.cancel` (v0.34.51) removes `c`'s entry from `waiters`
  and — since PR #890 review round 5 — promotes the contiguous reader run at
  the head when no writer holds and the new head is a reader
  (`RwLockState.cancelPromotes`, `cancelRun`), exactly as the deployed lock's
  withdrawal of a served head passes the turn to the readers behind it; a
  writer head keeps waiting for the readers (INV-R1), and a withdrawal from
  anywhere but the head promotes nobody (`rwLock_cancel_nonhead_admits_no_one`).
  It preserves all five INV-R conjuncts (`rwLock_withdraw_preserves_wf` +
  `rwLock_promoteReaderRun_preserves_wf`), is never an effective release and
  never installs a writer (`rwLock_cancel_not_effective_release`,
  `rwLock_cancel_admits_only_the_head_reader_run`), so it costs the waiters
  behind it nothing — it can only admit them sooner.  The old `cancel` was the
  neutral `waiters.filter` (`rwLock_cancel_admits_no_one`), which contradicted
  the lock and made a served reader's holder status path-dependent; see the
  round-5 bullet below.  Four things new code must respect.
  (1) **Which liveness conclusion you may cite changed.**  A theorem concluding
  "`c` *leaves the queue*" is satisfied by a withdrawal and is unchanged
  (`rwLock_writer_admitted_within_release_budget`); a theorem concluding "`c`
  *becomes the holder*" is false of a window in which `c` withdraws, so
  `rwLock_writer_liveness`, `rwLock_queued_liveness`, `rwLock_reader_liveness`
  and every `admissionStep*_bounded` now take an explicit
  `RwLockExecution.noCancelIn c k₁ k₂` premise.  It narrows by `.mono`, and a
  concrete trace discharges it through the decidable whole-trace form
  `cancelFree`.  The premise reaches CC-5: `lockContention_delay_bounded` and
  the alphabet bound carry it, and `lockContentionRun` carries it per step, so
  an accepted run supplies it for free.  (2) **`leave_waiters_implies_holder`
  has a third disjunct**, not a narrower hypothesis — withdrawing *is* a way to
  leave the queue.  (3) **Both refinement bridges relate it.**  The CAS-retry
  one honestly performs no atomic access (`opCorresponds.cancel_no_queue`,
  `honestBlock.cancel_no_queue`) — a queueless lock has no queue for a
  withdrawal to disturb.  The ticket-FIFO one (v0.34.52) carries it properly;
  see the next bullet, and the deployed lock carries it at v0.34.53 — the one
  after that.  (4) **Both 2PL unwinds emit one** since v0.34.54 — see the
  shrinking-phase bullet below.
- **The ticket lock's ledger tombstones; the queue it represents is the
  *live* one** (WS-LC LC2, v0.34.52).  `now_serving` owes one advance per
  ticket ever issued, so a withdrawal cannot remove a ticket from the middle
  of the interval — `QueuedRwLockConcrete.cancelled` (the implementation's
  per-core slot array) marks it instead, and `liveLedger` is the ledger minus
  those.  Five things new code must respect.  (1) **`ledgerTickets` is
  unchanged**: the ticket column is still exactly `[now_serving,
  next_ticket)`, so `await_turn`'s spin bound and every other arithmetic
  consequence are untouched.  What moved is `queuedSim`'s queue conjunct,
  which now reads `liveLedger`.  (2) **`queuedSim` has a fourth conjunct**,
  `queuedHeadLive`: the served ticket is never a tombstone.  It is a
  *block-boundary* property — a `pass_turn` uncovers a head that may be
  withdrawn, and the skip loop restores it before the block ends — which is
  why it is not in `QueuedTicketWf`.  With it, "no live request" and "no
  outstanding ticket" are the same statement, so the calm-lock block shapes
  are as they were.  (3) **A turn may be passed only for a ticket nobody has
  withdrawn** (`opEnabled`), so a skip must *claim* the slot first; the claim
  is a compare-exchange and it is the arbiter between the canceller and the
  previous holder's loop.  (4) **Promotion is read off the ledger, not
  computed from the served ticket**: `promoteFrom` / `readerAdmitFrom` walk
  the live entries and retire tombstones between them, because the old
  `promoteOps` gave promoted readers *consecutive* tickets, which a mid-queue
  withdrawal falsifies.  (5) **The FIFO capstone is about position, not
  arithmetic**: `queuedRwLock_admits_in_spec_order` says the `i`-th waiter is
  the `i`-th live entry, holding some outstanding ticket — a sharper claim
  than the `now_serving + offset + i` it replaces, since that formula is
  simply false once anything has withdrawn.
- **The deployed lock's acquisition splits when it may have to be withdrawn**
  (WS-LC LC3, v0.34.53).  `QueuedRwLock::acquire_read` / `acquire_write` are
  the *fused* spellings — they take a ticket and spin to completion inside one
  call, so there is no instant at which a caller holds a ticket and could
  abandon it.  A caller that may have to unwind takes `enqueue(core, mode)`,
  spins on `is_served(ticket)`, and then calls **exactly one** of
  `complete_read`, `complete_write` or `cancel` for that ticket; a request ends
  in one of three ways — a completion followed by a release, a withdrawal that
  returns `CancelOutcome::Withdrawn`, or a withdrawal that returns `Holding`
  followed by a release (PR #890 review round 5, next bullet but two).  Five
  things new code must respect.  (1) **Exactly one terminator per ticket,
  always.**  `next_ticket` is an unconditional `fetch_add` and `now_serving`
  owes one advance per ticket ever issued, so a ticket that is neither
  completed nor withdrawn stalls the lock permanently — the failure is a hang,
  not a data race, and no assertion catches it.  (2) **The withdrawal is published before the head is checked,
  and both directions carry a `SeqCst` fence.**  `cancel` stores `ticket + 1`
  into its own slot, fences, and only then asks whether it is being served;
  `claim_withdrawal_of` fences before reading the slots.  This is the
  store-buffer (Dekker) shape — a store to one location followed by a load of
  another — and **`SeqCst` on the four accesses alone is not sufficient**: loom
  found the interleaving in which neither side retires the ticket, and the
  fences are what removed it.  Reordering the publish after the head check, or
  dropping either fence, loses the race in the direction that stalls the lock.
  (3) **The compare-exchange is the arbiter.**  Exactly one of {the
  withdrawing core, the previous holder's skip loop} succeeds in clearing a
  given slot, and that one advances `now_serving` past the ticket; the loser
  does nothing.  Deleting the arbitration and testing the slot instead admits
  two cores at once.  (4) **One outstanding ticket per core per lock, and
  `enqueue` waits for the core's last withdrawal to be retired.**  The slot
  array is indexed by core id (`MAX_WAITERS` entries, asserted in range) and
  holds one withdrawal, so a core may not take a second ticket while its
  first withdrawal is unclaimed: the second `cancel` would overwrite the
  publication and the first ticket would never be retired — `now_serving`
  stops on it and the lock stalls — on the contract-respecting sequence
  enqueue, withdraw, enqueue, withdraw (WS-LC closure audit, v0.34.56: the
  first cut shipped it, and all four LC3 loom models withdrew once per core).
  `enqueue` therefore parks until the slot is empty
  (`await_withdrawal_retired`), a wait that ends before any later ticket
  could be served and so costs nothing a fresh ticket would not, and the
  non-blocking `try_acquire_*` are refused in that state; `cancel` refuses a
  ticket `now_serving` has already passed, since a stale publication would
  park the core's next `enqueue` for good; a holder's withdrawal returns on
  the held word before it publishes (PR #890 review round 3 — the
  `debug_assert` that stood there vanishes in release builds), and a
  `debug_assert` still refuses a withdrawal naming another core's served
  write ticket.  The Lean model
  carries the rule as `QueuedTicketWf.ledgerCoresNodup` with the issue enabled
  only for a core holding no ticket, `publish_slot_empty` is the theorem that
  the unconditional store never overwrites, and the `acquire*_enqueue` blocks
  require `¬ withdrawalPending`, so the model no longer admits the trace the
  lock refuses.  A live double enqueue — two tickets, neither terminated —
  remains the caller's contract: `ledgerCoresNodup` states it and nothing at
  runtime checks it.  `pass_turn`'s skip loop is bounded by the withdrawals
  published while it runs, **not** by `MAX_WAITERS` — a core whose tombstone
  was just retired may re-enqueue at the head and withdraw again — so the
  per-core iteration cap that used to sit there fired on a correct execution
  and is gone; the invariant it checks now is `now_serving ≤ next_ticket`.
  `NO_WITHDRAWAL` is `0` and slots hold `ticket + 1`, so ticket `0` is
  withdrawable.  (5) **The split surface crosses the FFI**, because the unwind's
  caller is on the Lean side: `ffiRwLockEnqueue`, `ffiRwLockIsServed`,
  `ffiRwLockCompleteRead`, `ffiRwLockCompleteWrite`, `ffiRwLockCancel` and
  `ffiRwLockCancelCount` join the sixteen SM2.D symbols, reconciled across the
  three surfaces by `scripts/check_lock_ffi_symmetry.sh`.
- **A release by a non-holder, a re-acquisition by a holder, and a
  withdrawal by a holder are the deployed lock's no-ops — decided by its held
  word, not by the caller** (PR #890 review rounds 2 and 3).  `QueuedRwLock`
  carries one `held` word per core (`HELD_NONE` / `HELD_READ` /
  `HELD_WRITE`), set at the core's admission and cleared at its release, and
  `acquire_read` / `acquire_write` / `release_read` / `release_write` /
  `cancel` each read the caller's word before they touch anything else: a
  holder re-acquiring returns, a non-holder releasing returns, a holder
  withdrawing returns before anything is published (round 3 — a writer still
  holds its ticket, so a withdrawal that reached the publish was claimed at
  once and passed the turn under the set bit, and the release passed it
  again, past a live waiter; a `debug_assert` had stood in for the identity
  and vanishes in release builds).  The RAII guards record whether they
  acquired, so a nested same-core guard is a no-op both ways rather than a
  release of the outer scope's hold (round 3); `enqueue` by a holder is
  outside the contract and reported in debug builds.  Before the word existed `release_read` was an unconditional
  `fetch_sub` and `release_write` an unconditional clear-and-pass-turn, so a
  non-holder's release in a release build underflowed the reader count or
  handed the turn on while the real writer still held — and the
  two-phase-locking unwind (`unwindAll`, next bullet) releases **every**
  member of a footprint, holding or not, relying on exactly the identity the
  lock did not implement, while the refinement claimed it as a stutter no
  code path performed.  Four things new code must respect.  (1) **The
  relation now represents the holders**: `queuedSim`'s fifth conjunct is
  `queuedHeldSim` — a core's word reads `HELD_READ` iff the spec has it as a
  reader and `HELD_WRITE` iff the spec's writer is that core — so the
  holder no-op blocks of `queuedBlock` (`acquireRead_holder`,
  `acquireWrite_holder`, `cancel_holder`, `releaseRead_noop`,
  `releaseWrite_noop`) are the one held-word load and are
  *derived* in `queuedBlock_preserves_queuedSim`; every acquire and release
  block opens with that load (`heldLoad`), and the effective releases clear
  the word (`heldStore c none`) **before** the state word moves, and the
  withdrawal block opens with the held load before the publish
  (`cancelPublish` is enabled only for a core holding nothing) — orders
  `build.rs` pins for both releases and for `cancel`
  (`scan_queued_rw_lock_protocol_intact`, its third check).
  (2) **A queued waiter re-acquiring is decided by its request word** (the
  next bullet): at round 2 it had no block, because the implementation had
  no branch and the one-outstanding-ticket contract (`ledgerCoresNodup`) was
  what ruled the call out — `queuedBlock` said so by having no shape rather
  than a fictional stutter, and that honest gap is the one the class
  closure filled.  (3) **The CAS-retry `rw_lock.rs` has no such no-ops
  and its bridge no longer claims them**: it keeps no holder bookkeeping, so
  its four `honestBlock` `_noop` constructors and `opCorresponds.noop` —
  each a `[]` block for a call on which that code performs an atomic access
  — are gone, and its trace-level theorems cover exactly the traces that
  respect its caller contract (acquire only while uninvolved, release only
  what you hold), stated in its module docs.  **The `TicketLock` bridge
  makes the same choice** (round 4 — the sweep this fix owed its sibling):
  `ticket_lock.rs` has no per-core word, so a re-acquiring holder parks
  forever and a non-holder's release admits the next waiter under the
  holder; `ticketBlock`'s `tryAcquire_noop` / `release_noop` were the same
  fiction and are gone, `TicketLockState.callerContract` states which
  operations the bridge covers, and `ticketBlock_respects_contract` /
  `ListTicketBlocks_contractTrace` prove every shape and every admitted
  trace is inside it.  A silent no-op there would mask what the
  kernel-entry consumers halt on (`assert_not_holding_round_lock`), which
  is why the deployed `QueuedRwLock` is the only lock that implements the
  spec's no-ops as branches: the unwind relies on them there and nothing
  does here.  (4) **The gates ask the lock
  the question.**  The Tier-5 oracle issues a non-holder's release, a
  holder's re-acquisition and a holder's withdrawal (with the ticket the
  core actually held) to the real ticket lock and holds every core's word
  to the spec's holders after each op (`check_holders`); a queued
  waiter's re-acquisition is issued to the ticket lock since the class
  closure (it was issued to neither at round 2), and the CAS-retry lock
  is sent neither call.  On the host a std thread stands in for a PE and the
  per-CPU stub answers core 0 to every thread, so the bridge's cross-thread
  tests give each thread its own PE identity (`per_cpu::HostCoreIdentity`,
  test-only): several threads under one id are one PE issuing overlapping
  acquisitions, which the held word turns into no-ops and stranded counts —
  the first host lane after the word landed hung in exactly that shape.
  The loom gate gained
  `unwind_by_a_non_holder_never_touches_the_holder` and
  `every_pair_of_units_is_safe` — every unordered pair of the lock's
  single-lifecycle units, one unit per thread, unbounded (fourteen units
  since round 5, so 105 models with the diagonal); two of them are the
  unwind at a member the core holds, as a reader and as the writer (round
  3), and two the enqueue-twice-then-acquire shapes (the class closure).
  The three **chained** units (round 5: read then write, write then read,
  withdraw then read — a second acquisition beginning on the words the
  first lifecycle left) meet every unit in
  `every_chained_unit_meets_every_unit`, 48 models under a **stated
  preemption bound** (`CHAINED_PREEMPTION_BOUND = 3`), because a thread
  running two lifecycles has twice the atomic and yield points and an
  unbounded exploration of two of them did not finish in a per-PR lane; the
  bound is in the code, the script and the docs, never implied.  What that
  enumeration is **not** is the SM2.C-defer plan's "op-sequences of length
  ≤ 4" (round 5): that sentence is the single-threaded census
  `per_core_census_to_depth_four`, derived from the matrix's classification,
  and the loom claim is stated as the pairs it runs.
- **A queued core's second acquisition is the deployed lock's no-op too —
  decided by its request word — and every per-core entry point decides on
  the core's own words before it writes** (the class behind PR #890 review
  rounds 2 and 3, closed at the cause).  Rounds 2 and 3 and the closure
  audit's stall were one defect: the lock did not know the executing core's
  own situation — no held word, then one `cancel` did not read, and no
  record of a core's live request at all — so the refinement asserted no-op
  blocks of paths the code did not have and the consumers relied on caller
  contracts.  `QueuedRwLock` now carries a third word per core, `request`
  (`ticket + 1` for the core's one live request, `NO_REQUEST` for none; set
  by `take_ticket`, cleared at a reader's entry, the writer's release, a
  withdrawal's publish and a refused single attempt's pass), and every
  entry point decides the core's case — idle, queued, withdrawn, holding —
  on `held`, `request` and `cancelled` before it writes anything shared.
  Five things new code must respect.  (1) **One outstanding ticket per core
  is a fact the lock establishes, not a contract**: `enqueue` by a queued
  core returns the ticket it already holds, by a reader holder the
  `HELD_TICKET` sentinel (served at once, a no-op at every terminator), and
  the fused acquisitions and the guards return on `involved`; a `cancel` or
  `complete_*` by a core with no request is **refused** (`own_request`,
  every build), one naming a ticket other than the core's own is reported in
  debug builds and withdraws or completes the recorded one, and `complete_*`
  wait for their own turn rather than trusting the poll.  (2) **The
  per-core state matrix is the behavioural pin and `build.rs` holds it to
  the code**: `per_core_state_matrix` classifies every per-core entry point
  in every per-core state, `PER_CORE_ENTRY_POINTS` must equal the lock's
  `pub fn`s taking `core_id` (derived from the code view), and every one of
  the twelve is pinned at the level of **statements** (round 4 — order is
  not control: a harmless earlier read satisfied round 2's first-read-
  before-first-write check while the real branch was inverted or its
  `return` moved below the write): `core_entry_point_status` requires the
  controlling branch to be a top-level `if` of the entry point's own
  brace-matched body with exactly the pinned condition and a block ending
  in a diverging `return`, placed before the statement performing the
  shared write; a name the condition reads bound by the pinned load and
  not rebound in between; `own_request` called at top level; a guard's
  acquisition the only occurrence of the call, inside `if acquired`; and
  the helpers held to their exact forms (`involved` the disjunction,
  `own_request` an `assert!`).  `verify_core_entry_point_scanner` holds the
  checker itself to token-preserving mutations.  A new entry point fails
  the build until it is classified.  (3) **The Lean
  blocks are conditioned on the words, and the abstract facts are derived**:
  `queuedSim`'s sixth conjunct is `queuedRequestsSim` (a core's word
  records `t` iff `(t, c)` is a live ledger entry; the seventh,
  `queuedRequestModesSim`, pins a live request's mode word to the spec's
  queued mode — round 5, below), every per-core branch
  hypothesis of `queuedBlock` reads `c ∈ conc.heldRead` / `(c, t) ∈
  conc.requests` rather than `c ∈ abs.readers`, and
  `queuedBlock_preserves_queuedSim` derives the spec's branch from the
  relations (`queuedSim_involved_of_request`, `queuedSim_involved_of_held`,
  `queuedSim_not_involved`) — so a relation pinning a word to the wrong fact
  fails the proof, where before the step cases consumed the abstract
  hypothesis and consulted the relation nowhere.  The queued no-op blocks
  are `acquireRead_queued` / `acquireWrite_queued` (two loads); `cancel` has
  `cancel_holder`, `cancel_noRequest` and `cancel_queued`; the promotion
  carries the relation through the admitted readers' cleared requests and
  takes the live cores' distinctness (INV-R3) for it.  (4) **The gates ask
  the lock**: the Tier-5 oracle issues a queued waiter's re-acquisition and
  an uninvolved core's withdrawal to the ticket lock and holds every core's
  request word to the spec's queue and held writer (`check_requests`); the
  loom enumeration includes enqueue-twice-then-acquire in both modes, and
  its mutation inverts the `involved` load in `acquire_read`.  (5)
  **`request` lives on the second cache line by design** (128 bytes): the
  shared words fill the first, the owner-only arrays — `request` and, since
  round 5, `request_mode` — the second, and
  `shared_words_fill_the_first_line_and_requests_the_second` pins the
  layout.
- **A withdrawal of a request the spec has already admitted realises the
  admission; the deployed lock decides which on its own words, and the Tier-5
  comparison is of identities, per step** (PR #890 review round 5).  After a
  writer's `release_write` returns, the head waiter is *served* but not yet
  *completed*: the spec's release promoted it atomically, so its `cancel`
  there is the holder no-op, while the lock retired the served ticket and had
  one holder fewer than the spec.  The bridge folds every waiter's entry into
  the release block that promotes it, so that interval does not exist in the
  model, and the fold was sound only if nothing a served core can do differs
  from the entered state — which `cancel` broke.  And the spec's own `cancel`
  was the neutral filter while the lock's withdrawal of a served head passed
  the turn to the readers behind it, so whether a queued reader was a spec
  holder was **path-dependent**, and no history-free decision in the lock
  could be right.  Six things new code must respect.  (1) **The spec moved,
  not the lock's memory** (the improvement direction): `cancel` promotes the
  head reader run (the bullet above), and with that "served reader ⟹
  holder", "served writer ⟹ holder iff `state == 0`" and "queued reader ⟹
  holder iff no live write request is ahead of it" are decidable from the
  lock's words.  (2) **The mode is the lock's record.**  `enqueue(core, mode)`
  stores `request_mode` before the request word (`take_ticket`), `complete_*`
  in the other mode is refused on it in every build, and `cancel` decides on
  it: a write request enters when served with no reader (a CAS from `0` that
  cannot fail — only the served core can add a reader), a read request enters
  when `write_request_ahead` — the other cores' request and mode words, read
  in that order, over `[now_serving, ticket)` — finds no live writer, and
  waits for its turn to do so; anything else is the LC3 withdrawal verbatim.
  The verdict is stable: a writer ahead can only leave.  (3) **`cancel`
  returns `CancelOutcome`** — `Withdrawn`, nothing owed; `Holding`, the core
  holds and owes a release — and the two-phase-locking unwind needs no branch,
  since the release that follows every withdrawal releases what a `Holding`
  entered.  (4) **The Lean relation carries the mode**: `requestModes` beside
  `requests`, `requestModeStore` in `takeTicketOps` ahead of the request
  store, `queuedRequestModesSim` (a live request's recorded mode is
  `specModeOf` — the queued mode, or `write` for the held writer) as
  `queuedSim`'s seventh conjunct, carried through the promotion with INV-R3;
  the withdrawal block is `withdrawOps ++ cancelPromoteFrom`, the CAS-retry
  bridge's `cancel_promoting` carries the run as a promoting release does,
  and a `Holding` withdrawal has no block of its own — it is the deferred
  half of the entry the promoting block already folded, which is what makes
  the served interval sound to fold again.  (5) **The gates ask the lock.**
  The oracle holds each withdrawal's verdict to the spec's (`expect_outcome`:
  a queued waiter's must be `Withdrawn`, a holder's and an uninvolved core's
  the no-op), mirrors the promoting withdrawal (`promote_reader_run`), holds
  the mode words (`check_requests`), and both oracles print **one identity
  line per state** — `W=<core|->;R=<sorted reader cores>;Q=<core:r|w,...>`,
  the initial state included — read back out of the ticket lock's per-core
  words on the Rust side, where `W=<flag>;R=<count>;Q=<length>` had let a
  wrong-waiter promotion, a reordered queue or a changed mode agree on every
  count; the harness compares whole outputs and captures both exit statuses.
  The matrix has nine start states (`(CoreState, Env)` — queued and served
  in both modes, a served writer behind a reader, withdrawn, holding, idle)
  under one classification `cell`, and the census replays every sequence of
  up to four entry points from each; `build.rs` holds `run_unit` to every
  per-core entry point, which is how the two guard spellings were found to
  be in no loom unit.  `scripts/check_lock_ffi_symmetry.sh` holds every
  symbol's parameter and return types across the three surfaces, since
  `ffi_rw_lock_enqueue` gained an argument and `ffi_rw_lock_cancel` a
  result.  (6) **The unbounded loom models do not spin against each other**:
  loom's branch budget is exhausted by two threads spinning at once, so a
  model has one waiting thread and the driving thread completes served
  requests after the race; and a third acquisition in a two-thread model
  multiplies the schedules past what an unbounded run finishes, so the
  ordering in which one core withdraws twice behind two successive writers
  is pinned sequentially
  (`a_second_withdrawal_behind_a_new_writer_is_retired_by_its_release`)
  rather than modelled.
- **The two-phase-locking shrinking phase withdraws before it releases**
  (WS-LC LC4, v0.34.54).  `withLockSet`'s third phase and the revalidated
  entry's refusal path are both `unwindAll` — one definition, so the two
  cannot answer "what does a bracket do on the way out" differently.  Five
  things new code must respect.  (1) **The order is load-bearing.**  Two
  identities meet at each member: a release by a non-holder is the identity,
  and a withdrawal by a holder is the identity (INV-R4 keeps holders out of
  `waiters`) — on the deployed lock, a withdrawal by a core the spec has
  admitted *realises* the admission (`CancelOutcome::Holding`, PR #890 review
  round 5) and the release that follows releases it — so both orders are
  correct on a well-formed state and neither needs a branch.  Withdrawing first is what makes the payoff
  *unconditional* — the release arms promote **from** `waiters`, so a core
  still queued when its own release runs can be promoted into a holder slot
  the withdrawal already passed.  `rwLock_release_then_cancel_not_queued`
  records the other order so a refactor that swaps the folds has to answer
  it.  (2) **The payoff is about `waiters`, not about holding.**
  `unwindAll_leaves_no_queued_request` says the unwinding core has no queued
  request at any member, with no distinctness and no resolvability condition
  on the footprint — the withdrawal fold establishes it everywhere and no
  release arm enqueues.  It deliberately does **not** say the core is
  uninvolved: a core holding a *write* lock, unwound at a member declared
  `.read`, keeps `writerHeld`, and ruling that out needs the growing phase's
  mode agreement threaded through.  (3) **The insensitivity predicate is
  about the phase**: `UnwindInsensitive` / `UnwindInsensitiveOn` carry two
  clauses, one per operation.  A separate `CancelInsensitive` beside a
  `ReleaseInsensitive` would be one question with two answers and every
  capstone would have to remember to demand both; discharging the pair costs
  nothing, since each witness is its release half with one name changed.
  Every `withLockSet` invariant-carriage lemma likewise gained a
  withdrawal-stability hypothesis.  (4) **`releaseAll` still means release
  only** and every theorem about it is unchanged; `cancelAll` sits beside it
  and `unwindAll` is the composite.  A statement characterising what a
  *bracket* does names `unwindAll`.  (5) **The bracket stays
  projection-invisible**: the golden trace is byte-identical, and
  `unwindAll_lockWritesOnly` / `_preserves_projection` / `_confinedToCore`
  carry the information-flow results across unchanged.

  Two things were **re-homed rather than duplicated** in the same cut, each
  having lived downstream of the definition it is about: the at-any-key
  characterisation of the object-store update, and the per-primitive
  extension-invariant preservation lemmas — which existed in *three* copies
  (`LockSetHeld`, `NonInterferencePerCore`, `IPC/CrossCore/Cancellation`)
  because no two of those modules are in each other's import closure.  They
  now sit once, beside `updateObjectLockAt` in `WithLockSet`, which all three
  import.  `LockId.lookup_object_eq` — the missing third sibling of the
  lookup's kind and lock-state projections — was added, since without it a
  caller that knows what the store holds at a key could conclude nothing
  about what a lookup there returned.
- **A lock-delay bound is denominated, and by an assumption the kernel does not
  make** (WS-LC LC5, v0.34.55).  `RwLockExecution` carries `stepCost : Nat →
  Nat` — the cycles between step `k` and `k+1` — **with no default**, so all
  nine construction sites declare a cost model where a reviewer can see it.
  Five things new code must respect.  (1) **Three denominations, three
  assumptions.**  A bound in *lock operations* is unconditional given fairness
  (`rwLock_writer_admissionStep_bounded`).  A bound in *cycles* needs a
  per-critical-section ceiling (`RwLockExecution.BoundedCriticalSection`,
  supplied as a hypothesis: `rwLock_writer_admitted_within_cycle_budget`,
  `lockContention_elapsed_bounded`).  A bound in *hardware ticks* needs a
  counter frequency, which is a board fact, so it lives in a **staged** module
  (`Locks/ReleaseBudgetTiming.lean`) and not in the production lock model at
  all.  Quoting a figure as a time without naming which conversion produced it
  is quoting a number with no denominator.  (2) **`BoundedCriticalSection` is a
  Prop about the field, never a structure invariant.**  An execution whose
  critical sections are unbounded is a perfectly good execution and every step
  bound still holds of it; what fails is only the *reading* of that bound as
  wall-clock.  Do not add it to `RwLockExecution` as a field or a well-formedness
  conjunct — that would refuse executions the model should admit, and would make
  the step bounds conditional on something they do not need.  (3) **The cycle
  forms are corollaries, and each one collapses back.**
  `rwLock_writer_cycle_budget_at_unit_cost` and
  `lockContention_elapsed_at_unit_cost` instantiate the cycle bound to the step
  bound it came from, because a denomination that had quietly weakened the claim
  would look exactly like one that had not.  A new cycle-denominated result
  states its own collapse.  (4) **The generic and execution-level forms both
  stay.**  `lockContention_wallClock_bounded` takes a cost function (the general
  statement, over any cost model); `lockContention_elapsed_bounded` reads
  `e.stepCost` (the instance at this execution's own).  A caller holding an
  execution should reach for the latter and not re-supply what the execution
  already carries; the typed evidence arms consume the execution-level forms
  precisely because that pins both.  (5) **`MAX_RELEASE_DELAY` is 1024 *lock
  operations*.**  `releaseBudgetCycles` converts it under a ceiling and
  `releaseBudgetTicks` under a timer configuration; on the RPi5's 54 MHz /
  1 ms timer the same 1024 steps span from a single tick to 1024 ticks
  depending on the ceiling assumed (`releaseBudgetTicks_rpi5_range`), which is
  why the step figure alone was never a time.  **A duration converts by the
  ceiling** (PR #890 review round 4): `hardwareTimerToModelTick` floors an
  *absolute* counter value, and an interval that begins mid-tick crosses one
  boundary more than its length suggests, so `releaseBudgetTicks` uses
  `hardwareDurationToModelTicks` and `elapsed_ticks_le_releaseBudgetTicks`
  is stated from any start counter (`hardwareTimerToModelTick_sub_le_duration`
  is the relation between the two conversions).  New code converting an
  interval must not reach for the absolute conversion.

  `elapsedBetween` and its two bounds moved here from
  `InformationFlow/FineLockFlow`, where they had been introduced with a note
  that the execution datatype "has no such notion" — it has one now, so the
  vocabulary belongs beside the datatype that carries it.
- **Registered uncovered lock domains** are enumerated in Lean, not in prose:
  `UncoveredLockDomain` (`InformationFlow/FineLockFlow.lean`) names each gap and
  its owner, and its completeness theorem forces a new domain to be registered.
- **An operation's `_modifiedFields` list is a proof obligation, not a
  comment** (WS-RR RR7.19, v0.34.70; completed by the RR7 audit round,
  v0.34.109).  The six `*_modifiedFields` lists in
  `Kernel/CrossSubsystem.lean` had no consumer at all: an operation could write
  a field its own list omits and nothing would notice.  RR7.9 found one such
  omission by reading (`capabilityOp_modifiedFields`, missing the four CDT
  fields); giving the lists an obligation found a second immediately
  (`storeObject_modifiedFields`, missing `.asidTable`, which `storeObject`'s
  record update writes when the stored or displaced object is a `.vspaceRoot`);
  and writing the four theorems v0.34.70 had promised and not shipped found two
  more, plus the gap that had made one of them impossible to state.  Four
  things new code must respect.  (1) **Declaring a write-set obliges you to
  prove it**: `preservesFieldsOutside fs st st'` says every `StateField`
  outside `fs` is unchanged, quantified over the whole field type rather than
  over whatever the author enumerated, and **every one of the six lists carries
  a `_preservesFieldsOutside` theorem at its own list** — `storeObject`,
  `revokeService`, `serviceRegisterDependency`, the retype, the four capability
  operations (`cspaceMintWithCdt`, `cspaceCopy`, `cspaceMove`,
  `cspaceDeleteSlot`) and both dual-queue operations — each false at an
  under-declared list.  (2) **`StateField` is total over `SystemState`, and the
  pin is a theorem, not a count**: `SystemState.eq_of_fieldEq_all` proves that
  agreement on every constructor is state equality, through
  `SystemState.mk.injEq`, so a field added to the structure without a
  constructor fails to elaborate.  At v0.34.70 the enumeration named sixteen of
  twenty-seven fields, so a write to `scThreadIndex` — which the receive path's
  donation return performs — could not be *declared* at all, and every
  write-set claim in the tree was silent about eleven fields.  (3)
  **Over-declaring is the safe direction** (`preservesFieldsOutside_mono`); it
  costs disjointness, never soundness.  `ipcEndpointOp_modifiedFields` is
  `storeObject`'s set **plus `.scheduler` and `.scThreadIndex`** (the wake and
  the deschedule; the donation return), and `capabilityOp_modifiedFields` is
  `storeObject`'s set plus the four CDT fields.  The v0.34.70 lists were
  `storeObject`'s set alone and `[.objects, .lifecycle, …CDT]`, both *false* of
  their operations — the second under the very sentence RR7.19 had retracted
  for the first.  Tightening the index/ASID fields back out is registered debt
  (`docs/REGISTERED_DEBT.md` §C), not an assumption.  (4) **The lists are
  consumed**: `predicateFramedByDisjointWrites` turns "this read-set and that
  write-set are disjoint" into "this operation preserves that predicate", so an
  omitted field licenses a preservation conclusion the operation does not
  earn.  A list that composes another is *defined over* it
  (`lifecycleRetypeObject_modifiedFields = storeObject_modifiedFields`; the IPC
  and capability lists are `storeObject_modifiedFields ++ …`), so a correction
  cannot reach one and miss another; and each composite theorem is proved from
  one lemma per primitive the operation is built from, composed by
  `preservesFieldsOutside_trans`, never by a second reading of the operation.
- **Every declared `LockSet` footprint carries a size bound, stated at its own
  arity** (WS-RR RR7.18, v0.34.69).  `boundedWait_under_2pl`, the
  `KernelOperation` invariant and the WCRT surface all take
  `S.size ≤ maxLockSetSize` as a premise, so a footprint without one is a
  transition that reasoning is **silent** about — worse than one it bounds
  loosely.  `lockSetTransitions_within_bound` is a hand-written conjunction and
  had 31 of the tree's **47** footprints; the missing thirteen included every
  state-resolved `*OnCore` form, which is what RR7.12's bracket actually
  acquires.  New code must respect two things.  (1) **The bound is stated over
  every argument, never at a default.**  A footprint that gains a trailing
  `Option … := none` leaves its existing bound elaborating — the default fills
  the new argument in silently — so the shape the live transition declares is
  unbounded while the theorem's name still promises a bound.  That has now
  happened five times (`notificationSignal` at SM9.C.8, `endpointReceive` at
  PR #873 round 8, `endpointSend` and `endpointCall` at RR7.7, and
  `endpointReply`, found by the census: its bound was stated at five of six
  arguments while the live `.reply` dispatch resolves the sixth to `some`).
  (2) **The set is derived, not listed**:
  `SeLe4n/Testing/LockFootprintBoundCensus.lean` collects every `def` whose type
  ends in `LockSet` and named `lockSet_…`, builds the statement its bound *must*
  have from the definition's own telescope, and decides by one `isDefEq` — so a
  new footprint without a bound, or with one at the wrong arity, fails Tier 1
  the day it is written.  A legitimate exemption goes in `boundExemptions` with
  a reason; the list is empty and meant to stay so.
- **Staged modules**: 69 staged-only, listed in
  `scripts/staged_module_allowlist.txt` and gated by
  `scripts/check_production_staging_partition.sh`.  Production must not import
  staged.  (67 until `v0.35.76`, which promoted `Locks/DynamicChainExtension`
  with the RR7.40 footprint that consumes it and staged
  `Architecture/VSpaceARMv8` and `Capability/CSpaceWalkFootprint` — see the
  five-modules note below.  This sentence read **68** from that cut until
  `v0.35.191`, while the allowlist held 69: a hand-kept figure beside a
  derivation, which is what the gate's own output line reports and this prose
  should not restate.  Read the gate, not this number.)  WS-RR RR5.15 promoted five (the three state-committing kernel
  entries `SecondaryEntry` / `PerCoreTimerEntry` / `PerCoreRescheduleEntry`,
  plus the two modules their closure pulls in): an `@[export]` emits a symbol
  only when its module is in `SeLe4n.lean`'s import closure, so a linked image
  carried **one** `T lean_*` entry symbol while `kernel_entry.rs` declared five
  as hard `extern "C"`.  `scripts/check_kernel_entry_exports.py` (Tier 1) now
  verifies each symbol against the built static archive — object code, not a
  text anchor — over a requirement *derived* from **every** HAL `extern "C"`
  declaration: each must be defined by the archive, by the HAL's own assembly
  (a `.global` directive **and** a label for the same name, outside any
  preprocessor conditional, in a source on the `cc::Build` chain that
  `.compile("sele4n_hal_asm")` is called on in a function reachable from
  `main` — the cross gate's own live-chain resolution — and, when a cross
  build's assembled archive is present, also defined by that object code; a
  directive alone declares binding and defines nothing, PR #889 review
  rounds 3–4), or by a reconciled
  `EXPECTED_UNRESOLVED` entry (empty since WS-BP BP4.1 wrote
  `lean_kernel_main`, its one entry until then; an
  entry the HAL stops declaring, the archive starts defining, or — round 6 —
  the Lean tree starts exporting fails, the last because an exported symbol
  whose module sits outside the import closure is exported and undefined at
  once).  Every inventory the gate reads — the Lean exports, the HAL
  declarations, the assembly providers — is read over the shared code views
  with string contents blanked (round 6), so a quoted attribute, block or
  directive is not a symbol.  The
  first cut required the *intersection* of the Lean exports and the HAL
  declarations, which is exactly the set a rename on either side leaves — the
  unresolved spelling drops out of both and the gate passed (PR #889 review).
  **The boot entry's contract left this gate at round 17** and is decided by
  the elaborator in `SeLe4n/Testing/BootEntryContract.lean`: whichever
  declaration carries `@[export lean_kernel_main]` (found with
  `getExportNameFor?`, so any attribute list and any namespace) must call
  `Platform.FFI.bootAndInitialiseRPi5OrHalt` — the checked RPi5 boot with its
  failure handled, so a refused boot parks the PE — and no path from it may
  reach a kernel-state installer except through that call, walked over
  `Expr.getUsedConstants`.  Building the module is the check, and four
  witnesses (a compliant entry and three token-preserving deviations) keep it
  decisive whatever the entry is; since WS-BP BP4.1 wrote it the contract also
  refuses an environment with none.  What the Python gate still holds is
  the link-level half — vacuous until the entry existed, decisive since,
  so the idle-thread, labeling and reservation guarantees cannot be bypassed
  by an entry that boots through `bootFromPlatform` directly.  Executing the
  call is necessary and not sufficient (round 9): the entry must **branch** on
  the checked boot's `Except` and halt on `.error`
  (`boot_entry_handles_failure`), because a failed boot installs no kernel
  state and returning to Rust would idle the image as though it had booted —
  `discard` and `let _ ←` are refused, the arms are parsed so the `.error`
  arm's own body must halt (round 10: a halt in a following `.ok` arm read as
  the error arm's), no diverging statement may precede the handling match, and
  the match must be on the binding the boot produced rather than on a
  rebinding of its name.  The inventory
  it reads includes the library root `SeLe4n.lean` (round 7), and the
  assembly providers are read off the compile's *executed* chain — top-level
  statements of its own function, at brace depth zero, at or before the
  compile — rather than by receiver spelling.  Since round 8 the receiver
  is a **binding instance**, not a name: `rust_code_view.binding_statement_before`
  resolves it to the last top-level `let [mut] <receiver>` — or, since round
  9, `<receiver> = …`, since a `mut` builder is rebound by assignment with no
  second `let` — strictly before the compile statement, `assembled_sources_in` counts `.file()` calls from
  that instance on, the cross gate's build-script check requires the
  instance and refuses a receiver the compile's function does not bind, and
  the archive parsers accept global text (`T`) only
  (`executable_definitions`), since every requirement the gate reconciles
  is an `extern "C" fn` and a data object under the old name would have
  resolved a call into data.
  Since round 12 every one of those names is **resolved** rather than
  matched: the export attribute is parsed from the list
  (`lean_code_view.attribute_arguments`, shared with `build.rs`, so
  `@[inline, export lean_kernel_main]` is the same export on both sides),
  and an `extern` declaration's requirement is its effective linker
  name, `#[link_name = "…"]` included — located on the string-free view
  and read from the aligned kept one (round 17), so an attribute quoted
  in a doc string renames nothing.  The Lean-side name resolution that
  used to sit here — the suffix rule, the binder scan, the halt
  derivation — went with the boot-entry contract to the elaborator at
  round 17.  `build.rs` refuses a `#[link_name]` alias
  outright for a Lean symbol: the readiness derivation reads the Rust
  identifier, so an aliased seam is attributed to no gate at all.
- **The WS-SM theorem total is measured, not summed — and it counts
  propositions, not registrations.**
  `SeLe4n/Kernel/Concurrency/PhaseTheoremManifest.lean` registers one entry per
  phase SM0..SM10, each naming the theorem inventories that phase owns.  Those
  inventories hold **1135 entries**, of which **919 are theorems**: the
  inventories register a phase's whole surface, so 216 entries are `def`s —
  lock-set footprints, PIP chain-start markers, per-core invariant predicates,
  WCRT cost functions — and
  every inventory's construction macro proves only that the name *resolves*,
  never that its type is a `Prop`.  **Quote 919, and quote it as theorems; 1135
  is the entry count.**  A `List.length` cannot tell the two apart, so the
  propositionality census at the end of that module resolves each identifier
  against the environment and fails elaboration on drift.  **Eight of the eleven
  phases register zero theorems**, so only SM2, SM3 and SM5 contribute: six
  (SM1, SM6..SM10) carry no inventory at all, and **SM0 and SM4 carry
  *assumption ledgers*** — `smpLatentInventory` and `smpRetiredInventory` —
  which `smpPhaseTheoremCount` correctly excludes, leaving those two phases'
  own theorems unmeasured just the same.  Building only the six missing
  inventories would therefore not close the gap; the debt is eight phases wide.
  That gap is real, and the honest zero is what makes it visible.  Adding a
  phase without an entry
  fails elaboration; adding an inventory no phase claims fails Tier 0
  (`scripts/generate_smp_theorem_manifest.py --check`).  New code must not
  reintroduce a hand-written per-phase figure.

### Closed workstreams

Every closed workstream is listed in the *Workstream registry* of
[`docs/REGISTERED_DEBT.md`](docs/REGISTERED_DEBT.md) with the versions it
spans; what each one changed is in [`CHANGELOG.md`](CHANGELOG.md) at those
versions.  **WS-RC** closed at v0.31.2 with R6–R14 absorbed into WS-SM per
SM0.Q, and **WS-AN** closed at v0.30.11.

## Workstream planning documents

**Phases and sub-tasks are numbered in the order they are to be
implemented.**  A plan's numbering is its schedule: a reader who works
`RR0, RR1, RR2, …` in order must never violate a dependency, and must never
need a separate note telling them to take a later-numbered phase early.

Concretely:

- **Phase number is execution order.**  If phase 6 has to run second, it is
  phase 1 — renumber it.  A "sequencing note" that contradicts the numbering
  means the numbering is wrong, not that the note is helpful; the plan then
  has to be read twice and will be misread once.
- **Sub-task numbers run sequentially within a phase** (`RR2.1`, `RR2.2`,
  …), in execution order, with no letter groups and no `.0`.  Thematic
  grouping belongs in prose or a column, not in the identifier — a reader
  cannot tell from `RR2.C.3` whether it precedes `RR2.B.1`.
- **No backward dependencies.**  A sub-task may only consume the output of a
  lower-numbered sub-task.  If step 3 needs what step 9 measures, either the
  order is wrong or the two steps belong in the same phase.  State the
  dependency in the row that consumes it, so the constraint is visible where
  it binds.
- **Genuine parallelism is stated, not implied.**  Say which phases may
  overlap and which may never (typically because they edit the same files).
  Absent that statement, sequential execution is the contract.
- **A transition goes live only after the proofs that cover it.**  When one
  sub-task makes a transition reachable — wiring a dispatch arm, flipping a
  seam, repointing a caller at a new base — and another supplies its
  preservation, progress or refinement obligations, the proofs carry the lower
  number, or both land in one sub-task.  This is the numbering rule's
  *semantic* half and the numeric half does not imply it: a plan can be
  perfectly sequential with no backward dependency and still schedule a live
  kernel transition three PRs ahead of its own invariant surface, which is
  precisely the blocker most remediation phases exist to close.  Three
  independent instances of this shipped in one plan (WS-RR phases RR2, RR4 and
  RR5), each caught one review round at a time, because the rule as first
  written checked only that the numbers ascended.  When splitting is
  impossible — the theorems unfold the very function the switch replaces, so
  neither half compiles alone — that is the signal to merge the rows, not to
  order them.

- **Renumbering is cheap before work starts and expensive after.**  Get the
  order right at authoring time; once sub-task IDs appear in commit messages
  and CHANGELOG entries they are effectively frozen.

This applies to every plan under `docs/planning/`, and to the per-phase
tables in `CLAUDE.md`'s status index.

**The structural half is machine-checked.**
`scripts/check_workstream_plan.py` (Tier 0) holds every plan that declares an
exact `Sub-task count` to its own arithmetic: sub-task numbers run 1..N per
phase, the phase map matches the rows, the declared total matches the phase
map, a findings column sums to its acceptance total, no row consumes itself or
a later one, and every `<PREFIX><phase>.<sub>` citation — in the plan and in
`UNFINISHED_SMP_WORK.md`, `REGISTERED_DEBT.md`, `CLAUDE.md` and `AGENTS.md`
— resolves to a real row.  It reads the git index, so it checks what is being
committed rather than what happens to be in the tree.  Legacy letter-group
plans (`SM6.A.1`) and plans declaring an estimate range are reported but not
held to flat numbering; closed workstreams are not renumbered.

What it deliberately does **not** check is whether a reference that resolves
still *means* what it did before a renumber, and it cannot see the semantic
ordering rule above.  Those stay a reader's job — which is why the rule is
stated, not merely gated.

## PR checklist

- [ ] Workstream ID identified
- [ ] Scope is one coherent slice
- [ ] Transitions are explicit and deterministic
- [ ] Invariant/theorem updates paired with implementation
- [ ] Module build verified (pre-commit hook installed and not
      bypassed)
- [ ] `test_smoke.sh` passes (minimum); `test_full.sh` for theorem
      changes
- [ ] Documentation synchronized (see "Documentation rules")
- [ ] Patch version bumped and all version locations synced
      (`./scripts/bump_version.sh <version>`; verified by
      `scripts/check_version_sync.sh`) + `CHANGELOG.md` entry added
      (see "Versioning policy")
- [ ] No website-linked paths renamed or removed (see
      `scripts/website_link_manifest.txt`)
- [ ] No `claude.ai/code/session_*` URL in commit messages or PR
      title/body/summary (see "Session URL hygiene" below)

## Session URL hygiene

When this codebase is edited from inside the Claude Agent SDK / Claude
Code on the web, the runtime exposes a per-session URL of the form
`https://claude.ai/code/session_<id>`. **This URL must never appear in
any artifact that ships to the public repository or to GitHub.**

**Forbidden locations:**

1. PR titles, descriptions, summaries, or any update to a PR body.
2. Commit messages — subject, body, footers, `Refs:` lines, and
   `Co-Authored-By` trailers. Once pushed, commit metadata is
   effectively unrewritable.
3. In-tree documentation, `CHANGELOG.md` entries, source comments,
   docstrings, or test fixtures.
4. GitHub issue bodies, issue comments, PR review bodies, PR review
   comments, or any other rendered text posted via GitHub MCP tools
   (`mcp__github__add_issue_comment`,
   `mcp__github__pull_request_review_write`,
   `mcp__github__create_pull_request`,
   `mcp__github__update_pull_request`, etc.).
5. Plan files or task descriptions checked into the repo
   (e.g. `docs/planning/*.md`, `docs/audits/*.md`).

**Why**: session URLs are unstable (rotate or expire without notice),
opaque to anyone outside the original session (no audit value), and
displace useful cross-references. Internal handles do not belong in
shared artifacts. Per the minimum-disclosure norm, the URL gives a
reviewer nothing they can act on.

**Use instead** — cite the canonical document or identifier:

```
Refs: docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md §8 (Phase R4)
Refs: docs/REGISTERED_DEBT.md WS-RC R3 closeout
Refs: #761                            # related GitHub PR or issue
Refs: 7da2572                         # related commit SHA
```

A commit message or PR body should typically include exactly one
`Refs:` line pointing at the most-specific canonical document.
Multiple `Refs:` lines are acceptable when the change touches several
closure cites.

**Remediation when a session URL has already been published:**

- **Local commit not yet pushed**: amend (`git commit --amend`) and
  push.
- **Pushed commit (any branch)**: do **not** force-push to scrub it.
  Treat it as a one-time leak; ensure subsequent commits comply.
- **PR title/body or issue/review comment**: edit via the GitHub UI
  or `mcp__github__update_pull_request` — these are freely editable.

This rule applies regardless of who or what added the URL — the agent
itself, a hook or GitHub Action, a copy-paste, or a checked-in plan
that gets quoted later. If any in-repo template appears to instruct
including a session URL, treat the example as obsolete and update that
template in the same PR.

## Vulnerability reporting

While executing any task in this codebase, if you discover a possible
software vulnerability that could reasonably warrant a CVE designation,
you **must** immediately report it to the user before continuing. This
applies to vulnerabilities found in:

- **Project code** — logic errors in transition semantics, capability
  checks, information-flow enforcement, or any component that could
  lead to privilege escalation, information leakage, denial of
  service, or violation of security invariants.
- **Dependencies and toolchain** — known or suspected vulnerabilities
  in Lean, Lake, elan, or any vendored/imported library encountered
  during builds, updates, or code review.
- **Build and CI infrastructure** — insecure patterns (command
  injection in shell scripts, unsafe file permissions, unvalidated
  inputs in test harnesses) that could be exploited in a development
  or CI environment.
- **Model/specification gaps** — cases where the formal model fails
  to capture a security-relevant behavior of the real seL4 kernel,
  creating a false assurance gap that could mask a real-world
  vulnerability.

**What to report:**

1. **Summary** — concise description of the vulnerability.
2. **Location** — file path(s) and line number(s).
3. **Severity estimate** — Critical / High / Medium / Low + your
   exploitability assessment.
4. **Reproduction or evidence** — how the issue manifests or could be
   triggered.
5. **Suggested remediation** — if apparent.

**How to report:**

- Stop current work and surface the finding in your response
  immediately.
- Do **not** silently fix a CVE-worthy vulnerability — always flag it
  explicitly so it can be tracked, triaged, and disclosed
  appropriately.
- If the vulnerability is in a third-party dependency, note whether an
  upstream advisory already exists.

This requirement applies regardless of whether the vulnerability is
directly related to the current task. Vigilance during routine work is
one of the most effective ways to catch security issues early.
