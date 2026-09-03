# AGENTS.md — seLe4n project guidance

> This file mirrors `CLAUDE.md` so that non-Claude coding agents (and any
> tool that follows the AGENTS.md convention) get the same project rules.
> If you edit one, edit the other in the same PR — the two files must
> stay byte-identical apart from this header.

## What this project is

seLe4n is a production-oriented microkernel written in Lean 4 with machine-checked
proofs, improving on seL4 architecture. Every kernel transition is an executable
pure function with zero `sorry`/`axiom`. First hardware target: Raspberry Pi 5.
Lean 4.28.0 toolchain, Lake build system, version 0.34.48.

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
SeLe4n/Kernel/FrozenOps/         Frozen-state kernel operations (experimental)
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
- `CHANGELOG.md` (~50963 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/DualQueueMembership.lean` (~22582 lines)
- `tests/SmpInformationFlowSuite.lean` (~11772 lines)
- `SeLe4n/Kernel/Concurrency/Locks/RwLock.lean` (~7902 lines)
- `SeLe4n/Kernel/API.lean` (~6841 lines)
- `SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean` (~5738 lines)
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean` (~5186 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~5127 lines)
- `SeLe4n/Kernel/IPC/Invariant/DispatchArmPreservation.lean` (~4997 lines)
- `SeLe4n/Platform/Boot.lean` (~4778 lines)
- `SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuite.lean` (~4750 lines)
- `docs/dev_history/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md` (~4721 lines)
- `SeLe4n/Model/State.lean` (~4503 lines)
- `docs/spec/SELE4N_SPEC.md` (~4337 lines)
- `docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md` (~4130 lines)
- `tests/NegativeStateSuite.lean` (~4115 lines)
- `SeLe4n/Kernel/InformationFlow/FineLockFlow.lean` (~3924 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` (~3919 lines)
- `SeLe4n/Kernel/InformationFlow/AuditRead.lean` (~3788 lines)
- `SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean` (~3456 lines)
- `SeLe4n/Kernel/CrossSubsystem.lean` (~3407 lines)
- `docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md` (~3388 lines)
- `tests/SmpTlbShootdownSuite.lean` (~3354 lines)
- `tests/OperationChainSuite.lean` (~3290 lines)
- `SeLe4n/Testing/MainTraceHarness.lean` (~3216 lines)
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` (~3210 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean` (~3159 lines)
- `docs/dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md` (~3140 lines)
- `docs/dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md` (~3134 lines)
- `SeLe4n/Model/Object/Structures.lean` (~3116 lines)
- `SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean` (~3087 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointCallInvariant.lean` (~2993 lines)
- `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean` (~2948 lines)
- `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean` (~2844 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/StoreObjectFrame.lean` (~2784 lines)
- `SeLe4n/Kernel/IPC/Invariant/DispatchPayoff.lean` (~2755 lines)
- `SeLe4n/Platform/FFI.lean` (~2741 lines)
- `SeLe4n/Kernel/Capability/Operations.lean` (~2674 lines)
- `SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean` (~2639 lines)
- `SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean` (~2637 lines)
- `SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean` (~2602 lines)
- `SeLe4n/Kernel/Architecture/TlbShootdown.lean` (~2562 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/PerOperation.lean` (~2542 lines)
- `SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean` (~2505 lines)
- `tests/ModelIntegritySuite.lean` (~2477 lines)
- `docs/dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md` (~2476 lines)
- `docs/dev_history/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md` (~2472 lines)
- `SeLe4n/Kernel/InformationFlow/TaintPropagation.lean` (~2382 lines)
- `docs/dev_history/audits/AUDIT_v0.25.14_WORKSTREAM_PLAN.md` (~2340 lines)
- `docs/dev_history/audits/AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md` (~2339 lines)
- `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` (~2325 lines)
- `docs/audits/AUDIT_v0.30.11_DEEP_VERIFICATION.md` (~2325 lines)
- `SeLe4n/Kernel/IPC/Invariant/QueueNextBlocking.lean` (~2290 lines)
- `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean` (~2287 lines)
- `SeLe4n/Model/Object/Types.lean` (~2264 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreChooseThread.lean` (~2243 lines)
- `SeLe4n/Prelude.lean` (~2137 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Core.lean` (~2099 lines)
- `SeLe4n/Kernel/IPC/Invariant/QueueMembership.lean` (~2079 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/QueueNextTransport.lean` (~2074 lines)
- `SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean` (~2059 lines)
- `SeLe4n/Kernel/Scheduler/PriorityInheritance/PerCore.lean` (~2042 lines)
- `SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean` (~2034 lines)
- `SeLe4n/Kernel/Architecture/Invariant.lean` (~2033 lines)
- `SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean` (~1967 lines)
- `docs/dev_history/planning/V3_PROOF_CHAIN_HARDENING_E_G6_PLAN.md` (~1966 lines)
- `SeLe4n/Kernel/InformationFlow/Policy.lean` (~1924 lines)
- `docs/dev_history/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md` (~1917 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreWake.lean` (~1909 lines)
- `SeLe4n/Kernel/Concurrency/Locks/TicketLock.lean` (~1901 lines)
- `docs/dev_history/planning/V3E_IPC_UNWRAP_CAPS_LOOP_COMPOSITION_PLAN.md` (~1891 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreCbs.lean` (~1890 lines)
- `docs/dev_history/audits/AUDIT_v0.30.6_COMPREHENSIVE.md` (~1889 lines)
- `tests/InformationFlowSuite.lean` (~1871 lines)
- `SeLe4n/Kernel/Concurrency/Locks/Serializability.lean` (~1859 lines)
- `SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean` (~1833 lines)
- `SeLe4n/Model/FreezeProofs.lean` (~1827 lines)
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` (~1822 lines)
- `SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean` (~1822 lines)
- `docs/dev_history/audits/AUDIT_v0.27.6_WORKSTREAM_PLAN.md` (~1801 lines)
- `docs/dev_history/audits/AUDIT_v0.25.21_WORKSTREAM_PLAN.md` (~1800 lines)
- `SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean` (~1794 lines)
- `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` (~1778 lines)
- `docs/dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md` (~1776 lines)
- `SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean` (~1746 lines)
- `docs/dev_history/audits/AUDIT_v0.25.14_COMPREHENSIVE.md` (~1739 lines)
- `docs/dev_history/audits/WORKSTREAM_PLAN_WS_O_SYSCALL_RUST_WRAPPERS.md` (~1725 lines)
- `docs/planning/UNFINISHED_SMP_WORK.md` (~1723 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyInvariant.lean` (~1709 lines)
- `docs/dev_history/AUDIT_v0.22.10_WORKSTREAM_PLAN.md` (~1674 lines)
- `tests/FaultHandlingSuite.lean` (~1660 lines)
- `tests/SmpIpcSuite.lean` (~1660 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` (~1508 lines)
- `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean` (~1491 lines)
- `SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean` (~1488 lines)
- `SeLe4n/Kernel/Architecture/SyscallReturn.lean` (~1485 lines)
- `docs/dev_history/audits/AUDIT_v0.28.0_WORKSTREAM_PLAN.md` (~1480 lines)
- `docs/dev_history/planning/V3B_LOAD_FACTOR_BOUNDED_MIGRATION_PLAN.md` (~1457 lines)
- `docs/dev_history/audits/AUDIT_v0.25.3_WORKSTREAM_PLAN.md` (~1452 lines)
- `SeLe4n/Kernel/FrozenOps/Operations.lean` (~1425 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreSwitchToThread.lean` (~1423 lines)
- `docs/dev_history/audits/WS_RC_R5_DEFERRED_COMPLETION_PLAN.md` (~1414 lines)
- `docs/dev_history/AUDIT_v0.23.21_WORKSTREAM_PLAN.md` (~1411 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean` (~1394 lines)
- `SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean` (~1393 lines)
- `docs/dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md` (~1382 lines)
- `tests/SyscallDispatchSuite.lean` (~1381 lines)
- `tests/LockSetSuite.lean` (~1377 lines)
- `docs/planning/SMP_DECLASSIFICATION_COMPLETION_PLAN.md` (~1370 lines)
- `docs/dev_history/audits/AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md` (~1357 lines)
- `docs/dev_history/audits/AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md` (~1342 lines)
- `docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md` (~1331 lines)
- `SeLe4n/Kernel/IPC/Invariant/LookupCongruence.lean` (~1326 lines)
- `tests/FrozenOpsSuite.lean` (~1324 lines)
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean` (~1317 lines)
- `SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean` (~1296 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` (~1291 lines)
- `SeLe4n/Kernel/InformationFlow/Taint.lean` (~1261 lines)
- `docs/dev_history/audits/AUDIT_v0.22.17_WORKSTREAM_PLAN.md` (~1252 lines)
- `tests/SmpCancellationSuite.lean` (~1246 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreDomain.lean` (~1241 lines)
- `docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md` (~1238 lines)
- `SeLe4n/Kernel/IPC/Operations/Donation/Primitives.lean` (~1235 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean` (~1233 lines)
- `SeLe4n/Kernel/Scheduler/Invariant.lean` (~1216 lines)
- `SeLe4n/Kernel/Scheduler/Invariant/PerCorePreservation.lean` (~1200 lines)
- `tests/SmpSurfaceAnchors.lean` (~1195 lines)
- `SeLe4n/Kernel/Concurrency/Locks/DynamicChainExtension.lean` (~1186 lines)
- `docs/dev_history/audits/AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md` (~1178 lines)
- `tests/SmpCacheMaintenanceSuite.lean` (~1170 lines)
- `SeLe4n/Kernel/RobinHood/Bridge.lean` (~1169 lines)
- `SeLe4n/Kernel/Scheduler/RunQueue.lean` (~1168 lines)
- `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean` (~1165 lines)
- `SeLe4n/Platform/DeviceTree.lean` (~1154 lines)
- `SeLe4n/Platform/RPi5/MmioAdapter.lean` (~1154 lines)
- `tests/KernelErrorMatrixSuite.lean` (~1154 lines)
- `SeLe4n/Kernel/Architecture/VSpace.lean` (~1142 lines)
- `SeLe4n/Machine.lean` (~1105 lines)
- `tests/PerObjectLockSuite.lean` (~1104 lines)
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean` (~1085 lines)
- `SeLe4n/Kernel/Lifecycle/Suspend.lean` (~1076 lines)
- `docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md` (~1071 lines)
- `tests/SyscallReturnAbiSuite.lean` (~1068 lines)
- `SeLe4n/Kernel/IPC/DualQueue/Core.lean` (~1046 lines)
- `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean` (~1043 lines)
- `SeLe4n/Kernel/InformationFlow/Projection.lean` (~1030 lines)
- `SeLe4n/Model/FrozenState.lean` (~1007 lines)
- `SeLe4n/Kernel/IPC/Operations/SchedulerLemmas.lean` (~998 lines)
- `SeLe4n/Kernel/IPC/Operations/CapTransfer.lean` (~995 lines)
- `docs/dev_history/audits/AUDIT_v0.19.6_WORKSTREAM_PLAN.md` (~984 lines)
- `docs/planning/SMP_RELEASE_READINESS_PLAN.md` (~971 lines)
- `docs/planning/SMP_PER_CORE_STATE_PLAN.md` (~968 lines)
- `tests/SmpFoundationsSuite.lean` (~965 lines)
- `docs/dev_history/planning/WS_X_LEAN_ETHEREUM_FORMALIZATION_PLAN.md` (~958 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointCall.lean` (~950 lines)
- `SeLe4n/Kernel/Concurrency/Locks/RwLockRefinement.lean` (~943 lines)
- `SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean` (~942 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreTickCbsPreservation.lean` (~941 lines)
- `SeLe4n/Kernel/Concurrency/MemoryModel.lean` (~935 lines)
- `SeLe4n/Kernel/InformationFlow/Declassification.lean` (~935 lines)
- `docs/dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md` (~930 lines)
- `docs/planning/SMP_TLB_SHOOTDOWN_PLAN.md` (~924 lines)
- `docs/dev_history/audits/AUDIT_v0.28.0_COMPREHENSIVE.md` (~921 lines)
- `tests/SmpCbsSuite.lean` (~919 lines)
- `docs/dev_history/audits/AUDIT_H3_HARDWARE_BINDING_v0.25.27.md` (~911 lines)
- `docs/dev_history/audits/AUDIT_v0.25.10_WORKSTREAM_PLAN.md` (~909 lines)
- `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/Signal.lean` (~891 lines)
- `docs/dev_history/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md` (~884 lines)
- `SeLe4n/Kernel/IPC/CrossCore/NotificationSignal.lean` (~877 lines)
- `SeLe4n/Kernel/IPC/Operations/Fault.lean` (~868 lines)
- `docs/dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md` (~859 lines)
- `docs/planning/SMP_RUST_HAL_PLAN.md` (~848 lines)
- `tests/SmpTimerSuite.lean` (~840 lines)
- `tests/DecodingSuite.lean` (~833 lines)
- `tests/SmpCrossCoreCallSuite.lean` (~833 lines)
- `SeLe4n/Kernel/SyscallDispatchEntry.lean` (~830 lines)
- `SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean` (~824 lines)
- `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` (~823 lines)
- `docs/dev_history/audits/WS_RC_R4_CLOSEOUT_PLAN.md` (~818 lines)
- `SeLe4n/Kernel/SchedContext/BindingAffinity.lean` (~816 lines)
- `SeLe4n/Kernel/InformationFlow/AuditRecord.lean` (~811 lines)
- `tests/WithLockSetSuite.lean` (~809 lines)
- `docs/dev_history/AUDIT_v0.21.7_WORKSTREAM_PLAN.md` (~808 lines)
- `docs/dev_history/audits/AUDIT_CODEBASE_v0.11.6.md` (~806 lines)
- `docs/planning/SYSCALL_RETURN_ABI_PLAN.md` (~800 lines)
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
  `check_identifier_naming.py` so a `$( … )` body is lexed rather than copied.  The rule is unchanged and now has a mechanism:
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

What remains is owed to SM10.1: return-frame *delivery* at the context restore,
and the cancellation/timeout error-frame staging.  Until that seam flips, a
blocked caller's frame is poisoned with the fail-closed
`blocked_resume_sentinel_regs()` so a stale request register can never decode as
a success.  A caller that took a fault at the seam is outcome tag 2
(`.faulted`) and is never poisoned-and-resumed: the core halts pending SM10.1
(PR #887 review round 5).

Plan: [`docs/planning/SYSCALL_RETURN_ABI_PLAN.md`](docs/planning/SYSCALL_RETURN_ABI_PLAN.md).

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
| SM2 | LANDED | v0.31.9 | Memory model, TicketLock, RwLock, FFI bridge, refinement |
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
| WS-RR | IN FLIGHT | RR0 v0.34.26; RR1 v0.34.41; RR2 v0.34.42; RR3 v0.34.43; RR4 v0.34.44; RR5 v0.34.48 | Pre-SM10 remediation: the audit's 3 blockers, 11 security findings, fault IPC, de-threading closure, lock completion (187 subs across RR0..RR8) |
| SM10 | BLOCKED on WS-RR | — | Release closure (→ v1.0.0) |

**Plans**: master overview at
[`docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md`](docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md);
per-phase plans at `docs/planning/SMP_*.md`.

### Standing constraints and registered debt

These are *current facts about the tree*, not history — they change what new
code may assume:

- **Kernel entry is serialised by one global ticket lock** (SM5.I, v0.32.142,
  `rust/sele4n-hal/src/kernel_entry.rs`), acquired outside
  `SHOOTDOWN_ROUND_LOCK` and self-servicing pending shootdowns while spinning.
  It brackets all five state-committing entries (syscall dispatch, per-core
  timer tick, `.reschedule` SGI receiver, secondary bring-up entry, cross-core
  suspend); the primary's `lean_kernel_main` boot install remains outside and
  its ordering is an SM10.1 obligation (see kernel_entry.rs module docs).
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
  write is refused.
  Live WCRT is therefore weaker
  than `PerCoreWcrt.lean`'s fine-lock bound, which remains a statement about the
  intended discipline.
- **SM3.C.9 is deferred**: the `@[export]` bodies are, with one exception, not
  yet wrapped in `withLockSet`, so the per-object fine locks are a model-level
  discipline.  The exception is the `.tcbSuspend` arm of
  `syscallDispatchCrossCoreEntry` (`SeLe4n/Kernel/SyscallDispatchEntry.lean`),
  which resolves `lockSetForSyscall` and brackets its action — it is the one
  arm `lockSetForSyscall` answers `some` for; the other 32 answer `none`.  The
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
- **`ipcInvariantFull` has its dispatch payoff — three theorems, under
  stated packs and confinements.**  The whole bundle family is de-threaded:
  the RR3.1 gate (`scripts/check_ipc_invariant_dethreading.py`, Tier 0)
  reports **zero** conjuncts bound on a post-state across all **146**
  `*_preserves_ipcInvariantFull*` / `*_establishes_ipcInvariantFull*`
  statements, measured over the comment-free code view with the conjunct set,
  the bundle family and each bundle's own pre-state all *derived* rather than
  listed, and prints `[PASS] ipcInvariantFull is de-threaded end to end`;
  `docs/planning/ipc_dethreading_pending.txt` carries zero registrations and
  the gate holds that register in both directions.  The payoff tier (WS-RR
  RR3.15–RR3.26, v0.34.43): `dispatchCapabilityOnly_preserves_ipcInvariantFull`
  (`SeLe4n/Kernel/API.lean`, **production**) covers every capability-gated arm
  under the pre-state pack `capabilityDispatchQuiescence`, composing the
  production per-arm layer
  `SeLe4n/Kernel/IPC/Invariant/DispatchArmPreservation.lean`;
  `dispatchWithCap_preserves_ipcInvariantFull` and
  `dispatchSyscall_preserves_ipcInvariantFull`
  (`SeLe4n/Kernel/IPC/Invariant/DispatchPayoff.lean`) extend it over the IPC
  fall-through arms and the lookup/taint prologue under
  `syscallDispatchQuiescence` — **staged**, because the `.call` arm composes
  the staged `EndpointCallInvariant` surface (see the call-chain bullet
  below); they relocate to production when that surface promotes.  The
  flow-checked tier is covered too:
  `dispatchWithCapChecked_preserves_ipcInvariantFull` and
  `dispatchSyscallChecked_preserves_ipcInvariantFull` (same module, staged)
  reduce every mirrored arm to the unchecked payoff — machine-checking the
  dispatcher's "mirrors the unchecked arm" comments — and close the four
  live SM9 arms from their transitions' frames, under
  `checkedSyscallDispatchQuiescence` (the base pack plus the declassifying
  signal's unbound-delivery confinement).  Both packs carry inhabitation
  witnesses built through the retype and binding levers — the base pair
  (`syscallDispatchQuiescence_inhabited`,
  `checkedSyscallDispatchQuiescence_inhabited`) for the state-shaped fields,
  plus a per-arm family (`…_inhabited_signal` / `…_retype` / `…_send` /
  `…_receive` / `…_call` / `…_mint` / `…_reply` / `…_bind` / `…_unbind` /
  `…_suspend` / `checked…_inhabited_declassifySignal`, `DispatchPayoff` §7b)
  that fires
  each *indexed* field's premises — so an unsatisfiable pack field cannot
  hide; the two interiors beyond the levers' reach (a caller-carrying
  reply, a CSpace-resolved `replyRecv` capability — both created only by
  the call rendezvous) are registered WS-DT debt.  What new
  code must respect: (1) the payoff holds *under the packs* — every field is
  a pre-state fact, dischargeable before the step, with the state-shaped ones
  collected in `SeLe4n/Kernel/IPC/Invariant/Reachability.lean`
  (`ipcReachable`, boot-inhabited by `ipcReachable_default`) — so a caller
  supplies the pack rather than citing the theorem bare; (2) the stated
  confinements: `.notificationSignal` is covered on the unbound-delivery path
  only (SM6.D's registered debt), the `.replyRecv` composite excludes a live
  donation edge naming the woken caller (the AUD-3 window), and the retype
  and suspend arms demand their quiescence packs (`retypeTargetDetached`,
  `threadIpcFieldsQuiescent` — revoke, suspend and cancel *before* retype or
  suspend); (3) production code must not cite the two staged payoffs.  The
  operation-hardening and relocation residuals are registered as debt under
  **WS-DT — CLOSED** in
  [`docs/REGISTERED_DEBT.md`](docs/REGISTERED_DEBT.md) (plan retired to
  [`docs/dev_history/planning/IPC_INVARIANT_DETHREADING_PLAN.md`](docs/dev_history/planning/IPC_INVARIANT_DETHREADING_PLAN.md));
  RR8.3 retires this bullet.
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
  (`IPC/Invariant/DispatchArmPreservation.lean`, production).  What no
  transition-level bundle covers yet: `notificationSignalBoundOnCore`
  (SM6.D's registered bound-delivery debt) — the flow-`Checked` dispatch
  wrappers gained their own payoff tier
  (`dispatchWithCapChecked_preserves_ipcInvariantFull` /
  `dispatchSyscallChecked_preserves_ipcInvariantFull`, staged) in the same
  cut.
- **Every SchedContext hand-off must migrate the replenish queue.**  The CBS
  replenishments of a SchedContext live on its *bound thread's* home core
  (`replenishQueueAffinityConsistentOnCore`, SM5.H), so any transition that
  rebinds `boundThread` across cores must call `migrateSchedContextReplenishment`
  or the invariant is false from the instant it commits.  Three live paths do
  (`applyCallDonationOnCore`, `applyReplyDonationOnCore`, `replyRecvReturnDonation`,
  all at v0.34.42), each with a `replenishQueueAffinityConsistent_smp` preservation
  theorem.  The pre-SM10 audit found only two of the three, because it enumerated
  the donation *primitives* and `.replyRecv` composes them from the API layer —
  the enumeration-versus-derivation shape the key-conventions section above warns
  about.  A same-core hand-off is a definitional no-op
  (`migrateSchedContextReplenishment_noop`), so the migration costs nothing where
  it is not needed and there is no reason to omit it.
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
  had counted as live) — and the HAL's `lean_`-prefixed
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
  is the pin the derivation must reproduce, and the **one** upcall that runs
  ungated — the primary's `lean_kernel_main` boot install, which cannot sit
  behind the gate because it is the call that initializes the runtime the gate
  stands for — is `LEAN_UPCALLS_OUTSIDE_THE_GATE`, with its occurrence count
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
  unreachable (`bootAndInitialisePlatform_eq_checked_boot`).  **The declared
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
  `allCores`.  So `∀ c, idleThreadEnqueuedOnCore st c` holds of the live boot
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
  `.Inactive` only — stated as `threadInactiveFlagConsistent`, proved of the
  boot state (`…_threadInactiveFlagConsistent`), and owed across the scheduler
  and IPC surfaces as registered debt (RR7.36).  New code must not cite
  `threadStateConsistent` of a post-dispatch state.
  The idle slots are **reserved** by `PlatformConfig.wellFormed`
  (`idleSlotsReserved`: no `initialObjects` entry and no boot VSpace root in
  `[idleThreadIdBase, idleThreadIdBase + numCores)`), so a successful checked
  boot is fresh (`bootFromPlatformChecked_ok_idleSlotsFreshAt`) and the idle
  fold provably overwrites nothing without a freshness hypothesis — before,
  an accepted config object at an idle id was silently replaced by the fold.
  The reservation also covers every object a config entry *references*
  (`bootObjectReferencesReservedIdleSlot`, total over `KernelObject` and over
  every field that can hold an object, thread or scheduling-context id — a
  notification's `boundTCB` and an untyped's `children` and `parent`
  included, PR #889 review rounds 2, 4 and 6; a VSpace root holds none), and
  a config that fails it is refused with its own
  diagnostic rather than as a duplicate id.  Beyond the config, the idle
  objects are unreachable by user authority at all: `syscallResolveCap` — the
  one resolution every invoked capability passes through — refuses a
  capability naming a reserved idle object (`capTargetsReservedIdleObject`,
  `syscallResolveCap_ok_not_reserved`), so a boot CNode or a transfer that
  carried one yields a slot that resolves like an empty one and no
  `.tcbSuspend` can remove a core's only guaranteed runnable thread.
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
  hypothesis; the staged dispatch payoff states that hypothesis as the pack
  field `replyNoPendingFault` and the fault branch's composition into it is
  registered WS-RR debt.  **`.replyRecv` does not route through the seam yet**
  — `replyRecvBody` fuses a reply leg, a receive leg and a donation return, and
  a fault reply changes what the latter two are handed — so a handler must
  answer a fault with `.reply` and take its next request separately; that is
  registered debt too, and new code must not assume `.replyRecv` retires a
  fault.  (4) `IpcMessage.label` is set by kernel-originated messages only —
  a user send leaves it at `0` — because carrying a user's label would let a
  thread holding a send capability to a fault endpoint mint a message bearing a
  `seL4_Fault_tag`.  Restoring seL4's sender-side label pass-through needs its
  own authority story and is registered debt.  (5) The handler capability is
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
- **Registered uncovered lock domains** are enumerated in Lean, not in prose:
  `UncoveredLockDomain` (`InformationFlow/FineLockFlow.lean`) names each gap and
  its owner, and its completeness theorem forces a new domain to be registered.
- **Staged modules**: 62 staged-only, listed in
  `scripts/staged_module_allowlist.txt` and gated by
  `scripts/check_production_staging_partition.sh`.  Production must not import
  staged.  WS-RR RR5.15 promoted five (the three state-committing kernel
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
  `EXPECTED_UNRESOLVED` entry (`lean_kernel_main`, until SM10.1 writes it; an
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
  The gate also holds the boot entry to the checked platform boot from the day
  it exists: whichever Lean declaration carries `@[export lean_kernel_main]`
  must **execute** `bootAndInitialisePlatform` as a top-level statement of its
  body (bound with `←`, a `match` scrutinee, a bare call or `discard`, with no
  `return`/`throw` above it) and reference **no other kernel-state installer**
  — the installers derived by closing "names `kernelStateRef` /
  `kernelLabelingContextRef` for anything but `.get`" under reference across
  the Lean tree, pinned against the real tree — over the comment-free,
  string-free view (`boot_entry_binding_failures`, `kernel_state_writers`;
  round 3 accepted an identifier occurrence, which a string literal, an unrun
  `let … :=` binding, a dead branch and a call executed then routed around all
  satisfy — round 5) — vacuous until SM10.1 writes the entry, decisive after,
  so the idle-thread, labeling and reservation guarantees cannot be bypassed
  by an entry that boots through `bootFromPlatform` directly.
- **The WS-SM theorem total is measured, not summed — and it counts
  propositions, not registrations.**
  `SeLe4n/Kernel/Concurrency/PhaseTheoremManifest.lean` registers one entry per
  phase SM0..SM10, each naming the theorem inventories that phase owns.  Those
  inventories hold **1113 entries**, of which **903 are theorems**: the
  inventories register a phase's whole surface, so 210 entries are `def`s —
  lock-set footprints, per-core invariant predicates, WCRT cost functions — and
  every inventory's construction macro proves only that the name *resolves*,
  never that its type is a `Prop`.  **Quote 903, and quote it as theorems; 1113
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
