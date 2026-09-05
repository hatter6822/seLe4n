# CLAUDE.md — seLe4n project guidance

> A mirror of this file lives at `AGENTS.md` so that non-Claude coding
> agents (and any tool that follows the AGENTS.md convention) get the
> same project rules. If you edit one, edit the other in the same PR —
> the two files must stay byte-identical apart from this header.

## What this project is

seLe4n is a production-oriented microkernel written in Lean 4 with machine-checked
proofs, improving on seL4 architecture. Every kernel transition is an executable
pure function with zero `sorry`/`axiom`. First hardware target: Raspberry Pi 5.
Lean 4.28.0 toolchain, Lake build system, version 0.34.55.

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
- `CHANGELOG.md` (~53342 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/DualQueueMembership.lean` (~22582 lines)
- `tests/SmpInformationFlowSuite.lean` (~11797 lines)
- `SeLe4n/Kernel/Concurrency/Locks/RwLock.lean` (~9161 lines)
- `SeLe4n/Kernel/API.lean` (~6926 lines)
- `SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean` (~5742 lines)
- `SeLe4n/Platform/Boot.lean` (~5724 lines)
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean` (~5186 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~5130 lines)
- `SeLe4n/Kernel/IPC/Invariant/DispatchArmPreservation.lean` (~5001 lines)
- `SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuite.lean` (~4750 lines)
- `docs/dev_history/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md` (~4721 lines)
- `docs/spec/SELE4N_SPEC.md` (~4687 lines)
- `SeLe4n/Model/State.lean` (~4503 lines)
- `docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md` (~4130 lines)
- `SeLe4n/Kernel/InformationFlow/FineLockFlow.lean` (~4126 lines)
- `tests/NegativeStateSuite.lean` (~4115 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` (~3919 lines)
- `SeLe4n/Kernel/InformationFlow/AuditRead.lean` (~3788 lines)
- `SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean` (~3456 lines)
- `SeLe4n/Kernel/CrossSubsystem.lean` (~3407 lines)
- `docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md` (~3388 lines)
- `tests/SmpTlbShootdownSuite.lean` (~3354 lines)
- `tests/OperationChainSuite.lean` (~3290 lines)
- `SeLe4n/Kernel/Concurrency/Locks/QueuedRwLockRefinement.lean` (~3270 lines)
- `SeLe4n/Testing/MainTraceHarness.lean` (~3216 lines)
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` (~3210 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean` (~3159 lines)
- `docs/dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md` (~3140 lines)
- `docs/dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md` (~3134 lines)
- `SeLe4n/Model/Object/Structures.lean` (~3116 lines)
- `SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean` (~3105 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointCallInvariant.lean` (~2994 lines)
- `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean` (~2939 lines)
- `SeLe4n/Platform/FFI.lean` (~2930 lines)
- `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean` (~2844 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/StoreObjectFrame.lean` (~2784 lines)
- `SeLe4n/Kernel/IPC/Invariant/DispatchPayoff.lean` (~2755 lines)
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
- `SeLe4n/Model/Object/Types.lean` (~2266 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreChooseThread.lean` (~2243 lines)
- `SeLe4n/Prelude.lean` (~2137 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Core.lean` (~2112 lines)
- `SeLe4n/Kernel/IPC/Invariant/QueueMembership.lean` (~2079 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/QueueNextTransport.lean` (~2074 lines)
- `SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean` (~2059 lines)
- `SeLe4n/Kernel/Scheduler/PriorityInheritance/PerCore.lean` (~2042 lines)
- `SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean` (~2034 lines)
- `SeLe4n/Kernel/Architecture/Invariant.lean` (~2033 lines)
- `SeLe4n/Kernel/InformationFlow/Policy.lean` (~2028 lines)
- `SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean` (~1967 lines)
- `docs/dev_history/planning/V3_PROOF_CHAIN_HARDENING_E_G6_PLAN.md` (~1966 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreCbs.lean` (~1946 lines)
- `docs/dev_history/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md` (~1917 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreWake.lean` (~1909 lines)
- `SeLe4n/Kernel/Concurrency/Locks/TicketLock.lean` (~1901 lines)
- `docs/dev_history/planning/V3E_IPC_UNWRAP_CAPS_LOOP_COMPOSITION_PLAN.md` (~1891 lines)
- `docs/dev_history/audits/AUDIT_v0.30.6_COMPREHENSIVE.md` (~1889 lines)
- `tests/InformationFlowSuite.lean` (~1885 lines)
- `SeLe4n/Kernel/Concurrency/Locks/Serializability.lean` (~1878 lines)
- `SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean` (~1833 lines)
- `SeLe4n/Model/FreezeProofs.lean` (~1827 lines)
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` (~1822 lines)
- `SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean` (~1822 lines)
- `docs/dev_history/audits/AUDIT_v0.27.6_WORKSTREAM_PLAN.md` (~1801 lines)
- `docs/dev_history/audits/AUDIT_v0.25.21_WORKSTREAM_PLAN.md` (~1800 lines)
- `SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean` (~1794 lines)
- `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` (~1778 lines)
- `docs/planning/UNFINISHED_SMP_WORK.md` (~1778 lines)
- `docs/dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md` (~1776 lines)
- `SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean` (~1746 lines)
- `docs/dev_history/audits/AUDIT_v0.25.14_COMPREHENSIVE.md` (~1739 lines)
- `docs/dev_history/audits/WORKSTREAM_PLAN_WS_O_SYSCALL_RUST_WRAPPERS.md` (~1725 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyInvariant.lean` (~1709 lines)
- `docs/dev_history/AUDIT_v0.22.10_WORKSTREAM_PLAN.md` (~1674 lines)
- `tests/FaultHandlingSuite.lean` (~1660 lines)
- `tests/SmpIpcSuite.lean` (~1660 lines)
- `tests/SyscallDispatchSuite.lean` (~1645 lines)
- `SeLe4n/Kernel/Concurrency/Locks/RwLockRefinement.lean` (~1620 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` (~1508 lines)
- `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean` (~1491 lines)
- `SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean` (~1488 lines)
- `SeLe4n/Kernel/Architecture/SyscallReturn.lean` (~1485 lines)
- `docs/dev_history/audits/AUDIT_v0.28.0_WORKSTREAM_PLAN.md` (~1480 lines)
- `docs/dev_history/planning/V3B_LOAD_FACTOR_BOUNDED_MIGRATION_PLAN.md` (~1457 lines)
- `docs/dev_history/audits/AUDIT_v0.25.3_WORKSTREAM_PLAN.md` (~1452 lines)
- `tests/SmpSurfaceAnchors.lean` (~1443 lines)
- `SeLe4n/Kernel/FrozenOps/Operations.lean` (~1425 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreSwitchToThread.lean` (~1423 lines)
- `docs/dev_history/audits/WS_RC_R5_DEFERRED_COMPLETION_PLAN.md` (~1414 lines)
- `docs/dev_history/AUDIT_v0.23.21_WORKSTREAM_PLAN.md` (~1411 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean` (~1394 lines)
- `SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean` (~1393 lines)
- `docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md` (~1392 lines)
- `docs/dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md` (~1382 lines)
- `tests/LockSetSuite.lean` (~1377 lines)
- `docs/planning/SMP_DECLASSIFICATION_COMPLETION_PLAN.md` (~1370 lines)
- `docs/dev_history/audits/AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md` (~1357 lines)
- `docs/dev_history/audits/AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md` (~1342 lines)
- `SeLe4n/Kernel/IPC/Invariant/LookupCongruence.lean` (~1326 lines)
- `tests/FrozenOpsSuite.lean` (~1324 lines)
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean` (~1317 lines)
- `SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean` (~1296 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` (~1294 lines)
- `docs/planning/SMP_RELEASE_READINESS_PLAN.md` (~1291 lines)
- `SeLe4n/Kernel/InformationFlow/Taint.lean` (~1261 lines)
- `docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md` (~1261 lines)
- `docs/dev_history/audits/AUDIT_v0.22.17_WORKSTREAM_PLAN.md` (~1252 lines)
- `tests/SmpCancellationSuite.lean` (~1247 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreDomain.lean` (~1241 lines)
- `SeLe4n/Kernel/IPC/Operations/Donation/Primitives.lean` (~1235 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean` (~1233 lines)
- `SeLe4n/Kernel/Scheduler/Invariant.lean` (~1216 lines)
- `SeLe4n/Kernel/Scheduler/Invariant/PerCorePreservation.lean` (~1200 lines)
- `SeLe4n/Kernel/Concurrency/Locks/DynamicChainExtension.lean` (~1188 lines)
- `docs/dev_history/audits/AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md` (~1178 lines)
- `tests/SmpCacheMaintenanceSuite.lean` (~1170 lines)
- `SeLe4n/Kernel/Concurrency/Locks/WithLockSet.lean` (~1169 lines)
- `SeLe4n/Kernel/RobinHood/Bridge.lean` (~1169 lines)
- `SeLe4n/Kernel/Scheduler/RunQueue.lean` (~1168 lines)
- `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean` (~1165 lines)
- `SeLe4n/Platform/DeviceTree.lean` (~1154 lines)
- `SeLe4n/Platform/RPi5/MmioAdapter.lean` (~1154 lines)
- `tests/KernelErrorMatrixSuite.lean` (~1154 lines)
- `SeLe4n/Kernel/Architecture/VSpace.lean` (~1142 lines)
- `SeLe4n/Machine.lean` (~1128 lines)
- `tests/PerObjectLockSuite.lean` (~1104 lines)
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean` (~1085 lines)
- `SeLe4n/Kernel/Lifecycle/Suspend.lean` (~1076 lines)
- `docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md` (~1071 lines)
- `tests/SyscallReturnAbiSuite.lean` (~1068 lines)
- `SeLe4n/Kernel/Concurrency/Locks/LockSetHeld.lean` (~1063 lines)
- `SeLe4n/Kernel/IPC/DualQueue/Core.lean` (~1046 lines)
- `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean` (~1043 lines)
- `SeLe4n/Kernel/InformationFlow/Projection.lean` (~1030 lines)
- `SeLe4n/Model/FrozenState.lean` (~1007 lines)
- `tests/SmpIdleSuite.lean` (~999 lines)
- `SeLe4n/Kernel/IPC/Operations/SchedulerLemmas.lean` (~998 lines)
- `SeLe4n/Kernel/IPC/Operations/CapTransfer.lean` (~995 lines)
- `tests/SmpFoundationsSuite.lean` (~990 lines)
- `docs/dev_history/audits/AUDIT_v0.19.6_WORKSTREAM_PLAN.md` (~984 lines)
- `tests/SmpCbsSuite.lean` (~977 lines)
- `docs/planning/SMP_PER_CORE_STATE_PLAN.md` (~968 lines)
- `docs/dev_history/planning/WS_X_LEAN_ETHEREUM_FORMALIZATION_PLAN.md` (~958 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointCall.lean` (~950 lines)
- `SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean` (~942 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreTickCbsPreservation.lean` (~941 lines)
- `SeLe4n/Kernel/Concurrency/MemoryModel.lean` (~935 lines)
- `SeLe4n/Kernel/InformationFlow/Declassification.lean` (~935 lines)
- `docs/dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md` (~930 lines)
- `docs/planning/SMP_TLB_SHOOTDOWN_PLAN.md` (~924 lines)
- `docs/dev_history/audits/AUDIT_v0.28.0_COMPREHENSIVE.md` (~921 lines)
- `docs/dev_history/audits/AUDIT_H3_HARDWARE_BINDING_v0.25.27.md` (~911 lines)
- `docs/dev_history/audits/AUDIT_v0.25.10_WORKSTREAM_PLAN.md` (~909 lines)
- `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/Signal.lean` (~891 lines)
- `docs/dev_history/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md` (~884 lines)
- `SeLe4n/Kernel/IPC/CrossCore/NotificationSignal.lean` (~877 lines)
- `SeLe4n/Kernel/SyscallDispatchEntry.lean` (~875 lines)
- `SeLe4n/Kernel/IPC/Operations/Fault.lean` (~868 lines)
- `docs/dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md` (~859 lines)
- `docs/planning/SMP_RUST_HAL_PLAN.md` (~848 lines)
- `tests/SmpTimerSuite.lean` (~840 lines)
- `tests/DecodingSuite.lean` (~833 lines)
- `tests/SmpCrossCoreCallSuite.lean` (~833 lines)
- `SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean` (~824 lines)
- `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` (~823 lines)
- `docs/dev_history/audits/WS_RC_R4_CLOSEOUT_PLAN.md` (~818 lines)
- `SeLe4n/Kernel/SchedContext/BindingAffinity.lean` (~816 lines)
- `SeLe4n/Kernel/InformationFlow/AuditRecord.lean` (~811 lines)
- `tests/WithLockSetSuite.lean` (~811 lines)
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
  spelling beside it was still copied verbatim.  None was a new class;
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
  applied to a configuration, decided by one `Meta.isDefEq` against a
  metavariable.  Every question the walk approximated is then answered exactly
  or has no subject: the entry *is* the boot, so nothing precedes it, there is
  no bind whose instance could be lawless, `isDefEq` zeta- and beta-reduces so
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
| SM2 | LANDED | v0.31.9; SM2.C-defer closed v0.34.49 | Memory model, TicketLock, RwLock, FFI bridge, refinement (WS-RR RR6 closed the deferred completion: the deployed lock is `QueuedRwLock` and refines the FIFO spec) |
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
| WS-RR | IN FLIGHT | RR0 v0.34.26; RR1 v0.34.41; RR2 v0.34.42; RR3 v0.34.43; RR4 v0.34.44; RR5 v0.34.48; RR6 v0.34.49 | Pre-SM10 remediation: the audit's 3 blockers, 11 security findings, fault IPC, de-threading closure, lock completion (187 subs across RR0..RR8) |
| SM10 | BLOCKED on WS-RR | — | Release closure (→ v1.0.0) |

**Plans**: master overview at
[`docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md`](docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md);
per-phase plans at `docs/planning/SMP_*.md`.

### WS-LC Lock datatype completion — COMPLETE (v0.34.50 → v0.34.54; closure audit v0.34.55)

The two SM2.C **datatype** residuals RR6 re-registered rather than absorbed —
`RwLockOp` had no withdrawal and `RwLockExecution` no notion of time.  Scoped
ahead of WS-RR RR7 because the fine-lock migration tracks widen `withLockSet`
footprints onto more syscall arms, and the withdrawal is what makes those
footprints unwindable.

| Phase | Status | Version | Scope (one line — detail in the canonical sources) |
|-------|--------|---------|----------------------------------------------------|
| LC1 | LANDED | v0.34.50 | The abstract withdrawal: `RwLockOp.cancel`, INV-R preservation, the liveness restatement, the CAS-retry bridge |
| LC2 | LANDED | v0.34.51 | The ticket-FIFO refinement of the withdrawal: the withdrawal word, skip-aware promotion, the capstones over live entries |
| LC3 | LANDED | v0.34.52 | The deployed withdrawal: `QueuedRwLock::cancel`, loom, miri, Tier-5, and the foreign-function surface |
| LC4 | LANDED | v0.34.53 | The two-phase-locking consumers: `cancelAll`, the revalidated refusal unwind, the `withLockSet` unwind |
| LC5 | LANDED | v0.34.54 | SM2.C-T: the timed execution and the cycle-denominated bounds; LC5.10 retired both debt rows |

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
  satisfied every other readiness question while being a different predicate, and the **one** upcall that runs
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
  unreachable (`bootAndInitialisePlatform_eq_checked_boot`) — of the
  **bound** config (round 7): `bindPlatformConfig` puts the caller's IRQ
  table and objects under the binding's `machineConfig` and `bootVSpaceRoot`,
  so a caller cannot omit the canonical root or describe other hardware.
  The hardware entry is `bootAndInitialiseRPi5`, the generic entry fixed at
  `RPi5Platform`; SM10.1's `lean_kernel_main` calls it and nothing else.
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
  operand is a raw id from a message register escapes it: `.schedContextBind`
  resolves its capability to the SchedContext and takes the thread from
  `args.threadId`, which let an ordinary SchedContext capability bind the idle
  TCB and re-prioritise it (round 11, P1).  Raw operands are therefore refused
  at their lift points — `validateThreadIdArg` and `validateObjIdArg` reject a
  reserved idle id (`validateThreadIdArg_ok_not_reserved`,
  `dispatchCapabilityOnly_schedContextBind_idle_operand_refused`) — so a new
  arm taking a bare id is covered the day it is written.  `.lifecycleRetype`'s
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
  be pinned to.

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
- **The deployed reader-writer lock is the ticket-FIFO one, and each lock has
  its own refinement bridge** (WS-RR RR6, v0.34.49).  `STATIC_RW_LOCK_POOL` is
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
  below), and both are closed: **SM2.C-C** at v0.34.53 (spec, both refinements,
  the deployed lock and both consumers) and **SM2.C-T** at v0.34.54 (the timed
  execution) — see the two bullets below.
- **A queued core may withdraw its request.**
  `RwLockOp.cancel` (v0.34.50) removes `c`'s entry from `waiters` and writes
  nothing else — three frame facts by `rfl` — preserves all five INV-R
  conjuncts, and is neither a release nor an admission
  (`rwLock_cancel_not_effective_release`, `rwLock_cancel_admits_no_one`), so it
  costs the waiters behind it nothing.  Four things new code must respect.
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
  withdrawal to disturb.  The ticket-FIFO one (v0.34.51) carries it properly;
  see the next bullet, and the deployed lock carries it at v0.34.52 — the one
  after that.  (4) **Both 2PL unwinds emit one** since v0.34.53 — see the
  shrinking-phase bullet below.
- **The ticket lock's ledger tombstones; the queue it represents is the
  *live* one** (WS-LC LC2, v0.34.51).  `now_serving` owes one advance per
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
  (WS-LC LC3, v0.34.52).  `QueuedRwLock::acquire_read` / `acquire_write` are
  the *fused* spellings — they take a ticket and spin to completion inside one
  call, so there is no instant at which a caller holds a ticket and could
  abandon it.  A caller that may have to unwind takes `enqueue(core)`, spins on
  `is_served(ticket)`, and then calls **exactly one** of `complete_read`,
  `complete_write` or `cancel` for that ticket.  Five things new code must
  respect.  (1) **Exactly one terminator per ticket, always.**  `next_ticket`
  is an unconditional `fetch_add` and `now_serving` owes one advance per ticket
  ever issued, so a ticket that is neither completed nor withdrawn stalls the
  lock permanently — the failure is a hang, not a data race, and no assertion
  catches it.  (2) **The withdrawal is published before the head is checked,
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
  enqueue, withdraw, enqueue, withdraw (WS-LC closure audit, v0.34.55: the
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
  reader and `HELD_WRITE` iff the spec's writer is that core — so the four
  `_noop` blocks of `queuedBlock` are the one held-word load and are
  *derived* in `queuedBlock_preserves_queuedSim`; every acquire and release
  block opens with that load (`heldLoad`), and the effective releases clear
  the word (`heldStore c none`) **before** the state word moves, and the
  withdrawal block opens with the held load before the publish
  (`cancelPublish` is enabled only for a core holding nothing) — orders
  `build.rs` pins for both releases and for `cancel`
  (`scan_queued_rw_lock_protocol_intact`, its third check).
  (2) **A queued waiter re-acquiring has no block**: the spec no-ops on it
  and the lock has no branch for it — the core is inside its own
  acquisition, or holds a split-API ticket it must terminate first — so the
  one-outstanding-ticket contract (`ledgerCoresNodup`) is what rules the
  call out, and `queuedBlock` says so by having no shape rather than a
  fictional stutter.  (3) **The CAS-retry `rw_lock.rs` has no such no-ops
  and its bridge no longer claims them**: it keeps no holder bookkeeping, so
  its four `honestBlock` `_noop` constructors and `opCorresponds.noop` —
  each a `[]` block for a call on which that code performs an atomic access
  — are gone, and its trace-level theorems cover exactly the traces that
  respect its caller contract (acquire only while uninvolved, release only
  what you hold), stated in its module docs.  (4) **The gates ask the lock
  the question.**  The Tier-5 oracle issues a non-holder's release, a
  holder's re-acquisition and a holder's withdrawal (with the ticket the
  core actually held) to the real ticket lock and holds every core's word
  to the spec's holders after each op (`check_holders`); a queued
  waiter's re-acquisition is issued to neither lock, and the CAS-retry lock
  is sent neither call.  On the host a std thread stands in for a PE and the
  per-CPU stub answers core 0 to every thread, so the bridge's cross-thread
  tests give each thread its own PE identity (`per_cpu::HostCoreIdentity`,
  test-only): several threads under one id are one PE issuing overlapping
  acquisitions, which the held word turns into no-ops and stranded counts —
  the first host lane after the word landed hung in exactly that shape.
  The loom gate gained
  `unwind_by_a_non_holder_never_touches_the_holder` and
  `every_pair_of_units_is_safe` — every unordered pair of the lock's nine
  operation units on two threads, unbounded, which is the SM2.C-defer plan's
  "op-sequences of length ≤ 4" acceptance criterion stated as the
  enumeration it always should have been; two of the nine are the unwind at
  a member the core holds, as a reader and as the writer (round 3) — so the
  model count is thirteen.
- **The two-phase-locking shrinking phase withdraws before it releases**
  (WS-LC LC4, v0.34.53).  `withLockSet`'s third phase and the revalidated
  entry's refusal path are both `unwindAll` — one definition, so the two
  cannot answer "what does a bracket do on the way out" differently.  Five
  things new code must respect.  (1) **The order is load-bearing.**  Two
  identities meet at each member: a release by a non-holder is the identity,
  and a withdrawal by a holder is the identity (INV-R4 keeps holders out of
  `waiters`), so both orders are correct on a well-formed state and neither
  needs a branch.  Withdrawing first is what makes the payoff
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
  make** (WS-LC LC5, v0.34.54).  `RwLockExecution` carries `stepCost : Nat →
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
  1 ms timer the same 1024 steps span from under one tick to 1024 ticks
  depending on the ceiling assumed (`releaseBudgetTicks_rpi5_range`), which is
  why the step figure alone was never a time.

  `elapsedBetween` and its two bounds moved here from
  `InformationFlow/FineLockFlow`, where they had been introduced with a note
  that the execution datatype "has no such notion" — it has one now, so the
  vocabulary belongs beside the datatype that carries it.
- **Registered uncovered lock domains** are enumerated in Lean, not in prose:
  `UncoveredLockDomain` (`InformationFlow/FineLockFlow.lean`) names each gap and
  its owner, and its completeness theorem forces a new domain to be registered.
- **Staged modules**: 63 staged-only, listed in
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
  **The boot entry's contract left this gate at round 17** and is decided by
  the elaborator in `SeLe4n/Testing/BootEntryContract.lean`: whichever
  declaration carries `@[export lean_kernel_main]` (found with
  `getExportNameFor?`, so any attribute list and any namespace) must call
  `Platform.FFI.bootAndInitialiseRPi5OrHalt` — the checked RPi5 boot with its
  failure handled, so a refused boot parks the PE — and no path from it may
  reach a kernel-state installer except through that call, walked over
  `Expr.getUsedConstants`.  Building the module is the check, and four
  witnesses (a compliant entry and three token-preserving deviations) keep it
  decisive before SM10.1 writes the entry.  What the Python gate still holds is
  the link-level half — vacuous until SM10.1 writes the entry, decisive after,
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
  inventories hold **1133 entries**, of which **919 are theorems**: the
  inventories register a phase's whole surface, so 214 entries are `def`s —
  lock-set footprints, per-core invariant predicates, WCRT cost functions — and
  every inventory's construction macro proves only that the name *resolves*,
  never that its type is a `Prop`.  **Quote 919, and quote it as theorems; 1133
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
