# AGENTS.md — seLe4n project guidance

> This file mirrors `CLAUDE.md` so that non-Claude coding agents (and any
> tool that follows the AGENTS.md convention) get the same project rules.
> If you edit one, edit the other in the same PR — the two files must
> stay byte-identical apart from this header.

## What this project is

seLe4n is a production-oriented microkernel written in Lean 4 with machine-checked
proofs, improving on seL4 architecture. Every kernel transition is an executable
pure function with zero `sorry`/`axiom`. First hardware target: Raspberry Pi 5.
Lean 4.28.0 toolchain, Lake build system, version 0.33.99.

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
  `docs/i18n/*/README.md` badges (+ the `de` / `fr` `Version` rows); the
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
```

Run at least `test_smoke.sh` before any PR. Run `test_full.sh` when changing
theorems, invariants, or documentation anchors.

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
or sorry is found. Do NOT bypass it with `--no-verify`.

## Source layout

Top-level subsystems (the filesystem is the authoritative file list — it
changes more often than this map can track):

```
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
- `CHANGELOG.md` (~45000 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/DualQueueMembership.lean` (~20336 lines)
- `docs/WORKSTREAM_HISTORY.md` (~11927 lines)
- `tests/SmpInformationFlowSuite.lean` (~11136 lines)
- `SeLe4n/Kernel/Concurrency/Locks/RwLock.lean` (~7902 lines)
- `SeLe4n/Kernel/API.lean` (~5748 lines)
- `SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean` (~5702 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~5096 lines)
- `SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuite.lean` (~4764 lines)
- `docs/dev_history/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md` (~4721 lines)
- `docs/gitbook/12-proof-and-invariant-map.md` (~4563 lines)
- `SeLe4n/Model/State.lean` (~4503 lines)
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean` (~4450 lines)
- `docs/spec/SELE4N_SPEC.md` (~4161 lines)
- `docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md` (~4130 lines)
- `tests/NegativeStateSuite.lean` (~4112 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` (~3919 lines)
- `SeLe4n/Kernel/InformationFlow/FineLockFlow.lean` (~3884 lines)
- `SeLe4n/Kernel/InformationFlow/AuditRead.lean` (~3788 lines)
- `SeLe4n/Platform/Boot.lean` (~3628 lines)
- `SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean` (~3443 lines)
- `SeLe4n/Kernel/CrossSubsystem.lean` (~3394 lines)
- `docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md` (~3388 lines)
- `tests/SmpTlbShootdownSuite.lean` (~3354 lines)
- `tests/OperationChainSuite.lean` (~3290 lines)
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` (~3222 lines)
- `SeLe4n/Testing/MainTraceHarness.lean` (~3214 lines)
- `docs/dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md` (~3140 lines)
- `docs/dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md` (~3134 lines)
- `SeLe4n/Model/Object/Structures.lean` (~3115 lines)
- `SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean` (~3087 lines)
- `docs/planning/SMP_RUST_HAL_PLAN.md` (~3029 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean` (~2853 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointCallInvariant.lean` (~2805 lines)
- `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean` (~2775 lines)
- `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean` (~2733 lines)
- `SeLe4n/Kernel/Capability/Operations.lean` (~2674 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/StoreObjectFrame.lean` (~2657 lines)
- `SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean` (~2641 lines)
- `SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean` (~2639 lines)
- `SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean` (~2602 lines)
- `docs/planning/SMP_INFORMATION_FLOW_PLAN.md` (~2578 lines)
- `SeLe4n/Kernel/Architecture/TlbShootdown.lean` (~2562 lines)
- `SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean` (~2505 lines)
- `tests/ModelIntegritySuite.lean` (~2477 lines)
- `docs/dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md` (~2476 lines)
- `docs/dev_history/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md` (~2472 lines)
- `docs/dev_history/audits/AUDIT_v0.25.14_WORKSTREAM_PLAN.md` (~2340 lines)
- `docs/dev_history/audits/AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md` (~2339 lines)
- `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` (~2328 lines)
- `docs/audits/AUDIT_v0.30.11_DEEP_VERIFICATION.md` (~2325 lines)
- `docs/planning/SMP_DECLASSIFICATION_COMPLETION_PLAN.md` (~2289 lines)
- `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean` (~2287 lines)
- `SeLe4n/Kernel/InformationFlow/TaintPropagation.lean` (~2278 lines)
- `SeLe4n/Kernel/IPC/Invariant/QueueNextBlocking.lean` (~2274 lines)
- `SeLe4n/Platform/FFI.lean` (~2249 lines)
- `SeLe4n/Model/Object/Types.lean` (~2204 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreCbs.lean` (~2182 lines)
- `docs/planning/SMP_TLB_SHOOTDOWN_PLAN.md` (~2178 lines)
- `SeLe4n/Prelude.lean` (~2137 lines)
- `SeLe4n/Kernel/Scheduler/PriorityInheritance/PerCore.lean` (~2131 lines)
- `docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md` (~2083 lines)
- `SeLe4n/Kernel/IPC/Invariant/QueueMembership.lean` (~2079 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/QueueNextTransport.lean` (~2074 lines)
- `SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean` (~2059 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/PerOperation.lean` (~2039 lines)
- `SeLe4n/Kernel/Architecture/Invariant.lean` (~2025 lines)
- `docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md` (~2022 lines)
- `SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean` (~2019 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreChooseThread.lean` (~1989 lines)
- `SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean` (~1967 lines)
- `docs/dev_history/planning/V3_PROOF_CHAIN_HARDENING_E_G6_PLAN.md` (~1966 lines)
- `docs/dev_history/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md` (~1917 lines)
- `SeLe4n/Kernel/Concurrency/Locks/TicketLock.lean` (~1901 lines)
- `docs/dev_history/planning/V3E_IPC_UNWRAP_CAPS_LOOP_COMPOSITION_PLAN.md` (~1891 lines)
- `docs/dev_history/audits/AUDIT_v0.30.6_COMPREHENSIVE.md` (~1889 lines)
- `SeLe4n/Kernel/Concurrency/Locks/Serializability.lean` (~1859 lines)
- `SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean` (~1831 lines)
- `SeLe4n/Model/FreezeProofs.lean` (~1827 lines)
- `docs/dev_history/audits/AUDIT_v0.27.6_WORKSTREAM_PLAN.md` (~1801 lines)
- `docs/dev_history/audits/AUDIT_v0.25.21_WORKSTREAM_PLAN.md` (~1800 lines)
- `SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean` (~1792 lines)
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` (~1790 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Core.lean` (~1785 lines)
- `docs/dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md` (~1776 lines)
- `tests/InformationFlowSuite.lean` (~1773 lines)
- `docs/dev_history/audits/AUDIT_v0.25.14_COMPREHENSIVE.md` (~1739 lines)
- `SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean` (~1737 lines)
- `docs/dev_history/audits/WORKSTREAM_PLAN_WS_O_SYSCALL_RUST_WRAPPERS.md` (~1725 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreWake.lean` (~1706 lines)
- `docs/dev_history/AUDIT_v0.22.10_WORKSTREAM_PLAN.md` (~1674 lines)
- `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` (~1670 lines)
- `docs/planning/SMP_FOUNDATIONS_PLAN.md` (~1665 lines)
- `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean` (~1488 lines)
- `SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean` (~1488 lines)
- `docs/dev_history/audits/AUDIT_v0.28.0_WORKSTREAM_PLAN.md` (~1480 lines)
- `docs/dev_history/planning/V3B_LOAD_FACTOR_BOUNDED_MIGRATION_PLAN.md` (~1457 lines)
- `docs/dev_history/audits/AUDIT_v0.25.3_WORKSTREAM_PLAN.md` (~1452 lines)
- `docs/dev_history/audits/WS_RC_R5_DEFERRED_COMPLETION_PLAN.md` (~1414 lines)
- `docs/dev_history/AUDIT_v0.23.21_WORKSTREAM_PLAN.md` (~1411 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` (~1398 lines)
- `SeLe4n/Kernel/FrozenOps/Operations.lean` (~1397 lines)
- `docs/dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md` (~1382 lines)
- `tests/LockSetSuite.lean` (~1375 lines)
- `tests/SmpIpcSuite.lean` (~1373 lines)
- `docs/dev_history/audits/AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md` (~1357 lines)
- `docs/dev_history/audits/AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md` (~1342 lines)
- `docs/planning/SMP_PANIC_HANG_REMEDIATION_PLAN.md` (~1342 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyInvariant.lean` (~1337 lines)
- `SeLe4n/Kernel/InformationFlow/Policy.lean` (~1321 lines)
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean` (~1316 lines)
- `SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean` (~1288 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreDomain.lean` (~1277 lines)
- `SeLe4n/Kernel/InformationFlow/Taint.lean` (~1261 lines)
- `docs/dev_history/audits/AUDIT_v0.22.17_WORKSTREAM_PLAN.md` (~1252 lines)
- `tests/SmpCancellationSuite.lean` (~1246 lines)
- `SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean` (~1244 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` (~1241 lines)
- `docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md` (~1237 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean` (~1233 lines)
- `SeLe4n/Kernel/Scheduler/Invariant.lean` (~1216 lines)
- `SeLe4n/Kernel/Scheduler/Invariant/PerCorePreservation.lean` (~1200 lines)
- `SeLe4n/Kernel/Concurrency/Locks/DynamicChainExtension.lean` (~1186 lines)
- `tests/FrozenOpsSuite.lean` (~1184 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean` (~1182 lines)
- `docs/dev_history/audits/AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md` (~1178 lines)
- `docs/planning/SMP_PER_CORE_STATE_PLAN.md` (~1172 lines)
- `tests/SmpCacheMaintenanceSuite.lean` (~1170 lines)
- `SeLe4n/Kernel/Scheduler/RunQueue.lean` (~1168 lines)
- `SeLe4n/Kernel/RobinHood/Bridge.lean` (~1167 lines)
- `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean` (~1165 lines)
- `SeLe4n/Platform/DeviceTree.lean` (~1154 lines)
- `tests/SmpSurfaceAnchors.lean` (~1154 lines)
- `SeLe4n/Platform/RPi5/MmioAdapter.lean` (~1153 lines)
- `docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md` (~1151 lines)
- `SeLe4n/Kernel/Architecture/VSpace.lean` (~1142 lines)
- `tests/KernelErrorMatrixSuite.lean` (~1140 lines)
- `SeLe4n/Kernel/Architecture/SyscallReturn.lean` (~1138 lines)
- `docs/planning/WS_RC_R4_TYPE_LEVEL_PROMOTION_PLAN.md` (~1111 lines)
- `SeLe4n/Machine.lean` (~1105 lines)
- `tests/PerObjectLockSuite.lean` (~1097 lines)
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean` (~1085 lines)
- `SeLe4n/Kernel/Lifecycle/Suspend.lean` (~1076 lines)
- `docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md` (~1071 lines)
- `tests/SyscallDispatchSuite.lean` (~1051 lines)
- `tests/SyscallReturnAbiSuite.lean` (~1049 lines)
- `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean` (~1043 lines)
- `SeLe4n/Kernel/InformationFlow/Projection.lean` (~1029 lines)
- `SeLe4n/Kernel/IPC/Operations/SchedulerLemmas.lean` (~1027 lines)
- `docs/planning/SYSCALL_RETURN_ABI_PLAN.md` (~1022 lines)
- `SeLe4n/Kernel/IPC/DualQueue/Core.lean` (~1012 lines)
- `SeLe4n/Model/FrozenState.lean` (~1007 lines)
- `docs/planning/SMP_CROSS_CORE_IPC_PLAN.md` (~988 lines)
- `docs/dev_history/audits/AUDIT_v0.19.6_WORKSTREAM_PLAN.md` (~984 lines)
- `docs/dev_history/planning/WS_X_LEAN_ETHEREUM_FORMALIZATION_PLAN.md` (~958 lines)
- `SeLe4n/Kernel/Concurrency/Locks/RwLockRefinement.lean` (~943 lines)
- `SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean` (~942 lines)
- `SeLe4n/Kernel/Concurrency/MemoryModel.lean` (~935 lines)
- `SeLe4n/Kernel/InformationFlow/Declassification.lean` (~935 lines)
- `docs/dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md` (~930 lines)
- `tests/SmpFoundationsSuite.lean` (~928 lines)
- `docs/dev_history/audits/AUDIT_v0.28.0_COMPREHENSIVE.md` (~921 lines)
- `docs/dev_history/audits/AUDIT_H3_HARDWARE_BINDING_v0.25.27.md` (~911 lines)
- `docs/dev_history/audits/AUDIT_v0.25.10_WORKSTREAM_PLAN.md` (~909 lines)
- `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/Signal.lean` (~891 lines)
- `SeLe4n/Kernel/IPC/Operations/CapTransfer.lean` (~890 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreSwitchToThread.lean` (~886 lines)
- `docs/dev_history/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md` (~884 lines)
- `SeLe4n/Kernel/IPC/CrossCore/NotificationSignal.lean` (~882 lines)
- `docs/dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md` (~859 lines)
- `SeLe4n/Kernel/Capability/Invariant/Preservation/BadgeIpcCapsAndCdtMaps.lean` (~837 lines)
- `tests/DecodingSuite.lean` (~827 lines)
- `SeLe4n/Kernel/SyscallDispatchEntry.lean` (~826 lines)
- `SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean` (~824 lines)
- `docs/dev_history/audits/WS_RC_R4_CLOSEOUT_PLAN.md` (~818 lines)
- `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` (~815 lines)
- `tests/WithLockSetSuite.lean` (~809 lines)
- `SeLe4n/Kernel/InformationFlow/AuditRecord.lean` (~808 lines)
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
  `CLAUDE.md` / `docs/WORKSTREAM_HISTORY.md` prose. Historical
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
  register (`docs/audits/`, `docs/WORKSTREAM_HISTORY.md`). Never leave
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
6. `docs/WORKSTREAM_HISTORY.md` if workstream status changes
7. Regenerate `docs/codebase_map.json` if Lean sources changed

Canonical ownership: root `docs/` files own policy/spec text. GitBook
chapters under `docs/gitbook/` are mirrors that summarize and link to
canonical sources. `docs/WORKSTREAM_HISTORY.md` is the single canonical
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

- [`docs/WORKSTREAM_HISTORY.md`](docs/WORKSTREAM_HISTORY.md) — the canonical
  per-phase record, including "What's next".
- [`CHANGELOG.md`](CHANGELOG.md) — the per-version narrative, one entry per PR.
- [`docs/CLAUDE_HISTORY.md`](docs/CLAUDE_HISTORY.md) — archived workstreams.
- `docs/planning/SMP_*.md` — the per-phase plans, linked from the table below.

When a cut lands, update the row's status/version here and write the detail in
`CHANGELOG.md` and `docs/WORKSTREAM_HISTORY.md`.  A row that grows past one line
of summary is a sign the narrative belongs in those files instead.

### WS-RA Syscall Return ABI — COMPLETE (v0.33.37; RA.B.5b + RA.B.8 at v0.33.38)

The kernel returns seL4's ARM64 frame exactly: `x0` = badge / primary result at
full 64-bit width, `x1` = `MessageInfo` whose **offset** label carries the error
(`0` = success, `d + 1` = discriminant `d` — offset because discriminant 0,
`.invalidCapability`, is a real error and direct carriage would alias it with
success), `x2`-`x5` = message registers.  `SYSCALL_ABI_VERSION = 2`, pinned in
Lean, `sele4n-types` and the HAL.

What remains is owed to SM10.E: return-frame *delivery* at the context restore,
and the cancellation/timeout error-frame staging.  Until that seam flips, a
blocked caller's frame is poisoned with the fail-closed
`blocked_resume_sentinel_regs()` so a stale request register can never decode as
a success.

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
| SM5.A–I | LANDED | v0.31.38–62 | Per-core scheduler: selection, switch, wake, timer, idle, PIP, domain, CBS, invariant suite |
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
| SM9 | IN FLIGHT | — | Declassification completion (A–D landed; E = tests + closure) |
| SM10 | PENDING | — | Release closure (→ v1.0.0) |

**Plans**: master overview at
[`docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md`](docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md);
per-phase plans at `docs/planning/SMP_*.md`.

### Standing constraints and registered debt

These are *current facts about the tree*, not history — they change what new
code may assume:

- **Kernel entry is serialised by one global ticket lock** (SM5.I, v0.32.142,
  `rust/sele4n-hal/src/kernel_entry.rs`), acquired outside
  `SHOOTDOWN_ROUND_LOCK` and self-servicing pending shootdowns while spinning.
  It brackets all three state-committing entries.  Live WCRT is therefore weaker
  than `PerCoreWcrt.lean`'s fine-lock bound, which remains a statement about the
  intended discipline.
- **SM3.C.9 is deferred**: the `@[export]` bodies are not yet wrapped in
  `withLockSet`, so the per-object fine locks are a model-level discipline.  The
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
- **SM4.C.11**: per-core Liveness forms (`Scheduler/Liveness/*.lean`) remain
  `bootCoreId`-pinned; migration is Scheduler-subsystem scope, not SM4.D.
- **Registered uncovered lock domains** are enumerated in Lean, not in prose:
  `UncoveredLockDomain` (`InformationFlow/FineLockFlow.lean`) names each gap and
  its owner, and its completeness theorem forces a new domain to be registered.
- **Staged modules**: 60 staged-only, listed in
  `scripts/staged_module_allowlist.txt` and gated by
  `scripts/check_production_staging_partition.sh`.  Production must not import
  staged.

### Closed workstreams

- **WS-RC** remediation CLOSED (v0.30.11 → v0.31.2): R0–R5 landed; R6–R14
  absorbed into WS-SM per SM0.Q.
- **WS-AN** portfolio COMPLETE (v0.30.11): 12 phases (AN0–AN12).
- **WS-AK through WS-AA**: archived to
  [`docs/CLAUDE_HISTORY.md`](docs/CLAUDE_HISTORY.md).

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
Refs: docs/WORKSTREAM_HISTORY.md WS-RC R3 closeout
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
