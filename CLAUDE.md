# CLAUDE.md — seLe4n project guidance

> A mirror of this file lives at `AGENTS.md` so that non-Claude coding
> agents (and any tool that follows the AGENTS.md convention) get the
> same project rules. If you edit one, edit the other in the same PR —
> the two files must stay byte-identical apart from this header.

## What this project is

seLe4n is a production-oriented microkernel written in Lean 4 with machine-checked
proofs, improving on seL4 architecture. Every kernel transition is an executable
pure function with zero `sorry`/`axiom`. First hardware target: Raspberry Pi 5.
Lean 4.28.0 toolchain, Lake build system, version 0.32.82.

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
  + `AGENTS.md`; the root `README.md` badge + `Version` row; the ten
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
- `CHANGELOG.md` (~32032 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/DualQueueMembership.lean` (~20449 lines)
- `docs/WORKSTREAM_HISTORY.md` (~9538 lines)
- `SeLe4n/Kernel/Concurrency/Locks/RwLock.lean` (~6631 lines)
- `SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuite.lean` (~4764 lines)
- `docs/dev_history/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md` (~4721 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~4566 lines)
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean` (~4351 lines)
- `docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md` (~4130 lines)
- `tests/NegativeStateSuite.lean` (~4036 lines)
- `SeLe4n/Model/State.lean` (~3991 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` (~3911 lines)
- `docs/spec/SELE4N_SPEC.md` (~3812 lines)
- `SeLe4n/Kernel/CrossSubsystem.lean` (~3394 lines)
- `SeLe4n/Platform/Boot.lean` (~3394 lines)
- `docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md` (~3388 lines)
- `docs/gitbook/12-proof-and-invariant-map.md` (~3252 lines)
- `SeLe4n/Testing/MainTraceHarness.lean` (~3196 lines)
- `docs/dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md` (~3140 lines)
- `docs/dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md` (~3134 lines)
- `SeLe4n/Model/Object/Structures.lean` (~3044 lines)
- `docs/planning/SMP_RUST_HAL_PLAN.md` (~3014 lines)
- `SeLe4n/Kernel/API.lean` (~2950 lines)
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` (~2809 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointCallInvariant.lean` (~2805 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean` (~2772 lines)
- `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean` (~2733 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/StoreObjectFrame.lean` (~2627 lines)
- `SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean` (~2505 lines)
- `tests/ModelIntegritySuite.lean` (~2477 lines)
- `docs/dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md` (~2476 lines)
- `docs/dev_history/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md` (~2472 lines)
- `docs/dev_history/audits/AUDIT_v0.25.14_WORKSTREAM_PLAN.md` (~2340 lines)
- `docs/dev_history/audits/AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md` (~2339 lines)
- `docs/audits/AUDIT_v0.30.11_DEEP_VERIFICATION.md` (~2326 lines)
- `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` (~2285 lines)
- `SeLe4n/Kernel/IPC/Invariant/QueueNextBlocking.lean` (~2258 lines)
- `tests/OperationChainSuite.lean` (~2209 lines)
- `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean` (~2187 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreCbs.lean` (~2182 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/PerOperation.lean` (~2096 lines)
- `SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean` (~2087 lines)
- `docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md` (~2083 lines)
- `SeLe4n/Prelude.lean` (~2071 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/QueueNextTransport.lean` (~2070 lines)
- `SeLe4n/Kernel/IPC/Invariant/QueueMembership.lean` (~2067 lines)
- `docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md` (~2022 lines)
- `SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean` (~2019 lines)
- `SeLe4n/Kernel/Capability/Operations.lean` (~1989 lines)
- `docs/dev_history/planning/V3_PROOF_CHAIN_HARDENING_E_G6_PLAN.md` (~1966 lines)
- `SeLe4n/Model/Object/Types.lean` (~1959 lines)
- `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean` (~1957 lines)
- `docs/dev_history/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md` (~1917 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreChooseThread.lean` (~1905 lines)
- `SeLe4n/Kernel/Concurrency/Locks/TicketLock.lean` (~1901 lines)
- `docs/dev_history/planning/V3E_IPC_UNWRAP_CAPS_LOOP_COMPOSITION_PLAN.md` (~1891 lines)
- `docs/dev_history/audits/AUDIT_v0.30.6_COMPREHENSIVE.md` (~1889 lines)
- `tests/SmpTlbShootdownSuite.lean` (~1862 lines)
- `SeLe4n/Kernel/Concurrency/Locks/Serializability.lean` (~1854 lines)
- `docs/dev_history/audits/AUDIT_v0.27.6_WORKSTREAM_PLAN.md` (~1801 lines)
- `docs/dev_history/audits/AUDIT_v0.25.21_WORKSTREAM_PLAN.md` (~1800 lines)
- `SeLe4n/Model/FreezeProofs.lean` (~1797 lines)
- `SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean` (~1782 lines)
- `docs/dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md` (~1776 lines)
- `docs/dev_history/audits/AUDIT_v0.25.14_COMPREHENSIVE.md` (~1739 lines)
- `docs/dev_history/audits/WORKSTREAM_PLAN_WS_O_SYSCALL_RUST_WRAPPERS.md` (~1725 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Core.lean` (~1706 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreWake.lean` (~1706 lines)
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` (~1701 lines)
- `docs/dev_history/AUDIT_v0.22.10_WORKSTREAM_PLAN.md` (~1674 lines)
- `SeLe4n/Kernel/Scheduler/PriorityInheritance/PerCore.lean` (~1671 lines)
- `docs/planning/SMP_FOUNDATIONS_PLAN.md` (~1665 lines)
- `tests/InformationFlowSuite.lean` (~1637 lines)
- `SeLe4n/Kernel/Architecture/Invariant.lean` (~1615 lines)
- `SeLe4n/Kernel/Architecture/TlbShootdown.lean` (~1498 lines)
- `docs/dev_history/audits/AUDIT_v0.28.0_WORKSTREAM_PLAN.md` (~1480 lines)
- `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean` (~1464 lines)
- `docs/dev_history/planning/V3B_LOAD_FACTOR_BOUNDED_MIGRATION_PLAN.md` (~1457 lines)
- `SeLe4n/Platform/FFI.lean` (~1453 lines)
- `docs/dev_history/audits/AUDIT_v0.25.3_WORKSTREAM_PLAN.md` (~1452 lines)
- `docs/dev_history/audits/WS_RC_R5_DEFERRED_COMPLETION_PLAN.md` (~1414 lines)
- `docs/dev_history/AUDIT_v0.23.21_WORKSTREAM_PLAN.md` (~1411 lines)
- `docs/dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md` (~1382 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` (~1363 lines)
- `docs/dev_history/audits/AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md` (~1357 lines)
- `tests/SmpIpcSuite.lean` (~1350 lines)
- `SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean` (~1342 lines)
- `docs/dev_history/audits/AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md` (~1342 lines)
- `docs/planning/SMP_PANIC_HANG_REMEDIATION_PLAN.md` (~1342 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyInvariant.lean` (~1337 lines)
- `tests/LockSetSuite.lean` (~1335 lines)
- `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` (~1328 lines)
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean` (~1316 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreDomain.lean` (~1267 lines)
- `docs/dev_history/audits/AUDIT_v0.22.17_WORKSTREAM_PLAN.md` (~1252 lines)
- `tests/SmpCancellationSuite.lean` (~1246 lines)
- `SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean` (~1244 lines)
- `docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md` (~1237 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean` (~1233 lines)
- `SeLe4n/Kernel/Scheduler/Invariant.lean` (~1216 lines)
- `SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean` (~1203 lines)
- `SeLe4n/Kernel/Scheduler/Invariant/PerCorePreservation.lean` (~1200 lines)
- `SeLe4n/Kernel/Concurrency/Locks/DynamicChainExtension.lean` (~1186 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` (~1184 lines)
- `docs/dev_history/audits/AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md` (~1178 lines)
- `docs/planning/SMP_PER_CORE_STATE_PLAN.md` (~1172 lines)
- `SeLe4n/Platform/DeviceTree.lean` (~1154 lines)
- `SeLe4n/Platform/RPi5/MmioAdapter.lean` (~1153 lines)
- `docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md` (~1151 lines)
- `tests/KernelErrorMatrixSuite.lean` (~1139 lines)
- `SeLe4n/Kernel/RobinHood/Bridge.lean` (~1137 lines)
- `docs/planning/WS_RC_R4_TYPE_LEVEL_PROMOTION_PLAN.md` (~1111 lines)
- `SeLe4n/Machine.lean` (~1105 lines)
- `tests/PerObjectLockSuite.lean` (~1097 lines)
- `docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md` (~1071 lines)
- `SeLe4n/Kernel/Scheduler/RunQueue.lean` (~1050 lines)
- `tests/SyscallDispatchSuite.lean` (~1047 lines)
- `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean` (~1043 lines)
- `SeLe4n/Kernel/FrozenOps/Operations.lean` (~1033 lines)
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean` (~1032 lines)
- `SeLe4n/Kernel/InformationFlow/Policy.lean` (~1023 lines)
- `SeLe4n/Kernel/IPC/Operations/SchedulerLemmas.lean` (~1007 lines)
- `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean` (~1002 lines)
- `SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean` (~999 lines)
- `docs/planning/SMP_CROSS_CORE_IPC_PLAN.md` (~988 lines)
- `docs/dev_history/audits/AUDIT_v0.19.6_WORKSTREAM_PLAN.md` (~984 lines)
- `SeLe4n/Kernel/Lifecycle/Suspend.lean` (~970 lines)
- `docs/dev_history/planning/WS_X_LEAN_ETHEREUM_FORMALIZATION_PLAN.md` (~958 lines)
- `SeLe4n/Kernel/Concurrency/Locks/RwLockRefinement.lean` (~943 lines)
- `SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean` (~940 lines)
- `SeLe4n/Kernel/InformationFlow/Projection.lean` (~940 lines)
- `SeLe4n/Kernel/Concurrency/MemoryModel.lean` (~935 lines)
- `SeLe4n/Kernel/IPC/DualQueue/Core.lean` (~931 lines)
- `docs/dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md` (~930 lines)
- `tests/SmpFoundationsSuite.lean` (~928 lines)
- `docs/dev_history/audits/AUDIT_v0.28.0_COMPREHENSIVE.md` (~921 lines)
- `docs/dev_history/audits/AUDIT_H3_HARDWARE_BINDING_v0.25.27.md` (~911 lines)
- `docs/dev_history/audits/AUDIT_v0.25.10_WORKSTREAM_PLAN.md` (~909 lines)
- `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/Signal.lean` (~891 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreSwitchToThread.lean` (~886 lines)
- `docs/dev_history/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md` (~884 lines)
- `SeLe4n/Kernel/IPC/CrossCore/NotificationSignal.lean` (~878 lines)
- `docs/dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md` (~859 lines)
- `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean` (~838 lines)
- `SeLe4n/Kernel/IPC/Operations/CapTransfer.lean` (~833 lines)
- `SeLe4n/Kernel/Capability/Invariant/Preservation/BadgeIpcCapsAndCdtMaps.lean` (~831 lines)
- `docs/dev_history/audits/WS_RC_R4_CLOSEOUT_PLAN.md` (~818 lines)
- `docs/planning/SMP_TLB_SHOOTDOWN_PLAN.md` (~814 lines)
- `tests/TwoPhaseArchSuite.lean` (~813 lines)
- `tests/WithLockSetSuite.lean` (~809 lines)
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
  new code must comply from day one.

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

- **WS-SM SMP multi-core completion workstream IN FLIGHT (v0.31.2 → v1.0.0)**:
  Unified workstream merging WS-RC's remaining R6..R14 phases with the
  SMP-specific SM-phases (SM0..SM9). Closes at v1.0.0 with a bootable
  verified SMP microkernel on Raspberry Pi 5.

  **Decisions (binding)**: per-object RW fine locks; path-a Vector state
  replacement; hierarchical-by-kind lock order (LockKind levels 0..9 from
  SM0.I); SMP enabled by default at v1.0.0 once SM5 lands; numCores via
  `PlatformBinding.coreCount` (RPi5 = 4); verified TicketLock + RwLock
  primitives with formal mutex/fairness theorems; SGI INTID 0..4 reserved
  for kernel SMP coordination (SM0.H).

  **Phase status** (current version: v0.32.80):

  | Phase | Status | Version | Summary |
  |-------|--------|---------|---------|
  | SM0 | CLOSED | v0.31.3 | Foundational types, honesty patches, lock hierarchy |
  | SM1 | CLOSED | v0.31.8 | Rust HAL: PSCI, per-CPU, secondary init, TLBI, SGI, QEMU |
  | SM2 | LANDED | v0.31.9 | Memory model, TicketLock, RwLock, FFI bridge, refinement |
  | SM3 | CLOSED | v0.31.9 | Per-object locks, lock sets, 2PL, deadlock-freedom, serializability |
  | SM4 | LANDED | v0.31.37 | Per-core Vector, SchedulerState, register banks, invariant migration, idle bootstrap |
  | SM5.A–I | LANDED | v0.31.38–62 | Per-core scheduler: selection, switch, wake, timer, idle, PIP, domain, CBS, invariant suite |
  | SM5.J | LANDED | v0.31.63→64 | WCRT under fine locks; **completion v0.31.64**: genuine per-core eventually-scheduled liveness (R5 trace model generalized ∀-core), execution-sensitive bridge, cycle-commensurate units |
  | SM5.K | LANDED | v0.31.63→64 | Tests + fixtures: 4-thread/4-core aggregate suite (+ multi-step dynamic simulation + cross-core round-trip), WCRT suite, golden trace fixture |
  | SM6.A | LANDED | v0.31.65→66 | Endpoint call across cores: `endpointCallOnCore` (receiver wake via SM5.C `wakeThread`, caller block via per-core `removeRunnableOnCore`) + lock-set correctness/membership/donation-extension/2PL-atomicity, cross-core wake SGI (Thm 3.2.1), per-core blocking, reply-state allocation, **full `ipcInvariantFull` preservation**, boot-core **+ per-core/∀-core (`lowEquivalent_smp`) NI**, WithCaps + donation + info-flow-checked dispatch. **v0.31.66: live `.call` LANDED** — `API.dispatchWithCap{,Checked}` routes through `endpointCallCrossCoreDispatch{,Checked}` (caller's core via `determineExecutingCore`), SMP dispatch stack promoted to production (staged 71→57). **v0.31.67: cross-core completion** — SGI-firing seam promoted (`SyscallDispatchEntry` + `PriorityInheritance.PerCore` + `Concurrency.Runtime`, staged 57→54), Rust flipped to `lean_syscall_dispatch_cross_core` (fires diff SGIs), `executingCore` threaded through `syscallDispatchFromAbi`/`syscallEntryChecked` (per-core caller-id), `.call` donation uses cross-core PIP (`propagatePipChainCrossCore`). PR #820 review #1/#2/#3/#5 closed. `tests/SmpCrossCoreCallSuite.lean` |
  | SM6.B | LANDED | v0.31.68→76 | Notification across cores + **bound notifications, LIVE**. `notificationSignalOnCore` (head waiter wake via SM5.C `wakeThread` to its home core, `.reschedule` SGI; signaller does not block) + `notificationWaitOnCore` (caller block via per-core `removeRunnableOnCore`). Theorems: SGI emission (`_remote_wake{,_preState}` + duals), multi-waiter discipline (`_wakes_head`+`_remaining_waiters`), 2PL atomicity, per-core wake locality, notification↔TCB binding lock-set membership, lock-set correctness + coherence (`notificationSignalWaiter?_eq_wake_head`), `ipcInvariant`/`objects.invExt` preservation, boot-core + per-core/∀-core (`lowEquivalent_smp`) NI of signal AND wait. **v0.31.70 bound notifications**: `Notification.boundTCB` field + `bind`/`unbindNotification` + `notificationSignalBound{,OnCore}` (bound-TCB-BlockedOnReceive delivery: dequeue from endpoint, deliver badge, cross-core wake) wired **LIVE** through `API`'s `.notificationSignal` arms via `notificationSignalBoundCrossCoreDispatch{,Checked}` (info-flow-checked); keystone moved to `PerCoreWake` to keep SM6.A `EndpointCallInvariant`/SM3 locks staged. Promoted to production (partition 57→55); trace byte-identical. `tests/SmpCrossCoreNotificationSuite.lean` (42 assertions). **v0.31.71 bind/unbind-notification syscalls**: `tcbBind/UnbindNotification` SyscallId (26/27) threaded through the full Lean ABI (encodings/`count` 26→28, `permittedKinds` + `lockSet_tcb{Bind,Unbind}Notification` + consistency + inventory 92→96, enforcement-boundary, dispatch arms, decoders) + the Rust `sele4n-types`/`sele4n-hal` mirrors + conformance; live via `API.dispatchCapabilityOnly`; trace fixture `[XVAL-002]` line updated (26→28 variants). **v0.31.72 audit closure**: the live cross-core wake now pokes the remote core — the diff-based SGI re-derivation `crossCoreSgiBody` (SM5.F.4) gated only on an effective-bucket change (PIP boost), so a wake (which leaves priority unchanged) re-derived no SGI and the remote thread waited for the next timer tick; it now also fires `.reschedule` for a thread newly runnable on a remote home core (`crossCoreSgiBody_remote_wake`), fixing SM6.A receivers + SM6.B waiters/bound TCBs (single-core inertness preserved). Hardening: badge-value pinning in the notification suite, SmpPipSuite wake-firing assertions, per-variant conformance roundtrips (98). **v0.31.73 PR-review remediation**: #2 signal/wait now carry `boundTCB := ntfn.boundTCB` (an ordinary signal no longer destroys a bound notification's binding); #3 the checked bound dispatch also gates `notification→receiver` (no badge leak to a low bound TCB); #4 `.notificationWait` routes per-core via `notificationWaitCrossCoreDispatch{,Checked}`; #5 `lockSet_notificationSignalBoundOnCore` covers the bound-delivery endpoint+TCB writes (`permittedKinds .notificationSignal` += `.endpoint`). **v0.31.74**: review #1 closed — `.tcbBindNotification` resolves the notification via a *capability* in the caller's CSpace (`msgRegs[0]` a CPtr through the verified `syscallLookupCap`), so a TCB-cap holder can no longer bind an arbitrary notification by raw ObjId; `unbindNotification` unchanged. **v0.31.75 tracked-debt closure**: single-core `notificationSignal`/`notificationWait` now also carry `boundTCB := ntfn.boundTCB` (dependent invariant proofs updated; trace byte-identical), and `SyscallDispatchSuite` gains a CSpace-with-caps `.tcbBindNotification` authority test (authorized bind / no-cap→`.invalidCapability` / read-only-cap→`.illegalAuthority`). **v0.31.76 deep-audit closure**: the bound-delivery 2PL footprint is now proven-covered (`lockSet_notificationSignalBoundOnCore_{endpoint,boundTcb}_write_mem` via the forward lemma `insertOrMerge_preserves_mem_of_ne`). Recorded proof-depth debt: bound-delivery non-interference (`endpointQueueRemoveDual` relinks the dequeued TCB's queue neighbours, so all-high NI needs a dual-queue endpoint-label invariant the codebase lacks; the covert channel is already prevented by the #3 flow gate). Closure target: `endpointQueueRemoveDual_preserves_projection{,OnCore}` → `notificationSignalBoundOnCore_delivery_path_NI{,_smp}`. |
  | SM6.C | LANDED | v0.31.77 | Reply path across cores + **live `.reply`/`.replyRecv` dispatch**.  `endpointReplyOnCore` (the unblocked caller — the recorded `blockedOnReply` thread — woken via SM5.C `wakeThread` on its *home* core with a `.reschedule` SGI; the replier does *not* block), `endpointReceiveDualOnCore` (the replyRecv receive leg: server blocked on *its own* core via `removeRunnableOnCore`, a `blockedOnSend` rendezvous sender woken on *its* home core), `endpointReplyRecvOnCore` (both legs, SGI union).  Theorems: cross-core wake SGI (`endpointReplyOnCore_remote_wake` + local/error duals), lock-set correctness (`endpointReplyOnCore_lockSet_correct` + `endpointReplyRecv_lockSet_correct` + state-resolved), payload delivery to the *right* TCB (`_perCore_delivery`), reply-state lifecycle (caller-TCB write lock `lockSet_endpointReply_target_tcb_write_mem`), reply-replay barrier + confused-deputy (`_replay_rejected` / `_not_blocked_eq` / `_wrong_replier_eq` — a delivered reply leaves the caller `.ready`, so replay fails closed), 2PL atomicity, per-core wake locality, `ipcInvariant`/`objects.invExt` preservation, boot-core + per-core/∀-core (`lowEquivalent_smp`) NI, donation-chain lock-set extension (`lockSet_endpointReply_donation_extension`) + cross-core return (`applyReplyDonationOnCore`, bootCore-bridged) + PIP reversion (`propagatePipChainCrossCore`), chain-length bound (`endpointReply_donation_chain_length_bounded`, ≤ fuel = objectIndex.length).  **Live**: `API.dispatchWithCap{,Checked}` `.reply` / `.replyRecv` arms route through `endpointReply{,Recv}CrossCoreDispatch{,Checked}` (executing core via `determineExecutingCore`); `EndpointReply` / `EndpointReplyInvariant` / `EndpointReplyDispatch` promoted to production (partition 55→56 staged, only `EndpointReplyNI` staged); the two `checkedDispatch_{reply,replyRecv}_eq_unchecked_when_allowed` equivalence theorems re-proven via the cross-core flow-allowed lemmas; trace byte-identical.  `tests/SmpCrossCoreReplySuite.lean` (27 assertions). |
  | SM6.D | LANDED | v0.32.58→59 | IPC across-core invariant bundle.  `ipcInvariantFull_perCore` (`IPC/Invariant/PerCoreBundle.lean`, production): the twenty-conjunct `ipcInvariantFull` restricted to per-core views — thread-subject conjuncts restricted to threads homed on core `c` (`threadHomeCore` = `cpuAffinity`.getD boot, provably the wake target: `determineTargetCore_eq_threadHomeCore`); shared-object clauses carried whole; `passiveServerIdle` via the SM4.D per-core form.  Exact decomposition `ipcInvariantFull_smp_iff_full_and_passive_smp` (∀-core bundle ↔ global + per-core passive slices); the four plan-named conjuncts (D.3–D.6: queue membership / NoDup / next-blocking / head-blocked) ship per-conjunct `_smp_iff` exactness + `_perCore_of_global` / `_of_forall_perCore` bridges; boot witness `default_ipcInvariantFull_smp`.  **SM6.D.2 preservation** (`PerCoreBundlePreservation.lean`, production): all six IPC ops (send/receive/call/reply+replyRecv/signal/wait) preserve every core's bundle view (`…_preserves_ipcInvariantFull_perCore` ×7) + the cross-core flagship `endpointCallOnCore_preserves_ipcInvariantFull_perCore` (staged with SM6.A) — nineteen conjuncts ride the single-core whole-bundle theorems through the bridges; the per-core passive slice rides the new `passiveServerIdleFrameOnCore` micro-frame family (SM4.B independence algebra, **no idle-core assumption**).  Axiom-clean.  Tests: `SmpCrossCoreCallSuite` §SM6.D (35 assertions) + Tier-3 anchors.  Note: the plan's "15 conjuncts" grew to 20 during the SM6.D reply-object hardening (v0.31.115→v0.32.57, findings A/D/E + the reply-fold); the 15-conjunct core is `ipcInvariantCore_of_smp`.  **v0.32.59 completion**: the OnCore proof-depth gap is CLOSED — production whole-bundle closures + per-core flagships for every cross-core transition: `notificationSignalOnCore`/`notificationWaitOnCore` (`NotificationInvariant.lean` §3–§6) and `endpointReplyOnCore`/`endpointReceiveDualOnCore`/`endpointReplyRecvOnCore` (`EndpointReplyInvariant.lean` §4–§11), all `…_preserves_ipcInvariantFull{,_perCore}` and unconditional over success/failure, via the new production transfer layer `IPC/Invariant/LookupCongruence.lean` (per-conjunct `…_of_getElem_eq` ×20 + `OffSchedulerAgrees` + step congruences) consumed by per-op agreement dichotomies (`…_post_agrees`); `endpointReplyRecvOnCore` closes **compositionally** (leg-wise `replyStashValid` fold reads; reply-leg transports `endpointReplyOnCore_tcb_backward`/`_endpoint_backward`/`_preserves_replyIdEstablishFresh`/`_reuse_freshens`) with a **disjunctive** `hReplyIdValid` covering seL4-MCS one-object reuse; the WithCaps trio behind the live `.send` (`endpointSendDualWithCaps`/`endpointReceiveDualWithCaps`/`endpointCallWithCaps`) gets `…_preserves_ipcInvariantFull_perCore` + `ipcUnwrapCaps_passiveServerIdleFrameOnCore` (`PerCoreBundlePreservation.lean` §6); boot-frame exactness `passiveServerIdleFrameOnCore_boot_iff` single-sources the D6 frame algebra.  Remaining tracked debt (plan §SM6.D scope note): bound-delivery whole-bundle (`endpointQueueRemoveDual` per-conjunct suite → `notificationSignalBoundOnCore_preserves_ipcInvariantFull{,_perCore}`) and `withLockSet` bundle carriage (`acquireLockOnObject/releaseLockOnObject_preserves_ipcInvariantFull` → `withLockSet_preserves_ipcInvariantFull_perCore`). |
  | SM6.E | LANDED | v0.32.60 | Cancellation across cores.  `descheduleThread` (the SM5.C `wakeThread` dual: home-core removal via `removeRunnableOnCore`, `.reschedule` SGI iff the victim was **actively current on a remote home core** — merely-queued victims need no poke, local victims reschedule synchronously, ghost-guard mirrored) + `cancelIpcBlockingOnCore` (the suspend pipeline's G2+G4+G7 slice across cores: the pure single-core teardown, then home-core deschedule + remote poke; reductions, SGI family, `objects.invExt` preservation) + per-core donation cancellation (`cancelBoundDonationOnCore` purges the SC's replenishments from the **victim's home core's** queue, fixing the single-core arm's `bootCoreId` hardcode; bootCore bridge is `rfl`; dispatcher `cancelDonationOnCore` returns the pre-state on error) — all **production** (`IPC/CrossCore/Cancellation.lean`, imported by `SeLe4n.lean`; staged partition unchanged at 56).  Lock-set migration (SM6.E.1/.3): `lockSet_cancelIpcBlocking` (victim TCB W + blocked-on endpoint/notification W + consumed Reply W) and `lockSet_cancelDonation` (victim TCB W + SC W + donated-owner TCB W), state-resolved forms, consistency vs `permittedKinds .tcbSuspend`, and member-by-member suspend-footprint coverage (`lockSet_tcbSuspend_*_write_mem` ×6).  **Footprint gap closed**: the SM6.D reply-fold's `reply.caller` write is now declared — `permittedKinds .tcbSuspend` += `.reply`, `lockSet_tcbSuspend` gains `consumedReplyId` (5 extensions, size 8 = `maxLockSetSize` exactly).  Atomicity (SM6.E.2/.4): `cancelIpcBlocking_atomic_under_lockSet` / `cancelDonation_atomic_under_lockSet` (exact plan names) + the OnCore companions.  Flagship `cancellation_cross_core_correct` (remote poke ∧ full home-core deschedule ∧ per-core locality ∧ object-level fidelity).  Single-core invExt surface: `cancelIpcBlocking`/`cancelDonation`(+arms)/`cleanupDonatedSchedContext`/`removeFromAll*`/`consumeReplyLink` `_preserves_objects_invExt` (`returnDonatedSchedContext_preserves_objects_invExt` de-privatised).  **v0.32.61 completion cut — the tracked debt closed or narrowed (plan §SM6.E completion record)**: (1) **live `.tcbSuspend` cross-core dispatch CLOSED** — `suspendThreadOnCore` (the complete per-core suspend, `resumeThreadOnCore`'s mirror: home-core G7-precapture, per-core donation arms, home-core removal, local `handleRescheduleSgiOnCore` / remote `.reschedule` SGI) is live behind `API.dispatchCapabilityOnly`'s `.tcbSuspend` arm (via `determineExecutingCore`); `crossCoreSgiBody` gained the **descheduled-current rule** (`crossCoreSgiBody_remote_deschedule` — the diff seam re-derives the victim's home-core poke; single-core inert), and the AN9-D Rust bracket flipped to the new FFI seam `suspend_thread_cross_core` (`suspendThreadCrossCoreEntry`, commit-then-fire); trace byte-identical, Rust HAL 724 green.  (2) **cancellation NI LANDED** (staged `CancellationNI`, staged-only 56→57): every SM6.E-new effect substantive (`descheduleThread_cancellation_NI{,_smp}`, ready-arm composite, ∀-core replenish/migration frames, donated-arm migration leg); the blocked-arm composites consume exactly the single-core teardown projection obligation the production closure form (AK6-F.18 G3) documents.  (3) **whole-bundle groundwork**: the `ipcInvariant` conjunct is CLOSED across the entire cancellation surface (fold keystone `RHTable.fold_preserves_of_lookup`, the state-correcting `notificationQueueWellFormed_filter_correct`, twelve single-core + five OnCore `_preserves_ipcInvariant` lemmas, transports `ipcInvariant_of_objects_eq`/`ipcInvariant_insert_*`); the remaining `ipcInvariantFull` conjuncts stay tracked with the per-key engine landed.  (4) **resolution frames CLOSED**: `cancelIpcBlocking_tcb_lookup`/`_getTcb?_none` → `_determineTargetCore_eq`/`_getTcb?_isSome_eq` → the invExt-only `cancelIpcBlockingOnCore_eq_descheduleThread_closed`.  Plus: observational atomicity (guarded observer layer `AcquireInsensitiveOn`/`lockSet_observer_atomic_on` in `LockSet2PL` §4c + the victim-`ipcState` capstone `cancelIpcBlockingOnCore_observer_atomic`), boot-instance bridges (`cancelIpcBlockingOnCore_bootHome_state_eq`, `cancelDonationOnCore_bootHome_{ok,error}`), the SM5.H corollaries (`descheduleThread_fully_descheduled`, `cancelBoundDonationOnCore_replenishments_purged`), the donated-arm §2b replenishment migration, and **two pre-existing single-core defect fixes** (the notification sweep's sole-waiter `.waiting`-with-`[]` invariant break, now state-correcting; `suspendThread`'s dead post-G4 G7 reschedule guard, now a G7-precapture).  **v0.32.62 PR-review cut (PR #831 P2 + root causes)**: a **third pre-existing single-core defect fixed** — `suspendThread` ran the PIP revert at the *victim before* the teardown cleared its `ipcState`, so each chain member's `pipBoost` recomputed with the victim still in `waitersOf` (a fixed-point no-op: a server retained the suspended victim's donated priority indefinitely); both suspend forms now use `timeoutThread`'s D4-N capture → clear → revert-from-server order, `suspendThreadOnCore` reverts via the SM5.F.4 cross-core walk (`propagatePipChainCrossCore` — per-home-core bucket migration, closing the suspend path's SM5.F per-core-PIP-migration gap), `suspendThreadCrossCoreEntry` fires the **diff-recovered** SGIs (`computeCrossCoreSgis`, exactly as the dispatch entry — the review's ask: re-bucketing pokes ride the diff), and the chain-walk obligation is declared (`pipChainStart_tcbSuspend`, SM3.B inventory 98 → 99 / chainStart 3 → 4, SM3.C contract amended for a non-static chain start).  **v0.32.63 (review 2)**: disinheritance **scheduling points** — a suspend deboosting a *still-current* server now (a) runs the gated **local** preemption point when the executing core's own current thread lost effective priority (`currentEffectivePrio?`/`currentDeboostedFrom` snapshot-recheck in both suspend forms; G7 factored into `suspendRescheduleOnCore` with arm-level SGI lemmas) and (b) pokes a **remote** core running the deboosted server via `crossCoreSgiBody`'s fourth rule (`crossCoreSgiBody_remote_deboost_current` — still-current + effective-priority drop; raises fire nothing; single-core inert).  **v0.32.64 (review 3)**: scheduler-lock footprint closure — `suspendThreadOnCoreSchedLockSet` gains the executing core (both run-queue write locks via the shared `sortedSchedCorePair` segment; ascending acquisition re-proven compositionally), the SM3.C.11 chain-walk contract now requires each step to hold the member's TCB write lock AND its home-core `SchedLockId.runQueue` write lock (the `updatePipBoostOnCore` re-bucketing is state-discovered; covers the `.call`/`.reply`/`.replyRecv` walks identically), and `candidateOutranksCurrentOnCore` is documented sound under `boundThreadPriorityConsistent` (the `_of_agree` bridge).  **v0.32.65 (review 4)**: **running-core suspend** — a fourth pre-existing defect class: an unbound victim (home = boot) still CURRENT on a secondary core (reachable by unbinding a running thread) was marked `.Inactive` while that core kept executing it; `runningCoreOf?` resolves the actual running core, `suspendThreadOnCore` deschedules + pokes IT (G4b + re-keyed G7), `crossCoreSgiBody`'s current rules re-keyed to the pre-state running core (inertness premises strengthened), and the sweeps are **write-set-honest** (insert-only-on-change; the splice's neighbour-TCB writes declared via `cancelSpliceNeighbors?` in the state-resolved footprint).  **v0.32.66 (audit closure)**: a three-auditor deep audit (conformance+vacuity / security / diff-seam+coverage) returned substantively-implemented, zero sorry/axiom, authority sound, fail-closed, no CVE-class findings; every surviving finding landed — the running-core run-queue lock in the suspend footprint (`sortedSchedCoreTriple`), the EDF **deadline** dimension in the diff rules (queued deadline change + weakened-current deadline-later fire), the `currentThreadUniqueAcrossCores` invariant slice (boot witness + deschedule preservation; full-surface adoption tracked), the AK6-F.18 G3 projection-sketch correction (the splice's neighbour queue-link writes ride the SM6.B endpoint-label debt), the donation-side observer capstone (`cancelDonationOnCore_observer_atomic`), doc/authority hardening (live-target header, `suspend_thread_cross_core` self-authorization obligation), and newly registered debt (`schedContextConfigure` boot-pinning).  `tests/SmpCancellationSuite.lean` (107 assertions, 17 scenario groups incl. §3.17 EDF/3-core; Tier-2 `smp_cancellation_suite` + Tier-3 anchors). |
  | SM6.F | LANDED | v0.32.67; depth cut v0.32.68 | Tests + fixtures — the SM6 closure phase.  `tests/SmpIpcSuite.lean` (`smp_ipc_suite`, **130 assertions / 14 groups** + golden-trace check): end-to-end pipelines composing the SM6.A/C transitions with the SM5 per-core scheduler (`handleRescheduleSgiOnCore` on the SGI's target core) — the **2-thread cross-core call/reply round trip** and the **4-thread SMP rendezvous** (both §8 acceptance-gate items closed), cross-core send/receive rendezvous, client-first ordering, the server `replyRecv` steady-state loop, fail-closed error paths, state-resolved 2PL footprints (exact size + WCRT-fits-1 ms-tick), live-dispatch coherence, plus (v0.32.68) the **SchedContext donation round trip** (`applyCallDonation`/`applyReplyDonationOnCore` + cross-core PIP), **capability transfer** (`ipcUnwrapCaps` grant-gated + `ipcMessageTooManyCaps`), **info-flow-checked dispatch** (call/reply `…CrossCoreDispatchChecked` allowed-vs-`.flowDenied`), the **live API path** (`dispatchSyscall{,Checked}` `.call`: CSpace cap resolution + authority gate + cross-core), **cancellation × IPC** (cancel a reply-blocked client ⇒ server's reply fails closed), and **scheduler contention** (a woken server does not preempt a higher-prio current).  `tests/SmpNotificationSuite.lean` (`smp_notification_suite`, **76 assertions / 10 groups**): wait→signal→SGI→dispatch round trip, multi-waiter home-core drain + badge isolation, `Badge.bor` accumulation + non-blocking consume, the **remote bound-TCB delivery** round trip, bind/unbind lifecycle, error paths, independence framing + footprints, plus (v0.32.68) the **three-waiter FIFO drain** (distinct home cores) and **checked dispatch** (wait-dispatch + the review-#3 notification→receiver badge-leak gate).  SM6.F.3 satisfied by SM6.E.6's `SmpCancellationSuite` (107 assertions / 17 groups).  `tests/fixtures/smp_ipc_4core.expected` (+`.sha256`): deterministic 16-line `[smp-ipc-4core]` golden trace computed from the live transition decisions, byte-for-byte verified in-suite, auto-gated by the Tier-2 companion walk.  `scripts/test_qemu_smp_ipc.sh`: Tier-4 QEMU `-smp 4` handshake exerciser (registered in `test_tier4_smp_bootcheck.sh`; SKIPs until the SM9.E bootable image exists, as its SM5 siblings).  Surface anchors: in-suite `#check` blocks + Tier-3 grep anchors (runners, Tier-2 wiring, fixture presence, lakefile registrations, QEMU registration). |
  | SM7.A | LANDED | v0.32.72 | TLB shootdown descriptor + per-core pending/ack state (all six sub-tasks; opens SM7 / SMP-C4 closure).  `Architecture/TlbShootdown.lean` (staged; SM7.B protocol transitions are the first runtime exerciser): `TlbShootdownDescriptor` (typed `TlbInvalidation` operand — one descriptor type covers the SM7.B.9–B.11 unmap/ASID-retire/full-flush callers — + initiating `CoreId`), `TlbShootdownState` (`pendingShootdowns : Vector (List …) numCores` + `shootdownAck : Vector Bool numCores`, SM4.B path-a accessors + `@[simp]` store/load algebra + `ext_perCore`; boot state quiescent), `enqueueShootdown` (FIFO tail-append, **fail-closed `none` at capacity** — a silently dropped descriptor is the SMP-C4 stale-TLB hazard; success ⟺ below-bound), `drainShootdowns` (whole-queue FIFO drain for the `.tlbShootdownReq` handler — the completeness half of Thm 3.3.1's remote case; exhaustive; deliberately ack-free so the runtime retires TLBIs before acknowledging), `acknowledgeShootdown` (monotone) + `beginShootdownRound` (initiator born-acknowledged, targets down — `_ackOnCore_iff`) + decidable `allAcked`/`shootdownQuiescent`/`pendingBounded`, `maxPendingPerCore = 16` with `…_preserves_pendingBounded` ×4, and the SM7.B.5 termination anchor `allCores_foldl_acknowledgeShootdown_allAcked`.  **Rust** (`shootdown.rs`, HAL 724→743 tests): `SHOOTDOWN_ACK` per-core cache-line-aligned `AtomicBool` (boots all-`true`), `ack_set` Release / `ack_is_set`+`all_acked` Acquire / `reset_for_round` Relaxed (publication via SM1.F.8 dsb-before-SGIR; cross-round hazard analysis in module docs), fail-closed bounds panics, `_in_slice` testable forms.  `tests/SmpTlbShootdownSuite.lean` (`smp_tlb_shootdown_suite`, the SM7.E.1 seed: 51 assertions / 7 groups incl. the 16-fill/17th-reject/drain-restores capacity walk + a full 4-core state-level round trip ending quiescent).  Staged partition 57→58.  **v0.32.73 completion cut — every v0.32.72 deferral closed**: (1) **SystemState mount** — `SystemState.tlbShootdown : TlbShootdownState := .initial` (the plan §4.1 "ConcurrencyState" placement realised the SM3.A.10 `objStoreLock` way) + `default_tlbShootdown_{initial,quiescent,pendingBounded}`; the pure `TlbInvalidation` operand module extracted from the staged `TlbiForSharing` (names unchanged) so `Model/State` stays FFI-free; `TlbShootdown` **promoted to production** (staged 58→57).  (2) **Round capstone** — `shootdownRound_restores_quiescent` (begin → per-target posting fold → per-target `completeShootdownOnCore` drain→ack composition ends quiescent, arbitrary initiator/targets, no Nodup) via the `foldl_completeShootdownOnCore_*` closed forms + `foldlM` posting frames.  (3) **Formal §4.1 capacity sufficiency** — `beginRound_foldlM_enqueueShootdown_isSome` + `foldlM_enqueueShootdown_isSome` close the serialised-round induction with the capstone.  (4) **Overflow escape hatch** — `enqueueShootdownOrCoalesce` (full queue collapses to one full-flush descriptor; total; `…_request_covered`; unconditional `…_preserves_pendingBounded`).  (5) **`ShootdownQueueLockId`** per-core queue-lock identifier with decidable total order (ascending-core acquisition vs concurrent different-VSpace initiators) — the SM7.B.7 seam.  (6) **FFI seam live** — Rust `ffi_shootdown_*` (u64-space checked, fail-closed) + `@[extern]` bindings + typed `CoreId` wrappers (`shootdownAckSet`/`shootdownAckIsSet`/`shootdownResetForRound`/`shootdownAllAcked`, `shootdownAck_ffi_core_in_range`); `shootdown.rs` conformance-pairing table + exhaustive 2⁴ `all_acked` test; HAL 743→750.  Suite 51→73 assertions / 11 groups; `TlbShootdownState` derives `DecidableEq`; TlbModel/State cross-refs; Staged.lean stale list → allowlist pointer; GitBook 12 proof-map entry.  **v0.32.74 audit cut (three-lane adversarial audit of PR #838)**: (1) **round-serialisation contract corrected** — the ack vector carries no round identity, so rounds must be serialised system-wide; the plan §3.2 VSpaceRoot-lock precondition is insufficient across distinct VSpaces (interleaved reset ⇒ early `allAcked` with a stale TLB live — the SMP-C4 hazard — plus a mutual-hang mode); the new fieldless provably-unique `ShootdownRoundLockId` (`_​singleton`) is the registered SM7.B.7 serialiser, all ten claim sites across Lean+Rust restate the contract, and the queue-lock order is re-documented as 2PL footprint + defense-in-depth (not exploitable today — SM7.B PENDING); (2) **coalescing coverage completed** — `enqueueShootdownOrCoalesce_pending_covered` (every previously queued descriptor pending or `.vmalle1`-superseded) closes the docstring's over-cite.  Everything else verified sound (vacuity probes, simp hygiene, orderings, FFI bounds, layout, test races, doc counts).  Suite 73→75; follow-up registered: crate-wide `@[extern]`↔`extern "C"` ABI conformance audit at SM9.E (pre-existing convention).  **v0.32.75 review-P1 cut (PR #838)**: offline cores stay acknowledged across a round — `reset_for_round` cleared all four `SHOOTDOWN_ACK` slots, but a partial-core boot (`smp_enabled=false` default, `smp_max_cores` caps, PSCI rejections) leaves cores that can never take the SGI and ack ⇒ `all_acked` unreachable, initiator hang.  Rust: `CORE_READY`-masked reset (`reset_for_round_in_slice_masked`; safety: every secondary bring-up runs `tlbi vmalle1` before MMU-enable, so late-onlined cores start with empty TLBs; HAL 750→755).  Lean: target-masked `beginShootdownRoundFor` (+`_ackOnCore_iff`/frames/`_allCores_eq` fully-online bridge) + the **hypothesis-free masked capstone** `shootdownRoundFor_restores_quiescent`.  SM7.B obligations extended: online-only target sets; no rounds concurrent with core bring-up.  Suite 75→81 / 12 groups. |
  | SM7.B | LANDED | v0.32.76 | Shootdown protocol — complete and LIVE.  `Architecture/TlbShootdownProtocol.lean` (production): invalidation-effect semantics on FFI encodings (`tlbEntryMatches` — the hardware's TLBI comparison, so `encodePageInvalidation`/`encodeAsidInvalidation` cover their entries unconditionally and collisions only over-invalidate), `tlbShootdownLocal` (B.1), `tlbShootdownBroadcast` (B.2: masked open + posting fold + exact `.tlbShootdownReq` SGI list; `_posts_singleton`/`_ack_iff`/frames/capacity) + the total coalescing form for the live wrappers (overflow collapses to a covered full flush), the `.tlbShootdownReq` handler transitions (B.3: drain/ack halves — TLB effect at the acknowledgment, so a set flag constructively means "view clean"; composed handler projects onto SM7.A `completeShootdownOnCore`; duplicate-SGI idempotent).  **Theorem 3.3.1 (B.8)**: `tlbShootdownBroadcast_invalidatesAllCores` over per-core views (`shootdownRoundViews` closed form via idempotence; non-vacuity bridge `handleTlbShootdownReqOnCore_applies_posted_op` + `tlbShootdownBroadcast_posts_singleton`) + the unmap instantiation + real-pipeline corollaries (`shootdownRound_tlb_no_matching_entry`, `_quiescent`, `_allAcked`).  `TlbShootdownWait.lean`: `shootdownAck_release_acquire` (B.4, vs the SM2.A model, concrete decide-checked witness), constructive `shootdown_wait_loop_terminates` (B.5, fold-max deadline witness), `shootdown_timeout_handling` (B.6, verdict exact both ways ⇒ the fail-closed panic fires only on a genuinely hung round; budget 540 000 ticks pinned both sides).  `TlbShootdownLockSet.lean` (B.7): cross-domain `TlbShootdownLockId` (object < round < queue, order suite, audit-contract edges as theorems), `lockSet_tlbShootdown_correct` (strictly ascending) + `_nodup` + footprint honesty vs the live diff (`lockSet_tlbShootdown_covers_commit`).  **Wiring (B.9–B.11)**: `.vspaceUnmap`/`.vspaceMap` arms → `vspaceUnmapPageWithShootdown`/`vspaceMapPageCheckedWithShootdownFromState` (caller's core via `determineExecutingCore`; WS-K-D delegation theorems + enforcement registry updated); `tlbFlushBy{ASID,Page}WithShootdown`; `asidAllocateWithShootdown` — the previously-missing `requiresFlush` consumer (B.10); `lifecycleRetypeDirectWithCleanupShootdown` (B.11, live) closes a genuine gap: retyping a live VSpaceRoot performed NO TLB maintenance — now the dead ASID is flushed locally + `.aside1` round posted (non-VSpaceRoot retypes provably unchanged).  B.12: `tlbShootdown_outer_correct` (state-identical under `.outer`) + the entry domain `rfl`-pinned to RPi5.  **Live seam**: `SyscallDispatchEntry.completeShootdownRounds` — diff-recovered round (`shootdownChangedTargets`/`shootdownPostedOps`) under THE global round lock (the CAS try-lock `SHOOTDOWN_ROUND_LOCK`, acquired cooperatively — the SM7.A audit obligation discharged; a lock-waiter services its own pending obligation between retries): masked reset, SGIs at online targets only (SM7.A P1), `tlbiForSharing` local broadcast, bounded wait (timeout ⇒ fail-closed panic), handler catch-up commit restoring quiescence; `TlbiForSharing` promoted to production (staged 57 → 56).  **Rust (HAL 755 → 769, clippy-clean)**: round lock, `wait_all_acked_bounded` (deadline-exact; spin + handler `sev` — a bare `wfe` could sleep past the timeout), the `.tlbShootdownReq` handler (local `tlbi vmalle1` → release `ack_set` → `sev`; fail-closed no-ack on bad core id) registered at boot, `online_mask`; trap layer routes SGIs via the new `gic::dispatch_irq_with_iar` — closing the SM1.F deferred-dispatch note with genuine `source_cpu` AND fixing a pre-existing GICv2 defect (SGI `GICC_EOIR` writes must echo the IAR source-CPU field per GIC-400 TRM §4.4.5; the masked EOI would have stranded per-source SGI instances active — lost wakeups — on any multi-core build).  Trace byte-identical.  `tests/SmpTlbShootdownSuite.lean` 81 → 150 assertions / 20 groups (§4.1–§4.8 incl. Theorem 3.3.1 computed over per-core views and the live map→unmap→shootdown pipeline).    **v0.32.77 completion cut — every landing deferral closed**: (1) **invariant-bundle carriage** — `pendingBounded st.tlbShootdown` is the **12th `proofLayerInvariantBundle` conjunct** (boot witness `default_tlbShootdown_pendingBounded`; the three adapter preservation proofs extended; Boot general bridge via the new `bootFromPlatform_tlbShootdown_eq`; freeze wholesale), proven through every live shootdown-aware transition (`…_preserves_pendingBounded` ×9) on a new `…_tlbShootdown_eq` frame family spanning the retype-cleanup pipeline + VSpace base ops.  (2) **Handler commutativity** (`completeShootdownOnCore_comm` / `handleTlbShootdownReqOnCore_comm` via the retire-filter algebra + fold swap) — catch-up visit order is a convention.  (3) **Coalescing capstones**: `coalescingRound_restores_quiescent`/`_allAcked` (the round the runtime actually runs), the positive diff characterization `shootdownChangedTargets_coalescing_of_quiescent`, and the total-posting remote case of Thm 3.3.1 (`vspaceUnmapPageWithShootdown_remote_retire_removes`).  (4) **Remap-only map rounds + model fact**: the `.vspaceMap` wrapper posts only on remap (`vspaceHasTranslation`; `_fresh_inert`), and `vspaceMapPageCheckedWithFlushFromState_ok_fresh` pins that a successful map is ALWAYS fresh (`mapPage` rejects occupied vaddrs) ⇒ `…_never_posts` today (the round rides the unmap of unmap-then-map; the posting branch stays as a defense-in-depth seam).  (5) **Least-index wait** (`waitAllAckedBounded_least`, constructive `shootdown_wait_loop_terminates_least`) + **round-lock CAS model** (success-iff-free/mutex/release-liveness matching the Rust `compare_exchange`) + the cross-round publication chain `shootdownRoundLock_release_acquire` (+ witness) + the 4-core multi-pair B.4 witness.  (6) **Entry hardening**: named `shootdownRoundLockAcquireFuel`, `completeShootdownRounds_nil` (rfl), one `CORE_READY` snapshot per round (`shootdownOnlineMask`/`coreOnlineInMask`), the vmalle1-dominance `collapseShootdownOps` (effect-exact), `shootdownSharingDomain` DERIVED from `PlatformBinding.sharingDomain` (B.12 binding read), and the cooperative self-service arm flipped to the LOCAL `tlbi vmalle1` (`tlbiLocalFullFlush`).  (7) **storeObject sweep**: one further production retype entry owed TLB work — closed by `lifecycleRetypeWithCleanupShootdown` (the CSpaceAddr sibling, full theorem trio).  (8) **Typed-flush bridge** (`mem_adapterFlushTlbBy{VAddr,Asid}_of_…` — encoded ⊇ typed).  (9) **Test hardening**: Rust handler `_in` slice form with GENUINE false→true ack tests (prior global-vector assertions were vacuous), `round_lock_try_acquire_in` + 8-thread CAS mutex stress (HAL 769 → 772); suite §4.9 + §4.10 (live `.vspaceUnmap` through `dispatchSyscall`: CSpace + authority + posting + fail-closed) — 22 groups / 160 runtime assertions; SM7.E.2 seeded (`scripts/test_qemu_smp_shootdown.sh`, Tier-4-registered, SKIPs until SM9.E); legacy Rust `dispatch_irq` deprecated (masked-EOI form).  Tracked debt registered in plan §SM7.B completion cut (per-descriptor handler TLBIs, handler formal refinement at SM9.E, B.10 syscall reachability, step-4d direct-ack, SM7.C.6).  **v0.32.78 debt-closure cut**: every SM7.B tracked-debt item CLOSED or narrowed to a precisely-scoped residual.  **(1) Per-descriptor handler TLBIs (CLOSED)**: the `.tlbShootdownReq` handler retires the round's EXACT operands locally (one `tlbi` per descriptor via `tlb::tlbi_local`) instead of a blanket `vmalle1`, matching the Lean `handleTlbShootdownReqOnCore` per-descriptor effect — the initiator publishes the collapsed operands (under the round lock, before the SGIs; `dsb ish` orders it ahead) into a seqlock-guarded `ShootdownOpMailbox`, and the handler retires a stable snapshot per-descriptor, falling back to local `vmalle1` on ANY torn read / empty round / overflow / undecodable operand (over-invalidation-safe, never under-invalidates); `publishShootdownOps` live seam + `ffiShootdownPublish{Begin,Slot,Commit}` FFI + wrappers; HAL 772 → 780 (round-trip / torn-fallback / overflow-collapse / per-descriptor-count / op-tag conformance tests); trace byte-identical.  **(2) Formal refinement (NARROWED)**: the handler now refines the Lean TLB effect operand-for-operand (was ⊇ full flush); op-tag decode pinned identical both sides (`decode_tlb_invalidation` ↔ `TlbInvalidation.toOpTag`); residual is only the SM9.E linked-runtime proof.  **(3) B.10 (deferred, NO safety gap)**: `asidAllocateWithShootdown` is complete + proven but user-unreachable; audit confirms no runtime ASID-reuse path exists (`lifecycleRetype` makes fresh ASID-0 roots; `asidTable` is boot-only) — a completeness gap, not a safety hole; closure target SM8 (ASIDControl/ASIDPool object family + assign syscall).  **(4) Step-4d direct-ack (CLOSED by design)**: under the B.6 spin wait + IRQs-masked SVC path a direct-ack SGI cannot preempt the initiator nor add information the acquire-poll already reads — won't-implement.  **(5) withLockSet carriage (shootdown slice CLOSED)**: the 2PL bracket frames `tlbShootdown` (`withLockSet_tlbShootdown_eq`) ⇒ `withLockSet_preserves_pendingBounded` carries the 12th bundle conjunct; the twenty-conjunct `ipcInvariantFull` generalisation stays with SM6.D.  **(6) Host-test starvation (CLOSED)**: the yields already exist (every FIFO spin routes through `cpu::wfe()`'s `#[cfg(test)]` `yield_now`, SM2.E) and the authoritative `test_rust.sh` builds before testing, so the compile-contention window is absent from the real flow (an ad-hoc combined `cargo test --workspace` artifact); the round-lock mutex-stress test now caps contenders at `available_parallelism()`.  Suite 160 → 165 assertions (§4.11 op-encoding conformance + withLockSet carriage); Tier-3 anchors + conformance-pairing table extended.  Residual debt: SM7.C.6 (per-core restatement, with the SM7.C mount) and the SM9.E linked-runtime refinement.  **v0.32.79 PR #839 review-P1 cut**: (1) **shootdown targets now keyed on IRQ-readiness, not the release handshake — real bug fix.**  `reset_for_round`/`online_mask` read `smp::CORE_READY` (set by the primary the instant `CPU_ON` succeeds — before the secondary inits its GIC / arms its timer / unmasks IRQs), so a round during bring-up (or targeting a timer-init-failed core wedged in the fatal WFE loop with `CORE_READY` still true) reset that core's ack and waited for an SGI it could not service → the SM7.B.6 10 ms fail-closed panic (the timer-dead variant wedged *every* future round); fixed by a separate `smp::CORE_IRQ_READY` flag the secondary publishes itself after `enable_irq`, read by both masks via the shared `irq_ready_online()` snapshot (boot core born true; excluding a not-IRQ-ready core is safe — it holds no invalidatable TLB entry).  Lean is FFI-backed so only docstring prose changed; HAL 780 → 782.  (2) **posting/catch-up round-lock serialisation — TRACKED DEBT (model-fidelity, not a hardware hazard).**  The model posting + catch-up are not under `SHOOTDOWN_ROUND_LOCK` (which serialises only the hardware round), so concurrent rounds' catch-up folds can cross-drain the model pending queues; but each round's hardware TLB maintenance rides its own `(pre,post)` diff + SGIs + blocking `SHOOTDOWN_ACK` wait, and model quiescence gates only `pendingBounded` bookkeeping (idempotent over-application, never under-invalidation) — documented at the `completeShootdownRounds` site; closure target round-generation-tagged descriptors (a verified-model-type change, scoped to the SM7.C mount). |
  | SM7.C | LANDED | v0.32.80; operative cut v0.32.81 | Per-core TLB model — mounted + wired to the shootdown protocol.  New production module `Architecture/PerCoreTlbModel.lean` (imports `TlbModel` + `TlbShootdownProtocol`; in `SeLe4n.lean`).  **SM7.C.1**: `SystemState.perCoreTlb : Vector TlbState numCores := Vector.replicate numCores TlbState.empty` — the SMP generalisation of the scalar boot-core `tlb` (added **alongside** it, not a rewrite: the scalar stays the pre-SMP single-core layer, `perCoreTlb` is the SMP model the SM7.B protocol drives; both cohere empty at boot).  SM4.B path-a accessors `tlbOnCore`/`setTlbOnCore` + `@[simp]` store/load algebra + frame lemmas + `default_{perCoreTlb,tlbOnCore}`.  Carriage: freeze (`FrozenSystemState.perCoreTlb` + `freeze_preserves_perCoreTlb := rfl` guard + the `apiInvariantBundle_frozenDirectFull` conjunct), congruence (`OffSchedulerAgrees.perCoreTlb` + all six builders), boot frames (`applyMachineConfig`/`foldIrqs`/`foldObjects`/`bootFromPlatform_perCoreTlb_eq`).  **SM7.C.2** `tlbInsertOnCore` (HW walker fills one core; leaves others empty — the SMP asymmetry).  **SM7.C.3** `tlbInvalidateOnCore` (local invalidation reaches exactly this core; leaves others stale — the precise SMP hazard).  **SM7.C.4** `tlbInvalidateOnAllCores` (runs `tlbShootdownBroadcast` — posting to `tlbShootdown` — **and** evolves every view via the protocol's `shootdownRoundViews`, so `perCoreTlb` is a genuine consumer of the shootdown state machine, not a parallel structure).  **SM7.C.5** `tlbInvalidationConsistent_perCore` (∀ core, its view matches the page tables) — **the 13th `proofLayerInvariantBundle` conjunct**, generalising the 9th (`tlbConsistent st st.tlb`); threaded exactly like SM7.B's 12th (`pendingBounded`): boot witness `default_tlbInvalidationConsistent_perCore`, definitional transport through the three adapter preservation proofs (which touch only machine, and — for the context switch — scheduler.current, none of which the conjunct reads), the Boot general bridge, freeze wholesale.  **SM7.C.6** `tlbShootdown_invalidates_perCore` — Theorem 3.3.1 (`tlbShootdownBroadcast_invalidatesAllCores`) mounted: after a covering `tlbInvalidateOnAllCores` no core retains any covered entry (the SMP-C4 use-after-unmap closure).  **SM7.C.7** `tlbConsistency_cross_subsystem` — the memory-subsystem capstone (protocol × TLB-model × page-tables): a covering invalidation both removes every stale entry on every core AND preserves per-core consistency.  Information flow: `perCoreTlb` kept **out** of `projectState` (a TLB view is a covert timing channel, like `machine.timer`).  `tests/SmpTlbShootdownSuite.lean` §1 (49 `#check` anchors — the 30 at the v0.32.80 landing plus the operative-cut/completeness/NI symbols), §2 (elaboration witnesses), §5.1–§5.2 (15 runtime assertions — local-op SMP hazard + the cross-core Theorem-3.3.1 round).  Round-generation-tagged descriptors (the SM7.B v0.32.79 model-fidelity debt) remains a separately-scoped follow-on (a `TlbShootdownState` descriptor-type change orthogonal to the per-core view model; no hardware hazard).  **v0.32.81 completion cut — the model made operative on the live path**: v0.32.80 landed `perCoreTlb` as a parallel spec (the view function `shootdownRoundViews` took its arguments free-standing); the field now evolves by the round's **real per-descriptor drain**.  New operational handler `handleTlbShootdownReqOnCorePerCore` (the SM7.B single-view handler `handleTlbShootdownReqOnCore` **and** a retire of the *same* drained operands on core `c`'s own view; `_tlb_eq`/`_tlbShootdown_eq` = trace-safety anchors, `_applies_posted_op` = non-vacuity bridge to the abstract step, `_subset`/`_frame`/`_preserves_tlbInvalidationConsistent_perCore`).  **Live seam wired**: `SyscallDispatchEntry.completeShootdownRounds`'s catch-up fold swapped `handleTlbShootdownReqOnCore` → `handleTlbShootdownReqOnCorePerCore` — **trace byte-identical** (the per-core handler's `tlb`/`tlbShootdown` effects are *definitionally* the single-view's; `foldl_handleTlbShootdownReqOnCorePerCore_agrees` proves the two folds agree on those fields; only the projection-invisible `perCoreTlb` additionally evolves).  **Operative Theorem 3.3.1**: `shootdownRoundPerCore` (the round the live seam runs) + `shootdownRoundPerCore_perCoreTlb` (its real-drain `perCoreTlb` **equals** `shootdownRoundViews`) + `shootdownRoundPerCore_tlb_eq` (the A4 bridge: per-core round's `tlb`/`tlbShootdown` = single-view `shootdownRound`'s for **every** round, so the two models agree on the boot-visible view always) + `_invalidates_perCore` (Theorem 3.3.1 realised on the mounted field by the real drain) + `_frame`/`_preserves_tlbInvalidationConsistent_perCore`.  The scalar `tlb` stays the pre-SMP single-view (all-cores-conflated) model, `perCoreTlb` its per-core refinement — deliberately *not* pointwise-equal, related by `_tlb_eq`.  Completeness: `tlbInsertOnCore_preserves_tlbInvalidationConsistent_perCore` (the insert side of the 13th conjunct), `tlbInvalidateOnAllCoresCoalescing` (overflow-safe broadcast), computable `tlbConsistentCheck`/`tlbInvalidationConsistentCheck_perCore` + `_iff` + `Decidable` instances.  Hardening: `FrozenSystemState.perCoreTlb` now **required** (silent drop = compile error; six frozen test literals updated), `perCoreTlb_write_preserves_projection` (explicit NI witness), dead `perCoreTlb_vector_ext` removed.  Tests: suite §5.3 (operational round + bridge + coalescing + decidable checker); §1 anchors + Tier-3 anchors extended. |
  | SM7.D–E, SM8–SM9 | PENDING | — | Cache broadcast + shootdown tests (SM7.E.2–E.6), info-flow, release closure (→ v1.0.0) |

  **Plans**: master overview at
  [`docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md`](docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md);
  per-phase plans at `docs/planning/SMP_*.md`.

  **Key AK7 metrics at v0.32.77**: `RAW_MATCH_TOTAL` 133,
  `RAW_LOOKUP_TID` 1310, `GETTCB_ADOPTION` 2113,
  `GETSCHEDCTX_ADOPTION` 285 (re-anchored for the SM7.B completion cut —
  the single `RAW_LOOKUP_TID` increment is the additive frame-lemma proof
  `returnDonatedSchedContext_tlbShootdown_eq`, which cases on the same
  `objects[scId.toObjId]?` scrutinee its subject matches on — a raw-store
  *characterisation* proof, no new live raw read.  Prior anchor v0.32.61
  for the SM6.E completion cut —
  additive raw-store *characterisation* lemmas: the per-key TCB frames
  (`spliceOutMidQueueNode_tcb_lookup`, the sweeps' `_tcb_lookup`/`_no_tcb`
  families) and the `ipcInvariant` transports state facts ABOUT
  `objects[….toObjId]?`, the same class as `getTcb?_eq_some_iff`; every
  raw-match count is unchanged and the live `suspendThreadOnCore` reads
  exclusively through `getTcb?`.  Prior anchor v0.31.64 (SM5.J.4 per-core R5
  generalisation).  See `docs/dev_history/audits/AL0_baseline.txt`).

  **Rust HAL at v0.32.79**: 782 tests, zero clippy warnings,
  zero `#[ignore]`'d.

  **Staged modules**: 56 staged-only (via `Platform/Staged.lean` +
  `scripts/staged_module_allowlist.txt`); production/staged partition
  gate enforced by `scripts/check_production_staging_partition.sh`.  (SM6.C
  added `EndpointReplyNI` staged and promoted the cross-core reply transition /
  invariant / dispatch trio to production.)  (SM6.E's completion cut added
  `CancellationNI` staged.)  (SM7.A added `Architecture.TlbShootdown`
  staged; its v0.32.73 completion cut promoted it to production —
  `Model/State.lean` mounts it as `SystemState.tlbShootdown` — alongside
  the new pure production `Architecture.TlbInvalidation` operand module
  extracted from `TlbiForSharing`.)  (SM7.B promoted `TlbiForSharing`
  itself to production — the live `completeShootdownRounds` seam is its
  first runtime exerciser, closing the SM1.E "staged until SM7" note —
  and added the three production protocol modules
  `TlbShootdownProtocol` / `TlbShootdownWait` / `TlbShootdownLockSet`;
  staged 57 → 56.)  (SM7.C added the production module
  `Architecture.PerCoreTlbModel` — the per-core TLB model over the new
  `SystemState.perCoreTlb` field, whose `tlbInvalidationConsistent_perCore`
  is the 13th `proofLayerInvariantBundle` conjunct; staged count unchanged
  at 56.)

  **SM3.C.9 deferral**: migrating every `@[export]` body to wrap its
  transition in `withLockSet` requires the per-core kernel-state seam
  SM5 introduces; tracked as SM5.I follow-on.

  **SM6.A cross-core `.call` — COMPLETE (v0.31.66 live dispatch → v0.31.67
  multi-core completion)**: the live `.call` syscall routes through the cross-core
  dispatch and the multi-core path is complete.  `API.dispatchWithCap{,Checked}`'s
  `.call` arm calls `endpointCallCrossCoreDispatch{,Checked}` (below-API
  `EndpointCallDispatch`): the receiver is woken on its *home* core; the caller is
  descheduled on its *own* core (`determineExecutingCore`); the donated-priority
  boost propagates via the cross-core chain walk `propagatePipChainCrossCore`
  (FFI-free `Propagate`), migrating each boosted server's bucket on its home core.
  The **SGI-firing seam is production** (v0.31.67): `SyscallDispatchEntry`
  (`@[export lean_syscall_dispatch_cross_core]`) + its closure
  (`PriorityInheritance.PerCore`, `Concurrency.Runtime`) are in the `SeLe4n.lean`
  library (staged-only 71 → 57 → **54**), and the Rust `svc_dispatch` extern is
  flipped to it — the live syscall commits the verified post-state then fires the
  diff-recovered cross-core `.reschedule` SGIs (single-core-inert).  **Per-core
  caller identification** (v0.31.67): `syscallDispatchFromAbi` / `syscallEntryChecked`
  take an explicit `executingCore` and read `currentOnCore executingCore`;
  `syscallDispatchCrossCoreEntry` threads the hardware `currentCoreId`,
  `syscallDispatchInner` passes `bootCoreId` (boot-pinned, unchanged); the five
  `syscallDispatchFromAbi_*` bridges are generalised to an arbitrary core.
  Validated: trace byte-identical, all `.call` + SMP suites pass, partition (54) +
  AK7 + Rust HAL (724) green.  PR #820 review comments #1/#2/#3/#5 all closed (#4
  — the vestigial 2-arg `lean_endpoint_call_cross_core` export — is the remaining
  cleanup item, superseded by the full-context `syscallDispatchCrossCoreEntry`).

  **SM4.C.11 tracked debt**: per-core Liveness forms
  (`Scheduler/Liveness/*.lean`) remain bootCoreId-pinned; migration
  deferred to the Scheduler-subsystem scope, not SM4.D.

- **WS-RC remediation workstream CLOSED (v0.30.11 → v0.31.2)**:
  R0–R5 landed; R6–R14 absorbed into WS-SM per SM0.Q merge.
  Plan: [`docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md`](docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md).

- **WS-AN portfolio COMPLETE (v0.30.11)**:
  12 phases (AN0–AN12) landed. Archived to
  [`docs/CLAUDE_HISTORY.md`](docs/CLAUDE_HISTORY.md).

- **Older workstreams (WS-AK through WS-AA)**: archived to
  [`docs/CLAUDE_HISTORY.md`](docs/CLAUDE_HISTORY.md). Canonical
  per-phase record:
  [`docs/WORKSTREAM_HISTORY.md`](docs/WORKSTREAM_HISTORY.md) +
  [`CHANGELOG.md`](CHANGELOG.md).

  **Canonical detailed history**: per-sub-task landing notes, audit-pass
  refinements, and per-phase closeout details live in
  [`docs/WORKSTREAM_HISTORY.md`](docs/WORKSTREAM_HISTORY.md),
  [`CHANGELOG.md`](CHANGELOG.md), and
  [`docs/CLAUDE_HISTORY.md`](docs/CLAUDE_HISTORY.md) — not in this file.

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
