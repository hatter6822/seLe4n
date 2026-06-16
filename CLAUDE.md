# CLAUDE.md — seLe4n project guidance

> A mirror of this file lives at `AGENTS.md` so that non-Claude coding
> agents (and any tool that follows the AGENTS.md convention) get the
> same project rules. If you edit one, edit the other in the same PR —
> the two files must stay byte-identical apart from this header.

## What this project is

seLe4n is a production-oriented microkernel written in Lean 4 with machine-checked
proofs, improving on seL4 architecture. Every kernel transition is an executable
pure function with zero `sorry`/`axiom`. First hardware target: Raspberry Pi 5.
Lean 4.28.0 toolchain, Lake build system, version 0.31.99.

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
- `CHANGELOG.md` (~24758 lines)
- `docs/WORKSTREAM_HISTORY.md` (~8436 lines)
- `SeLe4n/Kernel/Concurrency/Locks/RwLock.lean` (~6631 lines)
- `docs/dev_history/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md` (~4721 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~4154 lines)
- `docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md` (~4130 lines)
- `tests/NegativeStateSuite.lean` (~4017 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` (~3906 lines)
- `docs/spec/SELE4N_SPEC.md` (~3806 lines)
- `SeLe4n/Kernel/CrossSubsystem.lean` (~3392 lines)
- `docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md` (~3388 lines)
- `SeLe4n/Platform/Boot.lean` (~3234 lines)
- `SeLe4n/Testing/MainTraceHarness.lean` (~3175 lines)
- `docs/dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md` (~3140 lines)
- `docs/dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md` (~3134 lines)
- `docs/gitbook/12-proof-and-invariant-map.md` (~3057 lines)
- `docs/planning/SMP_RUST_HAL_PLAN.md` (~3014 lines)
- `SeLe4n/Model/Object/Structures.lean` (~3006 lines)
- `SeLe4n/Model/State.lean` (~2949 lines)
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean` (~2673 lines)
- `SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean` (~2505 lines)
- `docs/dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md` (~2476 lines)
- `docs/dev_history/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md` (~2472 lines)
- `SeLe4n/Kernel/API.lean` (~2396 lines)
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` (~2369 lines)
- `docs/dev_history/audits/AUDIT_v0.25.14_WORKSTREAM_PLAN.md` (~2340 lines)
- `docs/dev_history/audits/AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md` (~2339 lines)
- `docs/audits/AUDIT_v0.30.11_DEEP_VERIFICATION.md` (~2326 lines)
- `tests/OperationChainSuite.lean` (~2201 lines)
- `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean` (~2187 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreCbs.lean` (~2178 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean` (~2103 lines)
- `docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md` (~2073 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/DualQueueMembership.lean` (~2065 lines)
- `tests/ModelIntegritySuite.lean` (~2052 lines)
- `docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md` (~2022 lines)
- `SeLe4n/Prelude.lean` (~1992 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/StoreObjectFrame.lean` (~1985 lines)
- `docs/dev_history/planning/V3_PROOF_CHAIN_HARDENING_E_G6_PLAN.md` (~1966 lines)
- `docs/dev_history/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md` (~1917 lines)
- `SeLe4n/Kernel/Concurrency/Locks/TicketLock.lean` (~1901 lines)
- `SeLe4n/Model/Object/Types.lean` (~1896 lines)
- `docs/dev_history/planning/V3E_IPC_UNWRAP_CAPS_LOOP_COMPOSITION_PLAN.md` (~1891 lines)
- `docs/dev_history/audits/AUDIT_v0.30.6_COMPREHENSIVE.md` (~1889 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/PerOperation.lean` (~1885 lines)
- `SeLe4n/Kernel/Capability/Operations.lean` (~1868 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/QueueNextTransport.lean` (~1860 lines)
- `SeLe4n/Kernel/Concurrency/Locks/Serializability.lean` (~1857 lines)
- `SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean` (~1812 lines)
- `docs/dev_history/audits/AUDIT_v0.27.6_WORKSTREAM_PLAN.md` (~1801 lines)
- `docs/dev_history/audits/AUDIT_v0.25.21_WORKSTREAM_PLAN.md` (~1800 lines)
- `SeLe4n/Kernel/IPC/Invariant/QueueMembership.lean` (~1792 lines)
- `SeLe4n/Model/FreezeProofs.lean` (~1792 lines)
- `docs/dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md` (~1776 lines)
- `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` (~1754 lines)
- `docs/dev_history/audits/AUDIT_v0.25.14_COMPREHENSIVE.md` (~1739 lines)
- `docs/dev_history/audits/WORKSTREAM_PLAN_WS_O_SYSCALL_RUST_WRAPPERS.md` (~1725 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Core.lean` (~1687 lines)
- `docs/dev_history/AUDIT_v0.22.10_WORKSTREAM_PLAN.md` (~1674 lines)
- `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean` (~1670 lines)
- `docs/planning/SMP_FOUNDATIONS_PLAN.md` (~1665 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreChooseThread.lean` (~1652 lines)
- `tests/InformationFlowSuite.lean` (~1638 lines)
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` (~1622 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreWake.lean` (~1558 lines)
- `SeLe4n/Kernel/Architecture/Invariant.lean` (~1529 lines)
- `SeLe4n/Kernel/Scheduler/PriorityInheritance/PerCore.lean` (~1488 lines)
- `docs/dev_history/audits/AUDIT_v0.28.0_WORKSTREAM_PLAN.md` (~1480 lines)
- `docs/dev_history/planning/V3B_LOAD_FACTOR_BOUNDED_MIGRATION_PLAN.md` (~1457 lines)
- `docs/dev_history/audits/AUDIT_v0.25.3_WORKSTREAM_PLAN.md` (~1452 lines)
- `docs/dev_history/audits/WS_RC_R5_DEFERRED_COMPLETION_PLAN.md` (~1414 lines)
- `docs/dev_history/AUDIT_v0.23.21_WORKSTREAM_PLAN.md` (~1411 lines)
- `docs/dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md` (~1382 lines)
- `docs/dev_history/audits/AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md` (~1357 lines)
- `docs/dev_history/audits/AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md` (~1342 lines)
- `docs/planning/SMP_PANIC_HANG_REMEDIATION_PLAN.md` (~1342 lines)
- `tests/LockSetSuite.lean` (~1309 lines)
- `SeLe4n/Platform/FFI.lean` (~1306 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreDomain.lean` (~1267 lines)
- `docs/dev_history/audits/AUDIT_v0.22.17_WORKSTREAM_PLAN.md` (~1252 lines)
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean` (~1244 lines)
- `docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md` (~1237 lines)
- `SeLe4n/Kernel/Scheduler/Invariant.lean` (~1213 lines)
- `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` (~1209 lines)
- `SeLe4n/Kernel/Scheduler/Invariant/PerCorePreservation.lean` (~1200 lines)
- `SeLe4n/Kernel/Concurrency/Locks/DynamicChainExtension.lean` (~1185 lines)
- `SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean` (~1183 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` (~1181 lines)
- `docs/dev_history/audits/AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md` (~1178 lines)
- `docs/planning/SMP_PER_CORE_STATE_PLAN.md` (~1172 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` (~1162 lines)
- `SeLe4n/Platform/DeviceTree.lean` (~1154 lines)
- `SeLe4n/Platform/RPi5/MmioAdapter.lean` (~1153 lines)
- `tests/KernelErrorMatrixSuite.lean` (~1139 lines)
- `SeLe4n/Kernel/RobinHood/Bridge.lean` (~1111 lines)
- `docs/planning/WS_RC_R4_TYPE_LEVEL_PROMOTION_PLAN.md` (~1111 lines)
- `tests/PerObjectLockSuite.lean` (~1097 lines)
- `docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md` (~1071 lines)
- `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean` (~1043 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean` (~1034 lines)
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean` (~1032 lines)
- `SeLe4n/Kernel/InformationFlow/Policy.lean` (~1023 lines)
- `SeLe4n/Kernel/Scheduler/RunQueue.lean` (~1023 lines)
- `SeLe4n/Kernel/FrozenOps/Operations.lean` (~1005 lines)
- `docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md` (~987 lines)
- `docs/dev_history/audits/AUDIT_v0.19.6_WORKSTREAM_PLAN.md` (~984 lines)
- `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean` (~983 lines)
- `SeLe4n/Machine.lean` (~977 lines)
- `docs/dev_history/planning/WS_X_LEAN_ETHEREUM_FORMALIZATION_PLAN.md` (~958 lines)
- `SeLe4n/Kernel/Concurrency/Locks/RwLockRefinement.lean` (~943 lines)
- `SeLe4n/Kernel/Concurrency/MemoryModel.lean` (~935 lines)
- `docs/dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md` (~930 lines)
- `tests/SmpFoundationsSuite.lean` (~928 lines)
- `docs/dev_history/audits/AUDIT_v0.28.0_COMPREHENSIVE.md` (~921 lines)
- `docs/dev_history/audits/AUDIT_H3_HARDWARE_BINDING_v0.25.27.md` (~911 lines)
- `docs/dev_history/audits/AUDIT_v0.25.10_WORKSTREAM_PLAN.md` (~909 lines)
- `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/Signal.lean` (~891 lines)
- `docs/dev_history/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md` (~884 lines)
- `SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuite.lean` (~868 lines)
- `docs/dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md` (~859 lines)
- `SeLe4n/Kernel/IPC/Operations/SchedulerLemmas.lean` (~848 lines)
- `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean` (~829 lines)
- `SeLe4n/Kernel/InformationFlow/Projection.lean` (~821 lines)
- `docs/dev_history/audits/WS_RC_R4_CLOSEOUT_PLAN.md` (~818 lines)
- `tests/TwoPhaseArchSuite.lean` (~812 lines)
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

  **Phase status** (current version: v0.31.77):

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
  | SM6.D–SM9 | PENDING | — | Cross-core cancellation, per-core IPC invariant bundle, TLB shootdown, info-flow, release closure (→ v1.0.0) |

  **Plans**: master overview at
  [`docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md`](docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md);
  per-phase plans at `docs/planning/SMP_*.md`.

  **Key AK7 metrics at v0.31.64**: `RAW_MATCH_TOTAL` 133,
  `RAW_LOOKUP_TID` 837, `GETTCB_ADOPTION` 1129,
  `GETSCHEDCTX_ADOPTION` 266 (re-anchored for the SM5.J.4 per-core R5
  generalisation — additive `maxBudgetInBandOnCore` / `maxPeriodInBandOnCore`
  mirror the bootCore raw pattern for the `rfl` bridges; see
  `docs/dev_history/audits/AL0_baseline.txt`).

  **Rust HAL at v0.31.62**: 724 tests, zero clippy warnings,
  zero `#[ignore]`'d.

  **Staged modules**: 56 staged-only (via `Platform/Staged.lean` +
  `scripts/staged_module_allowlist.txt`); production/staged partition
  gate enforced by `scripts/check_production_staging_partition.sh`.  (SM6.C
  added `EndpointReplyNI` staged and promoted the cross-core reply transition /
  invariant / dispatch trio to production.)

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
