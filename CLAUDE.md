# CLAUDE.md — seLe4n project guidance

> A mirror of this file lives at `AGENTS.md` so that non-Claude coding
> agents (and any tool that follows the AGENTS.md convention) get the
> same project rules. If you edit one, edit the other in the same PR —
> the two files must stay byte-identical apart from this header.

## What this project is

seLe4n is a production-oriented microkernel written in Lean 4 with machine-checked
proofs, improving on seL4 architecture. Every kernel transition is an executable
pure function with zero `sorry`/`axiom`. First hardware target: Raspberry Pi 5.
Lean 4.28.0 toolchain, Lake build system, version 0.31.40.

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
- `CHANGELOG.md` (~22653 lines)
- `docs/WORKSTREAM_HISTORY.md` (~7623 lines)
- `SeLe4n/Kernel/Concurrency/Locks/RwLock.lean` (~6631 lines)
- `docs/dev_history/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md` (~4721 lines)
- `docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md` (~4130 lines)
- `tests/NegativeStateSuite.lean` (~4016 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~3922 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` (~3906 lines)
- `docs/spec/SELE4N_SPEC.md` (~3806 lines)
- `SeLe4n/Kernel/CrossSubsystem.lean` (~3392 lines)
- `docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md` (~3388 lines)
- `SeLe4n/Platform/Boot.lean` (~3263 lines)
- `SeLe4n/Testing/MainTraceHarness.lean` (~3153 lines)
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
- `SeLe4n/Kernel/API.lean` (~2375 lines)
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` (~2369 lines)
- `docs/dev_history/audits/AUDIT_v0.25.14_WORKSTREAM_PLAN.md` (~2340 lines)
- `docs/dev_history/audits/AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md` (~2339 lines)
- `docs/audits/AUDIT_v0.30.11_DEEP_VERIFICATION.md` (~2326 lines)
- `tests/OperationChainSuite.lean` (~2201 lines)
- `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean` (~2187 lines)
- `docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md` (~2073 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/DualQueueMembership.lean` (~2065 lines)
- `tests/ModelIntegritySuite.lean` (~2052 lines)
- `docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md` (~2022 lines)
- `SeLe4n/Prelude.lean` (~1992 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/StoreObjectFrame.lean` (~1985 lines)
- `docs/dev_history/planning/V3_PROOF_CHAIN_HARDENING_E_G6_PLAN.md` (~1966 lines)
- `docs/dev_history/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md` (~1917 lines)
- `SeLe4n/Kernel/Concurrency/Locks/TicketLock.lean` (~1901 lines)
- `SeLe4n/Model/Object/Types.lean` (~1892 lines)
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
- `docs/dev_history/AUDIT_v0.22.10_WORKSTREAM_PLAN.md` (~1674 lines)
- `docs/planning/SMP_FOUNDATIONS_PLAN.md` (~1665 lines)
- `tests/InformationFlowSuite.lean` (~1622 lines)
- `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean` (~1619 lines)
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` (~1590 lines)
- `SeLe4n/Kernel/Scheduler/Operations/PerCoreChooseThread.lean` (~1544 lines)
- `SeLe4n/Kernel/Architecture/Invariant.lean` (~1529 lines)
- `docs/dev_history/audits/AUDIT_v0.28.0_WORKSTREAM_PLAN.md` (~1480 lines)
- `docs/dev_history/planning/V3B_LOAD_FACTOR_BOUNDED_MIGRATION_PLAN.md` (~1457 lines)
- `docs/dev_history/audits/AUDIT_v0.25.3_WORKSTREAM_PLAN.md` (~1452 lines)
- `docs/dev_history/audits/WS_RC_R5_DEFERRED_COMPLETION_PLAN.md` (~1414 lines)
- `docs/dev_history/AUDIT_v0.23.21_WORKSTREAM_PLAN.md` (~1411 lines)
- `docs/dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md` (~1382 lines)
- `docs/dev_history/audits/AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md` (~1357 lines)
- `docs/dev_history/audits/AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md` (~1342 lines)
- `docs/planning/SMP_PANIC_HANG_REMEDIATION_PLAN.md` (~1342 lines)
- `tests/LockSetSuite.lean` (~1307 lines)
- `SeLe4n/Platform/FFI.lean` (~1297 lines)
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
- `SeLe4n/Kernel/Scheduler/Operations/Core.lean` (~1027 lines)
- `SeLe4n/Kernel/InformationFlow/Policy.lean` (~1023 lines)
- `SeLe4n/Kernel/Scheduler/RunQueue.lean` (~1023 lines)
- `SeLe4n/Kernel/FrozenOps/Operations.lean` (~1000 lines)
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
- `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` (~907 lines)
- `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/Signal.lean` (~891 lines)
- `docs/dev_history/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md` (~884 lines)
- `docs/dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md` (~859 lines)
- `SeLe4n/Kernel/IPC/Operations/SchedulerLemmas.lean` (~848 lines)
- `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean` (~827 lines)
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

- **WS-SM SMP multi-core completion workstream IN FLIGHT (v0.31.2 → v0.31.3 → v0.31.4 → v0.31.5 → v0.31.6 → v0.31.7 → v0.31.8 → v0.31.9 → v1.0.0,
  branch `claude/review-codebase-memory-model-xxsh9`)**:
  Unified workstream merging WS-RC's remaining R6..R14 phases with the
  SMP-specific SM-phases (SM0..SM9).  Closes at v1.0.0 with a bootable
  verified SMP microkernel on Raspberry Pi 5.

  **Plans**:
  - Master overview:
    [`docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md`](docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md).
  - SM0 (foundations & honesty patches) — CLOSED at v0.31.3 (foundational types and honesty patches landed; type-level scaffolding ready for SM1):
    [`docs/planning/SMP_FOUNDATIONS_PLAN.md`](docs/planning/SMP_FOUNDATIONS_PLAN.md).
  - SM1+ phase plans (Rust HAL, verified locks, per-core state, per-core
    scheduler, cross-core IPC, TLB shootdown, info-flow, release closure):
    `docs/planning/SMP_*.md`.

  **Decisions (binding)**: per-object RW fine locks; path-a Vector state
  replacement; hierarchical-by-kind lock order (LockKind levels 0..9 from
  SM0.I); SMP enabled by default at v1.0.0 once SM5 lands; numCores via
  `PlatformBinding.coreCount` (RPi5 = 4); verified TicketLock + RwLock
  primitives with formal mutex/fairness theorems; SGI INTID 0..4 reserved
  for kernel SMP coordination (SM0.H).

  **WS-SM SM0 LANDED on branch
  `claude/complete-sm0-foundations-gldW8`** (v0.31.3, foundational types
  + honesty patches): closes the type-level scaffolding for the SM1..SM9
  follow-on phases.  21 sub-tasks across 6 categories landed in one cut:

  - **SM0.E + SM0.F**: foundational types
    `SeLe4n.Kernel.Concurrency.numCores` (`= 4`),
    `CoreId := Fin numCores`, `bootCoreId`, `allCores` enumeration with
    `numCores_pos` / `allCores_length` / `allCores_nodup` /
    `bootCoreId_valid` witnesses;
    `SharingDomain` inductive (`.inner` / `.outer`) plus
    `dsbForSharing` / `dsbStForSharing` `BarrierKind` selectors.
    Production-reachable via `Platform.Contract` (which now carries
    `PlatformBinding.sharingDomain`).
  - **SM0.G**: PlatformBinding extension — `coreCount`, `coreCountPos`,
    `bootCoreId : Fin coreCount`, `sharingDomain : SharingDomain`
    fields added to the typeclass; RPi5 (`coreCount := 4`,
    `bootCoreId := ⟨0, _⟩`, `sharingDomain := .inner`) and Sim instances
    updated.  Three pinning theorems
    (`numCores_eq_rpi5_coreCount`, `bootCoreId_val_eq_rpi5`,
    `rpi5_sharingDomain`) make the literal `Concurrency.numCores`
    structurally agree with the RPi5 binding's `coreCount` via `rfl`.
  - **SM0.H**: `SgiKind` enumeration (`reschedule`, `tlbShootdownReq`,
    `tlbShootdownAck`, `cacheBroadcast`, `haltAll`) with
    `toIntid : SgiKind → Fin 16` mapping to GIC-400 INTIDs 0..4;
    `toIntid_injective`, `toIntid_in_range`, `toIntid_lt_five` proofs.
  - **SM0.I**: `LockKind` 10-layer hierarchy (`objStore` → `untyped` →
    `cnode` → `tcb` → `endpoint` → `notification` → `reply` →
    `schedContext` → `vspaceRoot` → `page`) with
    `level_strictMono`, `level_surjective`, `level_bounded` theorems;
    `LockId` = `(kind, objId)` with lexicographic total order
    (`le_total`, `le_refl`, `le_trans`, `le_antisymm`, `lt_trichotomy`);
    `BklState` (`unheld` / `held CoreId`) with `bklState_unique_owner`.
  - **SM0.A + SM0.B**: `ArchAssumption` inductive grows from 5 to 6
    constructors with the new `singleCoreOperation` arm pointing at
    `bootFromPlatform_singleCore_witness` (closes SMP-H2 audit
    finding); `archAssumptionConsumer_distinct_6` proves all 15 pairs
    (C(6,2)) are distinct; `architecture_assumptions_index_total_6`
    is the new exhaustivity marker; `assumptionInventory_count`
    pins the inventory size at 6.
  - **SM0.C + SM0.D**: `SeLe4n.Kernel.Concurrency.Anchors` build-time
    `@`-references every `smpLatentInventory` entry's `identifier` and
    `sourceTheorem` so a renamed underlying symbol fails the build
    (closes SMP-H3 audit finding); `smpLatentInventory_identifiers_nodup`
    and `smpLatentInventory_sourceTheorems_nodup` close the NoDup gap
    (SMP-L1).
  - **SM0.J + SM0.K + SM0.L**: documentation honesty patches —
    every `dev_history/audits/...` cross-reference removed from
    production sources (`rust/sele4n-hal/src/`, `SeLe4n/Kernel/`); every
    "deferred to WS-V" SMP claim repointed to WS-SM phase plans;
    `AUDIT_v0.29.0_DEFERRED.md::DEF-R-HAL-L20` rewritten from
    "RESOLVED" to "PARTIALLY RESOLVED — scaffolding only; full
    activation in WS-SM" with cross-references to the WS-SM phase
    plans.
  - **SM0.M + SM0.N + SM0.O**: structural fixes in the Rust HAL —
    `.smp_stacks` zeroed at boot (closes SMP-M3); TPIDR_EL1 set in
    `secondary_entry` to per-CPU data block (closes SMP-M4) with new
    `PerCpuData` struct + `PER_CPU_DATA[4]` array seam;
    `MAX_SECONDARY_CORES` pinned to `PlatformBinding.coreCount - 1`
    via Rust `const _: () = assert!(...)` (closes SMP-L2).  10 new
    Rust unit tests cover layout, alignment, zero-initialisation,
    distinctness, stride, and out-of-range panic.
  - **SM0.S + SM0.T + SM0.R**: testing infrastructure —
    `tests/SmpFoundationsSuite.lean` with 50+ surface-anchor `#check`s
    plus 41 runtime decidable assertions (`lake exe smp_foundations_suite`),
    wired into tier-2 negative + tier-3 invariant surface;
    `scripts/test_tier4_smp_bootcheck.sh` SKIP-only stub reserves the
    tier-4 slot for SM1.H..SM8.E to populate; `docs/codebase_map.json`
    regenerated.

  **WS-RC R0..R5 LANDED at v0.31.2** (historical record preserved in
  [`docs/CLAUDE_HISTORY.md`](docs/CLAUDE_HISTORY.md) and
  [`docs/WORKSTREAM_HISTORY.md`](docs/WORKSTREAM_HISTORY.md)).
  R6..R14 absorbed into SM-prefixed sub-tasks per the SM0.Q merge —
  see
  [`docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md`](docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md)
  §15 for the per-phase absorption mapping.

  **WS-SM SM1.A LANDED on branch
  `claude/implement-psci-completion-TUW1u`** (PSCI completion, first
  sub-phase of SM1).  Eight sub-tasks landed in one cut, closing
  SMP-M5 (PSCI completion) by wrapping the full ARM DEN0022D §5
  surface beyond `cpu_on`:

  - **SM1.A.1**: `psci::cpu_off()` — power down the calling PE
    (`hvc #0` SMC32 id `0x8400_0002`).  Successful calls do not
    return (the PE is off); failure paths return a `PsciResult`.
  - **SM1.A.2**: `psci::affinity_info()` — query a target PE's
    on/off state.  New `AffinityInfoState` enum (`On`/`Off`/
    `OnPending`) with `from_raw` / `to_raw` round-trip.  SMC64 id
    `0xC400_0004`.
  - **SM1.A.3**: `psci::system_off() -> !` — power off the system
    (SMC32 id `0x8400_0008`).
  - **SM1.A.4**: `psci::system_reset() -> !` — cold system reset
    (SMC32 id `0x8400_0009`).
  - **SM1.A.5**: `psci::psci_version()` — query firmware version.
    New `PsciVersion` struct with `major` / `minor` u16, `from_raw`
    / `to_raw` round-trip, `at_least(major, minor)` feature-gate
    comparator.  SMC32 id `0x8400_0000`.
  - **SM1.A.6**: `psci::migrate_info_type()` — Trusted-OS migration
    query.  New `MigrateInfoType` enum (`UniProcessor`/
    `Multiprocessor`/`NotRequired`).  SMC32 id `0x8400_0006`.
  - **SM1.A.7**: Function-id pinning — compile-time `const _: () = { ... }`
    assertions verify every PSCI id matches the ARM SMCCC encoding
    (bit 31 Fast call, bit 30 SMC32/64, bits 29..24 OEN=4 for
    Standard Secure Service Calls, bits 23..16 reserved-zero).
    Plus seven runtime test functions (`psci_function_ids_*`)
    covering literal match, pairwise distinctness, SMC width, OEN,
    and reserved-bits-clear.
  - **SM1.A.8**: Module-level documentation map — `psci.rs` header
    lists all seven wrappers with DEN0022D § references, function
    ids, return-code matrix (Table 5), and the HVC-vs-SMC dispatch
    rationale.

  **Test coverage**: 45 PSCI unit tests (43 active + 2 `#[ignore]`'d
  for `system_off` / `system_reset` since they return `!` and would
  hang the test runner).  Two audit passes added: 8 decoder-failure-
  path tests (`decode_affinity_info_result_*` and
  `decode_migrate_info_type_result_*`) that exercise the i32 → Result
  conversion branches without an HVC trap; plus 5 edge-case /
  const-context tests (`psci_version_from_raw_zero_is_zero_zero`,
  `psci_version_to_raw_zero_zero_is_zero`,
  `psci_version_from_raw_u32_max_is_u16_max_u16_max`,
  `psci_version_to_raw_u16_max_u16_max_is_u32_max`,
  `const_context_decoders_evaluate`) covering boundary inputs and
  forcing every `const fn` decoder into a compile-time `const`
  binding (the binding is the proof of const-ness — non-const fns
  fail to compile).  Total HAL tests: 253 (was 215).  Zero clippy
  warnings.  Full Tier 0+1+2 smoke test passes.  Items deferred
  past v1.0.0 with correctness impact: NONE.
  Follow-on: SM1.B..H (per-CPU data + TPIDR_EL1, secondary-core full
  init, DTB cmdline, IS-variant TLBI, SGI primitive, per-core UART,
  QEMU SMP integration) — see
  [`docs/planning/SMP_RUST_HAL_PLAN.md`](docs/planning/SMP_RUST_HAL_PLAN.md) §§5.2..5.8.

  **Audit-pass-1 refinements** (post-initial-landing):
  - HIGH-severity soundness fix: dropped `options(..., noreturn)`
    from `system_off` / `system_reset` HVC asm blocks.  Per the
    Rust reference, `noreturn` is UB if the asm returns; per
    DEN0022D §5.1.9 / §5.1.10 a non-conforming firmware that does
    not implement SYSTEM_OFF / SYSTEM_RESET returns `NOT_SUPPORTED`
    (-1).  Replaced with `clobber_abi("C")` + an explicit
    `loop { core::hint::spin_loop(); }` after the asm so the `-> !`
    type is honoured even on non-conforming firmware (the kernel
    spin-parks in the safest possible state rather than triggering
    UB).
  - Documentation accuracy: DEN0022D sub-section citations
    realigned to revision D numbering (CPU_OFF §5.1.3, CPU_ON
    §5.1.4, AFFINITY_INFO §5.1.5, MIGRATE_INFO_TYPE §5.1.7,
    SYSTEM_OFF §5.1.9, SYSTEM_RESET §5.1.10).  The function IDs
    are stable across revisions and remain the canonical
    identifier.
  - Testability: extracted pure decoders
    `decode_affinity_info_result(i32) -> Result<..., PsciResult>`
    and `decode_migrate_info_type_result(i32) -> Result<..., PsciResult>`
    so the failure paths are unit-testable without an HVC trap.
  - API: `#[must_use]` added to `cpu_on` / `cpu_off` /
    `psci_version` (Result-returning functions inherit
    `#[must_use]` from `Result`).
  - Test coverage: `psci_result_is_success_only_for_zero`
    expanded from 4 variants to all 10.
  - Documentation honesty: removed a false claim that wrappers
    route through `PlatformBinding.psciConduit = HVC` (there is no
    such field at v1.0.0); wrappers hard-code `hvc #0` because
    RPi5 is the only v1.0.0 hardware target.  Future conduit
    parameterisation is tracked as a post-1.0 SM1 closure item.

  **Audit-pass-2 refinements** (second deep audit, post-pass-1):
  - Labeling correctness: `cpu_on` was incorrectly labeled
    `WS-SM SM1.A.1` in its section header and docstring.  Per the
    plan, SM1.A.1 is `cpu_off`; `cpu_on` is the pre-existing
    AN9-J.1 (DEF-R-HAL-L20) wrapper that predates SM1.A.  Re-
    labeled accordingly.
  - Documentation accuracy: rewrote the module docstring's
    cross-cluster-ordering section to honestly distinguish PE-
    affecting calls (`cpu_on`, `cpu_off`, `system_off`,
    `system_reset` — barrier required for caller-state visibility
    on the target) from pure queries (`psci_version`,
    `migrate_info_type`, `affinity_info` — no state transfer to
    target).  `affinity_info`'s wrong "should the target be
    OnPending" rationale rewritten honestly.
  - Broken rustdoc link to `docs/planning/SMP_RUST_HAL_PLAN.md`
    replaced with plain-text reference (the `../../../` relative
    path resolved to a non-existent target in rustdoc's HTML
    output).
  - SAFETY-comment clarity: `cpu_on`'s "disable preserved-flags"
    wording reworked — the asm doesn't disable anything, it just
    omits `preserves_flags` (default off).
  - Test MPIDR realism: `cpu_on_host_stub_returns_success` now
    uses `0x0000_0001` (Aff0=1, matching
    `smp::SECONDARY_MPIDR_TABLE[0]`) instead of the unrealistic
    `0x0001_0000` (Aff2=1).
  - Missing `PsciVersion` edge-case tests added
    (`from_raw(0)`, `from_raw(u32::MAX)`, `to_raw` inverse
    directions; round-trip test extended with boundary inputs
    `(0,0)`, `(u16::MAX, u16::MAX)`, asymmetric mid-range
    bit-pattern combinations).
  - Missing `at_least` edge cases added (`(0, 0)` on every
    version, smallest `(0, 0)` version, largest
    `(u16::MAX, u16::MAX)` version, major-only-dominates case).
  - Const-context test (`const_context_decoders_evaluate`)
    added: forces every `const fn` decoder into a `const`
    binding.  A future PR that loses const-ness would fail to
    compile — the binding itself is the proof.
  - `lib.rs` annotation for `pub mod psci` extended to mention
    WS-SM SM1.A and the full DEN0022D §5 surface (previously
    only cited AN9-J.1).

  **WS-SM SM1.B LANDED at v0.31.4 on branch
  `claude/per-cpu-tpidr-el1-1OBHA`** (per-CPU data + TPIDR_EL1,
  closes SMP-M4).  Seven sub-tasks landed in one cut, completing the
  per-CPU base register seam introduced as an empty stub at SM0.N:

  - **SM1.B.1**: `PerCpuData` struct migrated from `smp.rs` to the
    dedicated module `rust/sele4n-hal/src/per_cpu.rs`.  The SM0.N
    `_reserved: [u64; 8]` placeholder is replaced with a populated
    `core_id: u64` first field plus a `_reserved: [u64; 7]` tail
    (still one cache line wide for false-sharing avoidance).  Two
    const constructors: `new(core_id)` and `zero()` (back-compat
    alias for `new(0)`).
  - **SM1.B.2**: Static array population — `PER_CPU_DATA[i].core_id
    == i` for `i ∈ 0..MAX_SECONDARY_CORES`, via four
    `PerCpuData::new(0..3)` invocations.  Three compile-time
    `const _: ()` assertions pin `size_of::<PerCpuData>() == 64`,
    `align_of::<PerCpuData>() == 64`, and
    `PER_CPU_DATA.len() == MAX_SECONDARY_CORES + 1`.  Asm-visible
    `PER_CPU_DATA_SLOT_SIZE_SYM` (consumed by `boot.S`'s `madd`
    stride) survives the module move via `#[no_mangle]`.
  - **SM1.B.3**: `current_per_cpu() -> &'static PerCpuData` —
    reads `TPIDR_EL1` on aarch64, returns a static-lifetime
    reference into `PER_CPU_DATA`.  Host stub returns
    `&PER_CPU_DATA[0]`.  Safety invariants documented inline (EL1
    reachability, TPIDR_EL1-pre-set, pointer-validity).
  - **SM1.B.4**: `current_core_id_from_tpidr() -> u64` — fast
    core-id lookup via `current_per_cpu().core_id`.  Preferred over
    MPIDR + mask on hot paths.  Host stub returns 0.
  - **SM1.B.5**: Lean FFI — Rust `#[no_mangle] pub extern "C" fn
    ffi_current_core_id` in `ffi.rs`; Lean
    `@[extern "ffi_current_core_id"] opaque
    Platform.FFI.ffiCurrentCoreId : BaseIO UInt64`; Lean-side typed
    wrapper `Concurrency.currentCoreId : BaseIO CoreId` in the new
    file `SeLe4n/Kernel/Concurrency/Runtime.lean` with the standard
    `if h : raw.toNat < numCores then ⟨raw.toNat, h⟩` discipline.
    Out-of-range falls back to `panic!` (witnessed by the new
    `Inhabited CoreId` instance in `Concurrency.Types` —
    `bootCoreId`).  Unreachable on hardware under
    `check_per_cpu_invariants`.
  - **SM1.B.6**: `check_per_cpu_invariants()` runtime gate —
    iterates `PER_CPU_DATA` and panics if any slot's `core_id`
    disagrees with its array index.  Called from
    `rust_boot_main` Phase 4 before the `TPIDR_EL1` write.
    `boot.rs` also `kprintln`s the live core id post-TPIDR-set for
    boot-log diagnostics on hardware.
  - **SM1.B.7**: 30 unit tests in `per_cpu::tests` (10 migrated
    from the SM0.N `smp::tests::sm0n_*` block under `sm1b_*` names
    with expanded coverage, 15 newly authored at SM1.B landing
    for SM1.B-specific functionality, 5 added at audit-pass-2 for
    the `check_per_cpu_invariants_in` inner form + panic-path
    regression cases): struct alignment + size,
    const-constructor `new` and `zero` semantics, byte-level zero
    discharge for the reserved tail, array
    layout/stride/distinct-addresses, asm-stride observability via
    `PER_CPU_DATA_SLOT_SIZE_SYM`, out-of-range panic,
    `current_per_cpu` returns boot slot on host and points inside
    `PER_CPU_DATA` at a cache-line boundary,
    `current_core_id_from_tpidr` returns 0 on host and is
    in-range, `check_per_cpu_invariants` passes on the production
    initialiser AND on well-formed / empty test slices, panics on
    three distinct mis-population patterns (wrong-core-id,
    first-slot-wrong, zero-default-regression),
    pairwise-distinct + canonical-range cross-checks on `core_id`,
    accessor agreement with `per_cpu_slot_addr`.  3 new tests in
    `ffi::tests` (`ffi_current_core_id` host return 0, range
    invariant, agreement with the per-CPU accessor).  4 back-compat
    tests in `smp::tests` (replacing the 11 sm0n_* tests that
    migrated): verifying the `crate::smp::*` re-exports of
    `PerCpuData`, `PER_CPU_DATA`, the slot-size constants, and
    `per_cpu_slot_addr` still resolve.

  **Test coverage**: 281 HAL tests, zero `#[ignore]`'d (up from 253
  at SM1.A close, which had 2 ignored tests — converted to
  compile-time fn-pointer signature checks at v0.31.4 audit-pass-3),
  zero clippy warnings workspace-wide.  4 new Lean surface-anchor
  `#check`s plus 4 new decidable examples plus a runtime
  `runCurrentCoreIdChecks` section in
  `tests/SmpFoundationsSuite.lean` (Inhabited default = bootCoreId,
  marker theorem discharge on every CoreId).  Full Tier 0+1+2
  smoke test passes.  Items deferred past v1.0.0 with correctness
  impact: NONE.

  **Module reachability**: `Concurrency.Runtime` is in the
  production import closure via `SeLe4n/Platform/Staged.lean`
  (added to `scripts/staged_module_allowlist.txt` per the WS-RC
  R12.B partition gate); SM5 will move it from staged →
  production-reached when per-core scheduler state lands.

  **FFI-link discipline note**: per the project's fail-closed FFI
  convention (`Platform/FFI.lean` header docstring), the Lean test
  executables do NOT link against `libsele4n_hal.a`.  Any path
  that invokes an `@[extern] opaque` symbol from host code
  surfaces as a link error rather than a silent stub call.  The
  SmpFoundationsSuite test therefore exercises only the structural
  properties of `currentCoreId` (typed signature, marker theorem,
  Inhabited default).  The runtime behaviour of the host stub is
  covered exhaustively by the Rust `per_cpu::tests` and
  `ffi::tests` modules; the hardware behaviour (the actual `mrs
  tpidr_el1` read) will be covered by SM1.H's QEMU `-smp 4`
  boot-trace test.

  **WS-SM SM1.C LANDED at v0.31.5 on branch
  `claude/review-codebase-secondary-core-PgqGR`** (secondary-core
  full init, closes SMP-C2).  Twelve sub-tasks landed in one cut,
  rewriting the previously-thin `rust_secondary_main` shell into the
  full per-core boot sequence (MMU → VBAR → GIC → timer → IRQ →
  Lean kernel) shared symmetrically with the primary boot path:

  - **SM1.C.1**: `mmu::init_mmu_secondary(core_id)` plus extracted
    `mmu::init_mmu_per_core(core_id)` helper.  The primary's
    `init_mmu()` now routes through `init_mmu_per_core(0)` after
    `build_identity_tables()`; secondaries call `init_mmu_secondary`
    which skips the table-build step (the boot L1 table is a
    read-only global populated once by the primary) and applies
    the per-core MMU enable sequence — TLB invalidate, page-table
    D-cache clean, TTBR0/1/TCR/MAIR programming, SCTLR_EL1 write
    with the AK5-C full bitmap (M | C | I | SA | SA0 | WXN | EOS |
    EIS | RES1).  Audit follow-up cfg-gated the `pt_pa_raw < 2^44`
    debug_assert to aarch64 (host x86_64 binary base addresses
    routinely exceed 2^44 on PIE builds; the assert false-faulted
    on host test invocations).
  - **SM1.C.2**: `boot::install_exception_vectors()` — VBAR_EL1
    installation extracted from the formerly-private `set_vbar`
    function and made `pub` so secondaries reach it via
    `crate::boot::install_exception_vectors`.  The primary's
    `rust_boot_main` Phase 2 now calls the same helper.  Two new
    build.rs scanners pin the primary/secondary symmetry: one
    rejects an inline `write_vbar_el1` in `boot.rs` (other than
    the helper body itself), the other requires
    `install_exception_vectors(` in `smp.rs`.
  - **SM1.C.3**: `gic::init_cpu_interface_secondary(core_id)` —
    wraps the existing `init_cpu_interface(GICC_BASE)` (banked
    per-core; CTLR/PMR/BPR enables) with a per-core diagnostic
    kprintln.  Primary's `init_gic` continues to handle the
    global distributor.
  - **SM1.C.4**: `timer::init_timer_secondary(tick_hz)` — per-core
    timer arming (CNTP_CVAL_EL0 + CNTP_CTL_EL0.ENABLE).
    Deliberately does NOT reset the global `TICK_COUNT` (primary-
    owned monotonic counter) or rewrite `TIMER_INTERVAL`
    (populated by primary; same value on every core via shared
    CNTFRQ_EL0).  Returns `Result<(), TimerError>` for parity with
    `init_timer`; failure (CntfrqNotProgrammed, ZeroTickHz) halts
    just the affected secondary via WFE loop, leaving other cores
    running.
  - **SM1.C.5**: `rust_secondary_main` body rewrite — eight-step
    sequence: (0) spin on CORE_READY[i] with bounded WFE; (1) MMU
    via `init_mmu_secondary`; (2) VBAR via `install_exception_vectors`;
    (3) GIC via `init_cpu_interface_secondary`; (4) timer via
    `init_timer_secondary` (fatal-on-fail path halts the core); (5)
    `enable_irq()` to unmask IRQ delivery; (6) Lean kernel entry
    via `lean_secondary_kernel_main(context_id)` (gated on
    `feature = "hw_target"`); (7) idle fallback `loop { wfe() }`.
    Diagnostic `kprintln` after every step gives the boot trace a
    deterministic banner pattern QEMU `-smp 4` (SM1.H) can grep.
    A new build.rs scanner enumerates the six required call sites
    by name (`init_mmu_secondary`, `init_cpu_interface_secondary`,
    `init_timer_secondary`, `enable_irq`,
    `lean_secondary_kernel_main`) and fails the build if any is
    silently dropped.
  - **SM1.C.6**: `SeLe4n.Kernel.SecondaryEntry.secondaryKernelMain
    : UInt64 → BaseIO Unit` — new module
    `SeLe4n/Kernel/SecondaryEntry.lean` with the
    `@[export lean_secondary_kernel_main]` attribute that produces
    the C-callable wrapper the Rust HAL's `rust_secondary_main`
    resolves.  At SM1.C the body is `pure ()` (a deliberate
    placeholder; SM5 replaces it with the per-core scheduler
    entry).  Surface-anchor theorem
    `secondaryKernelMain_returns_unit_marker` proves the
    placeholder semantics by `rfl` for downstream Tier-3 scans.
    Module reached via `SeLe4n/Platform/Staged.lean` (added to the
    staged-module allowlist per WS-RC R12.B); SM5 moves it
    production-reached.
  - **SM1.C.7..C.11**: documentation-only sub-tasks — per-core
    stack reservation in `link.ld` (already in place; verified
    unchanged), MMU page-table reuse rationale (`mmu.rs` module
    docstring), per-core SCTLR_EL1 bitmap (covered by SM1.C.1
    via `init_mmu_per_core`), per-core VBAR_EL1 (covered by
    SM1.C.2 via `install_exception_vectors`), SError handler
    masked policy retained (per the existing single-core
    convention).
  - **SM1.C.12**: 32 new host tests — 6 in `mmu::tests` (sm1c1_*
    suite: callable on host, accepts all secondary core_ids,
    debug_assert panic on core 0, signature pinning), 4 in
    `boot::tests` (sm1c2_* suite: callable on host, signature
    pinning, idempotence), 4 in `gic::tests` (sm1c3_* suite:
    same shape), 7 in `timer::tests` (sm1c4_* suite: Ok on host,
    ZeroTickHz rejection, TICK_COUNT preservation,
    TIMER_INTERVAL preservation, signature pinning), 11 in
    `smp::tests` (sm1c5_* suite: ABI signature, every helper
    resolves via its crate module, full-set callability,
    aggregate idempotence, `#[no_mangle]` discipline).  Plus 12
    new Lean assertions in `tests/SmpFoundationsSuite.lean`
    (`#check` surface anchors for `secondaryKernelMain` and its
    marker theorem; `runSecondaryKernelMainChecks` runtime
    section with marker-theorem reachability, runtime BaseIO
    invocation, and boundary UInt64 input tolerance).

  **Test coverage**: 313 HAL tests (up from 281 at SM1.B close,
  zero `#[ignore]`'d, zero clippy warnings workspace-wide).  Tier
  0+1+2+3 all green.  Items deferred past v1.0.0 with correctness
  impact: NONE.

  **Module reachability**: `Kernel.SecondaryEntry` is staged via
  `Platform.Staged` (added to the SM1.B/SM1.C closure in the
  allowlist); SM5 promotes it production-reached when per-core
  scheduler state lands.

  **Audit-pass-1 refinements** (post-initial-landing):
  - **`enable_mmu` host-portability fix**: the existing AK5-E.3
    debug_assert `pt_pa_raw < (1usize << 44)` was unconditional.
    On x86_64 host PIE binaries the static base address is
    routinely `0x55...` (≥ 2^44), so SM1.C.1's per-core helper
    tests that exercised `init_mmu_per_core(0)` on host triggered
    a false-positive panic.  Gated the 44-bit-PA check on
    `cfg!(target_arch = "aarch64")`.  The 4-KiB alignment check
    (the first debug_assert) remains unconditional because
    `repr(align(4096))` makes the property hold on every target.
  - **Build-script regression scanners**: three new scanners in
    `rust/sele4n-hal/build.rs` (`scan_boot_rs_uses_install_exception_vectors`,
    `scan_smp_rs_uses_install_exception_vectors`, and
    `scan_smp_rs_invokes_secondary_init_helpers`) pin the SM1.C.2
    primary/secondary symmetry and the SM1.C.5 init-helper call
    chain at build time.  A future refactor that drops any of
    these contracts fails the build with an actionable
    diagnostic.

  **Audit-pass-2 refinements** (deep-audit post-pass-1):
  - **HIGH-severity defense-in-depth: PSCI context_id validation
    (two-layer)**.  Pre-audit `rust_secondary_main` and
    `boot.S::secondary_entry` accepted any `context_id` and
    proceeded with hardware init / SP arithmetic.  Two failure
    modes under malicious or malformed PSCI firmware:
    (a) `context_id == 0` (boot-core slot) would alias a
        secondary's per-core state with the boot core's
        `PerCpuData` slot once it ran the per-core init
        (`PER_CPU_DATA + context_id * stride` = boot slot).
    (b) `context_id >= 4` (CORE_READY.len() on RPi5) computed
        SP via `__smp_secondary_stack_top - (context_id - 1) *
        64 KiB`; for context_id == 4 the SP lands at
        `__smp_secondary_stacks_bottom`, ADJACENT to the boot
        core's `.stack` region — `rust_secondary_main`'s
        prologue push would corrupt boot-core stack frames
        BEFORE any Rust-level validator could halt.
    Defense: TWO layers reject the same conditions.
    - **Layer 1 (asm)** `boot.S::secondary_entry` Step 1.5:
      `cbz x0, .L_secondary_invalid` + `cmp x0, MAX_CORE_COUNT_SYM`
      / `b.hs .L_secondary_invalid`.  Runs AFTER DAIF mask but
      BEFORE any SP / TPIDR_EL1 arithmetic uses `context_id`,
      preventing boot-core stack corruption.  Bound read from
      the new `MAX_CORE_COUNT_SYM` `.rodata` symbol (not a
      literal) for single-source-of-truth parity with
      `PER_CPU_DATA_SLOT_SIZE_SYM` (SM1.B).
    - **Layer 2 (Rust)** `rust_secondary_main` Step 0:
      `validate_secondary_context_id(context_id: u64) ->
      Option<usize>` `const fn` validator.  Both layers halt
      the offending core in a low-power WFE loop with DAIF
      masked.  Primary and other secondaries continue running.
    13 new HAL tests cover both layers:
    `smp::tests::sm1c5_validate_context_id_*` (7 tests) +
    `smp::tests::sm1c5_max_core_count_sym_*` (6 tests).  Two
    new build-script scanners pin both layers' textual presence
    (`scan_smp_rs_invokes_secondary_init_helpers` Step 0 +
    `scan_boot_s_for_secondary_entry_context_id_validation`).
  - **Stale docstring fixes**: `smp.rs` module docstring's
    "What this module owns" section called `rust_secondary_main`
    a "placeholder" (stale post-SM1.C); rewrote it.  `lib.rs`
    `smp` module description mentioned only "AN9-J scaffolding";
    extended to cite WS-SM SM1.C.
  - **Vestigial scanner-bait removal**: deleted `let
    _kernel_entry_symbol_name: &str = "lean_secondary_kernel_main";`
    from `rust_secondary_main`.  The cfg-gated `extern "C" { fn
    lean_secondary_kernel_main(...) }` block and the
    `unsafe { lean_secondary_kernel_main(core_id) }` call site
    already satisfy the build-script scanner's textual presence
    check; the extra binding was dead code.

  **Audit-pass-3 refinements** (third deep-audit, post-pass-2):
  - **Validator truncation defense**: `validate_secondary_context_id`
    did `let core_idx = context_id as usize` BEFORE the bounds
    check.  On a 64-bit target this is identity, but on a
    hypothetical 32-bit port the cast truncates u64 to u32,
    silently accepting any `context_id` whose high bits were
    set but whose low 32 bits aliased a valid secondary slot
    (e.g., `0x1_0000_0001` → `core_idx = 1` → `Some(1)`).
    Reformulated to do the bounds check in `u64` space FIRST,
    then narrow to `usize` only on the accepted path —
    correct on every plausible `usize` width.  New test
    `sm1c5_validate_context_id_rejects_u64_with_high_bits_aliasing_secondary`
    exercises the boundary cases (`0x1_0000_0001`,
    `0x1_0000_0002`, `0x1_0000_0003`, `0x1_0000_0000`,
    `0xFFFF_FFFF_0000_0000`) — all must reject.
  - **Tier-3 invariant-surface anchors for SecondaryEntry**:
    `scripts/test_tier3_invariant_surface.sh` gained `#check`
    lines for `secondaryKernelMain` and
    `secondaryKernelMain_returns_unit_marker`.  Previously the
    Lean SecondaryEntry module was exercised only by the
    SmpFoundationsSuite (tier-2); the tier-3 surface check
    catches a rename / removal of either symbol at the build
    step, before reaching the test suite.

  **WS-SM SM1.D LANDED at v0.31.6 on branch
  `claude/review-dtb-cmdline-phase-EkoTA`** (DTB cmdline + Phase 5,
  closes the kernel-cmdline contract).  Six sub-tasks landed in one
  cut, wiring `rust_boot_main` Phase 5 to parse the DTB-supplied
  `/chosen/bootargs` and bring up secondaries based on the parsed
  configuration:

  - **SM1.D.1**: `rust/sele4n-hal/src/cmdline.rs` (NEW FILE, ~1400
    LoC including tests) — full self-contained DTB walker +
    cmdline parser.  Highlights:
    - `CmdlineConfig` struct (`smp_enabled: bool`,
      `smp_max_cores: usize`) `#[derive(Debug, Clone, Copy,
      PartialEq, Eq)]` for value-typed passing through the boot
      path.  `Default::default()` returns `smp_enabled = true`
      and `smp_max_cores = MAX_SECONDARY_CORES + 1 = 4` per
      maintainer decision #7 (SM1.D.3).
    - `parse_cmdline(s: &str) -> CmdlineConfig` — robust token
      parser.  Splits on ASCII whitespace, recognises
      `key=value` (typed; quoted with `"..."` / `'...'`) and
      flag-only tokens (none currently recognised; reserved
      for future use).  Malformed values fall back to the
      default for the affected option — the parser never
      panics on user input.  Unknown keys are silently ignored
      (forward-compat).  `smp_enabled` accepts the
      Linux-conventional truthy/falsy aliases (`true`/`false`,
      `yes`/`no`, `on`/`off`, `1`/`0`); `smp_max_cores` parses
      via `usize::from_str` and clamps to
      `MAX_SECONDARY_CORES + 1`.
    - Full RFC-grade DTB walker — `parse_fdt_header`,
      `validate_fdt_header`, `find_bootargs_in_dtb`,
      `extract_bootargs_into`, `extract_bootargs_from_blob_into`.
      Walks the `/chosen` node by depth-tracking the
      DFS traversal of the structure block; reads
      `bootargs` property + trims trailing null; copies into
      caller-supplied buffer; validates UTF-8 with
      `unwrap_or_default` fallback to `""`.  Fuel-bounded by
      `FDT_WALK_FUEL = 4096`; depth-bounded by
      `FDT_MAX_DEPTH = 32`.  Self-contained (does **not** route
      through the Lean-side `Platform.DeviceTree` parser to
      avoid the circular dependency where the kernel needs the
      cmdline parsed *before* it is initialised).  The plan's
      original sketch returned `&'static str` from
      `extract_bootargs`; the implemented form uses a
      caller-supplied buffer so the lifetime is sound (the DTB
      memory is not guaranteed `'static` once the kernel
      reclaims its early-boot allocations).
    - `parse_cmdline_from_dtb(dtb_ptr: u64) -> CmdlineConfig` —
      one-shot helper combining `extract_bootargs_into` (with a
      `[u8; MAX_BOOTARGS_LEN = 1024]` stack buffer) and
      `parse_cmdline`.  This is the entry point `rust_boot_main`
      Phase 5 calls.
    - `apply_cmdline_and_start_smp(&CmdlineConfig) -> u32` —
      stores `cfg.smp_enabled` into `smp::SMP_ENABLED` atomic
      and invokes `smp::bring_up_secondaries_with_limit` when
      enabled.
  - **SM1.D.2**: Phase 5 wired into `rust_boot_main` after the
    TPIDR_EL1 / IRQ-enable phase (now Phase 4) and before the
    handoff summary / Lean kernel entry (now Phase 6).  The
    phase emits diagnostic kprintln lines (`"[boot] cmdline
    parsed: smp_enabled=…, smp_max_cores=…"`, `"[boot] Phase 5:
    bringing up secondary cores (max=…)…"`, `"[boot] Phase 5: N
    secondary cores online"`) so a QEMU `-smp 4` boot trace
    has a deterministic pattern downstream tests (SM1.H) can
    grep.  The phase header banner gains an
    `SMP    : enabled|disabled (max cores: …)` row matching the
    existing per-subsystem rows for UART / MMU / VBAR / GIC /
    Timer.  `KERNEL_VERSION` bumped from `0.31.5` → `0.31.6`.
  - **SM1.D.3**: production default is `smp_enabled = true`,
    encoded in `CmdlineConfig::default()`.  Per maintainer
    decision #7, v1.0.0 ships SMP-on by default — operators
    that need single-core boot opt out via the kernel command
    line.  The `smp::SMP_ENABLED` atomic still defaults to
    `false` at module load (so a kernel that halts before
    reaching Phase 5 does not accidentally spawn secondaries);
    Phase 5 explicitly stores the parsed value before invoking
    the bring-up loop.
  - **SM1.D.4**: documentation — per-object locks (SM0.I) are
    inside their owning objects with `.unheld` defaults, so
    locks are usable from the moment the static array is loaded.
    No init-order hazard exists for the SMP coordination path;
    documented in the Phase 5 source comment.
  - **SM1.D.5**: `per_cpu::check_per_cpu_invariants()` moved
    from Phase 4 (just before TPIDR_EL1 write) to Phase 1
    (just after UART init).  The check is platform-independent
    (verifies static const-init), so any phase works for
    correctness; running it as early as possible surfaces a
    regressed `PER_CPU_DATA` initialiser before the rest of
    boot can deepen the failure mode.  The Phase 1 banner now
    prints `"[boot] per-cpu data verified (N cores)"`.
  - **SM1.D.6**: `smp::bring_up_secondaries_with_limit(max_cores:
    usize) -> u32` — limit-aware bring-up entry point that
    takes a **total core count** (boot core + secondaries) and
    slices the MPIDR table accordingly.  `max_cores = 0` or `1`
    spawns no secondaries; `max_cores = 4` spawns all 3
    secondaries; `max_cores > 4` saturates to 4.  Useful for
    QEMU `-smp 2 -append "smp_max_cores=2"` regression testing
    without touching `MAX_SECONDARY_CORES`.

  **Test coverage**: 395 HAL tests (up from 327 at SM1.D start);
  68 new tests across three modules — 54 under
  `cmdline::tests::*` (parser branches, `parse_bool` aliases,
  quoted values, DTB-blob fixtures covering valid /
  missing-`chosen` / missing-`bootargs` / malformed-header paths,
  MAX_BOOTARGS_LEN buffer-size handling, UTF-8 validation
  fallback), 9 in `smp::tests::sm1d6_*` (covering
  `bring_up_secondaries_with_limit` saturation behaviour:
  zero/one/two/three/full/oversize/disabled, function-pointer
  signature pin, host-side global-state callability), and 5 in
  `boot::tests::sm1d_*` (pinning Phase 5 cmdline-helper
  resolution + default-config invariants).  Zero clippy warnings
  workspace-wide.  Full Tier 0+1+2 smoke test passes (Lean
  build, 395/395 HAL tests, 94/94 ABI conformance tests).

  **Build-script regression scanner**: new
  `scan_boot_rs_phase5_uses_cmdline` in `rust/sele4n-hal/build.rs`
  pins the textual presence of `cmdline::parse_cmdline_from_dtb(`
  and `cmdline::apply_cmdline_and_start_smp(` inside `boot.rs`.
  A refactor that drops either call (silently disabling Phase 5)
  fails the build with an actionable diagnostic before any
  binary is produced.

  **Audit-pass-1 refinements** (post-initial-landing deep audit;
  no separate version bump — refinements ship inside v0.31.6):
  - **HIGH-severity `/chosen` sub-node bootargs filtering**:
    the initial-landing walker matched `bootargs` anywhere in
    the `/chosen` subtree (including `/chosen/sub/bootargs`).
    A malicious DTB exploiting this could silently disable SMP
    by placing `/chosen/sub/bootargs = "smp_enabled=false"`.
    Fixed by adding `depth == chosen_depth` to the PROP match
    guard so only direct `/chosen/bootargs` is honoured.  Per
    FDT spec §3.5 the canonical property is the direct child;
    per §5.4.1 properties precede sub-nodes, so the direct
    bootargs is also found first when both exist.
  - **HIGH-severity `totalsize` slice-construction UB defense**:
    on aarch64 we constructed a slice over `totalsize` bytes
    where `totalsize` is read from the DTB itself.  A malicious
    `totalsize = 0xFFFF_FFFF` (~4 GiB) would trigger Undefined
    Behaviour at slice construction (Rust requires the full
    extent valid).  Added 2 MiB `MAX_DTB_SIZE` upper bound
    enforced both on aarch64 (against `hdr.totalsize`) and on
    the host test entry (against `blob.len()`).  DTBs exceeding
    the bound fall back to the default `CmdlineConfig` (same
    behaviour as missing DTB).
  - **MEDIUM `last_comp_version` forward-compat check**: the
    initial-landing form ignored the `last_comp_version` field
    (FDT spec §5.2: minimum parser version required to read the
    DTB).  A future v18+ DTB with new fields at v17 offsets
    would be silently misread.  Added `FDT_PARSER_VERSION = 17`
    constant and reject DTBs whose `last_comp_version > 17`.
  - **MEDIUM integer-overflow hardening**: every offset/length
    addition in the walker now uses `checked_add`; the property
    padding computation uses `(4 - (len % 4)) % 4` instead of
    `(len + 3) & !3` to avoid 32-bit overflow on adversarial
    `len`.  In practice unreachable on legitimate input but
    defends against future refactors that bypass validation.
  - **Test-isolation infrastructure**: added `pub(crate) fn
    bring_up_secondaries_with_limit_inner` (in `smp.rs`) and
    `pub(crate) fn apply_cmdline_and_start_smp_inner` (in
    `cmdline.rs`) — inner forms taking explicit state
    references so tests exercise the dispatch chain without
    touching the global `smp::SMP_ENABLED` atomic.  The
    pre-audit tests verified the algorithm by computing the
    expected slice manually; the post-audit tests go through
    the actual function under test.
  - **Code-quality**: simplified boot.rs Phase 5 (single
    unconditional `apply_cmdline_and_start_smp` call instead of
    duplicated calls in both arms of an `if`); renamed
    `rust_boot_main`'s `_dtb_ptr` parameter to `dtb_ptr` now
    that it's used unconditionally in Phase 5.

  **Audit-pass-1 test coverage delta**: 420 HAL tests (was 395
  at initial landing; +25 audit-pass tests across cmdline.rs
  and smp.rs).  Per-file math: +17 audit-pass-1 tests in
  cmdline.rs (4 chosen sub-node / version regression tests, 2
  MAX_DTB_SIZE bound tests, 2 sanity / pin tests, 1 padding
  stress, 6 apply_inner dispatch tests, 2 signature pins) + 8
  inner-form tests in smp.rs (`sm1d6_inner_*` covering
  zero/one/two/four max_cores, oversize saturation, disabled
  state, short-table defense, signature pin).  Zero clippy
  warnings workspace-wide; full Tier 0+1+2 smoke green; full
  Tier 3 invariant surface green.

  **Audit-pass-2 refinements** (second deep audit, post-pass-1;
  also in v0.31.6):
  - **MEDIUM `validate_fdt_header` boundary hardening**: added
    checks that `off_dt_struct >= FDT_HEADER_SIZE` and
    `off_dt_strings >= FDT_HEADER_SIZE` so a hostile DTB with
    `off_dt_struct = 0` (structure block overlapping the
    header) is rejected at validate rather than fail-closing
    in the walker.  An `off_dt_strings` overlapping the header
    could also have a property's nameoff lookup return header
    bytes as a property name — same rejection.
  - **MEDIUM fail-closed regression tests for malformed-walker
    paths**: added `dtb_with_unknown_fdt_token_yields_empty`
    (unknown FDT token → None),
    `dtb_with_nop_chain_terminates_via_fuel_exhaustion`
    (FDT_NOP chain without FDT_END terminates via fuel
    exhaustion rather than spinning), and
    `dtb_with_deep_nesting_rejected_via_depth_bound` (>
    FDT_MAX_DEPTH nested nodes rejected).  These close
    coverage gaps in the malicious-DTB threat model.
  - **Cleanup**: removed the obsolete pre-pass-1 test
    `apply_disabled_returns_zero_online` (was a no-op that
    didn't call the function under test; pass-1's
    `apply_inner_*` tests supersede it).

  **Audit-pass-2 test coverage delta**: 425 HAL tests (was 420
  at audit-pass-1 close).  Per-file math: +6 audit-pass-2
  regression tests in cmdline.rs (3 header-offset bound, 1
  unknown token, 1 NOP fuel exhaustion, 1 depth bound) − 1
  obsolete pre-pass-1 cleanup.  Net +5; full Tier 0+1+2+3 still
  green.

  **Items deferred past v1.0.0 with correctness impact**: NONE.

  Follow-on: SM1.E (IS-variant TLBI), SM1.F (SGI primitive),
  SM1.G (Per-core UART), SM1.H (QEMU SMP integration test) —
  see
  [`docs/planning/SMP_RUST_HAL_PLAN.md`](docs/planning/SMP_RUST_HAL_PLAN.md)
  §§5.5..5.8.

  **WS-SM SM1.E/F/G/H LANDED at v0.31.7 on branch
  `claude/review-codebase-tlb-plan-L8PzR`** (cross-core TLBI
  broadcast + SGI primitives + per-core kprintln + QEMU SMP
  integration tests).  Twenty-one sub-tasks across four phases
  landed in one cut, completing the SM1 Rust HAL surface so SM5+
  per-core kernel state lands on a fully-functional cross-core
  HAL.

  - **WS-SM SM1.E.1**: 4 IS-variant TLBI wrappers
    (`tlbi_vmalle1is`, `tlbi_vae1is`, `tlbi_aside1is`,
    `tlbi_vale1is`) with `dsb ish` + `isb` post-TLBI bracket per
    ARM ARM D8.11.  Each broadcasts to every PE in the
    inner-shareable domain, the operative cross-core TLB
    invalidation primitive that SM7 (TLB shootdown) consumes.
  - **WS-SM SM1.E.2**: 4 OS-variant TLBI wrappers
    (`tlbi_vmalle1os`, `tlbi_vae1os`, `tlbi_aside1os`,
    `tlbi_vale1os`) with `dsb osh` + `isb` post-TLBI bracket.
    Pre-positioned for multi-cluster ports (BCM2712 is
    single-cluster, so functionally identical to IS on RPi5).
  - **WS-SM SM1.E.3**: `tlbi_for_sharing(domain, op)` dispatcher
    with two new typed enums: `SharingDomain` (Inner/Outer
    mirrors the Lean SM0.F enum) and `TlbInvalidation`
    (Vmalle1/Vae1/Aside1/Vale1 op selector).  Routes to one of
    the eight underlying IS/OS variants based on the platform's
    binding.  Single entry point that kernel-side TLB
    invalidation must use.
  - **WS-SM SM1.E.4**: Lean FFI binding `ffiTlbiForSharing` +
    typed `Architecture.tlbiForSharing` wrapper (in NEW FILE
    `SeLe4n/Kernel/Architecture/TlbiForSharing.lean`, ~270 LoC
    incl. tag-encoding theorems).  Encodes
    `(SharingDomain, TlbInvalidation)` as `(domainTag, opTag,
    asid, vaddr)` tuple for C-callable transmission.  Tag
    encoding pinned at the type level via injectivity +
    in-range theorems
    (`SharingDomain.toTag_injective`,
    `SharingDomain.toTag_in_range`,
    `TlbInvalidation.toOpTag_in_range`,
    `TlbInvalidation.toOpTag_distinct_constructors`).  Module
    staged via `Platform.Staged` for SM7 consumption.
  - **WS-SM SM1.E.5** (deferred to SM7): kernel-side caller
    migration — at SM1.E the existing `ffi_tlbi_*` exports
    (local non-broadcast TLBI) remain reserved for the boot-time
    MMU-init path before secondaries start.  SM7 (TLB shootdown)
    will migrate every kernel-side TLB callsite to route through
    `tlbiForSharing` per the SMP-correctness contract documented
    in `tlb.rs` module header.

  - **WS-SM SM1.F.1**: `GICD_SGIR` register constant + 16-INTID
    bound + 3 TargetListFilter discriminant constants
    (`SGI_TLF_CPU_TARGET_LIST = 0b00`,
    `SGI_TLF_ALL_BUT_SELF = 0b01`,
    `SGI_TLF_SELF_ONLY = 0b10`) per GIC-400 TRM §4.3.13.
    Encoder helper `encode_sgir(tlf, mask, intid) -> u32`
    factored out for bit-level testing.
  - **WS-SM SM1.F.2/3/4**: 3 send-SGI variants
    (`send_sgi(target_mask, intid)` for explicit per-target
    addressing; `send_sgi_to_self(intid)` for self-deferred
    work; `send_sgi_to_all_but_self(intid)` for the most common
    SMP-coordination broadcast).  All three panic on
    `intid >= 16` and emit `dsb ish` BEFORE the GICD_SGIR
    write per SM1.F.8 / ARM ARM B2.7.5 (prior kernel-state
    writes must be visible on every IS-domain PE before the SGI
    fires on the receiver).
  - **WS-SM SM1.F.5**: SGI handler dispatch infrastructure.
    `SgiHandler = fn(intid: u8, source_cpu: u8)` type;
    `static mut SGI_HANDLERS: [Option<SgiHandler>; 16]` per-INTID
    table (write-once at boot; read-only thereafter — the
    discipline that makes `static mut` sound here);
    `unsafe fn register_sgi_handler(intid, handler)` for
    boot-time registration; `fn lookup_sgi_handler(intid)`
    public reader; `fn dispatch_sgi(intid, source_cpu)`
    invoked from the trap handler when an SGI INTID is acked.
    `iar_source_cpu(iar) -> u8` extracts source-CPU bits
    `[12:10]` from `GICC_IAR` per GIC-400 TRM §4.4.4.
  - **WS-SM SM1.F.6**: 3 Lean FFI bindings
    (`ffiSendSgi`, `ffiSendSgiToSelf`, `ffiSendSgiToAllButSelf`)
    in `SeLe4n/Platform/FFI.lean` + matching Rust `#[no_mangle]
    pub extern "C"` exports in `ffi.rs`.  Lean callers wrap
    these via `SgiKind.toIntid` (typed `Fin 16`) so the
    Rust-side bound check never trips on a well-formed call.
  - **WS-SM SM1.F.7**: 33 new tests in `gic::tests::sm1f*`
    covering encoder bit-fields, range enforcement, dispatch
    routing, IAR source-CPU extraction, handler registration
    + lookup; 9 new tests in `ffi::tests::sm1f6*` covering
    every kernel-reserved INTID + signature pinning.
  - **WS-SM SM1.F.8**: ARM ARM B2.7.5 ordering documentation +
    NEW build-script scanner `scan_gic_rs_send_sgi_emits_dsb_ish`
    in `rust/sele4n-hal/build.rs` that pins every send_sgi*
    function body to emit `crate::barriers::dsb_ish()` BEFORE
    `mmio_write32(GICD_BASE + gicd::SGIR, ...)`.  A regression
    that drops the DSB or reorders it after the SGIR write
    fails the build with an actionable diagnostic.

  - **WS-SM SM1.G.1**: `UartLock` audit documentation block in
    `uart.rs` header.  Documents the AtomicBool spinlock's
    correctness under SMP via Acquire/Release semantics, plus
    the IRQ-safety contract via per-acquire DAIF mask.  Documents
    the FIFO-fairness gap that SM2's `TicketLock` will close
    when SM2.B lands — at which point `UartLock` is replaced
    structurally without changing the public `with_boot_uart`
    interface.
  - **WS-SM SM1.G.2**: Per-core boot banner verification.
    Already done in SM1.C.5 (each secondary emits 7 banner
    lines through MMU/VBAR/GIC/timer/IRQ-unmask init steps);
    SM1.H.1 verifies them.
  - **WS-SM SM1.G.3**: Per-core kprintln stress test.
    `tests/test_qemu_smp_kprintln_stress.sh` boots QEMU `-smp 4`
    and verifies the captured UART log has no torn output (no
    line with two `[core N]` prefixes, every core emits at
    least one stress line, etc.).  SKIPs at SM1.G if the
    stress-test routine isn't wired in the kernel image
    (kernel-side wiring is the SM5+ follow-on).
  - **WS-SM SM1.G.4**: `kprintln_core!` + `kprint_core!` macros.
    Prefix every line with `[core N]` where N is read from
    TPIDR_EL1 via `per_cpu::current_core_id_from_tpidr`.
    Useful for SMP boot tracing where per-core attribution
    matters.  6 new tests in `uart::tests::sm1g4*` cover macro
    expansion, the no-arg form, lock-balance discipline,
    and repeated invocations.

  - **WS-SM SM1.H.1**: `scripts/test_qemu_smp_bringup.sh` —
    full QEMU `-smp 4` bringup test.  Replaces the SM0.T
    SKIP-only stub.  Boots `-machine virt,secure=on,virtualization=on -cpu cortex-a76 -smp 4`,
    captures UART log, verifies each of cores 0..3 reaches its
    `[smp] core N: ready, entering kernel` banner.  Also
    verifies the boot core emits the Phase 5 `secondary core(s)
    online` banner.  SKIPs cleanly when QEMU or the kernel
    image is missing.
  - **WS-SM SM1.H.2**: Tier-4 nightly wiring.
    `scripts/test_tier4_smp_bootcheck.sh` (was a SKIP-only stub
    at SM0.T) now routes through SM1.H.1 + SM1.H.3 + SM1.H.5 +
    SM1.G.3 sub-tests, each handling its own SKIP conditions.
    Available via `NIGHTLY_ENABLE_EXPERIMENTAL=1
    ./scripts/test_nightly.sh`.
  - **WS-SM SM1.H.3**: `scripts/test_qemu_smp_minimal.sh` —
    minimal `-smp 2` bringup (boot + 1 secondary).  Useful for
    diagnostic boots after a HAL change without exercising
    the full 4-core race.
  - **WS-SM SM1.H.4**: UART log capture + banner verification.
    Embedded in SM1.H.1.
  - **WS-SM SM1.H.5**: `scripts/test_qemu_smp_sgi_roundtrip.sh`
    — cross-core SGI round-trip test.  Boot core sends an SGI
    to core 1; core 1's handler increments a shared counter
    then sends an ACK SGI back.  SKIPs at SM1.H if the
    kernel-side test handlers are not yet wired (Lean-side
    handler registration requires SM5+ per-core scheduler state
    to register from the verified kernel; the underlying HAL
    primitives are present + unit-tested at SM1.F).

  **Test coverage**: 510 HAL tests (up from 425 at SM1.D close;
  +85 new tests across `tlb.rs`, `gic.rs`, `ffi.rs`, `uart.rs`).
  Per-file: +32 in `tlb::tests::sm1e*` (operand encoding, IS/OS
  variants, dispatcher), +9 in `ffi::tests::sm1e4*` (TLBI
  dispatcher FFI), +33 in `gic::tests::sm1f*` (SGI primitives +
  handler dispatch + IAR source-CPU extractor), +9 in
  `ffi::tests::sm1f6*` (SGI FFI exports), +6 in `uart::tests::sm1g4*`
  (kprintln_core! macro), +1 ignored in `uart::tests::sm1g3_*`
  (cross-core stress placeholder).  Lean-side: +18 surface
  anchors + 11 decidable examples + 16 runtime assertions in
  `tests/SmpFoundationsSuite.lean` covering SM1.E.4 tag encoding
  + SM1.F.6 SGI FFI binding well-formedness.  Zero clippy
  warnings workspace-wide.

  **Build-script regression scanner**: NEW
  `scan_gic_rs_send_sgi_emits_dsb_ish` in
  `rust/sele4n-hal/build.rs` pins the SM1.F.8 ordering contract
  (every `send_sgi*` body must emit `crate::barriers::dsb_ish()`
  BEFORE `mmio_write32(GICD_BASE + gicd::SGIR, ...)`).

  **Module reachability**: `Architecture.TlbiForSharing` is
  staged via `Platform.Staged` (added to the SM1.E
  `staged_module_allowlist.txt` entry); SM7 promotes it
  production-reached when cross-core TLB shootdown lands.

  **Items deferred past v1.0.0 with correctness impact**: NONE.

  Follow-on: SM1.I (miscellaneous HAL improvements) and the
  SM2..SM9 phases — see
  [`docs/planning/SMP_RUST_HAL_PLAN.md`](docs/planning/SMP_RUST_HAL_PLAN.md)
  §5.9 and the master overview
  [`docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md`](docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md).

  **Audit-pass-1 refinements** (post-initial-landing deep audit;
  also in v0.31.7):
  - HIGH-severity: TLB encoder mask was 48 bits, should be 44 bits
    per ARM ARM C6.2.311 (VA[55:12] field; bits [47:44] are RES0 or
    TTL on FEAT_TTL hardware).  Mask tightened from
    `0x0000_FFFF_FFFF_FFFF` (48 bits) to `0x0000_0FFF_FFFF_FFFF`
    (44 bits).  Adversarial vaddr ≥ 2^56 would have silently set
    TTL=0b0001 (level-1 skip hint) on FEAT_TTL hardware,
    changing TLBI semantics.
  - HIGH-severity: `ffi_tlbi_for_sharing` silent fallback violated
    fail-closed.  Unknown `domain_tag` (≥ 2) fell back to Inner;
    unknown `op_tag` (≥ 4) silently became a no-op.  Both were
    caller-correctness violations (silently changed broadcast scope
    or skipped invalidation).  Refactored to use `Option`-returning
    `decode_sharing_domain_tag` / `decode_tlb_invalidation_tag`
    `const fn` helpers; FFI wrapper panics on None (fails closed
    under `panic = "abort"`).  Well-formed Lean callers cannot trip
    the panic (proven by `SharingDomain.toTag_in_range` /
    `TlbInvalidation.toOpTag_in_range`).
  - HIGH-severity: SGI delivery to secondaries was non-functional.
    Per GIC-400 TRM §4.3.5, GICD_ISENABLER0 (covering INTIDs 0..31)
    is banked per-core; primary's `init_distributor` only enabled
    its own bank.  Without per-core enable, SGIs sent to
    secondaries would stay pending forever, and secondary timer
    PPIs would never fire.  Fix: `init_cpu_interface_secondary`
    now writes ISENABLER0 = 0xFFFFFFFF from the secondary's bank.
  - MEDIUM: `kprintln_core!` was NOT per-line atomic despite
    documentation claiming it was.  Pre-audit macro expanded to two
    `kprint!` calls (body + `"\n"`), each acquiring the lock
    separately — IRQ between them could insert a torn line.
    Fix: single `with_boot_uart` closure with `writeln!` holds the
    lock for the entire `[core N] <body>\n` sequence.
  - MEDIUM: SGI handler tests raced on `static mut SGI_HANDLERS`
    (two tests both wrote to slot 14).  Refactored
    `dispatch_sgi` / `register_sgi_handler` / `lookup_sgi_handler`
    into testable `_in`-suffixed inner forms taking explicit slice
    references; tests use stack-local handler tables.
  - MEDIUM: `static_mut_refs` lint warnings from the new SGI
    wrappers (would be hard errors in Rust edition 2024).  Fixed
    by switching to `&raw mut` / `&raw const` syntax.

  **Audit-pass-1 test coverage delta**: 527 HAL tests (was 510 at
  initial landing; +17 net new defensive tests including the bogus
  silent-fallback tests removed).  Zero clippy warnings workspace-
  wide.

  **Audit-pass-3 refinements** (third deep-audit, post-pass-2):
  - HIGH: per-core GICD_ICPENDR0 clear added to
    `init_cpu_interface_secondary`.  Pass-2 added IGROUPR0,
    IPRIORITYR0..7, ISENABLER0; pass-3 completes the banked-write
    parity by also clearing ICPENDR0 (banked per-core per GIC-400
    TRM §4.3.8).  Defense-in-depth against stale pending bits left
    by hostile PSCI or soft-reset paths.
  - MEDIUM: canonical init order — reordered the per-core
    distributor writes in `init_cpu_interface_secondary` to match
    GIC-400 TRM §3.1.1 Table 3-1: GROUP → PRIORITY → CLEAR_PENDING
    → ENABLE → CTLR (was: ENABLE → PRIORITY → GROUP, functionally
    fine on fresh boot but not spec-compliant for re-init).
  - STRENGTHENING: new `tlbiForSharing_ffi_args_in_range` theorem
    in `SeLe4n.Kernel.Architecture.TlbiForSharing` — explicit
    Lean-side proof that well-formed callers cannot trip the Rust
    FFI fail-closed panic.  Surface-anchored in
    `tests/SmpFoundationsSuite.lean` + tier-3 invariant surface.
  - 2 new GIC tests pin ICPENDR0 mask + canonical init order.

  **Audit-pass-2 refinements** (second deep audit, post-pass-1;
  also in v0.31.7):
  - HIGH: per-core GICD_IPRIORITYR0..7 + GICD_IGROUPR0 init in
    `init_cpu_interface_secondary`.  Pass-1 added ISENABLER0, but
    IPRIORITYR0..7 and IGROUPR0 are also banked per-core (GIC-400
    TRM §4.3.11 / §4.3.4).  Without per-core priority init,
    secondaries' PPI/SGI priorities reset to implementation-defined
    values (often 0xFF = MASKED by GICC_PMR=0xFF per TRM §4.4.2).
    Even with ISENABLER0 enabled, priority 0xFF rejects delivery
    so SGIs to secondaries would still silently fail.  Fix:
    write priority 0xA0 to all 8 IPRIORITYR registers + IGROUPR0=0.
  - LOW: QEMU script kernel-image path misleading.
    `${REPO_ROOT}/rust/target/aarch64-unknown-none/release/sele4n-hal`
    never exists because `sele4n-hal` is `[lib]` not `[[bin]]`.
    Require explicit `SELE4N_KERNEL_IMAGE` env var; SKIP message
    documents that the kernel binary target is SM5+ work.
  - LOW: SgiHandler docstring missing safety contract (no panic,
    no reentrancy, must be fast).  Added.  Plus fixed off-by-one
    in `register_sgi_handler_in` assert message ("at least
    MAX_SGI_INTID + 1" → "at least MAX_SGI_INTID").
  - LOW: trap.rs `handle_irq` "unhandled INTID" comment didn't
    mention SGIs.  Updated to note SM5+ SGI dispatch wiring needs
    a `dispatch_irq` refactor preserving source_cpu from GICC_IAR.

  **WS-SM SM1.I LANDED at v0.31.8 on branch
  `claude/review-hal-improvements-jwTzB`** (miscellaneous HAL
  improvements; closes SM1 acceptance gate).  Six sub-tasks landed
  in one cut, completing the SM1 Rust HAL surface with the SM5
  landing seams + cross-core test infrastructure required for the
  SM5+ per-core scheduler integration:

  - **WS-SM SM1.I.1**: `trap.rs::handle_irq_per_core` — per-core
    IRQ handler entry that reads the calling core's id via
    TPIDR_EL1 (`per_cpu::current_core_id_from_tpidr`), records
    per-core IRQ dispatch / timer-tick / SGI statistics via
    `per_cpu_stats::record_*`, then dispatches via
    `gic::dispatch_irq` with per-core attribution in the
    unhandled-INTID log line.  Added as the SM5 landing seam —
    SM5 will redirect `trap.S`'s IRQ entry from `handle_irq` to
    `handle_irq_per_core`.  Both functions have identical
    `extern "C" fn(&mut TrapFrame)` signatures so the SM5 swap is
    a single function-pointer change.  SGI dispatch increments
    the per-core counter but does NOT route through the SGI
    handler table (`gic::dispatch_irq` discards the source-CPU
    bits of GICC_IAR; SM5 will refactor `dispatch_irq` to
    preserve the full IAR).  New build-script scanner
    `scan_trap_rs_handle_irq_per_core_intact` pins the function's
    existence, `#[no_mangle]` attribute, `record_irq_dispatch`
    call, and `current_core_id_from_tpidr` read at elaboration
    time so SM5's swap cannot regress silently.
  - **WS-SM SM1.I.2**: GICC_PMR per-core banking documentation in
    `gic.rs` module header.  Per GIC-400 TRM §4.4.2 / §3.1.4, the
    priority mask register is banked per-core at hardware level —
    each core's banked view is reached via the same MMIO base
    address.  Documentation covers: PMR per-core banking,
    distributor banking for INTIDs 0..31 (GICD_IGROUPR0,
    GICD_IPRIORITYR0..7, GICD_ICPENDR0, GICD_ISENABLER0 — why
    `init_cpu_interface_secondary` must run on every secondary),
    and DAIF.I per-PE scoping (ARM ARM C5.2.5).  Cross-referenced
    in `interrupts.rs` covering DAIF + PMR composition (two
    layers of per-core IRQ masking, both inherently per-PE).
  - **WS-SM SM1.I.3**: per-core idle-wait primitives at three
    layers — Rust (`cpu::idle_wait`, `cpu::idle_wait_bounded`),
    FFI (`ffi_idle_wait`, `ffi_idle_wait_bounded`), Lean
    (`Concurrency.Runtime.idleWait`, `Concurrency.Runtime.idleWaitBounded`).
    Wraps `cpu::wfe` / `cpu::wfe_bounded` with idle-TCB-tailored
    docstrings.  At SM1.I.3 the Lean kernel has no per-core idle
    TCB to call these from; SM5 will wire the idle-thread body to
    invoke these wrappers.  Tier-3 surface scanner pins both FFI
    exports and the Lean typed wrappers so the SM5 wiring cannot
    regress.
  - **WS-SM SM1.I.4**: per-core exception statistics module
    `rust/sele4n-hal/src/per_cpu_stats.rs` (~550 LoC).  Introduces
    `PerCpuStats` struct (`#[repr(C, align(64))]` — one cache line
    per slot, eliminates false sharing between cores' counters)
    with six AtomicU64 counters (`irq_count`, `timer_tick_count`,
    `sgi_count`, `syscall_count`, `vmfault_count`,
    `user_exception_count`) + 2-slot reserved tail for SM5+
    growth.  Compile-time `const _: ()` assertions pin
    `size_of::<PerCpuStats>() == 64` and `align_of::<PerCpuStats>()
    == 64`.  `PER_CPU_STATS` global array with one slot per core.
    Write path: `record_*` functions (Relaxed atomics, wait-free,
    off the correctness path) called from
    `handle_irq_per_core` (SM1.I.1) and from
    `handle_synchronous_exception` (SVC → syscall_count; DABT/
    IABT → vmfault_count; alignment / unknown EC →
    user_exception_count).  Read path: `*_count_for(core_id)`
    Relaxed-snapshot accessors with defensive out-of-range
    return-0 contract.  Inner forms (`record_*_in_slice`,
    `current_per_cpu_stats`) for unit-testing cross-core
    scenarios without racing on the global static.  Aggregate
    `total_irq_count` / `total_syscall_count` helpers for
    single-line diagnostic display.  FFI exports
    `ffi_per_core_irq_count` (+ 3 siblings) and Lean typed
    wrappers `Concurrency.perCoreIrqCount(core : CoreId)` (+ 3
    siblings) with marker theorem
    `perCoreIrqCount_returns_baseio_uint64_marker` as Tier-3
    surface anchor.
  - **WS-SM SM1.I.5**: comprehensive SEV / WFE coordination
    documentation in `cpu.rs` module header (~140 lines).  Covers
    ARMv8-A local event register semantics (ARM ARM B2.10), `wfe`
    (C6.2.353) / `sev` (C6.2.243) / `sevl` (C6.2.244) instruction
    semantics, inner-shareable broadcast scope (BCM2712 =
    single-cluster = one IS domain), kernel policy for emitting
    SEV (`bring_up_secondaries`, SM2+ lock release, cross-core
    SGI fallback), when NOT to use SEV (memory ordering, interrupt
    delivery, synchronisation primitive), bounded WFE interaction
    with the local event register.  Plus new `cpu::sev()` and
    `cpu::sevl()` wrappers around the underlying instructions for
    testability (the production SEV emission still lives inline in
    `smp.rs::bring_up_secondaries_inner` to keep it co-located
    with the AN9-J.4.d broadcast point).
  - **WS-SM SM1.I.6**: 8 new cross-core test scenarios in
    `smp::tests::sm1i6_*` exercising the SM1.I infrastructure —
    per-core stats no-aliasing, validator per-core dispatch,
    init helper idempotence, CORE_READY monotonicity, SGI
    distribution, full composition.  All tests use the existing
    `*_inner` / `*_in_slice` helpers so each test owns its own
    state and never depends on global mutable atomics that cargo's
    parallel test runner could race against.

  **Test coverage**: 583 HAL tests at initial-landing snapshot (up from 510 at SM1.E/F/G/H
  close — +73 SM1.I tests covering: 16 in `per_cpu_stats::tests`
  for the new module, 11 in `trap::tests` for SM1.I.1 +
  per-core-stats wiring, 8 in `cpu::tests` for SM1.I.3 + SM1.I.5
  wrappers, 17 in `ffi::tests` for the new FFI exports, 8 in
  `smp::tests::sm1i6_*` cross-core scenarios, 1 deferred in
  `uart::tests`).  Lean-side: 12 new surface anchors + runtime
  decidable examples in `tests/SmpFoundationsSuite.lean` covering
  SM1.I.3 / SM1.I.4 FFI binding well-formedness and Lean typed
  wrapper structural witnesses.  Zero clippy warnings workspace-
  wide.  Full Tier 0+1+2+3 still green.

  **Audit-pass-1 refinements** (post-initial-landing): two
  pre-existing parallel-test races surfaced under the SM1.I
  expansion (more tests touching shared globals + more parallel
  cargo workers).  Both fixed with private `std::sync::Mutex`
  serialization within the test profile:
  - UART_LOCK observation tests (`sm1g4_kprintln_core_*_acquires_lock_*`)
    converted from the pre-SM1.I racy "observe global atomic
    before/after" pattern to a deterministic re-acquire pattern:
    after the macro returns, the test acquires the lock itself
    via `with_boot_uart` — if the macro had failed to release,
    this would deadlock-spin and cargo's test timeout surface
    the regression.  Plus `SM1G4_OBSERVATION_MUTEX` serializes
    the observation tests against each other.
  - TIMER_INTERVAL / TICK_COUNT tests (the cluster of write-then-
    read tests on these two atomics) wrapped in a private
    `TIMER_GLOBAL_STATE_MUTEX` so concurrent timer tests don't
    overwrite each other's pre-conditions.  Stress-testing
    confirms failure rate drops from ~10–15% to 0% across both
    fixes.

  **Build-script regression scanner**: NEW
  `scan_trap_rs_handle_irq_per_core_intact` in
  `rust/sele4n-hal/build.rs` pins the four SM1.I.1 contract
  properties (function existence, `#[no_mangle]`, `record_irq_dispatch`
  call, `current_core_id_from_tpidr` read) at elaboration time
  so the SM5 swap cannot regress silently.

  **Module reachability**: `Concurrency.Runtime` extension
  (`idleWait`, `idleWaitBounded`, `perCore*Count`) is already in
  the staged closure via `Platform.Staged` (SM1.B's earlier
  registration covers the file).  No additional staging required.

  **Audit-pass-2 refinements** (post-audit-pass-1 deep audit;
  also in v0.31.8):
  - **CORRECTNESS**: moved `record_irq_dispatch()` from the
    pre-dispatch path INTO the `gic::dispatch_irq` closure so
    only `Handled(intid)` IRQs advance the counter (not spurious
    INTIDs >= 1020 or out-of-range `[224, 1020)` INTIDs).  The
    counter now matches its docstring claim of "non-spurious
    IRQs that reach the dispatcher" rather than "every IAR
    read".  More useful for SM5+ scheduler observability.
  - **CODE-QUALITY**: simplified the SGI branch condition in
    `handle_irq_per_core` from `(intid as u8) < MAX_SGI_INTID &&
    intid < u32::from(MAX_SGI_INTID)` (redundant) to just
    `intid < u32::from(MAX_SGI_INTID)`.
  - **DEFENSE-IN-DEPTH**: every `record_*` function in
    `per_cpu_stats.rs` switched from `fetch_add(1) + 1` to
    `fetch_add(1).wrapping_add(1)`.  Counter wrap at `u64::MAX`
    is practically unreachable (~200 years at GHz frequency) but
    the wrapping form has defined behavior at every input,
    avoiding a debug-build panic at the boundary.  3 new wrap
    tests cover the boundary.
  - **DEFENSE-IN-DEPTH**: every `ffi_per_core_*_count(core_id: u64)`
    FFI export now performs the bound check in `u64` space
    before the `as usize` cast.  Sele4n's only target is aarch64
    (u64 == usize), so the cast is identity in practice; the
    defense ensures a hypothetical 32-bit port wouldn't silently
    truncate the high bits and alias an out-of-range probe (e.g.,
    `core_id = 0x1_0000_0001` truncated to `1`) to an in-range
    slot.  4 new truncation-defense tests cover the boundary.
  - **TEST COVERAGE**: 2 new runtime invocation tests for
    `handle_irq_per_core` (verify no panic, verify counter
    advances).  5 new Lean marker theorems for sibling per-core
    stats wrappers + idle-wait wrappers (`perCoreTimerTickCount`,
    `perCoreSgiCount`, `perCoreSyscallCount`, `idleWait`,
    `idleWaitBounded`) — surface-anchored in tier-3 +
    SmpFoundationsSuite.

  **Test coverage after audit-pass-2**: 592 HAL tests (+9 from
  audit-pass-1; total +82 over SM1.E/F/G/H baseline of 510)
  + 1 ignored (`sm1g3_cross_core_kprintln_stress` placeholder).
  Zero clippy warnings workspace-wide.  Full Tier 0+1+2+3 still
  green.  Stress-tested 10/10 runs of the full Rust suite with
  `--features std`.

  **Audit-pass-3 refinement** (post-audit-pass-2 external audit;
  also in v0.31.8): closed one HIGH-severity test-race the
  audit-pass-1 / pass-2 mutex fixes had missed.

  - **HIGH (test reliability)**: the SM1.I.4 trap-handler tests
    that observe `crate::per_cpu_stats::PER_CPU_STATS[0]`
    counters were not serialised against each other under
    cargo's parallel runner.  The
    `sm1i4_per_core_counters_track_distinct_exception_branches`
    test (which asserts `vm_after == vm_before` — strict
    equality, no tolerance for parallel writers) had an observed
    ~2% transient failure rate, surfacing whenever a sister test
    (`sm1i4_handle_sync_dabt_*` / `sm1i4_handle_sync_iabt_*`)
    incremented `vmfault_count` between the two snapshots.
    Audit-pass-3 adds a private
    `static SM1I4_OBSERVATION_MUTEX: std::sync::Mutex<()>` in the
    trap-tests module and wraps all 7 SM1.I.4 trap-handler tests
    that observe `PER_CPU_STATS[0]` via the mutex.  The 6 tests
    using `after > before` don't strictly need it (they tolerate
    parallel writers), but holding the mutex serialises them
    against the `assert_eq!` test, ensuring all observations are
    race-free.  Stress test post-fix: 50/50 runs pass (previously
    ~1/50 transient failure).

  **Audit-pass-4 refinements** (second external audit pass; also
  in v0.31.8): closed one HIGH-severity latent UB risk, one
  MEDIUM-severity log-tearing risk, and one LOW doc overcount.

  - **HIGH (latent UB on early-boot EL1 exceptions)**:
    `handle_synchronous_exception` reads TPIDR_EL1 via the
    `per_cpu_stats::record_*` path (SM1.I.4 wiring), but the
    Phase 4 TPIDR_EL1 write meant any EL1-originated synchronous
    exception during Phases 1-3 (kernel bug: misaligned access,
    instruction abort on unmapped kernel page) would dereference
    uninitialised TPIDR_EL1 as a pointer — UB before the
    defensive `assert!` could fire.  Fix: Phase 1 now writes
    TPIDR_EL1 immediately after `check_per_cpu_invariants` has
    validated the static array.  Phase 4's write is retained as
    an idempotent re-write (one extra `mrs tpidr_el1` cycle) so
    the SM5 landing-seam contract remains structurally visible
    at the Phase-4 site.  No correctness change on the happy
    path; the EL1-early-boot-exception window now reads valid
    TPIDR_EL1 instead of UB.

  - **MEDIUM (log tearing)**: `handle_irq_per_core` used
    `kprintln!("[core {}] ...", core_id, ...)` for SGI and
    unhandled-INTID log lines.  `kprintln!` expands to two
    separate `kprint!` calls (body + `"\n"`), each acquiring the
    UART lock separately; under SMP a concurrent writer between
    the prefix and the body could tear the log line.  Fix:
    switched both lines to `kprintln_core!` which holds the
    UART lock for the entire `[core N] <body>\n` sequence per
    SM1.G.4 audit-pass-1 atomicity contract.

  - **LOW (doc overcount)**: one residual "12 new cross-core
    test scenarios" in `docs/planning/SMP_RUST_HAL_PLAN.md`
    §5.9 header was missed by the audit-pass-3 sed sweep.
    Fixed to "8".

  - **DEFENSE-IN-DEPTH (poisoning)**: every `MUTEX.lock().unwrap()`
    in the three audit-pass-1/2/3 observation mutexes
    (`SM1G4_OBSERVATION_MUTEX`, `SM1I4_OBSERVATION_MUTEX`,
    `TIMER_GLOBAL_STATE_MUTEX`) converted to
    `MUTEX.lock().unwrap_or_else(|e| e.into_inner())`.  Without
    this, a failed `assert!` inside any mutex holder would
    poison the mutex and cascade-fail every subsequent test
    with `PoisonError`, burying the diagnostic of the *original*
    failure.  The recovery pattern lets subsequent tests run
    normally and surface their own diagnostics.  21 occurrences
    converted across trap.rs / uart.rs / timer.rs.

  **Items deferred past v1.0.0 with correctness impact**: NONE.

  **SM1 acceptance gate** (per
  [`docs/planning/SMP_RUST_HAL_PLAN.md`](docs/planning/SMP_RUST_HAL_PLAN.md)
  §8): all items checked.  WS-SM SM1 CLOSED at v0.31.8 with all
  nine sub-phases LANDED (SM1.A–SM1.I).  SM2 (verified lock
  primitives) and SM3+ (per-object locks → per-core scheduler →
  cross-core IPC → TLB shootdown → info-flow → release closure)
  follow per the master overview.

  **WS-SM SM2.A LANDED at v0.31.9 on branch
  `claude/review-codebase-memory-model-xxsh9`** (abstract memory
  model; foundation for SM2.B TicketLock + SM2.C RwLock release-
  acquire pairing proofs).  Twelve sub-tasks landed in one cut,
  exporting an operational ARMv8.1-A LSE memory model with the
  full happens-before partial-order witness chain that SM2.B and
  SM2.C will consume:

  - **SM2.A.1**: `MemoryOrder` inductive (5 ctors: `.relaxed`,
    `.acquire`, `.release`, `.acqRel`, `.seqCst`) with
    `isAcquire` / `isRelease` Bool selectors and 5 lookup
    witnesses (`acquire_isAcquire`, `release_isRelease`,
    `acqRel_both`, `seqCst_both`, `relaxed_neither`).  Maps to
    ARM ARM B2.3.7 release/acquire semantics.
  - **SM2.A.2**: `AtomicLocation` struct (single `id : Nat` field)
    with three concrete encoding helpers (`nextTicketOf`,
    `servingOf`, `rwLockStateOf`) and the
    `ticketLock_fields_distinct` non-aliasing witness.
  - **SM2.A.3**: `MemoryEvent` structure (6 fields: `core`, `loc`,
    `isWrite`, `order`, `value`, `seqNum`) with auto-derived
    `DecidableEq` so traces carry `Nodup`.
  - **SM2.A.4**: `MemoryTrace` structure (single `events : List
    MemoryEvent` field) plus `.empty` seed, `.append e` extension,
    and three structural witnesses (`empty_events`,
    `append_events`, `append_length`).
  - **SM2.A.5**: `MemoryTrace.wellFormed` predicate (two
    conjuncts: events `Nodup` + per-core `Pairwise` seqNum
    monotonicity) plus auto-derived `Decidable` instance and the
    `empty_wellFormed` witness.  Plus `eventPos` (canonical
    position via `List.idxOf`) with four bridging properties:
    `eventPos_lt_length` (in-trace events have valid index),
    `eventPos_eq_length_of_not_mem` (out-of-trace events return
    sentinel), `eventPos_get_eq` (`events.get` at the canonical
    index recovers the event under `LawfulBEq`), and
    `eventPos_inj` (positions uniquely identify events).
  - **SM2.A.6**: `synchronizesWith` (9-conjunct relation per ARM
    ARM B2.3.7 — both endpoints in trace, release-store +
    acquire-load discipline, same location, observed=released
    value, positional ordering) with two rejection witnesses
    (`synchronizesWith_relaxed_load_rejected`,
    `synchronizesWith_relaxed_store_rejected`).
  - **SM2.A.7**: `sequencedBefore` (4-conjunct relation — both
    endpoints in trace, same core, smaller seqNum) and
    `happensBefore` inductive (3 constructors: `.seq` lifts
    sequenced-before, `.sync` lifts synchronizes-with, `.trans`
    composes).  Plus `happensBefore_in_trace` (both endpoints
    derive from `in trace`) and `happensBefore_strict_positional`
    (the foundational inductive invariant — every hb edge
    strictly increases trace position under wellFormed).
  - **SM2.A.8**: `happensBefore_irreflexive` (Theorem 3.1.8.1) —
    no event hb-precedes itself.  Proved via the strict-positional
    invariant.
  - **SM2.A.9**: `happensBefore_transitive` (Theorem 3.1.8.2) —
    hb is closed under composition.  Immediate from the `.trans`
    constructor.
  - **SM2.A.10**: `happensBefore_antisymmetric` (Theorem 3.1.8.3)
    — distinct events cannot be mutually hb-related.  Proved via
    the strict-positional invariant and `Nat.lt_asymm`.
  - **SM2.A.11**: `happens_before_partial_order` (Theorem 3.1.8 —
    aggregate) — combines irreflexive, transitive, antisymmetric
    into a single statement.  The canonical surface anchor for
    SM2.B / SM2.C release-acquire pairing.  Plus
    `happens_before_strict_partial_order` (kernel-convenient
    form) and `happensBefore_no_cycle` (smoke-test form).
  - **SM2.A.12**: `tests/MemoryModelSuite.lean` (~675 LoC) —
    64 surface-anchor `#check` lines covering every public
    symbol, 39 decidable examples covering the data-type
    constructors / `wellFormed` true and false cases / RMW
    positive cases / single-event and append-step wellFormed
    cases / `eventPos` behaviour / partial-order shape /
    constructive `synchronizesWith` and `sequencedBefore`
    witnesses / helper-theorem lifts, and a runnable executable
    (`lake exe memory_model_suite`) with 50 runtime assertions
    via `assertBool`.  Wired into Tier 2 (negative) and Tier 3
    (invariant surface) per `scripts/test_tier2_negative.sh` and
    `scripts/test_tier3_invariant_surface.sh`.

  **File**: `SeLe4n/Kernel/Concurrency/MemoryModel.lean`
  (~700 LoC).  Staged via `SeLe4n/Platform/Staged.lean` (entry
  added to `scripts/staged_module_allowlist.txt` per the WS-RC
  R12.B partition gate); SM2.B (TicketLock) is the first runtime
  exerciser.

  **Mathematical correctness highlights**:
  - The proofs use a single foundational helper
    (`pairwise_get_lt`, private) that lifts `List.Pairwise R l`
    to per-position ordering `R l[i] l[j]` for `i < j`.  Proved
    by direct induction on `Pairwise` (~30 LoC).
  - The strict-positional invariant
    (`happensBefore_strict_positional`) is the inductive
    invariant that discharges both irreflexivity and
    antisymmetry.  Proof uses `Nat.lt_trichotomy` on positions
    in the seq case to discharge the wellFormed monotonicity
    against the sequenced-before hypothesis.
  - The `eventPos_inj` proof uses `Fin.eq_of_val_eq` +
    `congrArg t.events.get` to avoid the "motive is not type
    correct" failure that a direct `rw` on the dependent Fin
    index would hit.  The Nodup hypothesis is *not* required —
    `eventPos` is a function (returning the FIRST occurrence
    via `idxOf`), so equal positions yield equal events under
    any list shape.
  - No `Classical.choose`, no `noncomputable`: `eventPos` uses
    the computable `List.idxOf` (Nat-valued, with sentinel
    `l.length` for out-of-list events).

  **RMW design decision (audit-pass refinement)**: the
  per-core seqNum monotonicity in `wellFormed` uses non-strict
  `≤` (not strict `<`).  This deviates from the literal plan
  pseudocode (which uses `<`) but is required to model ARMv8.1-A
  LSE atomic Read-Modify-Write operations (`LDADDA`, `STADDL`,
  `CASAL`, …) per the plan's own §3.1.3 commentary: RMW ops are
  modelled as TWO events sharing one `seqNum` (load + store).
  A strict `<` would reject all RMW traces, blocking SM2.B's
  `next_ticket.fetch_add(1, Acquire)` proofs.  The non-strict
  `≤` allows RMW pairs at one atomic op while still preventing
  seqNum decrease within a core.  Strict ordering for
  happens-before is recovered by the strict `<` in
  `sequencedBefore` plus the `Nodup` clause.  Trade-off
  documented in the `wellFormed` docstring.

  **Helper theorems for SM2.B/SM2.C consumers**: in addition to
  the four canonical partial-order witnesses, the module
  exports eight convenience lifters:
  `sequencedBefore_implies_happensBefore`,
  `synchronizesWith_implies_happensBefore`,
  `MemoryTrace.wellFormed.nodup`,
  `MemoryTrace.wellFormed.pairwise`,
  `happensBefore_eventPos_lt`,
  `happensBefore_endpoints_in_trace_with_pos`,
  `MemoryTrace.singleton_wellFormed` (base case for the
  operational-semantics induction), and
  `MemoryTrace.wellFormed_append` (inductive step: appending a
  fresh event with monotone seqNum preserves wellFormed).
  These reduce the tactic burden on SM2.B (TicketLock) and
  SM2.C (RwLock) release-acquire pairing proofs, and let SM2.B/C
  build long well-formed traces step-by-step via a structural
  fold.

  **Axiom budget for SM2.A**: 0 Lean axioms, 0 sorries.  All
  ARMv8.1-A LSE semantics enter operationally as constraints on
  the trace shape; no `axiom` or `sorry` declarations.

  **Test coverage**: 50 new runtime assertions in
  `tests/MemoryModelSuite.lean` (full Tier 2 negative pass: every
  `decide` example also runs at runtime); 49 new tier-3 surface
  anchors in `scripts/test_tier3_invariant_surface.sh` (covers
  the four canonical theorems + eight helper lifters + all data-
  type and `eventPos` surfaces); 32 public-exported theorems +
  1 private helper in `MemoryModel.lean` (4 canonical partial-
  order + 8 helper lifters + 20 supporting witnesses and bridges);
  existing 592 HAL tests still pass; existing `smp_foundations_
  suite` still passes.  Full Tier 0+1+2+3 smoke test green.

  **Items deferred past v1.0.0 with correctness impact**: NONE.

  Follow-on: SM2.B (TicketLock spec + Rust impl) — **LANDED below**;
  SM2.C (RwLock), SM2.D (FFI bridge + integration), SM2.E
  (documentation) per
  [`docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md)
  §§5.3..5.5.

  **WS-SM SM2.B LANDED post-v0.31.9 on branch
  `claude/review-ticketlock-tasks-2ca8a`** (verified TicketLock
  spec + Rust impl; closes the second sub-phase of SM2 with all
  16 sub-tasks landed).  Three commits across the branch:

  - **SM2.B.1..B.9 + B.14 + B.15** (commit `ea4ea25`):
    abstract spec + substantive wf-preservation.
    `TicketLockState` 4-field structure (`nextTicket`,
    `serving`, `pending`, `held`) with `Repr`, `Inhabited`,
    `DecidableEq` derived; `unheld` canonical seed;
    `TicketLockOp` 3-constructor inductive (`tryAcquire`,
    `release`, `observeServing`).  Operational semantics:
    `captureTicket`, `observeServing`, `applyOp` (with fast-
    path immediate-promote), `promotePending`,
    `releaseAndPromote`.

    The `wf` predicate carries **8 conjuncts** (improvement
    over the plan's 7) — INV-T1..T7 from the plan plus a new
    **INV-T8 (count parity)**:
    `nextTicket = serving + |pending| + heldCount`.  The
    7-invariant form admits a non-reachable state
    `(held = some _, serving = nextTicket)` that
    `applyOp .tryAcquire` cannot exit via a wf-preserving
    step; INV-T8 closes the gap exactly.  Per the project's
    `implement-the-improvement` rule, the spec is strengthened
    to match the reachable state space.  Documented in the
    `wf` docstring with explicit counter-example.

    Substantive theorems:
    `ticketLock_mutex` (`Option.some` injectivity);
    `ticketLock_tryAcquire_preserves_wf` (~150 LoC: 4-branch
    case analysis × 8 invariants);
    `ticketLock_observeServing_preserves_wf` (trivial);
    `ticketLock_releaseAndPromote_preserves_wf` (~228 LoC:
    4-branch case analysis × 8 invariants);
    `ticketLock_release_preserves_partial_wf` (weaker form for
    raw `applyOp .release`); `ticketLock_wf_invariant`
    (aggregator); `ticketLock_applyOp_deterministic` +
    `ticketLock_promotePending_deterministic` (function-
    totality witnesses); `ticketLock_acquire_preserves_wf` +
    `ticketLock_release_preserves_wf` (SM2.B.15 closure-form
    aliases).

    The Lean 4.28 record-projection iota-reduction issue
    (where `omega` doesn't see through `{...}.field` projections
    in goal contexts) is resolved via the rfl-equality +
    explicit `rw` pattern: each preservation case introduces
    `have h_n : {post}.nextTicket = s.nextTicket := rfl` etc.,
    then `rw [h_n, h_s, h_p, h_hc]` rewrites the goal into a
    form omega can solve directly.

    File-local helpers: `nodup_snd_unique_entry`,
    `nodup_fst_unique_entry`, `nodup_fst_filter_length` (the
    third rewritten to avoid `simp`-driven predicate
    normalisation that diverged between goal and IH).

  - **SM2.B.10..B.13** (commit `9a18b83`): FIFO + bounded-wait
    + RA-pairing + reachability.  Five nextTicket-monotonicity
    helpers (`applyOp_nextTicket_monotone`,
    `applyOp_release_nextTicket_eq`,
    `promotePending_nextTicket_eq`,
    `releaseAndPromote_nextTicket_eq`,
    `applyOp_tryAcquire_captures`).  Pigeonhole helpers
    (`nodup_subset_length_le` generic; `nodup_corelist_length_bound`
    at Fin numCores).  Four theorems:
    `ticketLock_fifo` + `ticketLock_fifo_trace` (single-step +
    multi-step nextTicket monotonicity); `ticketLock_bounded_wait`
    (`nextTicket ≤ serving + numCores`);
    `ticketLock_release_acquire_pairing` +
    `ticketLock_release_acquire_happensBefore` (bridge to
    SM2.A `MemoryModel`); `ticketLock_reachability` (every
    reachable state is wf, via `KernelStep` inductive +
    `Reachable` RT closure).

  - **SM2.B.16 + tests + wiring** (commit `fb17624`): Rust
    impl + Lean test suite + build infrastructure.
    `rust/sele4n-hal/src/ticket_lock.rs` (538 LoC including
    tests): `TicketLock` `#[repr(C, align(64))]` with two
    `AtomicU64` fields; three public methods (`acquire`,
    `release`, `with_lock`); RAII `TicketLockGuard<'a>` with
    Drop-based release.  ARM ARM citations
    (LDADDA / LDAR / STADDL / SEV) in module docstring.

    21 Rust unit tests: initial-state, fast-path acquire,
    increment behaviour, full acquire-release cycle, with_lock
    execute + release, nested distinct locks, guard ticket
    accessor, cache-line alignment, const-fn-in-static, Default
    impl, signature pinning, FIFO at sequential level,
    100-cycle monotone counter, panic-safety
    (`with_lock_releases_on_panic`), cross-thread mutex stress
    (4 threads × 1000 ops, no lost updates), cross-thread FIFO
    observation (captured tickets form a permutation of
    0..NUM_THREADS), u64-wrap defensive documentation.  Zero
    clippy warnings.

    Lean test suite (`tests/TicketLockSuite.lean`, 458 LoC):
    90+ surface anchors covering every public SM2.B symbol;
    25+ decidable examples for unheld, fast-path/slow-path
    acquire, release-and-promote, observeServing identity,
    no-op tryAcquire, determinism, FIFO chain; 35 runtime
    `assertBool` assertions in `lake exe ticket_lock_suite`.

    Wiring: registered in `lakefile.toml` (`ticket_lock_suite`
    exe), `Staged.lean`, `staged_module_allowlist.txt`,
    `test_tier2_negative.sh` (runtime),
    `test_tier3_invariant_surface.sh` (surface anchors).

  **Audit-pass refinements** (included): `observeServing_eq_serving`
  witness theorem added so the abstract observation primitive
  is not orphaned.  Cross-thread Rust stress tests + panic-
  safety test added.

  **Test coverage**: 314 Lean jobs clean; 613 Rust HAL tests
  (was 592 baseline + 21 new for TicketLock; zero ignored);
  35 Lean runtime assertions in `ticket_lock_suite`.  Zero
  clippy warnings.  Full Tier 0+1+2+3 smoke test green.

  **Items deferred past v1.0.0 with correctness impact**: NONE.

  Follow-on: SM2.C (RwLock spec), SM2.D (FFI bridge +
  integration), SM2.E (documentation) per
  [`docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md)
  §§5.3..5.5.

  **WS-SM SM2.D LANDED on branch
  `claude/review-ffi-bridge-plan-traAL`** (FFI bridge + integration;
  closes the fourth sub-phase of SM2 with all 8 sub-tasks landed
  per the plan's acceptance gate).  Bridges the verified Lean
  TicketLock and RwLock specifications into a stable C-callable
  surface that the Lean kernel can consume via `@[extern]`
  declarations, plus the typed RAII combinators and SM2 theorem
  inventory:

  - **SM2.D.1 (Lean FFI for TicketLock)**: 6 `@[extern]`
    declarations in `SeLe4n/Platform/FFI.lean` —
    `ffiTicketLockStaticHandle`, `ffiTicketLockAcquire`,
    `ffiTicketLockRelease`, `ffiTicketLockPeekHolder`,
    `ffiTicketLockAcquireCount`, `ffiTicketLockReleaseCount`.
    Plus typed wrappers (`acquireTicketLock`, `releaseTicketLock`,
    `peekTicketLockHolder`, …) in NEW FILE
    `SeLe4n/Kernel/Concurrency/LockBridge.lean` (~470 LoC) with
    `TicketLockHandle` carrying a structural bound proof
    (`raw.toNat < staticTicketLockPoolSize`).
  - **SM2.D.2 (Lean FFI for RwLock)**: 10 `@[extern]` declarations
    (`ffiRwLockStaticHandle`, `ffiRwLockAcquireRead`,
    `ffiRwLockReleaseRead`, `ffiRwLockAcquireWrite`,
    `ffiRwLockReleaseWrite`, `ffiRwLockSnapshot`, plus 4
    per-counter accessors).  Typed wrappers
    (`acquireReadLock` / `releaseReadLock` / `acquireWriteLock` /
    `releaseWriteLock` / `snapshotRwLock`) with `RwLockHandle`.
  - **SM2.D.3 (RAII combinators)**: `withTicketLock`,
    `withReadLock`, `withWriteLock` in `LockBridge.lean` bracket
    an action with acquire / release.  Three marker theorems
    (`withTicketLock_unfold`, `withReadLock_unfold`,
    `withWriteLock_unfold`) pin the definitional unfolding;
    Tier-3 surface anchored.  Tests in NEW FILE
    `tests/LockBridgeSuite.lean` exercise structural properties.
  - **SM2.D.4 (Lock-state tracing)**: per-slot Relaxed AtomicU64
    counters in `rust/sele4n-hal/src/lock_bridge.rs`
    (`TICKET_LOCK_ACQUIRE_COUNT`, `TICKET_LOCK_RELEASE_COUNT`,
    plus 4 for RwLock); read accessors exposed via FFI.
    Always-on (wait-free); used by SM2.D.8 to verify FFI calls
    actually serialise.
  - **SM2.D.5 (Static linker-time check)**: TWO build.rs scanners
    (`scan_lock_bridge_rs_intact`,
    `scan_ffi_rs_exposes_lock_ffi_exports`) pin every required
    helper and every FFI export at elaboration time.  Plus NEW
    cross-language script `scripts/check_lock_ffi_symmetry.sh`
    (wired into Tier 0 hygiene) verifying that the Lean
    `@[extern]` declarations, Rust `pub extern "C"` exports, Rust
    helpers, and the Lean `lockPrimitives_count` vs. Rust
    `SM2_THEOREM_COUNT` constant all agree.
  - **SM2.D.6 (Surface anchors)**: NEW FILE
    `tests/SmpSurfaceAnchors.lean` covers every public SM2.D
    symbol with `#check` lines + decidable examples + runtime
    structural assertions.  Tier-3 wired.
  - **SM2.D.7 (`lockPrimitives` aggregator)**: NEW FILE
    `SeLe4n/Kernel/Concurrency/LockPrimitives.lean` (~210 LoC)
    aggregates all 22 substantive SM2 theorems (4 memory-model +
    6 TicketLock + 10 RwLock + 2 refinement) into a typed
    `LockPrimitiveTheorem` list with a `lockPrimitives.length =
    22` size witness + per-category count witnesses
    (`_memoryModel_count = 4`, `_ticketLock_count = 6`,
    `_rwLock_count = 10`, `_refinement_count = 2`,
    `_partition_sum`) + a NoDup witness on substantive
    identifiers.  Rust mirror: `SM2_THEOREM_COUNT = 22` in
    `lock_bridge.rs`; the cross-language script enforces
    agreement.
  - **SM2.D.8 (Cross-core test)**: 3 cross-thread tests in
    `lock_bridge.rs::runtime_tests::sm2d8_*` exercising
    `STATIC_TICKET_LOCK_POOL[3]` / `STATIC_RW_LOCK_POOL[3]` from
    4 threads × N ops; verifies trace-counter deltas exactly match
    expected totals (no lost updates, no double-increments).
    Plus a writer-readers-exclusion test asserting INV-R1 holds
    under cross-thread contention.  Coordinated via a private
    `SM2D8_SLOT3_MUTEX` so the three tests serialise against each
    other.

  **Handle encoding (SM2.D version)**: a `u64` opaque handle
  interpreted as a pool index (0..3 for each kind).  SM5 will
  extend the encoding for per-object locks via a high-bit tag;
  SM2.D-reserved low values remain source-compatible.  Decoders
  are fail-closed (`decode_ticket_lock_handle` / `decode_rw_lock_handle`
  return `Option`; FFI wrappers panic on `None`).

  **Test coverage**: 32 new SM2.D Rust unit tests in
  `lock_bridge.rs::tests` + `lock_bridge.rs::runtime_tests` +
  `ffi.rs::tests` (24 handle/layout/decoder tests + 9 FFI export
  tests + 3 cross-thread tests, totalling 736 HAL tests up from
  704 at SM2.B close).  Lean-side: 60+ surface-anchor `#check`s
  in `tests/SmpSurfaceAnchors.lean` + 25+ decidable examples +
  ~35 runtime structural assertions across the two new Lean test
  suites.  Zero clippy warnings.  Full Tier 0+1+2+3 smoke test
  green on SM2.D-specific paths.

  **Pre-existing flakiness note** (CLOSED via WS-SM SM2.E
  Panic-Hang Remediation, see
  [`docs/planning/SMP_PANIC_HANG_REMEDIATION_PLAN.md`](docs/planning/SMP_PANIC_HANG_REMEDIATION_PLAN.md)):
  the `queued_rw_lock::cross_thread_tests` from SM2.C-defer
  previously deadlocked under heavy host-side load (~10 % of runs)
  AND surfaced a residual writer-readers exclusion panic
  (~35 % rate in `cross_thread_state_invariant_no_writer_with_readers`).
  Closed via a multi-layer fix:
  * **Mode-encoded four-state parked machine** (PARKED_NOT_IN_QUEUE /
    PARKED_WAITING_READER / PARKED_WAITING_WRITER / PARKED_ADMITTED)
    eliminates the stale-mode-read race that PR #790 commit-3 left
    unresolved.  The walker's parked.load(Acquire) carries the mode
    atomically; the CAS direction (WAITING_READER → ADMITTED vs
    WAITING_WRITER → ADMITTED) is the authoritative mode source.
  * **Stale-self tail detection** in both `acquire_read` and
    `acquire_write` (treat `raw_prev_tail == core_id` as
    `NONE_SENTINEL`).
  * **CAS-claim before state update** in NONE-path self-admit spin;
    revert via CAS (not STORE) to avoid clobbering concurrent admits.
  * **Signal-on-every-release** in `release_read` plus walk-past-stale
    in `signal_next_waiter` (bounded by `MAX_WAITERS` step count).
  * **Writer admission via `state.CAS(0, WRITER_BIT)`** (never
    `fetch_or`) — closes the `WRITER_BIT | reader_bits` mutex
    violation.
  * **Cascade CAS-loop with WRITER_BIT precondition** — closes the
    cascade-during-writer admit race + WRITER_BIT underflow on undo.
  * **Host-side `wfe()` yield_now under `#[cfg(test)]`** — eliminates
    OS scheduler starvation that produces residual host-only hangs.

  Stress result (200×): 0/200 panics, ~3 % residual hangs on host
  (down from ~50 % baseline + 35 % residual panic rate).  On
  hardware with real WFE: 0 % hangs.  Three contractual patterns
  pinned by the new `scan_queued_rw_lock_protocol_intact` build-
  script scanner (four-state parked machine constants present,
  stale-self tail detection in both acquire paths, forbidden
  `fetch_or(WRITER_BIT` absent).  Plus an implementation of the
  previously-`#[ignore]`'d `sm1g3_cross_thread_kprintln_stress_no_lock_leak`
  test, replacing the `unimplemented!()` placeholder with a real
  host-meaningful lock-leak invariant check that exercises both
  the `kprintln_core!` macro and `with_boot_uart` direct path.
  HAL test count: 712 passed, 0 ignored (was 709 declared / 707
  passed pre-PR — the +5 net is from the SM2.E protocol tests and
  SM1.G.3 conversion; the +5 baseline-failing test now passes).
  Zero clippy warnings (including `-D warnings` strict on
  `--all-targets`).

  **Module reachability**: `Concurrency.LockBridge`,
  `Concurrency.LockPrimitives`, and
  `Concurrency.Locks.TicketLockRefinement` are staged via
  `Platform/Staged.lean` + `staged_module_allowlist.txt`.  SM3+
  per-object locks will move them production-reached.

  **Audit-pass-1 refinements** (post-initial-landing deep audit):
  - **HIGH (encapsulation)**: replaced the raw-pointer cast against
    `TicketLock`'s `repr(C)` layout (used by
    `lock_bridge.rs::ticket_lock_peek_holder` to read its private
    fields) with proper public methods `TicketLock::peek_next_ticket`
    and `peek_serving`.  The pre-audit pattern was a soft contract —
    a future refactor adding a debug field at the start of
    `TicketLock` would silently invalidate the assumed offsets.  Two
    new direct tests
    (`sm2d1_peek_next_ticket_matches_internal_counter`,
    `sm2d1_peek_serving_matches_internal_counter`) plus one
    cross-check (`sm2d1_peek_invariant_serving_le_next_ticket`)
    pin the accessor semantics.
  - **MEDIUM (32-bit truncation defense)**: refactored
    `decode_ticket_lock_handle` / `decode_rw_lock_handle` to do the
    bound check in `u64` space BEFORE the `as usize` cast.  Sele4n
    targets aarch64 (64-bit) so `usize == u64` and the cast is
    identity; a hypothetical 32-bit port however would truncate
    `handle` to 32 bits if cast first, silently aliasing
    `0x1_0000_0001` to slot 1.  Mirrors the audit-pass-2 fix in
    `ffi_per_core_*_count` (SM1.I.4).  New test
    `sm2d_decode_handles_reject_u64_with_high_bits_aliasing_slot`
    pins the rejection.
  - **MEDIUM (test concurrency)**: unified the `SM2D_TRACE_TEST_MUTEX`
    across `lock_bridge::runtime_tests` and `crate::ffi::tests`
    (previously distinct mutex instances).  Both test modules
    observe the same pool slots (0..2) with strict-equality
    counter-delta assertions; under cargo's default parallel test
    runner they could race, breaking the assertion.  The new
    shared mutex (defined at lock_bridge module scope, exposed via
    `pub(crate)`) provides a single serialisation point.
  - **HIGH (refinement-theorem aliasing)**: removed the
    SM2.D.7 aggregator's inline alias where
    `rust_ticketLock_refines_lean` (F-01 in the plan) was pointing
    at `ticketLock_release_acquire_pairing` for lack of a named
    refinement theorem.  Per the
    implement-the-improvement rule, the missing theorem is now
    substantively implemented in NEW FILE
    `SeLe4n/Kernel/Concurrency/Locks/TicketLockRefinement.lean`
    (mirroring `RwLockRefinement.lean`'s structure) with
    `TicketLockConcrete` struct, `ticketLockSim` simulation
    relation, four per-operation preservation witnesses
    (`ticketLockSim_unheld`,
    `ticketLockSim_preserved_by_tryAcquire`,
    `ticketLockSim_preserved_by_release`,
    `ticketLockSim_preserved_by_observeServing`), and the F-01
    aggregator theorem `rust_ticketLock_refines_lean`.  The
    `lockPrimitives_substantive_identifiers_nodup` theorem (which
    formerly excluded the refinement category to permit aliasing)
    gains a strengthened sibling
    `lockPrimitives_identifiers_nodup` covering ALL 22 entries.
  - **LOW (cross-language symmetry)**: the
    `scripts/check_lock_ffi_symmetry.sh` orphan checks now run in
    BOTH directions (Lean → EXPECTED and Rust → EXPECTED),
    catching the case where a declaration is added on one side
    without updating the symbol list.

  **Audit-pass-2 refinements** (post-audit-pass-1): added 6
  missing `*Count_eq_ffi` marker theorems for SM2.D.4 trace-
  counter accessors (`ticketLockAcquireCount_eq_ffi`,
  `ticketLockReleaseCount_eq_ffi`,
  `rwLockAcquireReadCount_eq_ffi`,
  `rwLockReleaseReadCount_eq_ffi`,
  `rwLockAcquireWriteCount_eq_ffi`,
  `rwLockReleaseWriteCount_eq_ffi`).  Symmetry fix with the
  SM2.D.1/2 pass-through markers — closes a Tier-3 surface
  scanning gap.

  **Audit-pass-3 refinements** (documentation sync): added
  the SM2.D section to `docs/spec/SELE4N_SPEC.md` (§2.7)
  mirroring the SM2.B/SM2.C structure.  Regenerated
  `docs/codebase_map.json` to reflect the new modules.

  **Audit-pass-4 refinements** (build-script hardening):
  extended `scan_lock_bridge_rs_intact` in
  `rust/sele4n-hal/build.rs` to also pin the textual presence
  of the 6 SM2.D.4 trace-counter statics
  (`TICKET_LOCK_*_COUNT`, `RW_LOCK_*_COUNT`) and the 2 handle
  decoders (`decode_ticket_lock_handle`,
  `decode_rw_lock_handle`).  Catches a wholesale refactor
  that drops them entirely with a clearer diagnostic than
  the downstream compile error.

  **Audit-pass-5 refinements** (typed-handle ergonomics):
  added `Inhabited` instances to `TicketLockHandle` and
  `RwLockHandle` for consistency with the project's other
  typed identifiers (e.g., `CoreId`).  The default value
  uses `mkTicketLockHandle ⟨0, _⟩` (and its RwLock
  counterpart), tying the default to the smallest valid
  pool slot.

  **Audit-pass-6 refinements** (independent external review,
  2 MEDIUM + 9 LOW findings):
  - **MEDIUM-1 (refinement docstring overstatement)**: the
    `rust_ticketLock_refines_lean` docstring claimed
    "every reachable Rust state is φ-related to a reachable
    Lean state".  The fourth conjunct (`ticketLockSim_preserved_by_observeServing`)
    is `h_sim → h_sim` — a tautology since `observeServing` is
    a pure read on both sides.  Together with the per-step
    witnesses we have initial-state correspondence + per-step
    preservation, NOT reachability closure.  Docstring weakened
    to match the actual content: "per-step preservation lemmas;
    full reachability-closure proof is a post-1.0 hardening
    candidate".
  - **MEDIUM-2 (sign error in peek_holder docstring)**:
    `ticket_lock_peek_holder` doc claimed "the `serving -
    next_ticket` difference (the number of in-flight acquires)".
    Under wf, `serving <= next_ticket`, so the non-negative
    difference is `next_ticket - serving`.  Doc fixed.
  - **LOW-3 (`Inhabited` anchors)**: added
    `#check (default : TicketLockHandle)` and the RwLock
    sibling to `tests/SmpSurfaceAnchors.lean`.
  - **LOW-4 (dead-weight `assertBool ... true`)**: replaced
    in both `tests/SmpSurfaceAnchors.lean` and
    `tests/LockBridgeSuite.lean` with a decidable post-condition
    that records elaboration reached the checkpoint.
  - **LOW-5 (redundant alias theorem)**: deleted
    `lockPrimitives_substantive_identifiers_nodup` — the
    stronger `lockPrimitives_identifiers_nodup` makes it
    redundant after the F-01 aliasing was removed in
    audit-pass-1.
  - **LOW-6 (redundant `& READER_MASK`)**: simplified
    `rw_lock_snapshot` to `writer_bit | count` (the count
    returned by `RwLock::snapshot` is already pre-masked).
  - **LOW-7 (redundant `& 0xFFFF_FFFF`)**: removed in test
    `sm2d1_ffi_ticket_lock_peek_holder_packs_state` — after
    `packed >> 32`, the high bits are zero so the mask is
    identity.
  - **LOW-8 (missing negative-side bit-extractor tests)**:
    added §6 in `tests/SmpSurfaceAnchors.lean`'s runtime
    suite verifying high bits don't bleed into the serving
    extraction and low bits don't bleed into the next-ticket
    extraction.
  - **LOW-9 (RAII docstring accuracy)**: `withTicketLock`
    docstring updated to honestly distinguish: (a) Lean
    `BaseIO` has no exceptions, (b) Rust HAL release uses
    `panic = "abort"`, (c) Rust test profile uses
    `panic = "unwind"` but Lean test executables don't link
    `libsele4n_hal.a`.
  - **LOW-10 (over-serialising `SM2D8_SLOT3_MUTEX`)**: split
    into `SM2D8_TICKET_SLOT3_MUTEX` (ticket-pool cross-thread
    test) and `SM2D8_RW_SLOT3_MUTEX` (rw-pool cross-thread
    tests).  Allows ticket and rw cross-core tests to run
    concurrently since they share no state.
  - **LOW-11 (hardcoded pool size)**: refactored
    `staticTicketLockPoolSize`/`staticRwLockPoolSize` to
    `= numCores` (was: hardcoded `= 4`).  Rust side:
    `STATIC_*_POOL_SIZE = crate::smp::MAX_SECONDARY_CORES + 1`
    with a `const _: ()` assertion pinning to the
    canonical 4-core value.  A future multi-platform port
    that bumps `numCores` / `MAX_SECONDARY_CORES`
    automatically propagates to both sides.

  **Items deferred past v1.0.0 with correctness impact**: NONE.

  Follow-on: SM2.E (documentation: `docs/spec/SELE4N_SPEC.md`
  §10 + GitBook chapter 17 + decision rationale doc) per
  [`docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md)
  §5.5.  SM2 closure at SM2.E close; SM3+ (per-object locks)
  consumes the SM2.D bridge.

  **WS-SM SM3.A LANDED on branch
  `claude/tender-gauss-FWPvo`** (per-object lock fields; closes
  the first sub-phase of SM3 with 9 of 11 sub-tasks LANDED and 2
  documented as N/A for seLe4n's object model).  Plan §5.1 of
  [`docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md`](docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md);
  wires SM2.C's abstract `RwLockState` into every kernel-object
  struct that seLe4n models, plus a table-level lock on the
  SystemState's object store, plus the per-variant projection
  function `objectLockOf` and the SM3.A.11 default-state theorems.

  - **SM3.A.1**: `TCB.lock : RwLockState` with default
    `RwLockState.unheld` (`SeLe4n/Model/Object/Types.lean`).  The
    manual `BEq TCB` instance grows from 22 to 23 conjuncts;
    `TCB.ext` gains an `hLock` hypothesis for the per-field
    extensionality witness; `TCB.not_lawfulBEq` is unaffected (its
    non-lawfulness derives from `registerContext`, not from any
    added field).
  - **SM3.A.2**: `Endpoint.lock` with default `unheld`.  Endpoint
    retains `deriving DecidableEq` because `RwLockState` derives
    `DecidableEq`.
  - **SM3.A.3**: `CNode.lock` with default `unheld`.  The manual
    `BEq CNode` is extended with the new conjunct;
    `CNode.beq_sound` is rewritten with `obtain` to be robust
    against future BEq additions (the previous positional pattern
    `h.1.1.1.1.1` was structurally fragile — adding a new conjunct
    silently shifted every index by one).
  - **SM3.A.4**: `Notification.lock` with default `unheld`.
  - **SM3.A.6**: `SchedContext.lock` with default `unheld`
    (`SeLe4n/Kernel/SchedContext/Types.lean`).  The SchedContext
    module gains a new import of `Concurrency.Locks.RwLock`; no
    cyclic dependency (RwLock depends transitively only on
    Prelude).
  - **SM3.A.7**: `VSpaceRoot.lock` with default `unheld`
    (`SeLe4n/Model/Object/Structures.lean`).  The manual
    `BEq VSpaceRoot` is extended; `VSpaceRoot.beq_sound` is
    rewritten with `obtain` for robustness; `VSpaceRoot.beq_refl`
    gains `Bool.and_true` in its simp set to handle the new
    trailing conjunct from the lock comparison.
  - **SM3.A.9**: `UntypedObject.lock` with default `unheld`.  The
    positional `UntypedObject.mk` calls in `empty_*` theorems and
    `UntypedObjectValid.empty` are converted to named-field syntax
    for robustness against future field additions.
  - **SM3.A.10**: ObjStore table-level lock + `objectLockOf`
    projection.  `SystemState.objStoreLock : RwLockState` field
    added with default `unheld`; per §4.4 of the plan, the
    underlying RobinHood hash table is held under a single
    table-level lock at the top of the SM0.I hierarchy
    (`LockKind.objStore`, level 0).  `KernelObject.objectLockOf`
    per-variant projection function defined with 7 `@[simp]`
    unfold lemmas (`objectLockOf_tcb` etc.).
    `FrozenSystemState.objStoreLock`, `FrozenCNode.lock`, and
    `FrozenVSpaceRoot.lock` fields added, forwarded unchanged by
    `freeze` / `freezeCNode` / `freezeVSpaceRoot` so the per-object
    lock state is preserved across the freeze boundary.
  - **SM3.A.11**: four default-state theorems —
    `default_objStoreLock_unheld` (proves
    `default.objStoreLock = .unheld` by `rfl`);
    `default_objects_locks_unheld` (the canonical SM3.A.11 closure
    theorem; vacuously discharged via `RHTable.getElem?_empty`);
    `default_objects_toList_empty` (computable `decide`-discharged
    witness); `default_objects_locks_unheld_via_toList` (the
    `toList` membership variant).

  **Skipped sub-tasks (documented as N/A for seLe4n's object
  model)**:

  - **SM3.A.5** (Reply): seLe4n does not model Reply as a
    separate kernel object; the reply discipline lives in TCB
    state (`ThreadIpcState.blockedOnReply`,
    `ThreadState.BlockedReply`, `TCB.pipBoost`).  Re-openable
    when a future workstream adds a first-class Reply object.
  - **SM3.A.8** (Page): seLe4n stores page mappings inline in
    `VSpaceRoot.mappings : RHTable VAddr (PAddr ×
    PagePermissions)` rather than as separate kernel objects.
    §4.3 of the plan rejects per-PTE locking as a v1.0.0 design
    decision — a single per-VSpaceRoot lock (SM3.A.7) suffices for
    serializability.  Re-openable when seLe4n adopts first-class
    Page objects.

  **Production/staged partition updates**:
  `Kernel.Concurrency.Locks.RwLock` and
  `Kernel.Concurrency.MemoryModel` moved from the staged allowlist
  into the production import closure — both modules are now
  reachable from production via `Model.Object.Types`'s new import
  of `Concurrency.Locks.RwLock` (which transitively imports
  `MemoryModel`).  The `STATUS: staged` markers in those files are
  removed in the same cut per the implement-the-improvement rule.
  `RwLockRefinement` remains staged-only at SM3.A (not yet wired
  to a runtime consumer; promotable in a later SM3 phase).

  **Test coverage**: NEW FILE `tests/PerObjectLockSuite.lean`
  (~646 LoC post-audit-pass-4) with 36 surface-anchor `#check`
  lines, 36 decidable examples, and 52 runtime `assertBool`
  assertions covering: default-state shape (objStoreLock unheld,
  toList empty); per-object default-lock witness for every kind
  including TCB via named-field construction with the 6 required
  fields (TCB, Endpoint, Notification, CNode, VSpaceRoot,
  UntypedObject, SchedContext); `KernelObject.objectLockOf`
  per-variant reduction (all 7 variants);
  `FrozenKernelObject.objectLockOf` per-variant reduction (full
  7-variant coverage post-audit-pass-4); frozen-state lock-field
  forwarding (`freezeCNode`, `freezeVSpaceRoot`, plus
  `freezeObject_preserves_objectLockOf` exercised on every
  variant); audit-pass-4 non-vacuous SM3.A.11 witnesses on
  post-insert states (3 variants — endpoint, cnode, vspaceRoot —
  exercise `objectLockOf` after `RHTable.insert` to give the
  universal-quantifier theorem a non-empty witness); `freeze
  mkEmptyIntermediateState` ObjStore-lock preservation; and
  `RwLockState.unheld` auxiliary properties from SM2.C
  (5-conjunct `wf`, `writerHeld = none`, `readers = []`,
  `waiters = []`).  Runnable as `lake exe per_object_lock_suite`.
  Wired into Tier 2 (negative) and Tier 3 (invariant-surface).
  Lean module build: 318/318 green.  Full Tier 0+1+2+3 smoke
  test passes.

  **Items deferred past v1.0.0 with correctness impact**: NONE.

  **Audit-pass-1 refinements** (self-review, included in the SM3.A
  cut):
  - TEST COVERAGE GAP (MEDIUM, runtime tier):
    `tests/PerObjectLockSuite.lean` had `#check @TCB.lock` /
    `#check @TCB.ext` surface anchors but no decidable example or
    runtime assertion for TCB's default-lock witness.  Added a
    minimal TCB construction (with the 6 required fields) +
    `lock = unheld` decidable example + `objectLockOf (.tcb _) =
    unheld` companion + runtime assertions in `§2` and `§3`.
    Total runtime assertions: 22 → 24.
  - DOCUMENTATION ACCURACY (LOW): the initial CHANGELOG / spec /
    history claims of "30+ surface anchors, 16 decidable examples,
    22 runtime assertions" were imprecise.  Actuals (counted via
    `grep -c "^#check"` / `grep -c "^example "` / `assertBool`
    invocations): 24 / 26 / 24.  Updated to the precise counts.

  **Audit-pass-2 refinements** (independent code review, 1 MEDIUM +
  7 LOW findings, all closed):
  - **MEDIUM (M-1) — `FrozenKernelObject.objectLockOf` symmetry**:
    The SM3.A.10 `KernelObject.objectLockOf` projection has 7
    `@[simp]` unfold lemmas, but `FrozenKernelObject` had no
    sibling projection.  Closed by adding
    `FrozenKernelObject.objectLockOf` with 7 `@[simp]`
    per-variant unfold lemmas + the aggregate witness
    `freezeObject_preserves_objectLockOf` (proved by
    case-analysis; every case discharges by `rfl`).  SM3.B's
    `LockId.lookup` for the frozen phase can now route through
    the symmetric projection.
  - **LOW (L-1) — §4.3 reference**: the plan / spec / CHANGELOG /
    CLAUDE / AGENTS cited "§4.3 rejects per-PTE locking" but
    §4.3 ("Per-object vs per-subsystem") did not actually
    mention per-PTE.  Closed via implement-the-improvement: §4.3
    is amended to include the per-PTE rejection rationale
    (3 numbered concerns: per-PTE lock overhead, hand-over-hand
    acquisition during RHTable probe-sequence relocation,
    hierarchy-level conflict with the SM0.I 10-level cap).
  - **LOW (L-2) — dead-weight assertBool**: two
    `assertBool ... true` invocations in
    `runDefaultStateChecks` reported PASS regardless of theorem
    elaboration.  Replaced with decidable closed-form checks —
    every entry in the default state's `toList` has
    `objectLockOf p.2 = unheld` and `wf` (vacuously true on the
    empty default state but exercises the decidable closed form).
  - **LOW (L-3) — missing `freeze_preserves_*` witnesses**:
    every other freeze-forwarded field has a `freeze_preserves_X`
    witness.  Added `freeze_preserves_objStoreLock`,
    `freezeCNode_preserves_lock`,
    `freezeVSpaceRoot_preserves_lock`.
  - **LOW (L-4) — test-count accuracy**: updated to the precise
    counts after the audit-pass-2 additions: 36 surface anchors,
    31 decidable examples, 29 runtime assertions (counted via
    `grep -c "^#check"`, `grep -c "^example "`, and
    `grep -c "^  assertBool "`).
  - **LOW (L-5) — missing `.tcb` decidable example in §3**:
    audit-pass-1 fixed the runtime tier; audit-pass-2 fixes the
    elaboration tier by adding the missing decidable example
    for `objectLockOf (.tcb _) = unheld`.
  - **LOW (L-6) — TCB §2 example rfl-only**: every other §2
    example had both `by decide` and `rfl` forms; TCB had only
    `rfl`.  Added the `by decide` companion.
  - **LOW (L-7) — allowlist comment**: the staged-module
    allowlist header comment elided the SM2.C historical
    context for `RwLockRefinement`.  Rewritten to clearly
    distinguish "modules moved OUT at SM3.A" from "entries
    pre-dating SM3.A that remain staged-only".

  **Test results after audit-pass-2**: 318/318 Lean modules
  build green; `lake exe per_object_lock_suite` reports 29/29 PASS
  (24 at audit-pass-1 + 5 new audit-pass-2 assertions); Tier
  0+1+2+3 green.

  **Audit-pass-5 refinements** (user-driven deferred-completion
  close-out; 9 substantive additions):
  - **Strengthened SM3.A.11 (non-vacuous form)**: added
    `SystemState.allObjectLocksUnheld` Prop conjunction
    (`objStoreLock = unheld ∧ ∀ id o ∈ store, objectLockOf o =
    unheld`) plus `SystemState.allObjectLocksUnheldB` Bool form;
    `default_allObjectLocksUnheld` proves both conjuncts hold on
    the default state (the first is substantive, not vacuous);
    `allObjectLocksUnheld_of_pointwise` constructor for arbitrary
    states.
  - **Preservation theorems for `storeObject`**:
    `storeObject_preserves_objStoreLock`,
    `storeObject_preserves_objectLockOf_off_target`,
    `storeObject_inserted_object_lookup`, and the aggregate
    `storeObject_preserves_allObjectLocksUnheld`.  Closes the
    audit-pass-4 finding "no preservation theorems for any
    kernel transition".
  - **Consistency theorems**: `KernelObject.objectLockOf_exists`
    (totality), `objectType_and_lockOf_total` (co-consistency),
    `objectLockOf_consistent_with_type` (per-variant kind-tag ↔
    lock-field).
  - **Reply/Page N/A structural enforcement**:
    `KernelObjectType.variants_count_exactly_seven` pins the
    variant cardinality; `variants_total` enumerates every value.
    A future workstream adding `Reply` or `Page` variant fails
    these witnesses, forcing the SM3.A.5 / SM3.A.8 decision to
    be revisited.
  - **`RwLockState.default = .unheld`**: `@[simp]` equivalence
    theorem.  Downstream code that writes `lock := default`
    simp-normalises to `lock := .unheld`.
  - **Manual `Repr FrozenVSpaceRoot`**: elides the
    `FrozenMap`-typed `mappings` field for trace output.  Closes
    the audit-pass-4 deferred Repr work.
  - **`perObjectLockTheorems` aggregator** (NEW FILE
    `SeLe4n/Model/Object/PerObjectLockInventory.lean`): 34-entry
    typed inventory in 5 categories (7 fieldDefault + 9
    projection + 5 defaultState + 8 preservation + 5
    consistency).  Per-category count witnesses, partition-sum
    theorem, Nodup witnesses on identifiers and descriptions.
  - **CLAIM_EVIDENCE_INDEX entry**: new SM3.A row at the top of
    the active-baseline claims table.
  - **Test suite expansion**: `tests/PerObjectLockSuite.lean`
    grew from ~646 LoC to ~806 LoC; runtime assertions from 41
    to 58.

  **Test results after audit-pass-5**: 319/319 Lean modules
  build green (was 318; +1 for `PerObjectLockInventory`);
  `lake exe per_object_lock_suite` reports 58/58 PASS; Tier
  0+1+2+3 green; Rust 988+ tests green; zero clippy warnings.

  **Audit-pass-6 refinements** (second external audit pass; also
  on the same branch): closes the 1 LOW finding "319/319 jobs"
  drift (audit-pass-5 promoted the inventory to production-
  reachable but `lake build` count was already 320 by then due to
  unrelated downstream additions; cross-references in CHANGELOG /
  CLAIM_EVIDENCE_INDEX / CLAUDE updated to 320), plus the
  "RwLockState `default` docstring stale" finding (RwLock.lean
  docstring at structure decl updated to reflect that `default
  = unheld` via the SM3.A audit-pass-5 `default_eq_unheld`
  theorem), plus the "inventory section comment counts wrong"
  finding (§4 said "5 entries" actual 8; §5 said "4 entries"
  actual 5; both corrected), plus the "dead-link to
  `allObjectLocksUnheld_iff_via_toList`" finding: per the
  implement-the-improvement rule, the missing bridge theorem is
  fully implemented in `Model/FreezeProofs.lean` —
  `get_some_of_toList_contains` (reverse direction of the
  audit-pass-5 `toList_contains_of_get`), the
  `toList_all_iff_forall_get_some` general `toList.all ↔ ∀ get?`
  bridge, and the SM3.A-specific
  `allObjectLocksUnheld_iff_via_toList` Prop ↔ Bool equivalence
  under `invExt`.  Plus 5 dead-weight `assertBool "...
  reachable" true` invocations in `runAuditPass5InvariantChecks`
  replaced with substantive decidable witnesses on a post-
  `storeObject` state (4 storeObject preservation witnesses + 1
  objectLockOf_consistent_with_type witness), plus a `Repr
  FrozenVSpaceRoot` runtime exercise (1 assertion).  Inventory
  promoted into production via `SeLe4n.lean` import (was
  test-only at audit-pass-5).

  **Test results after audit-pass-6**: 320/320 Lean modules
  build green (was 318 baseline, audit-pass-5 promoted inventory
  +1, audit-pass-6 added FreezeProofs bridge theorems +1; total
  +2);  `lake exe per_object_lock_suite` reports 60/60 PASS
  (audit-pass-5 was 58; audit-pass-6 +2 — dead-weight assertBool
  refactor net +1, Repr FrozenVSpaceRoot +1); Tier 0+1+2+3
  green; Rust 988+ tests green; zero clippy warnings.

  **Audit-pass-7 refinements** (user-reported correctness gaps;
  both closed with static guarantees that prevent recurrence):
  - **Issue #1: `BEq SchedContext` was missing the `lock`
    conjunct**.  The SM3.A.6 commit added `SchedContext.lock` but
    did NOT update the manual `BEq SchedContext` instance.  Two
    SchedContexts that differ ONLY in lock state compared equal
    under `==` — masking SM3.A.11 invariant regressions in any
    code/test that uses `==`.  The defect propagated through
    `BEq KernelObject`'s dispatch on `.schedContext`.  **Fix**:
    added `&& a.lock == b.lock` as a 12th conjunct.  Plus a new
    `tests/PerObjectLockSuite.lean` §4b section with 11 decidable
    regression tests (7 per-kernel-object struct + 4 KernelObject-
    variant) plus 8 runtime mirrors that construct two values
    differing only in `lock` and assert `(a == b) = false`.  A
    future workstream that adds a new kernel object or changes
    an existing BEq instance to drop the `lock` field fails this
    regression-prevention block.
  - **Issue #2: `PerObjectLockTheorem.identifier : String` had
    no compile-time check**.  A typo or stale rename in any
    inventory entry would still typecheck — the 34-entry
    inventory's claimed "rename/removal regression guard" was
    weakened by the `String`-typed field (the `_nodup` and
    `_count` proofs operated on strings, not on actual
    declarations).  **Fix**: added a `polt!` macro that
    captures the identifier's `Lean.Name` AND emits a
    `let _ := @<ident>; ()` term in a new `_elabCheck : Unit`
    field of `PerObjectLockTheorem`.  A typo or stale rename
    fails to elaborate with "unknown constant '<name>'" — the
    static guarantee a `String`-typed field cannot provide.
    Verified via three intentional regressions (each rolled
    back after verifying the build failure): typo on
    `Endpoint.lock` → `Endpoint.lockTYPO` fails with "Unknown
    constant"; silent rename of `default_objStoreLock_unheld`
    fails with "Unknown identifier"; the canonical 34 entries
    pass cleanly.

  **Test results after audit-pass-7**: 320/320 Lean modules
  build green; `lake exe per_object_lock_suite` reports 68/68
  PASS (was 60; +8 BEq regression assertions); 65 surface
  anchors, 61 decidable examples, 68 runtime assertions, ~1097
  LoC; Tier 0+1+2+3 green; Rust 988+ tests green; zero clippy
  warnings.

  **Static guarantees added in audit-pass-7** (preventing
  recurrence):
  - `BEq SchedContext` includes `&& a.lock == b.lock` — pinned
    by 11 decidable + 8 runtime regression tests.
  - Every kernel-object struct's BEq distinguishes lock state —
    pinned by per-kind regression tests covering TCB, Endpoint,
    CNode, Notification, UntypedObject, SchedContext, VSpaceRoot
    + the aggregate `BEq KernelObject` dispatch.
  - Inventory identifiers refer to actual declarations — pinned
    by the `polt!` macro's compile-time elaboration check.
  - Inventory identifier strings match their declaration names —
    pinned by macro stringification (the developer writes the
    declaration name once; the macro derives the string).

  Follow-on: SM3.B (`LockId.fromObject`, `LockId.lookup`,
  per-transition `lockSet`, `lockAcquireSequence` ordering
  theorems) — **LANDED below**.  SM3.C (`withLockSet` 2PL
  discipline) consumes both SM3.A and SM3.B; SM3.D/SM3.E close
  with deadlock-freedom and serializability theorems.  See
  [`docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md`](docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md)
  §§5.2..5.5.

  **WS-SM SM3.B LANDED on branch
  `claude/affectionate-goldberg-6MNJ9`** (LockSet, LockId
  projection, per-transition lockSet declarations, canonical sort
  theorems; closes the second sub-phase of SM3 with all 9
  sub-tasks LANDED).  Plan §5.2 of
  [`docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md`](docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md);
  builds the abstract lock-set type plus per-syscall lock-set
  declarations on top of SM3.A's per-object lock fields and
  SM0.I's `LockKind` / `LockId` total order.

  - **SM3.B.1**: `KernelObject.lockKind : KernelObject → LockKind`
    + 7 per-variant `@[simp]` unfolds + `lockKind_exists` + the
    agreement theorem with `objectType`
    (`lockKind_eq_of_objectType`) in
    `SeLe4n/Kernel/Concurrency/Locks/LockIdProjection.lean`.
    `LockId.fromObject (oid : ObjId) (o : KernelObject) : LockId`
    smart constructor with 7 per-variant convenience lemmas.  The
    plan's pseudocode signature `(o : KernelObject) → LockId` is
    adapted to seLe4n's data model: only `TCB` and `SchedContext`
    carry inner-struct IDs; the other variants are looked up by
    external ObjId in `SystemState.objects`, so taking the ObjId
    externally makes the projection total.
  - **SM3.B.2**: `LockId.lookup s l : Option (RwLockState ×
    KernelObject)` dispatches on `l.kind` and routes through the
    typed `getX?` accessors (`getTcb?`, `getEndpoint?`,
    `getNotification?`, `getCNode?`, `getVSpaceRoot?`,
    `getUntyped?`, `getSchedContext?`) — zero raw
    `match.*objects[...]?` sites.  Six structural theorems:
    `lookup_some_of_kindMatch`, `lookup_fromObject_of_present`,
    `lookup_kindMatch`, `lookup_lockState_eq`, plus three
    `@[simp]` fail-closed witnesses for the N/A `LockKind`
    variants (`lookup_objStore`, `lookup_reply`, `lookup_page`).
  - **SM3.B.3**: 25 per-transition `lockSet_<τ>` declarations in
    `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean`,
    one per `SyscallId` variant.  Each takes post-cap-resolution
    `ObjId`s plus `callerTid` (and `Option ObjId` for
    path-dependent locks like receiver TCB, blocked endpoint/
    notification).
  - **SM3.B.4**: `permittedKinds (sid : SyscallId) : List
    LockKind` declarative upper-bound + 25 per-transition
    `lockSet_consistent_<τ>` theorems.  Discharged through four
    generic builder lemmas
    (`lockSet_consistent_of_extended_base`,
    `lockSet_consistent_extendOpt`,
    `lockSet_consistent_base_plus_opt`,
    `lockSet_consistent_base_plus_two_opts`) plus per-transition
    `simp only [<lockBuilder>_kind] + decide` discharge of
    finite-list membership.
  - **SM3.B.5**: `LockSet` structure (List with Nodup-keys
    invariant) in `SeLe4n/Kernel/Concurrency/Locks/LockSet.lean`.
    `AccessMode.lub` (write dominates read; idempotent /
    commutative / associative) and `AccessMode.conflicts`
    (symmetric) algebra.  Smart constructors `empty`,
    `singleton`, `insert?` (strict; rejects duplicate keys),
    `insertOrMerge` (lub-merge on duplicate keys), `union`.
    `lockAcquireSequence (S : LockSet) : List (LockId ×
    AccessMode)` sorts `S.pairs` by `LockId` ascending via
    `List.mergeSort` with the `LockId ≤` Bool comparator.
  - **SM3.B.6**: `lockAcquireSequence_ordered` — the sort is
    `Pairwise (≤ on fst)` — discharged via
    `List.pairwise_mergeSort` + `LockId.le_trans` +
    `LockId.le_total`.
  - **SM3.B.7**: `lockAcquireSequence_complete` — every input
    pair appears in the sorted output (and vice versa).
  - **SM3.B.8**: `lockAcquireSequence_canonical` (plan §3.5.1) —
    the sorted sequence is the *unique* `≤`-sorted permutation of
    `S.pairs`.  Proof factors through `LockSet.fst_inj_at_pairs`
    (key uniqueness forces pair uniqueness on shared `fst`) and a
    custom by-induction "uniqueness of sorted permutation"
    helper.
  - **SM3.B.9**: NEW FILE `tests/LockSetSuite.lean` (~600 LoC)
    with 100+ surface anchors, decidable examples on small
    concrete LockSets exercising sort ordering and per-transition
    shape, 49 runtime `assertBool` assertions for per-transition
    size invariants and inventory partition counts.  Runnable as
    `lake exe lock_set_suite`.

  **SM3.B inventory (72 entries)**: NEW FILE
  `SeLe4n/Kernel/Concurrency/Locks/LockSetInventory.lean` (~290
  LoC) mirrors SM3.A's `PerObjectLockInventory.lean` pattern with
  a typed `LockSetTheorem` struct, a `lkst!` macro that
  compile-time elaborates identifiers, and a 72-entry list
  partitioned across five categories: `.projection` (10),
  `.lockSet` (25), `.consistency` (25), `.acquireSort` (5),
  `.algebra` (7).  Per-category count witnesses, partition-sum
  theorem, Nodup-on-identifiers and Nodup-on-descriptions
  witnesses (discharged via `native_decide` due to list size),
  and the coverage theorem
  `lockSet_consistent_aggregate_covers_every_syscall` pinning
  `consistency category count = SyscallId.count`.

  **Production/staged partition**: 5 new SM3.B modules
  (`LockSet`, `LockIdProjection`, `LockSetTransitions`,
  `LockSetInventory`, the re-export hub `Concurrency.LockSet`)
  staged via `Platform/Staged.lean` (added to the SM3.B closure
  in `scripts/staged_module_allowlist.txt`); SM3.C's `withLockSet`
  2PL combinator will promote them to production-reachable when
  the per-transition wrappers land.

  **AK7-cascade hygiene**: `LockId.lookup` dispatches on
  `l.kind` and routes through the typed `getX?` accessors, so
  the cumulative `RAW_MATCH_TOTAL` floor (122 at v0.31.2) is
  unchanged.  Typed-accessor adoption counts grew by 7 (one for
  each of the 7 kernel-object kinds the dispatcher consumes).

  **Test coverage** (audit-pass-1): 72 runtime assertions in
  `lock_set_suite` (was 49 at initial landing; +23 from audit-pass-1
  closures across §9 lub-merging, §10 union semantics, §11
  per-transition consistency runtime exercise, §12 canonical-sort
  determinism, §13 LockId.lookup fixture-state).  Lean-side: ~105
  surface anchors in `tests/test_tier3_invariant_surface.sh`
  (covering every public SM3.B symbol; +5 audit-pass-1 anchors for
  `LockSet.union_mem_inv` / `union_empty` / `containsKey_iff` /
  `empty_pairs` / `singleton_pairs`).  Existing test suites
  continue to pass (Tier 0+1+2+3 green).  Zero clippy warnings (no
  Rust changes).  Zero linter warnings.

  **Items deferred past v1.0.0 with correctness impact**: NONE.

  **Audit-pass-1 refinements** (post-initial-landing comprehensive
  deep audit; all closures land in the same v0.31.9 release cut):
  - **Code-quality cleanup**: removed no-op `simp only at h` in
    `DecidableEq LockSet`; rewrote `containsKey_iff` to use
    `obtain` + `subst` (eliminated `simp_all`); dropped unused
    `_hSortedRef` parameter from `lockAcquireSequence_canonical_aux`.
  - **Proof-style refactor**: replaced 76 repeated
    `simp only [tcbLock_kind, cnodeLock_kind, ..., untypedLock_kind];
    decide` invocations across the 25 per-transition consistency
    theorems with clean `simp; decide` (the `*Lock_kind` lemmas are
    `@[simp]` globally).  Removed the
    `set_option linter.unusedSimpArgs false` workaround that the
    verbose form required.  Net diff: −76 long `simp only` lines.
  - **Module-layering fix**: moved `LockSet.insertOrMerge_mem` from
    `LockSetTransitions.lean` (which only consumes it) to
    `LockSet.lean` (the module that defines `insertOrMerge`
    itself).
  - **Spec-gap closure**: added `LockSet.union_mem_inv` — a
    structural characterisation theorem for `LockSet.union`'s
    semantics.  Initial landing defined `union` without any
    theorem characterising its membership; audit-pass-1 closes
    the spec gap by proving `∀ p ∈ S₁.union S₂, p ∈ S₁ ∨ ∃ p' ∈
    S₂, p.fst = p'.fst`.  The asymmetry between "full pair match"
    on S₁ and "fst-key match" on S₂ reflects `insertOrMerge`'s lub
    merging.
  - **Test-coverage gap closures** (5 new check sections, +23
    runtime assertions):
    * §9 lub-merging: read+write, write+read, read+read at same
      key; self-suspend collapse; self-reply collapse.
    * §10 union semantics: disjoint / overlapping / empty.
    * §11 `lockSet_consistent_*` runtime application: specialise
      each consistency theorem to concrete args and verify the
      `List.all (decide ...)` discharge.
    * §12 canonical-sort determinism: same multiset built in 3
      different orders yields identical canonical output; within-
      kind sort is ascending by `ObjId.val`.
    * §13 `LockId.lookup` fixture-state: `some` branch for
      matching kind+ObjId; kind-mismatch fail-closed (TCB-tagged
      LockId at an Endpoint ObjId → `none`); absent-ObjId
      fail-closed; N/A-kind (`.objStore`/`.reply`/`.page`) fail-
      closed witnesses.
  - **Inventory expansion**: `lockSetTheorems` grew from 72 to 81
    entries.  +8 projection entries
    (`lockKind_eq_of_objectType` + 4 lookup structural theorems +
    3 fail-closed N/A witnesses); +1 algebra entry
    (`union_mem_inv`).  Per-category counts and partition-sum
    theorem updated; `lockSetTheorems_count = 81`.

  **Audit-pass-2 refinements** (second deeper deep audit, post-
  pass-1; all closures land in the same v0.31.9 release cut):
  - **Code-quality cleanup**: removed duplicate theorem
    `fromObject_lockKind_eq` (literally identical to
    `fromObject_kind`); removed unused `[DecidableEq α]`
    constraint from `list_fst_inj_of_nodup_keys` (proof never
    invokes decidability of equality).
  - **Substantive co-domain theorems**: `lockKind_exists` is
    genuinely trivial; audit-pass-2 adds 4 useful co-domain
    witnesses: `lockKind_in_modeledKinds` (returns one of 7
    modeled kinds), `lockKind_ne_objStore` /
    `lockKind_ne_reply` / `lockKind_ne_page` (fail-closed
    witnesses for the SystemState-level + N/A kinds).
  - **Donation-path scope** (initial audit-pass-2 form was
    documentation-only; **REPLACED by audit-pass-3 below** per
    CLAUDE.md's `Implement-the-improvement` rule — see audit-
    pass-3 entry for the actual fix).
  - **Inventory expansion**: `lockSetTheorems` grew from 81 to
    87 entries.  +4 projection (4 `lockKind_*` co-domain
    theorems); +1 acquireSort (`lockAcquireSequence_perm`); +1
    algebra (`LockSet.containsKey_iff`).
  - **Test suite expansion**: 72 → 83 runtime assertions.  +7
    in §14 `runLockKindCoDomainChecks` (co-domain claims on
    concrete `KernelObject` values); +4 in §15
    `runFstInjChecks` (LockSet.fst_inj structural witness).
    Plus 4 new surface anchors for the audit-pass-2 theorems.

  **Audit-pass-4 refinements** (deepest deep audit; closes one
  remaining defense-in-depth gap in audit-pass-3's donation fix;
  all closures land in the same v0.31.9 release cut):
  - **`originalOwner` separated from `replyTargetTid` in reply
    paths**: audit-pass-3's `lockSet_endpointReply` and
    `lockSet_replyRecv` assumed the kernel invariant
    `originalOwner == replyTargetTid` and only declared a single
    Option for the donation SC.  Per plan §4.1's "union over all
    paths" requirement, audit-pass-4 declares the originalOwner
    TCB lock as a SEPARATE `donatedOriginalOwnerTid : Option
    ThreadId` arg.  Under the well-formed invariant where
    originalOwner == replyTargetTid, the `insertOrMerge`
    lub-merge collapses the duplicate TCB entry — same behavior
    as before.  Under hypothetical invariant violation where
    they differ (defense-in-depth), the lockSet now correctly
    covers both objects.  This makes the reply paths symmetric
    with `lockSet_tcbSuspend` which already had the explicit
    Option ThreadId arg.
  - **PIP-chain dynamic-locking acknowledged**: traced
    `endpointCallWithDonation` and `endpointReplyWithDonation`
    through `propagatePriorityInheritance` /
    `revertPriorityInheritance`.  These walk arbitrarily-long
    chains of TCBs (the blocking graph), touching `pipBoost`
    fields and run-queue buckets.  The chain length is
    state-discovered, not statically pre-resolvable.  Plan
    §4.1's "variable number of locks" provision applies; SM3.C
    will handle PIP-chain locks via dynamic ladder extension
    (acquire next chain TCB in `ObjId.val` ascending order),
    preserving the SM0.I lock-id total order's deadlock-freedom
    guarantee without violating 2PL.  This is the genuinely-
    dynamic case that no static lockSet can cover, and the plan
    explicitly permits it.
  - **Test-coverage expansion**: 95 → 96 runtime assertions
    (+1 for the `donReplyDrift` invariant-violation
    defense-in-depth assertion).  Tests now cover both:
    * Well-formed reply (owner == target): lub-collapse to 4
      locks.
    * Hypothetical drift (owner ≠ target): 5 locks covering
      both.

  **Audit-pass-5 refinements** (structural PIP-chain obligation
  encoded at the type level; implements the chain-start signal
  audit-pass-4 only acknowledged as a doc note, per CLAUDE.md's
  `Implement-the-improvement` rule; all closures land in the same
  v0.31.9 release cut):
  - **3 new `pipChainStart_<τ>` declarations** for the 3
    PIP-invoking transitions:
    * `pipChainStart_endpointCall` — mirrors `receiverTid` (no
      waiting receiver ⇒ no chain).
    * `pipChainStart_endpointReply` — always emits revertPIP at
      `callerTid`.
    * `pipChainStart_replyRecv` — always emits revertPIP at
      `callerTid`.
    Each returns `Option ThreadId` exposing the chain start point
    as structural metadata about the transition (a "follow this
    dynamic obligation" signal), not a lockSet element.  Defense-
    in-depth: the chain-start TCB is contained in the static
    lockSet (verified by 2 runtime assertions).
  - **Structural separation from `lockSet_<τ>`**: Plan §4.1's
    `lockSet : args → Finset` signature is preserved unchanged.
    The chain-start hint is separate, surfacing the dynamic
    obligation explicitly at the type level — SM3.C cannot forget
    to handle the chain.  This permits SM3.C to use different
    dynamic strategies (optimistic walk + verify, lock-coupling,
    coarse PIP-graph lock) without changing `lockSet`'s
    signature.
  - **New SM3.C.11 sub-task** for dynamic chain-walk locking
    design ([plan §5.3](docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md)):
    introduces `withDynamicChainExtension` combinator (with
    optimistic-walk + verify strategy, `ObjId.val` ascending
    discipline, bounded retries), `dynamicChainHeld` predicate,
    `dynamic_chain_deadlock_free` theorem (proven via the
    each-core-holds-at-most-2-locks-at-strictly-ascending-ObjIds
    structural argument), `walkAndAcquire_terminates` theorem
    (`MAX_PIP_RETRIES = 64` budget), per-transition wrappers
    consuming `pipChainStart_*`, and 6 sub-sub-tasks
    (SM3.C.11.a..f).  SM3.C lifts from 4 PRs / 10 sub-tasks to
    5 PRs / 11 sub-tasks.
  - **Inventory expansion**: `lockSetTheorems` grew from 87 to
    90 entries.  +3 entries in the NEW `LockSetCategory.chainStart`
    variant; partition-sum theorem updated to 6-way;
    `lockSetTheorems_chainStart_count = 3` new witness.
  - **Test suite expansion**: 96 → 106 runtime assertions
    (+10 = +9 §16 `runPipChainStartChecks` + 1 chainStart
    inventory check).  3 new surface anchors + 6 new decidable
    examples + 4 new tier-3 invariant surface anchors.

  **Audit-pass-6 refinements** (external Codex code-review
  closure on PR #793; 4 P1 high-severity + 1 P2 medium-severity
  lock-set under-approximations resolved by re-tracing the actual
  kernel operations and extending the static lock-set
  declarations; per CLAUDE.md's `Implement-the-improvement`
  rule, no findings are documented away — each is materialised
  as a code change on the lockSet declaration):
  - **P1 `lockSet_tcbSetPriority`**: gains
    `boundSchedContextId : Option SchedContextId` arg.
    `setPriorityOp` → `updatePrioritySource` writes the bound SC
    via `st.objects.insert scId.toObjId (.schedContext sc')`
    whenever the target's binding is `.bound`/`.donated`.
    Without the lock, this races with concurrent SchedContext ops
    on the same object.
  - **P1 `lockSet_tcbSetMCPriority`**: same `Option
    SchedContextId` arg.  `setMCPriorityOp` calls
    `updatePrioritySource` in the priority-capping branch.
  - **P1 `lockSet_tcbSetIPCBuffer`**: gains
    `targetVSpaceRootObjId : Option ObjId` arg.
    `setIPCBufferOp` → `validateIpcBufferAddress` reads the
    target's VSpaceRoot via `getVSpaceRoot?` then traverses
    `root.lookup addr` (page-table walk).  Read lock sufficient.
  - **P2 `lockSet_serviceRegister`**: gains a mandatory
    `endpointObjId : ObjId` arg.  `registerService` reads
    `st.objects[epId]?` to verify the endpoint kind tag.  Read
    lock sufficient (the `serviceRegistry` map is the only write
    target).
  - **`permittedKinds` extensions**: `.tcbSetPriority` /
    `.tcbSetMCPriority` add `.schedContext`; `.tcbSetIPCBuffer`
    adds `.vspaceRoot`; `.serviceRegister` adds `.endpoint`.
    `.serviceRevoke` / `.serviceQuery` split out from
    `.serviceRegister` in the `permittedKinds` definition since
    they only touch the `serviceRegistry` map.
  - **Consistency-proof updates**: `_serviceRegister` gains a
    3rd literal-list rcases branch; `_tcbSetPriority` /
    `_tcbSetMCPriority` / `_tcbSetIPCBuffer` switch from
    `lockSet_consistent_of_extended_base` to
    `lockSet_consistent_base_plus_opt`.
  - **Source-level tracing**: each finding was verified by
    tracing the actual kernel code:
    `Kernel/SchedContext/PriorityManagement.lean:217-221` (SC
    write in `updatePrioritySource`),
    `:347` (`setMCPriorityOp` capping branch),
    `Kernel/Architecture/IpcBufferValidation.lean:76,79`
    (VSpace + mappings read),
    `Kernel/Service/Registry.lean:75` (endpoint object read).
    `revokeService` (only `serviceRegistry` erase) and
    `lookupServiceByCap` (only `serviceRegistry` fold) confirmed
    NOT to read kernel objects.
  - **Test suite expansion**: 106 → 133 runtime assertions
    (+27 across §4, §7, §11, §17).  NEW §17
    `runAuditPass6FootprintChecks` (+10): per-syscall lock
    presence, missing-lock-absence (none-case for IPC buffer),
    and canonical-sort hierarchy-level cross-checks (SC at
    level 7, VSpaceRoot at level 8, endpoint at level 4).
  - **Items deferred past v1.0.0 with correctness impact**: NONE.

  **Audit-pass-3 refinements** (donation-path FIX, replacing
  audit-pass-2's documentation workaround per the
  `Implement-the-improvement` rule; all closures land in the
  same v0.31.9 release cut):
  - **Donation-path lockSet extensions**: implemented the
    actual fix per plan §4.1's "union over all paths"
    requirement.  4 syscalls extended with pre-resolved Option
    args covering the full donation footprint:
    * `lockSet_endpointCall` — `+ donatedScId : Option
      SchedContextId` (for `applyCallDonation`).
    * `lockSet_endpointReply` — `+ donatedScId : Option
      SchedContextId` (for `applyReplyDonation` /
      `returnDonatedSchedContext`).
    * `lockSet_replyRecv` — `+ donatedScId : Option
      SchedContextId` (same as reply; the receive phase doesn't
      initiate donation).
    * `lockSet_tcbSuspend` — `+ bindingScId : Option
      SchedContextId` AND `+ donatedOriginalOwnerTid : Option
      ThreadId` (for `cancelDonation`'s `.bound` and
      `.donated` arms).
  - **Source-level tracing**: each extension was verified by
    tracing through the actual kernel code
    (`donateSchedContext`, `returnDonatedSchedContext`,
    `cancelDonation` dispatch arms).  The lockSets now declare
    exactly the set of objects the underlying transition may
    write.
  - **`permittedKinds` extensions**:
    * `.call` → adds `.schedContext`
    * `.reply` → adds `.schedContext`
    * `.replyRecv` → adds `.schedContext`
    * `.tcbSuspend` → adds `.schedContext`
  - **New consistency-proof builders**: `base_plus_three_opts`
    (for `replyRecv`) and `base_plus_four_opts` (for
    `tcbSuspend`).  Each chains the existing builders.
  - **Test suite expansion**: 83 → 95 runtime assertions (+12).
    New per-transition shape assertions for `tcbSuspend`
    `.bound`/`.donated`/full cases (+3), donation-extended
    reply / replyRecv shape (+2), consistency runtime checks for
    `.call` and `.reply` with donation (+2), permittedKinds
    extensions (+3), and §2 acquireSort with the SC at level 7
    sorting last (+2).

  **WS-SM SM3.C LANDED on branch
  `claude/quirky-mayer-lSoD2`** (withLockSet 2PL combinator,
  lockSetHeld predicate, 2PL discipline theorems, dynamic PIP
  chain-walk locking; closes the third sub-phase of SM3 with 10 of
  11 sub-tasks LANDED — SM3.C.9 deferred to SM5+).  Plan §5.3 of
  [`docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md`](docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md);
  wires SM3.B's per-transition `lockSet` declarations into the
  verified two-phase-locking discipline that SM3.D (deadlock-freedom)
  and SM3.E (serializability) build on.  Lands within the v0.31.9
  release cut (no version bump), mirroring SM3.A / SM3.B.

  - **SM3.C.1**: `withLockSet (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState) :
    SystemState × α` 2PL combinator — acquires every lock in
    `S.lockAcquireSequence` (LockId ascending), runs `action`,
    releases in reverse.  Pure-function form (the plan's `BaseIO`
    pseudocode is the FFI overload, deferred to SM5+).  `acquireAll`
    / `releaseAll` fold helpers with nil/cons unfold lemmas.  File
    `SeLe4n/Kernel/Concurrency/Locks/WithLockSet.lean`.
  - **SM3.C.2**: `acquireLockOnObject` / `releaseLockOnObject`
    dispatch on `l.kind` — `.objStore` advances
    `SystemState.objStoreLock`; modeled kinds route through
    `updateObjectAt` + `KernelObject.updateLock` (advancing the
    inner per-object `RwLockState` via `applyOp`); `.reply`/`.page`
    are no-ops.  `updateLock` carries 7 `@[simp]` unfolds +
    `updateLock_preserves_lockKind` /
    `updateLock_preserves_objectType` / `objectLockOf_updateLock`.
  - **SM3.C.3**: RAII discipline — the abstract `withLockSet` is a
    total pure function with no panic paths, so the release fold
    always runs after the action (structural, not exception-
    handler-based).  The Rust-side `panic = "abort"` discipline
    (SM2.D) covers the hardware panic case.
  - **SM3.C.4**: `lockHeld` / `lockSetHeld` SMP-migration
    precondition for Corollary 2.1.11
    (`SeLe4n/Kernel/Concurrency/Locks/LockSetHeld.lean`).
    `RwLockState.coreHolds` per-state predicate; `lockHeld`
    dispatches on `l.kind` (modeled kinds via `LockId.lookup`,
    `.objStore` via `s.objStoreLock`, fail-closed on `.reply`/
    `.page`); `lockSetHeld` forall-over-pairs.  Decidable;
    `lockSetHeld_empty` / `_singleton` / `_subset` (monotone) +
    `lockSetHeld_default_iff_empty` (a freshly-booted system holds
    no locks).
  - **SM3.C.5**: `lockSet_acquired_in_order` — acquire order is
    `LockId` ascending, lifting SM3.B.6's
    `lockAcquireSequence_ordered`.
  - **SM3.C.6**: `lockSet_released_in_reverse` — release order is
    descending (reverse of acquire).
  - **SM3.C.7**: `lockSet_atomic_under_2pl` +
    `withLockSet_three_phase_decomposition` (Theorem 2.1.10
    operational form — the result is the action's output on the
    post-acquire state composed with the release fold; no observer
    interleaves with the action phase).  File
    `SeLe4n/Kernel/Concurrency/Locks/LockSet2PL.lean`.
  - **SM3.C.8**: `lockSet_invariant_preserved` (Corollary 2.1.11,
    SUBSTANTIVE — not a tautology).  Proves by induction on the
    canonical acquisition sequence that the acquire fold preserves
    any lock-insensitive invariant.  The lock-insensitivity
    hypothesis is discharged structurally for the kind-discipline
    invariant class by the foundation lemmas
    `acquireLockOnObject_preserves_objStoreLock_of_modeled`,
    `releaseLockOnObject_preserves_objStoreLock_of_modeled`, and
    `updateObjectAt_preserves_objectType_at` (which threads the
    RHTable extension invariant `s.objects.invExt` through
    `getElem?_insert_self` / `getElem?_insert_ne` to show the kind
    tag at every key is preserved).
    `withLockSet_invariant_preserved` composes the acquire-fold +
    action + release-fold preservation into the full closure
    SM4..SM6 phase migrations consume.
  - **SM3.C.9**: DEFERRED to SM5+.  Migrating every `@[export]`
    body to wrap its transition in `withLockSet` requires the
    per-core kernel state seam SM5 introduces; at SM3.C the kernel
    is modelled single-core so the wrappers would be no-ops on the
    current abstract model.  A sequencing deferral, not a
    correctness gap.
  - **SM3.C.10**: `tests/WithLockSetSuite.lean` (~430 LoC) — 70+
    surface anchors, 12 decidable examples, 52 runtime `assertBool`
    assertions across 9 sections.  Runnable as
    `lake exe with_lock_set_suite`; Tier-2 + Tier-3 wired.
  - **SM3.C.11**: dynamic PIP chain-walk locking
    (`SeLe4n/Kernel/Concurrency/Locks/DynamicChainExtension.lean`).
    The 3 PIP-invoking transitions walk a blocking chain whose
    length is state-discovered, so no static lockSet can contain
    the chain TCBs.  `withDynamicChainExtension` consumes SM3.B's
    `pipChainStart_<τ>` signal and walks via `walkAndAcquire` (a
    fuel-bounded — `MAX_PIP_RETRIES = 64` — pure function returning
    a `WalkOutcome`).  The deadlock-freedom witness
    `walkAndAcquire_path_ascending_in_ObjId_if_terminated` proves
    that any terminating walk produces a path whose `ObjId.val`s
    are strictly ascending (the SM0.I total-order discipline that
    closes any potential wait-cycle).  `dynamicChainHeld` is the
    4-conjunct chain-held predicate.

  **SM3.C inventory (71 entries)**: `withLockSetTheorems` in
  `Sm3CInventory.lean` across 5 categories (`.combinator` = 31,
  `.held` = 11, `.ordering` = 3, `.atomicity` = 9, `.dynamicChain`
  = 17) with compile-time-checked `wlst!` macro + per-category
  counts + partition-sum + Nodup witnesses.

  **Module reachability**: all 5 SM3.C modules staged via the
  LockSet re-export hub (`Platform/Staged.lean` +
  `staged_module_allowlist.txt`); SM5+ per-core scheduler
  integration is the first production runtime exerciser.

  **AK7-cascade cleanliness**: routes through `RHTable.get?`
  method form + the generic `default_objects_get?_none` helper;
  the `RAW_MATCH_TOTAL` floor stays at the v0.31.2 baseline (122)
  and `RAW_LOOKUP_TID` drops 759 → 757.

  **Test coverage**: 320/320 Lean modules build green;
  `lake exe with_lock_set_suite` reports 88/88 PASS; full Tier
  0+1+2+3 green; AK7 cascade monotonicity all metrics pass.
  **Axiom budget for SM3.C**: 0 Lean axioms, 0 sorries (only the
  standard `propext` / `Quot.sound` / `Classical.choice`
  foundational axioms).  **Items deferred past v1.0.0 with
  correctness impact**: NONE.

  **Group-B deferred-gap closure** (post-landing audit; closes the
  provable-within-scope SM3.C gaps NOT gated on the SM5+ FFI seam):
  SM3.C.7 observational atomicity (`AcquireInsensitive` /
  `ReleaseInsensitive` observer predicates + `acquireAll_lockInsensitive`
  / `releaseAll_lockInsensitive` + `withLockSet_release_invisible` +
  the `lockSet_observer_atomic` capstone — a lock-insensitive observer
  sees only the action's effect, the 2PL acquire/release machinery
  invisible, so no observable intermediate state exists); SM3.C.8
  establishment (`acquireLockOnObject_establishes_lockHeld_modeled` +
  the per-step / fold frames + the multi-lock induction
  `acquireAll_establishes_lockHeld_of_distinct_present_unheld` + the
  `LockSet`-level `acquireAll_establishes_lockSetHeld`, with
  ObjId-distinctness auto-derived from `Nodup` keys + state resolution
  via `lockAcquireSequence_distinct_objId_of_resolves` — proving the
  growing phase genuinely establishes the `lockSetHeld` precondition
  the C.8 metatheorem rests on); SM3.C.11.c conjunct-1
  (`chainLockSeq_acquire_establishes_pathHeld`) plus the
  `blockingServer` transport (`blockingServer_eq_bind` /
  `acquireAll_preserves_blockingServer` /
  `chainFollowsBlockingServer_of_blockingServer_eq`) and the
  full-four-conjunct capstone
  `withDynamicChainExtension_establishes_dynamicChainHeld` (previously
  only the walker's path-structure conjuncts 2/3/4 were established,
  on the pre-acquire state); and SM3.C.11.d two-core deadlock-freedom
  (`dynamic_chain_deadlock_free` / `dynamic_chain_no_mutual_wait`,
  lifting the §6 single-core ascending-path lemma).  The stale §8
  docstring mislabelling write-locked as "the fourth conjunct" is
  corrected to "conjunct 1".  Tests: `WithLockSetSuite` gains §12
  RAII-release (a failing/early-exit action still releases every
  lock), §13 populated-state establishment, §14 observer-atomicity,
  and §15 a real 3-TCB blocking chain `5 → 7 → 10` (walker discovers
  the full path; conjuncts 1 & 4 verified on the acquired state;
  bounded-retry exhaustion at insufficient fuel; two-core
  disjoint-chain non-contention).  The SM3.C inventory grows 71 → 86
  (+5 held, +4 atomicity, +6 dynamicChain); all new theorems are
  axiom-clean; `RAW_LOOKUP_TID` drops 759 → 757 (chain lookups route
  through the `.get?` method form via the new `objects_getElem?_eq_get?`
  bridge).  Items still genuinely gated on the SM5+ per-core FFI seam
  (unchanged): the `withLockSetFFI` / FFI-executing acquire overloads
  (C.1/C.2 FFI forms), the `@[export]`-body migration (C.9), and the
  per-transition `withDynamicChainExtension` wrapper consuming
  `pipChainStart_*` (C.11.b).

  Follow-on: SM3.D (deadlock-freedom Theorem 2.1.9 via the
  `noDeadlock` predicate + `deadlockFreedom_under_2pl_and_ordering`
  + wait-graph acyclicity, consuming SM3.C's
  `lockSet_acquired_in_order` + the SM0.I total order) and SM3.E
  (serializability Theorem 2.1.10 + the single-core-proof-
  preservation Corollary 2.1.11 instantiations) close the SM3
  phase per
  [`docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md`](docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md)
  §§5.4..5.5.

  **WS-SM SM3.D LANDED on branch
  `claude/friendly-rubin-5wOsy`** (deadlock-freedom — Theorem 2.1.9,
  wait-graph acyclicity, bounded-wait, lock-discipline grounding;
  closes the fourth sub-phase of SM3 with all 7 sub-tasks LANDED).
  Plan §5.4 of
  [`docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md`](docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md);
  proves the architectural keystone of SM3 — **no execution of the
  verified microkernel can deadlock** when every transition acquires
  its locks under SM3.C's 2PL discipline in the SM0.I `LockId` total
  order.  Lands within the v0.31.9 release cut (no version bump;
  SM3.A..SM3.E close out together en route to v1.0.0).  New file
  `SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean` (~584 LoC) +
  `Sm3DInventory.lean` (37-theorem inventory), both staged via
  `Concurrency.LockSet` + `staged_module_allowlist.txt` (SM3.E is the
  first runtime exerciser); three `LockId` strict-order helpers
  (`LockId.lt_irrefl` / `lt_trans` / `lt_asymm`) added to SM0.I
  `Kind.lean`.

  - **SM3.D.1**: `noDeadlock` predicate (the two-core mutual-block
    deadlock) + the abstract `KernelExecution` per-core lock-state
    model (`held : CoreId → List LockId`, `blocked : CoreId → Option
    LockId`) + `blockedAt` / `heldBy` + `Decidable (noDeadlock e)`
    via the finite reformulation `noDeadlockDec` + `noDeadlock_iff_dec`
    (the existential's locks are pinned by the `blocked` fields, so
    the `∃ l₁ l₂ : LockId` collapses to a decidable per-pair test —
    no unbounded search over the infinite `LockId` type).
  - **SM3.D.2**: `LockId.le_total` recap (cited from SM0.I).
  - **SM3.D.3**: `lockOrder_strict` (`LockId` strict order is
    irreflexive ∧ transitive), bundling the new `Kind.lean` helpers
    `LockId.lt_irrefl` / `lt_trans` / `lt_asymm`.  (`Irreflexive` /
    `Transitive` are mathlib typeclasses unavailable in the core-only
    toolchain, so stated with explicit `∀`.)
  - **SM3.D.4 (Theorem 2.1.9)**: `deadlockFreedom_under_2pl_and_ordering`
    — no 2PL + ordered execution reaches a two-core deadlock.  Proof
    via the **ladder invariant** `ladder_of_2pl_and_order` (every lock
    a blocked core holds is *strictly* below the lock it waits for).
    The ladder is the exact point where the two hypotheses combine:
    `executionAcquiresInLockIdOrder` gives `held ≤ wanted`;
    `executionFollows2PL` (a core never blocks on a lock it holds)
    gives `wanted ∉ held`, hence `held ≠ wanted`, hence the strict
    `held < wanted` that the cycle contradiction needs.  Both
    hypotheses are genuinely used — neither is dead weight.
  - **SM3.D.5**: `waitGraph_acyclic_under_2pl` — the dual N-core form:
    the wait-for graph among blocked cores is a DAG.  Formalised with
    a mathlib-free transitive closure `ReachesPlus` and `Acyclic R :=
    ∀ c, ¬ ReachesPlus R c c`.  The wanted lock strictly increases
    along every wait edge (`blockedWaitsFor_wanted_lt`) and hence
    every path (`reachesPlus_wanted_lt`), so a cycle would force `w <
    w`.  The coherence corollary `noDeadlock_of_waitGraph_acyclic`
    derives the two-core SM3.D.4 from the N-core SM3.D.5 (a 2-cycle is
    a closed walk c₁ → c₂ → c₁).
  - **SM3.D.6**: `boundedWait_under_2pl` — a transition with lock-set
    size `≤ maxLockSetSize` (= 8) has total worst-case wait bounded by
    `maxLockSetSize · (numCores − 1) · T_cs`.  `WCRT` is modelled
    combinatorially as `totalWaitCost S tCs` (the sum of per-lock
    waits over the canonical acquire sequence), proved equal to
    `|S| · (numCores − 1) · T_cs` (`totalWaitCost_eq`) and bounded by
    the static cap.  `coreCount` is `Concurrency.numCores`.
  - **SM3.D.7**: `tests/DeadlockFreedomSuite.lean` (~357 LoC) — surface
    anchors for every SM3.D symbol, decidable examples on concrete
    `KernelExecution` fixtures, compile-time theorem-inhabitation
    `example`s, and 30 runtime `assertBool` assertions.  **Non-vacuity
    witness**: a genuine 2-core deadlock fixture (`execDeadlock`) that
    IS a mutual block AND *necessarily violates* the ordering
    hypothesis — demonstrating the theorem is sound and not a vacuous
    false-anchor (every deadlock state falsifies a hypothesis).

  **Grounding (§7)**: `execution_satisfies_hypotheses_of_all_prefix`
  discharges both abstract hypotheses from the SM3.B
  `lockAcquireSequence` canonical sort — a blocked core in
  `withLockSet`'s growing phase holds a `Nodup`-keyed ascending
  *prefix* of its transition's acquire order (`CorePrefixOf`) and
  waits on the next element, which forces 2PL
  (`coreFollows2PL_of_prefix`, via the `Nodup` split) and ordering
  (`coreAcquiresInOrder_of_prefix`, via `lockSet_acquired_in_order`).
  This realises the plan §3.7 step "By 2PL, H_c is the prefix of c's
  `lockAcquireSequence(S_c)`": the hypotheses are *consequences* of
  `withLockSet`, not assumptions.

  **Test coverage**: 30 runtime assertions in `deadlock_freedom_suite`
  (Tier-2 wired) + ~50 Tier-3 surface anchors (incl. the 3 new
  `Kind.lean` strict-order helpers).  Full Tier 0+1+2+3 green.
  **Axiom budget for SM3.D**: 0 Lean axioms, 0 sorries.  Items
  deferred past v1.0.0 with correctness impact: NONE.

  **Audit-pass-1 refinements** (deep self-audit; all gaps between the
  plan §5.4 and the initial landing closed — no version bump, refines
  ship inside the v0.31.9 cut):
  - **SM3.D.6 `boundedWait_under_2pl` strengthened to the full plan
    signature** — the initial landing's theorem was a weak
    combinatorial monotonicity fact (`totalWaitCost S ≤ bound`) that
    used neither the 2PL/ordering hypotheses nor a `KernelExecution`.
    The full version now takes `(e : KernelExecution) (c : CoreId)
    (op : KernelOperation) (tCs)` plus the two hypotheses and proves
    `noDeadlock e ∧ WCRT e c op tCs ≤ maxLockSetSize · (numCores−1) ·
    tCs` — the `noDeadlock` conjunct genuinely uses the hypotheses
    (the wait is bounded *because* there is no deadlock), the WCRT
    conjunct uses `op.sizeWithinBound`.  `WCRT` is contention-
    sensitive (`contendersAhead` counts the cores actually holding
    each lock, bounded by `numCores−1`), so it depends on the
    execution and the core (no dead parameters).  The weak form is
    retained as `totalWaitCost_le_bound`; `WCRT_le_totalWaitCost`
    bridges them.
  - **`KernelOperation` + `WCRT` modelled** (previously undefined) —
    `KernelOperation` is a `LockSet` footprint plus a `sizeWithinBound`
    proof; `WCRT` is the contention-summed worst-case response time.
  - **`maxLockSetSize` discharged for the real transitions** —
    `lockSetTransitions_within_bound` proves **all 25** SM3.B
    `lockSet_<τ>` declarations have size `≤ maxLockSetSize` (= 8), via
    the generic `insertOrMerge_size_le` / `lockSetOfList_size_le` /
    `lockSetExtendOpt_size_le` + `size_le_1..4` shape helpers.  The
    premise is no longer vacuous; `KernelOperation.of*` smart
    constructors build a `KernelOperation` from any real transition.
  - **Mode-aware (conflict) wait graph** (previously `AccessMode` was
    ignored) — `conflictWaitsFor` only fires when the requested mode
    *conflicts* (SM3.B `AccessMode.conflicts`) with a held mode (two
    readers create no edge); `conflictWaitGraph_acyclic_under_2pl`
    proves it acyclic via `Acyclic_mono` (the conflict graph is a
    subgraph of the plain wait graph).  The plan-signature
    `noDeadlock` / `waitGraph_acyclic_under_2pl` are unchanged (they
    match SM3.D.1's bare-`LockId` signature); the conflict layer is a
    proven refinement on top.
  - **Model↔kernel bridge** (the abstract `KernelExecution` was
    disconnected from SM3.C's concrete lock state) —
    `lockSetHeld_realizes_heldBy` proves that when a core genuinely
    holds a lock set `S` on a concrete `SystemState` (SM3.C
    `lockSetHeld`, which reads the per-object `RwLockState`), the
    abstract `heldBy (executionOfHeld c S blk)` agrees and each
    declared lock is concretely held (`lockHeld`).
  - **`twoCorePathScenario`** (plan §5.4 SM3.D.7) defined + the plan's
    existential example witnessed in the suite; **`lockOrder_strict_classes`**
    restates SM3.D.3 in the plan's exact `Irreflexive ∧ Transitive`
    form (mathlib-free namespaced abbrevs); **tier-4 QEMU
    deadlock-stress** SKIP-stub (`test_qemu_smp_deadlock_stress.sh`)
    reserves the plan §6.3 nightly slot (the formal guarantee already
    holds for all executions; the runtime spot-check needs SM5+ per-
    core scheduling).
  - **Inventory** grew 37 → 66 entries across 9 categories (added
    `.modeAware`, `.sizeBound`); the suite grew to 50+ runtime
    assertions across 12 sections.  **Axiom budget unchanged**: 0
    axioms, 0 sorries.

  **Audit-pass-2 refinements** (deeper test-soundness audit; the
  production proofs were confirmed axiom-clean — every headline
  theorem rests only on `propext`/`Quot.sound`, `ladder_of_2pl_and_order`
  on none — so this pass closes a *test-coverage* vacuity, not a code
  defect): the audit-pass-1 WCRT runtime test used a zero-contention
  execution (`contendersAhead = 0 ⟹ WCRT = 0`), so it asserted the
  bound only trivially.  Added the `execContention` fixture (core 1
  holds `tcb5`, core 0 blocked on it — deadlock-FREE, satisfies both
  hypotheses) plus runtime witnesses that `contendersAhead = 1` and
  `WCRT = 10` are genuinely **positive**, demonstrating the
  contention-sensitivity the `WCRT` model claims.  Also added
  compile-time inhabitation `example`s for `conflictWaitGraph_acyclic_under_2pl`,
  `KernelOperation.ofReplyRecv`, and a **non-vacuous**
  `lockSetHeld_realizes_heldBy` application (on a genuinely-held
  `objStore` singleton via SM3.C `acquireLockOnObject`).  No production
  symbols changed; the deadlock suite now runs ~56 assertions.

  **WS-SM SM3.E LANDED on branch
  `claude/determined-pasteur-apMXc`** (serializability — Theorem 2.1.10,
  conflict-graph acyclicity, commutativity, single-core proof
  preservation; closes the fifth and final sub-phase of SM3 with all 8
  sub-tasks LANDED — **SM3 CLOSED**).  Plan §5.5 of
  [`docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md`](docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md);
  proves the second architectural keystone of SM3 (after SM3.D's
  deadlock-freedom): **every interleaved execution under strict 2PL is
  conflict-equivalent to a serial execution** (Bernstein et al. 1987),
  the serial order being the commit-time order.  Together SM3.D
  (liveness) and SM3.E (correctness) are the twin levers that let the
  single-core proofs migrate cheaply in SM4..SM6 (Corollary 2.1.11).
  Lands within the v0.31.9 release cut (no version bump; SM3.A..SM3.E
  close out together en route to v1.0.0).  New file
  `SeLe4n/Kernel/Concurrency/Locks/Serializability.lean` (~1857 LoC) +
  `Sm3EInventory.lean` (111-theorem inventory), both staged via
  `Concurrency.LockSet` + `staged_module_allowlist.txt`.

  - **SM3.E.1**: `conflictOrder` + the `KernelTransitionInstance` schedule
    model `(lockSet, core, commitTime, acquireTime : LockId → Nat,
    action : SystemState → SystemState)`; `ktiSharesConflictingLock`
    (decidable via the Bool `ktiConflictsB` + `ktiConflictsB_iff` —
    finite double `List.any` over footprint pairs, bounding the
    `LockId` existential) + `ktiSharesConflictingLock_symm`.
  - **SM3.E.2**: `serialEquivalent` (same final state) + `applySequential`
    (foldl of actions); under strict 2PL each transition commits
    atomically (SM3.C.7), so this is the interleaved net effect on the
    commit-order schedule.
  - **SM3.E.3 (Theorem 2.1.10)**: `serializability_under_2pl` — every
    strict-2PL execution is serial-equivalent to the commit-sorted serial
    order (a permutation, commit-ascending = topological sort).  Proof:
    (a) `conflictGraph_acyclic` (the acyclic conflict graph) via the same
    `ReachesPlus`/strict-`<`-along-edges structure SM3.D used, now over
    commit times; (b) the state-equality via `applySequential_swap_adjacent`
    lifted to the `CommutingReorder` closure, with the insertion-sort
    `commitSort` (`commitSort_perm` + `commitSort_sorted` +
    `commitSort_commutingReorder` under the strict-2PL `outOfOrderCommute`
    hypothesis).  `serializability_under_2pl_exists` is the literal
    `∃ serial` form (non-vacuously witnessed by the commit sort, not the
    interleaved schedule); `commitSorted_respects_conflictPrecedes` is the
    valid-serialization half.
  - **SM3.E.4**: `strictly_2pl_preserved` (locks held until commit) +
    `KernelTransitionInstance.ofWithLockSet` (canonical growing-phase-
    before-commit instance) + `conflictOrder_commit_le` (strict 2PL forces
    conflict resolution in commit order).
  - **SM3.E.5**: ≥8 commutativity lemmas at two honest fidelities —
    **structural** `actionsCommute` for read-only
    (`readOnlyInstance_actionsCommute`, the plan's `cspaceRead_commutes`
    analog) and disjoint-subsystem (`setObjStoreLock_setScheduler_commute`)
    pairs (feeding the structural theorem); and **observational**
    `objStoreEquiv` for write/write on distinct objects
    (`updateObjectAt_objStoreEquiv_comm`).  The write/write case is
    observational because the Robin-Hood object store's slot layout is
    insertion-order-dependent; conflict-serializability IS an
    observational property (Bernstein), so this is faithful (documented,
    not overclaimed).
  - **SM3.E.6 (Corollary 2.1.11)**: `singleCore_proof_preservation` (the
    pre→post meta-theorem: single-core theorems lift to SMP gated only by
    lock-insensitivity + `lockSetHeld`), reusing SM3.C.8's
    `withLockSet_invariant_preserved`; `withLockSet_growing_phase_establishes_lockSetHeld`
    shows the `lockSetHeld` precondition is a *consequence* of
    `withLockSet`, not an assumption; `singleCore_invariant_preservation`
    is the invariant form.

  **Non-vacuity**: `serializability_of_readOnly_schedule` proves a
  hypothesis-free family (read-only / all-identity-action schedules) is
  serial-equivalent to its commit sort, so `serializability_under_2pl`
  is not vacuous.

  **Test coverage**: `tests/SerializabilitySuite.lean` — 60+ surface
  anchors + 18 decidable examples + 6 theorem-application inhabitation
  witnesses + 27 runtime `assertBool` assertions across 6 sections
  (`lake exe serializability_suite`); 8 major-theorem `#check` anchors
  (SM3.E.8) + runtime inventory check in `tests/SmpSurfaceAnchors.lean`.
  Tier-2 + Tier-3 wired.  **Axiom budget**: 0 Lean axioms, 0 sorries
  (only `propext` / `Quot.sound` / `Classical.choice`).  111-theorem
  SM3.E inventory across 9 categories.  Full Tier 0+1+2+3 green.  Items
  deferred past v1.0.0 with correctness impact: NONE.

  **SM3 acceptance gate** (per
  [`docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md`](docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md)
  §8): all formal items checked.  WS-SM SM3 CLOSED with all five
  sub-phases LANDED (SM3.A–SM3.E).  The `@[export]`-body migration
  (SM3.C.9) remains deferred to SM5+ per the per-core kernel-state seam.
  SM4 (per-core state) follows per the master overview.

  **Audit-pass-1 refinements** (post-landing self-audit; closed three
  honesty/completeness gaps per the `implement-the-improvement` rule —
  the initial theorems were true + axiom-clean but under-delivered on
  their stated intent):
  - **Orientation completeness**: `conflictGraph_acyclic`'s proof did not
    use the conflict relation (it is `Nat.lt` irreflexivity).  Added
    `conflictPrecedes_total_of_distinct_commit` (under the strict-2PL
    distinct-commit lock-exclusion property every conflicting pair is
    *comparable* — where `ktiSharesConflictingLock`/its symmetry is
    essential) + `conflictPrecedes_strict_total_of_distinct_commit` (the
    conflict graph is a strict *total* order, not merely acyclic — the
    genuine Bernstein content).
  - **Strict-2PL grounding**: `serializability_under_2pl`'s
    `outOfOrderCommute` hypothesis was prose-linked to 2PL only.  Added
    `conflictsCommitOrdered` (decidable lock-exclusion predicate),
    `outOfOrderCommute_of_conflictsCommitOrdered`, and the grounded
    `serializability_under_2pl_of_conflicts_ordered` (assumes only the
    primitive strict-2PL conditions) — mirroring SM3.D §7.
  - **Non-vacuous Cor 2.1.11**: the `singleCore_proof_preservation` test
    used the trivial `True` invariant.  Added per-step
    `acquire/releaseLockOnObject_preserves_objStoreLock_wf` +
    `withLockSet_preserves_objStoreLock_wf` (the lever on the REAL
    `objStoreLock.wf` invariant).
  - **`conflictOrder` connected to the serialization order**: the plan's
    primary SM3.E.1 relation was a near-orphan (no theorem proved the
    serialization respects it).  Added `conflictOrder_implies_conflictPrecedes`
    (under strict 2PL + distinct commit a `conflictOrder` edge IS a
    `conflictPrecedes` edge) + `commitSorted_respects_conflictOrder` (the
    commit sort never places a `conflictOrder` edge backward).
  SM3.E inventory grew 68 → 78 (+1 conflict, +2 acyclicity, +4
  serializability, +3 preservation); suite gains a §3b grounding section +
  the `objStoreLock.wf` and `conflictOrder`-bridge examples.  All
  axiom-clean; full Tier 0+1+2+3 green.

  **Audit-pass-3 refinements** (deepest deep audit; closed the three
  "honestly-deferred" SM3.E gaps the initial landing documented but did
  not implement — per the `implement-the-improvement` rule the
  acknowledged-but-unbuilt scope is the inferior artefact, so it is now
  materialised as code rather than a caveat.  No version bump; refines
  ship inside the v0.31.9 cut):
  - **Atomicity bridge (the avoided SM3.E.2/SM3.E.7 connection)**: the
    initial landing modelled `applySequential` as a `foldl` of *bare*
    `action`s and proved serial-equivalence at that abstraction, but
    never connected it back to the SM3.C.7 `withLockSet` atomicity
    result — so the headline theorem was about a schedule of raw
    actions, not a schedule of *2PL-wrapped transitions*.  Closed via
    a new §9 (5 theorems): `withLockSet_observation_eq_action` proves
    the observable post-state of a `withLockSet`-wrapped transition
    equals the action applied to the post-acquire state (the
    acquire/release fold is invisible to any lock-insensitive observer,
    discharged through SM3.C.7 `lockSet_observer_atomic` +
    `AcquireInsensitive`/`ReleaseInsensitive`); `applySequentialWithLockSet`
    (+ nil/cons simp lemmas) folds a list of `withLockSet`-wrapped
    transitions; `applySequentialWithLockSet_observation` lifts the
    single-step bridge to the whole schedule via `ActionPiCongr` /
    `applySequential_piCongr`.  This is the theorem that makes
    `serializability_under_2pl` a statement about the *real* 2PL kernel
    rather than an idealised raw-action fold.
  - **Observational serializability (the avoided write/write coverage)**:
    the initial SM3.E.5 proved `objStoreEquiv`-commutativity for
    write/write-to-distinct-objects as an *isolated* lemma, but the
    top-level `serializability_under_2pl` reordered via the *structural*
    `actionsCommute` (`Eq`), which write/write pairs do NOT satisfy (the
    Robin-Hood object store's slot layout is insertion-order-dependent).
    So the most important case for a real kernel — two cores writing
    distinct objects — was provably commuting in the lemma library but
    NOT carried by the headline theorem.  Closed via a new §10 (18
    theorems): `serializability_under_2pl_obs` proves serial-equivalence
    *up to `objStoreEquiv`* for any schedule whose actions commute
    observationally and preserve `invExt`, threading the RHTable
    extension invariant through the entire `commitSort` reorder
    (`ActionObsCongr` / `ActionPreservesInvExt` /
    `KernelTransitionInstance.wellBehavedObs` / `.actionsCommuteObs`,
    `applySequential_preservesInvExt` / `_obsCongr` /
    `_swap_front_obs` / `_cons_obs`, `outOfOrderCommuteObs`,
    `insertByCommitTime_obs`, `commitSort_obs`).  `objStoreWriteInstance`
    + `_wellBehavedObs` + `_actionsCommuteObs` provide the canonical
    write/write instance the headline now genuinely covers.  Conflict-
    serializability IS an observational property (Bernstein), so the
    `objStoreEquiv` fidelity is faithful, not a weakening.
  - **Second real Cor 2.1.11 instantiation (the avoided generality
    demonstration)**: audit-pass-1 grounded Cor 2.1.11 on the single
    `objStoreLock.wf` invariant, leaving the impression the lever might
    only work for that one toy invariant.  Closed via a new §8c (5
    theorems): `withLockSet_preserves_objectType_at` proves the 2PL
    machinery preserves a SECOND, structurally-different real invariant
    — the per-key kind-tag equality against the pre-state, bundled with
    `invExt` (`releaseLockOnObject_preserves_invExt`,
    `updateObjectLockAt_preserves_objectType_at`,
    `acquire`/`releaseLockOnObject_preserves_objectType_at`).  This is
    exactly the object-store structural invariant class SM4..SM6 phase
    migrations consume, demonstrating the Cor 2.1.11 lever generalises
    beyond `objStoreLock.wf`.
  SM3.E inventory grew 78 → 106 (+5 preservation, +5 atomicityBridge,
  +18 observational; two new `SerializabilityCategory` variants
  `.atomicityBridge` / `.observational`); the suite gains a write/write
  observational-serializability example (`writeWriteSched_wellBehavedObs`
  / `_outOfOrderCommuteObs`), an atomicity-bridge example, and a second-
  invariant `objectType` example, taking it to 27 runtime assertions /
  102 surface anchors.  All new theorems verified axiom-clean
  (`propext` / `Quot.sound` / `Classical.choice` only via
  `#print axioms`); full Tier 0+1+2+3 green.  Items deferred past
  v1.0.0 with correctness impact: NONE.

  **Audit-pass-4 refinements** (comprehensive axiom sweep + full code
  re-read): a `#print axioms` sweep over all 106 inventory theorems
  confirmed every one is axiom-clean (zero `sorryAx` / `native_decide` /
  `unsafe`; only `propext` / `Quot.sound` / `Classical.choice`), and a
  line-by-line read of §1–§10 found the proofs mathematically sound (no
  vacuity, no assumed-conclusion).  The audit surfaced ONE genuine gap
  and two stale docstrings, all closed:
  - **Atomicity-bridge non-vacuity (the gap)**: the §9 bridge takes
    `AcquireInsensitive` / `ReleaseInsensitive` as hypotheses but — unlike
    §8b (objStoreLock.wf), §8c (objectType), and §10 (write/write), each of
    which carries a concrete non-vacuity witness — no concrete non-trivial
    observer satisfying them was exhibited anywhere (SM3.C only `#check`s
    the predicates), so a reader could not rule out vacuity.  Closed with a
    new §9b: `acquireLockOnObject_preserves_scheduler` /
    `releaseLockOnObject_preserves_scheduler` (the lock primitives leave the
    `scheduler` field untouched), `schedulerObserver_acquireInsensitive` /
    `schedulerObserver_releaseInsensitive` (the `scheduler` projection is a
    genuine non-trivial observer discharging both hypotheses
    unconditionally), and `withLockSet_observation_scheduler_witness` (the
    bridge applied non-vacuously: a scheduler write wrapped in the full 2PL
    machinery is observed as `= sch`, the lock folds invisible).
  - **Stale docstring**: `Sm3EInventory.lean`'s header said "Seven
    categories" (nine since audit-pass-3) — corrected with the two new
    category bullets + the §8b/§8c/§9b sub-notes.
  Inventory grew 106 → 111 (+5 atomicityBridge); `atomicityBridge` count
  5 → 10; suite + surface anchors + tier-3 updated.  All 111 inventory
  theorems re-verified axiom-clean via `#print axioms`; full Tier 0+1+2+3
  green.  Items deferred past v1.0.0 with correctness impact: NONE.

  **WS-SM SM4.A LANDED at v0.31.11 on branch
  `claude/magical-turing-ZUaAB`** (per-core `Vector` bootstrap +
  PlatformBinding; opens SM4 — the path-a replacement of the singular
  `SchedulerState` fields with `Vector α coreCount` indexed by
  `CoreId`).  All eight sub-tasks landed in one cut per
  [`docs/planning/SMP_PER_CORE_STATE_PLAN.md`](docs/planning/SMP_PER_CORE_STATE_PLAN.md)
  §5.1; SM4.A.1 + SM4.A.2 are the new Lean-side work, SM4.A.3..SM4.A.8
  confirm/recap the SM0 deliverables the per-core `Vector` machinery
  rests on.

  - **SM4.A.1 + SM4.A.2**: `SeLe4n.PerCoreVector` bootstrap in
    `SeLe4n/Prelude.lean`.  Per plan §4.2 the implementation uses Lean
    core's `Array`-backed `Vector α n` (not `List.Vector`) — the only
    choice giving compile-time length safety (`CoreId = Fin n` indexing
    in-bounds by construction), O(1) random access, decidable equality,
    AND an `Array`-backed runtime.  Lean core's vector lemmas are stated
    in `getElem` (`Nat`-indexed) form; the SM4 per-core accessors index
    with a `Fin n` value via `Vector.get`, so this block re-expresses
    them in `Vector.get` form on top of the definitional bridge
    `get_eq_getElem` (`v.get i = v[i.val]`, by `rfl`).  Six helpers
    (`namespace SeLe4n.PerCoreVector`): `get_set_eq` (read-after-write at the
    same core returns the written value), `get_set_ne` (a per-core write
    frames every other core's slot), `toList_length` (`v.toList.length = n`),
    `replicate_get` (every slot of a replicate holds the value — the
    SM4.B.9 workhorse), `ext` (per-core `Vector.get`-form
    extensionality; deliberately NOT `@[ext]`-tagged so the core
    `_root_.Vector.ext` keeps firing under the `ext` tactic), and
    `nodup_of_finRange` (`(List.finRange n).Nodup` for arbitrary `n` —
    Lean core has `nodup_range` but no `nodup_finRange`; proved by
    induction via `finRange_succ` + `Fin.succ_ne_zero` + `Fin.succ_inj`;
    generalises `Concurrency.allCores_nodup`'s literal-4 `decide` to a
    platform-parameterised `coreCount`).  Helpers are untagged (no
    global `@[simp]`/`@[ext]` perturbation; consumers opt in locally).
    0 Lean axioms, 0 sorries.
  - **SM4.A.3**: runtime efficiency — confirmed `Vector α n` is
    `Array`-backed (`structure Vector where toArray : Array α`) with
    `@[inline, expose]` `get`/`set`/`replicate`, so it compiles to O(1)
    `Array` ops.  The full `lake exe sele4n` per-core-access trace lands
    at SM4.B.15 once `SchedulerState` is itself `Vector`-shaped.
  - **SM4.A.4**: RPi5 `coreCount = 4` confirmed, pinned to
    `Concurrency.numCores` via the existing
    `numCores_eq_rpi5_coreCount` (`rfl`).
  - **SM4.A.5**: added the single-core simulation binding
    `SimSingleCorePlatform` (`coreCount := 1`) alongside the 4-core SMP
    sims (`SimPlatform` / `SimRestrictivePlatform`, `coreCount := 4`),
    realising the single-core variant the SM0.G code comment
    anticipated.  `coreCount := 1` is the minimal non-degenerate
    per-core topology — the SM4.B.15 byte-identical single-core trace
    target, and the cheapest way to surface an implicit "exactly one
    current thread" assumption (plan §4.1).  Reuses every contract from
    the permissive sim binding; only the topology differs.
  - **SM4.A.6 / SM4.A.7 / SM4.A.8**: recaps of `CoreId = Fin numCores`,
    `bootCoreId`, and `allCores` (`allCores_length`, `allCores_nodup`).
    No new code; the suite anchors them and ties `nodup_of_finRange
    numCores` back to `allCores_nodup` (since `allCores =
    List.finRange numCores`).

  **Test coverage**: NEW FILE `tests/PerCoreVectorSuite.lean`
  (`lake exe per_core_vector_suite`) — 22 surface-anchor `#check`s, 40
  decidable/definitional examples, 34 runtime `assertBool` assertions
  across seven sections (Vector helpers, ext + nodup, Array backing,
  platform core-count topologies, CoreId/bootCoreId/allCores recap, the
  SM4.A.3 array-witness + SM4.A.5 topology-parametric exercise, and the
  SM4.A.1 instance anchors — `DecidableEq`/`Repr`/`Inhabited`/`BEq` on
  `Vector (Option ThreadId) numCores`).  Wired into Tier 2 (negative) +
  Tier 3 (invariant surface).  Full default build (320 jobs) green;
  Tier 0+1+2+3 green.  Items deferred past v1.0.0 with correctness
  impact: NONE.

  **Post-landing audit + completion pass** (+ three further audit passes):
  `#print axioms` confirmed all `SeLe4n.PerCoreVector` declarations depend only
  on `propext` / `Quot.sound`; a `SchedulerState`-mimicking probe
  confirmed they match downstream call sites under `rw`/`simp` even when
  `Vector.set`'s bounds proof is synthesized by `get_elem_tactic` (proof
  irrelevance ⇒ defeq), so SM4.B/SM5 consume them directly.  The audit
  corrected the initial `23/26/25` count miscount; subsequent passes
  closed the remaining non-optimal items: (1) **SM4.A.3 rigor** —
  codegen evidence (`Vector.get` → `lean_array_fget`, `set` →
  `lean_array_fset`, `replicate` → `lean_mk_array`; no `lean_list_*`)
  plus the persistent witness `get_eq_toArray_getElem` (`.get` indexes
  `toArray` directly); (2) **`nodup_of_finRange` made load-bearing** —
  `allCores_nodup` rewired through it, replacing the literal-`4`
  `decide`; (3) **single-core sim genuinely exercised** — a
  topology-parametric runtime fold of `Vector.get` over
  `List.finRange (coreCount P)` drives the binding's `coreCount`
  end-to-end (`SimSingleCore` = 1, `Sim`/`RPi5` = 4) and gives
  `toList_length` a binding-derived consumer; (4) **`length` renamed to
  `toList_length`** — bare `length` made `v.length` / `Vector.length`
  resolve to this `Prop`-valued lemma under the `open SeLe4n` every
  kernel file uses (a trap — the count is `v.size`; core has no
  `Vector.length`); (5) **instance anchors** — the suite verifies
  `Vector (Option ThreadId) numCores` carries
  `DecidableEq`/`Repr`/`Inhabited`/`BEq` (the §4.2 rationale SM4.B's
  `SchedulerState` depends on); (6) **`SeLe4n.Vector` namespace retired**
  → `SeLe4n.PerCoreVector` — a sub-namespace whose final component is
  `Vector` exposed every helper as `Vector.<name>` under `open SeLe4n`,
  shadowing/aliasing core's `_root_.Vector` (the `length` trap behind
  (4), plus the benign `ext` alias); a non-`Vector` namespace removes
  that whole collision class structurally, so `toList_length` is kept
  purely for semantic precision now.  Suite now: 22 / 40 / 34.  (The
  Fin-indexed `set` wrapper was deliberately **not** added — YAGNI: the
  raw-`set` `get_set_eq`/`_ne` lemmas already match SM5's
  `v.set c.val x` call sites by proof irrelevance.)

  Follow-on: SM4.B (`SchedulerState` path-a field replacement),
  SM4.C/SM4.D (scheduler + cross-subsystem theorem migrations), SM4.E
  (`bootFromPlatform_singleCore_witness` retirement +
  `bootFromPlatform_smp_witness`) per
  [`docs/planning/SMP_PER_CORE_STATE_PLAN.md`](docs/planning/SMP_PER_CORE_STATE_PLAN.md)
  §§5.2..5.5.

  **WS-SM SM4.B LANDED at v0.31.12 on branch
  `claude/sharp-carson-V2Y59`** (`SchedulerState` path-a `Vector`
  replacement; plan §5.2).  Replaces the seven singular per-core
  `SchedulerState` fields with `Vector α Concurrency.numCores` indexed
  by `CoreId`, on top of the SM4.A `PerCoreVector` bootstrap.  All
  fifteen sub-tasks landed in one green cut (decision #4: full path-a,
  no scalar shim).  Observably transparent — `lake exe sele4n` is
  **byte-identical** to `tests/fixtures/main_trace_smoke.expected`
  (SM4.B.15).

  - **SM4.B.1..7**: the fields `runQueue`, `current`, `replenishQueue`,
    `activeDomain`, `domainTimeRemaining`, `domainScheduleIndex`,
    `lastTimeoutErrors` flip scalar → `Vector α numCores` with defaults
    `Vector.replicate numCores <neutral>`.  `domainSchedule` and
    `configDefaultTimeSlice` stay system-wide.
  - **SM4.B.8**: the seven `…OnCore (c : CoreId)` read accessors (phase-1
    scalar wrappers) are now `Vector.get`-backed; seven matching
    `set…OnCore (c) (v)` writers added.  Accessors are deliberately
    **not** `@[simp]`; instead a **70-lemma `@[simp]` store/load
    algebra** (7 read-after-write `set…OnCore_…OnCore_self` + 7 same-field
    cross-core independence `set…OnCore_…OnCore_ne` (write core `c` leaves
    a distinct core `c'`'s same-field slot unchanged) + 42 cross-field
    frame `set…OnCore_…OnCore` + 14 system-wide-field frame lemmas) drives
    proof automation.  Because `Vector.get (Vector.set …)`
    is **not** definitional, these proved lemmas — not `rfl`/iota — are
    what let setter-state reads reduce under `simp`.
  - **SM4.B.9**: `default_state_perCoreInitialized` — every per-core
    read of the default scheduler returns the neutral value on every
    core (via `PerCoreVector.replicate_get`).
  - **SM4.B.10**: `SchedulerState.ext_perCore` — per-core
    extensionality (reproved through `PerCoreVector.ext`).
  - **SM4.B.11..13**: `Repr` derived and the explicit `Inhabited`
    instance re-derived for the `Vector`-shaped record; `default` is
    the all-`replicate` scheduler.  No `BEq`/`DecidableEq` instance
    exists or is needed (nothing compares schedulers via `==`), so
    SM4.B.12 is N/A.
  - **SM4.B.14**: immediate caller sites in `Model/State.lean`
    (`setCurrentThread`, freeze boundary, `runnable` =
    `(runQueueOnCore bootCoreId).toList`).
  - **SM4.B.15**: trace fixture byte-identical — the boot core
    (`bootCoreId`) behaves exactly as the former scalar, so the
    single-core scenario is unchanged.

  **Kernel-wide proof migration**: the flip cascades through the
  production import closure — `Scheduler/Operations/{Core,Preservation}`
  (incl. `switchDomain` / `scheduleDomain` and the EDF / priority-match /
  context / domain-time preservation proofs), `SchedContext`,
  `Lifecycle` (suspend/cleanup), IPC scheduler lemmas, priority
  inheritance, `InformationFlow` projection + NI proofs,
  `Architecture/Invariant`, `CrossSubsystem`, `Platform/Boot`,
  `Model/FreezeProofs`.  Every scalar record-update write becomes a
  `set…OnCore bootCoreId` call; every proof that previously reduced a
  record literal by `rfl`/iota now reduces the setter state through the
  `@[simp]` store/load algebra (read-after-write at the boot core,
  cross-field frames for untouched fields).  Key recurring NI pattern:
  `setRunQueueOnCore` frames every `projectState` component except
  `projectRunnable`, so the projection-preservation proofs reduce the
  other scheduler projections via the cross lemmas and discharge only
  the runnable filter.  The `bootFromPlatform_singleCore_witness`
  keystone is restated over `currentOnCore bootCoreId`; its full SM4.E
  retirement + `bootFromPlatform_smp_witness` remain a later sub-phase.

  **Test suites migrated**: `PerCoreSchedulerStateSuite` now exercises
  genuine per-core independence (a boot-core write leaves other cores'
  slots neutral); `Testing/StateBuilder`, `Testing/MainTraceHarness`
  (new `setBootRqCur` fixture helper), `NegativeStateSuite`,
  `OperationChainSuite`, `InformationFlowSuite`, `ModelIntegritySuite`,
  `TraceSequenceProbe`, and the syscall/error/cascade/priority suites
  build their scheduler fixtures through the per-core setters.  Full
  Tier 0+1+2 smoke green; trace fixture byte-identical; 0 `sorry` /
  0 `axiom`.  Follow-on: SM4.C/SM4.D (scheduler + cross-subsystem
  theorem migrations), SM4.E (witness retirement) per
  [`docs/planning/SMP_PER_CORE_STATE_PLAN.md`](docs/planning/SMP_PER_CORE_STATE_PLAN.md)
  §§5.3..5.5.

  **WS-SM SM4.C LANDED at v0.31.13 on branch
  `claude/elegant-wozniak-FkOsZ`** (per-core scheduler invariant
  migration; plan §5.3 / §5.6).  Lifts every scheduler invariant
  *predicate* from the single-core forms (pinned to `bootCoreId` after
  SM4.B) to per-core forms parameterised by an explicit `(c : CoreId)`,
  following plan §3.4's Pattern 1: each per-core form's body is the
  existing predicate's body with `bootCoreId` → `c` and `s.runnable` →
  `(s.runQueueOnCore c).toList`.  The migration is **additive and
  soundness-preserving**: every per-core form at `bootCoreId` is
  *definitionally equal* to the existing single-core predicate (proved
  as `Iff.rfl` by the boot-core bridge lemmas), so the live
  `schedulerInvariantBundle*` / `crossSubsystemInvariant` surface and
  the hundreds of preservation theorems that consume it stay untouched
  and green; SM4.C strictly adds the per-core layer SM5 consumes.

  NEW FILE `SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean` (~380 LoC,
  staged via `Platform/Staged.lean` + `staged_module_allowlist.txt`):

  - **§1 — 16 per-core predicate forms** (the per-core slice of
    `schedulerInvariantBundleExtended`'s genuinely-per-core conjuncts):
    `queueCurrentConsistentOnCore`, `runQueueUniqueOnCore`,
    `currentThreadValidOnCore`, `currentThreadInActiveDomainOnCore`,
    `timeSlicePositiveOnCore`, `currentTimeSlicePositiveOnCore`,
    `edfCurrentHasEarliestDeadlineOnCore`, `contextMatchesCurrentOnCore`,
    `runnableThreadsAreTCBsOnCore`, `schedulerPriorityMatchOnCore`,
    `domainTimeRemainingPositiveOnCore`, `currentBudgetPositiveOnCore`,
    `budgetPositiveOnCore`, `replenishmentPipelineOrderOnCore`,
    `replenishQueueValidOnCore`, `effectiveParamsMatchRunQueueOnCore`.
    The five system-wide predicates (`schedContextsWellFormed`,
    `schedContextBindingConsistent`, `boundThreadDomainConsistent`,
    `domainScheduleEntriesPositive`, `configTimeSlicePositive`) are
    core-independent and need no `c`.
  - **§2 — 16 boot-core bridges** (`…OnCore_bootCore_iff`): each is
    `Iff.rfl`, the non-orphan defeq grounding (`SchedulerState.runnable`
    is *definitionally* `(s.runQueueOnCore bootCoreId).toList`).
  - **SM4.C.29 — aggregate**: `schedulerInvariant_perCore st c` is the
    10-conjunct per-core analogue of `schedulerInvariantBundleFull`
    minus the system-wide `domainScheduleEntriesPositive`;
    `schedulerInvariant_smp st := ∀ c, schedulerInvariant_perCore st c`
    is the SMP form; `schedulerInvariant_perCore_aggregateForall` is
    the plan §5.6 bridge between them; 10 per-conjunct projections
    mirror the `schedulerInvariantBundleFull_to_*` family.
  - **§4 — bundle bridges to the live cross-subsystem surface**:
    `schedulerInvariantBundleFull_to_perCore_bootCore` (and the
    `Extended` lift) — every existing single-core preservation theorem
    yields a per-core preservation at `bootCoreId` *for free*; converse
    `…_bootCore_to_bundleFull` reassembles the full bundle.
  - **§5 — default-state**: `default_schedulerInvariant_perCore (c)` /
    `default_schedulerInvariant_smp` — every core satisfies the per-core
    invariant on the freshly-booted system (currentOnCore c = none ⟹
    current-dependent conjuncts vacuous; runQueue empty ⟹ ∀-runnable
    conjuncts vacuous; domainTimeRemaining = 5 > 0).
  - **SM4.C.30 — frame + cross-core pairwise independence**: the
    substantive cross-core-independence content.
    `schedulerInvariant_perCore_frame` is the general frame lemma (core
    `c`'s invariant depends only on core `c`'s `current` / `runQueue` /
    `domainTimeRemaining` slots, `st.objects`, and `st.machine.regs`).
    `schedulerInvariant_perCore_frame_idle` is the regs-independent
    variant for an idle core (`currentOnCore c = none` on both states)
    — needed for boot operations like `schedule`'s context restore
    that re-write `machine.regs`; idle cores' current-dependent
    conjuncts are vacuous, so register state is irrelevant.  Three
    cross-core independence corollaries
    (`_independent_of_setCurrentOnCore`, `…setRunQueueOnCore`,
    `…setDomainTimeRemainingOnCore`) instantiate the frame via the
    SM4.B `set…OnCore_…OnCore_ne` algebra.
    **`schedulerInvariant_perCore_pairwise`** is the SM4.C.30
    deliverable — per the implement-the-improvement rule,
    *strengthens* the plan's documentation-only `P ↔ P` form into a
    substantive theorem: for `c₁ ≠ c₂`, simultaneously overwriting all
    three of core `c₂`'s invariant-read slots (`current`, `runQueue`,
    `domainTimeRemaining`) leaves core `c₁`'s per-core invariant
    unchanged.  The `Vector` per-core indexing (SM4.B) is exactly what
    delivers this independence.
  - **§7 — SMP-preservation skeleton (the SM5 bridge)**:
    `schedulerInvariant_smp_of_bootCore_and_idle_frame` — the
    composition that turns a single-core boot-core preservation +
    non-boot-core framing into a full SMP preservation.  SM5's per-
    core operation needs to be reproven only at the core it writes;
    every other core discharges by the idle frame lemma.

  **Test coverage**: NEW FILE `tests/SchedulerInvariantPerCoreSuite.lean`
  (~330 LoC) + `scheduler_invariant_per_core_suite` lake exe — 60+
  Tier-3 surface anchors (every SM4.C public symbol), 12 elaboration-
  time `example`s applying every headline theorem to verified inputs,
  16 runtime `assertBool` assertions across four sections (default-
  state per-core foundations on every core in `allCores`; theorem-
  application checks; cross-core pairwise independence; bridge
  reflexivity).  Tier-2 + Tier-3 wired (`test_tier2_negative.sh` runs
  the suite; `test_tier3_invariant_surface.sh` has a dedicated SM4.C
  anchor block).  **Axiom budget for SM4.C**: 0 Lean axioms, 0 sorries
  — every theorem depends only on `propext` / `Quot.sound` /
  `Classical.choice` (verified via `#print axioms` on the headline
  theorems).  Full `lake build` (default target) + `lake build
  SeLe4n.Platform.Staged` + `bash scripts/check_production_staging_partition.sh`
  (35 staged-only modules) + Tier 0+1+2+3 all green.

  **WS-SM SM4.C audit-passes 1–5** (v0.31.14 → v0.31.18, same branch):

  - **Audit-pass-1 (v0.31.14)**: typed-accessor migration for the three
    SC-using per-core predicates + the four missing setter independence
    corollaries.  AK7 baseline restored to the v0.31.2 floor
    (`RAW_MATCH_TOTAL` 122; `GETTCB_ADOPTION` +56 net).  All sixteen
    per-core predicates use typed `getTcb?` / `getSchedContext?`
    accessors.  Seven setter independence corollaries (one per per-core
    setter).

  - **Audit-pass-2 (v0.31.15)**: 17 per-conjunct frame lemmas
    (§5.5 — fine-grained SM5 reasoning), plus the new
    `runQueueOnCoreWellFormed` predicate (plan §5.6 missing), plus the
    extended per-core aggregate `schedulerInvariant_perCore_extended`
    (§3.5) mirroring `schedulerInvariantBundleExtended` (composes the
    4 SC-using predicates with the base 10-conjunct aggregate).
    Extended bundle bridges + default + projections.  Extended frame
    + idle frame + pairwise + SMP-preservation skeleton (§8).
    27 runtime assertions.

  - **Audit-pass-3 (v0.31.16)**: three cross-subsystem per-core
    predicates per plan §5.6 (`schedContextRunQueueConsistent_perCore`,
    `priorityInheritance_perCore`, `activeDomainOnCore_isInDomainSchedule`),
    plus the cross-subsystem aggregate `schedulerInvariant_perCore_crossSubsystem`
    (§10) composing extended + the three cross-subsystem predicates.
    Boot-core bridges + defaults + per-conjunct frame lemmas (3) +
    aggregate bridges (incl. `crossSubsystemInvariant_to_perCore_crossSubsystem_bootCore`).
    41 runtime assertions.

  - **Audit-pass-4 (v0.31.17)**: per-operation per-core preservation
    theorems demonstrating the SM5-bridge payoff.  §11 adds
    `schedulerInvariant_perCore_holds_if_idle` (sufficient idle
    theorem) + `schedulerInvariant_smp_of_bootCore_preservation`
    (clean composition for ops that change `objects` / `regs`).  NEW
    FILE `SeLe4n/Kernel/Scheduler/Invariant/PerCorePreservation.lean`
    with 5 per-op aggregate preservation theorems
    (`schedule_preserves_schedulerInvariant_smp`,
    `handleYield_preserves_schedulerInvariant_smp`,
    `timerTick_preserves_schedulerInvariant_smp`,
    `switchDomain_preserves_schedulerInvariant_smp`,
    `scheduleDomain_preserves_schedulerInvariant_smp`) + chooseThread
    base bridge.  Each composes existing single-core preservation
    with the §11 composition.

  - **Audit-pass-5 (v0.31.18)**: 25 named per-conjunct per-op SMP
    preservation theorems (§7 of PerCorePreservation.lean) — plan §3.4
    Pattern 1 mechanical lifts of existing single-core preservation to
    per-core SMP form.  5 conjuncts (queueCurrentConsistent /
    runQueueUnique / currentThreadValid / domainTimeRemainingPositive /
    runnableThreadsAreTCBs) × 5 ops = 25 one-line projections from the
    aggregate per-op preservation.

  **Cumulative SM4.C state at v0.31.18**:
  - 16 per-core predicate forms (all typed-accessor).
  - 16 boot-core bridges.
  - 3 aggregates (`schedulerInvariant_perCore`, `…_extended`,
    `…_crossSubsystem`) + corresponding SMP forms + projections +
    bundle bridges + defaults.
  - 17 + 3 = 20 per-conjunct frame lemmas.
  - 7 setter independence corollaries + pairwise theorem.
  - 6 per-op aggregate preservation + 25 per-conjunct per-op
    preservation = 31 per-op theorems.
  - 2 modules: `SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean`
    (~1660 LoC) + `…/PerCorePreservation.lean` (~700 LoC).
  - 41 runtime assertions in `tests/SchedulerInvariantPerCoreSuite.lean`
    + 1 in `tests/SchedulerInvariantPerCorePreservationSuite.lean`.
  - 35 staged-only modules (was 34 at v0.31.13); production/staged
    partition gate green.
  - AK7 baseline at the v0.31.2 floor for raw-match counts; GETTCB +56
    / GETSCHEDCTX +27 net adoption growth.

  Items deferred past v1.0.0 with correctness impact: NONE.  Follow-on:
  SM4.D (cross-subsystem theorem migrations — IPC / Capability /
  Lifecycle / Architecture / InformationFlow / CrossSubsystem theorems
  that read `SchedulerState`) — **LANDED below**; SM4.E
  (`bootFromPlatform_singleCore_witness` retirement +
  `bootFromPlatform_smp_witness` per plan §3.8); post-SM4.C
  extensions: per-conjunct preservation for the 5 less-used conjuncts
  × 5 ops + per-extended-conjunct preservation × 5 ops; tighter
  `priorityInheritance_perCore_frame` once
  `blockingChain_objects_congr` lands in
  `Scheduler/PriorityInheritance/BlockingGraph.lean`.

  **WS-SM SM4.D LANDED at v0.31.30** (cross-subsystem per-core invariant
  migration; plan §5.4).  Following the exact SM4.C pattern, every
  cross-subsystem invariant that reads scheduler state is lifted from its
  single-core form (pinned to `bootCoreId` after SM4.B) to an **additive,
  soundness-preserving** per-core form parameterised by an explicit
  `(c : CoreId)` (plan §3.4 Pattern 1), plus the genuine `∀ c` system-wide
  SMP aggregate.  The live single-core invariant surface is untouched and
  stays green; the per-core layer is staged-only until SM5 consumes it.
  Five new staged modules (all axiom-clean — `propext` / `Quot.sound` /
  `Classical.choice` only):

  - **SM4.D.1/.2** `SeLe4n/Kernel/IPC/Invariant/PerCore.lean` (~550 LoC):
    the twelve IPC↔scheduler coherence predicates
    (`runnableThreadIpcReady`, the five `blockedOn…NotRunnable`,
    `currentThreadIpcReady`, `currentNotEndpointQueueHead`,
    `currentNotOnNotificationWaitList`, `passiveServerIdle`, plus the
    aggregates `ipcSchedulerContractPredicates` /
    `currentThreadDequeueCoherent`) lifted to `_perCore` forms with
    boot-core bridges (via `getTcb?_eq_some_iff` for the TCB predicates,
    `Iff.rfl` for the endpoint/notification ones), frame lemmas (each
    depends only on core `c`'s `runQueue` / `current` slot + `objects`),
    default-state witnesses, and the `∀ c` SMP aggregates (`_smp` +
    `_smp_at` + `_smp_to_singleCore` + defaults + per-conjunct
    projections).  The per-core bodies route TCB lookups through the typed
    `getTcb?` accessor (the SM4.C AK7 discipline — zero new `tid`-keyed raw
    lookups, `RAW_LOOKUP_TID` unchanged).  The `∀ c` form is the correct
    SMP semantics (e.g. a send-blocked thread is not runnable on *any*
    core's queue).
  - **SM4.D.3/.4** `SeLe4n/Kernel/Capability/Invariant/PerCore.lean`:
    `cleanupNoStaleSchedRef_perCore` (the scheduler conjunct of
    `cleanupHookDischarged`) + the full `cleanupHookDischarged_perCore` +
    bridge + frame + default + the SMP form `cleanupNoStaleSchedRef_smp`
    ("a retyped object's TCB must not be runnable on **any** core" — per
    the implement-the-improvement rule, the SMP-correct retype
    precondition, strictly stronger than the boot-core single-core check).
  - **SM4.D.9** `SeLe4n/Kernel/Architecture/InvariantPerCore.lean`:
    `registerDecodeConsistent_perCore` + bridge + frame + default + `∀ c`
    SMP aggregate (a sibling module, not an in-file extension, so it stays
    staged-only).
  - **SM4.D.12/.13/.14** `SeLe4n/Kernel/InformationFlow/ProjectionPerCore.lean`:
    the six scheduler-reading IF-M1 projections (`projectRunnable`,
    `projectCurrent`, `projectActiveDomain`, `projectDomainTimeRemaining`,
    `projectDomainScheduleIndex`, `projectMachineRegs`) + the aggregate
    `projectStateOnCore` lifted to `…OnCore` forms with boot-core bridges
    (`rfl`) and per-core observability frame lemmas (a write to core
    `c'`'s slot leaves core `c`'s projection unchanged — the SMP
    non-interference locality), plus `projectStateOnCore_congr`.
  - **SM4.D.19** `SeLe4n/Kernel/CrossSubsystemPerCore.lean` (capstone):
    `crossSubsystemInvariant_perCore` (per-core form of the master
    12-conjunct invariant; only its ninth conjunct
    `schedContextRunQueueConsistent` reads scheduler state, already
    migrated by SM4.C) and `crossSubsystemSchedulerContract_perCore` (the
    SM4.D bundle of *every* cross-subsystem scheduler-reading invariant in
    per-core form: IPC contract + dequeue coherence + passive-server
    idleness + architecture register-decode + SchedContext↔run-queue),
    with boot-core bridges, `∀ c` SMP forms, per-conjunct projections, and
    default-state witnesses.

  **N/A sub-tasks (documented, not weakened):** the operation files
  (SM4.D.1 IPC ops, SM4.D.5 Lifecycle ops, SM4.D.7 Service ops, SM4.D.18
  Platform/FFI, SM4.D.20 API) read `currentOnCore bootCoreId` as the
  *running* core — their core-parameterisation is genuinely SM5 (per-core
  scheduler) work, not invariant migration; SM4.B already routed their
  reads through the accessor.  Frozen state (SM4.D.16) stays scalar per
  the SM4.B phase-1 decision.  `Service` (SM4.D.7/.8),
  `Architecture/ExceptionModel` (SM4.D.10), `Architecture/InterruptDispatch`
  (SM4.D.11), `Architecture/VSpace` (SM4.D.21),
  `Architecture/SyscallEntry` (SM4.D.22), and the InformationFlow
  Invariant files (SM4.D.14) define **no** scheduler-reading predicate
  (confirmed by an exhaustive codebase scan) — only the IF projection
  frames (SM4.D.13) the NI proofs consume.

  **Test coverage:** new `tests/CrossSubsystemPerCoreSuite.lean`
  (`lake exe cross_subsystem_per_core_suite`) — 89 Tier-3 surface anchors,
  17 elaboration-time examples, and 18 runtime `assertBool` assertions
  across five sections (IPC, capability, architecture, information-flow
  with value-level decidable projection checks on the default state, and
  the cross-subsystem capstone).  Tier-2 + Tier-3 wired.  Production/
  staged partition gate now verifies **40** staged-only modules (was 35);
  SM5's per-core scheduler is the first runtime exerciser.  Default
  production build green (320 jobs); trace fixture byte-identical (SM4.D
  is purely additive).  Items deferred past v1.0.0 with correctness
  impact: NONE.  Follow-on: SM4.E (`bootFromPlatform_singleCore_witness`
  retirement + `bootFromPlatform_smp_witness` per plan §3.8).

  **WS-SM SM4.D audit-pass-1 LANDED at v0.31.31** (deep comprehensive
  audit; the v0.31.30 landing was sound + axiom-clean with no correctness
  defect — this closes one completeness gap, proves one documented
  intuition, and strengthens the suite per implement-the-improvement):
  - **Completeness gap (`lowEquivalent`)**: the initial direct-text scan
    missed `lowEquivalent` (in `Projection.lean`, SM4.D.13 scope), which
    reads scheduler state *transitively* via `projectState`.  Added
    `lowEquivalentOnCore` (per-core observable-state equivalence — the
    SM4.D.13 NI substrate SM6 consumes) + boot-core bridge + refl/symm/trans
    + `∀ c` `lowEquivalent_smp` + extractors, in `ProjectionPerCore.lean`.
    A re-scan for *all* indirect scheduler readers confirmed this was the
    only miss.
  - **`passiveServerIdle_smp` proved precise**: the `∀ c` per-core
    conjunction is *stronger* than the "not scheduled on any core ⟹
    passive" prose; added `passiveServerIdle_smp_not_scheduled_anywhere`
    proving that natural-SMP reading as a consequence, and corrected the
    docstrings.
  - **Capability SMP cleanup-hook**: added `cleanupHookDischarged_smp`
    (full SMP retype precondition) + `_smp_to_singleCore` +
    `_smp_to_noStaleSchedRef`, symmetric with `cleanupNoStaleSchedRef_smp`.
  - **Suite strengthened**: §3.6 value-level cross-core independence
    (write core 1's slot, `decide`-verify core 0's projection unchanged /
    core 1's updated — genuinely exercising the per-core `Vector` indexing
    through the projection layer); runtime assertions 18 → 24, surface
    anchors 89 → 102.
  - **Audit confirmations** (no change needed): zero compiler/linter
    warnings on a forced clean rebuild; no `set_option`/`sorry`/`admit`/
    `native_decide` in the SM4.D modules; AK7 `getTcb?`
    discipline holds (`RAW_LOOKUP_TID` baseline 810); endpoint/notification
    raw `objects[oid]?` correctly outside `RAW_MATCH` (equality, not
    `match`-style) and parallel to single-core.  All new theorems
    axiom-clean; suite 24/24 PASS; Tier 0–3 + Rust green; trace fixture
    byte-identical.

  **WS-SM SM4.D audit-pass-2 LANDED at v0.31.32** (closes the substantive
  "avoided work" the audit identified, completing SM4.D to SM4.C's bar):
  - **Per-operation cross-subsystem SMP-preservation** (the main gap): new
    staged module `SeLe4n/Kernel/CrossSubsystemPerCorePreservation.lean`
    (SM4.C-analogue) — `…_holds_if_idle` idle-discharge lemmas + generic
    `…_smp_of_singleCore_and_idle` lifters + the `passiveServerIdle_scheduledNowhere`
    natural-SMP form (the one predicate not vacuous-on-idle; its
    "scheduled-nowhere ⟹ passive" reading is implied directly by the
    single-core `passiveServerIdle`) + **11 concrete per-op preservation
    theorems** reusing the existing single-core preservation verbatim (8
    IPC ops → `ipcSchedulerContractPredicates_smp`; 2 architecture ops →
    `registerDecodeConsistent_smp`; `timerTick` → SchedContext↔run-queue),
    with the SM4.B `hNonBootIdle` structural hypothesis.
  - **Full typed-accessor discipline**: `currentNotEndpointQueueHead_perCore`
    / `currentNotOnNotificationWaitList_perCore` migrated to `getEndpoint?`
    / `getNotification?` (GETENDPOINT 33→42, GETNOTIFICATION 19→27;
    RAW_LOOKUP_TID still 810).
  - **`cleanupHookDischarged_smp` wired into a consumer**: `RetypeTargetSmp`
    + `mkRetypeTargetSmp` + `toRetypeTarget` (SMP retype precondition).
  - **Plan-document closure**: `SMP_PER_CORE_STATE_PLAN.md` §5.4 carries the
    per-sub-task disposition for all 22; §8 acceptance box checked.
  - **Tests**: §3.7 (preservation lifters) + §3.8 (non-vacuous
    populated-state projections — a real thread in core 0's queue/current,
    `decide`-verified present on core 0, absent on core 1).  Runtime
    assertions 24→32; anchors 102→121.
  - **Inventory-aggregator (item #8)**: intentionally not a separate macro
    module — the Tier-3 anchors + suite `#check`s already provide
    comprehensive rename-protection (SM4.C's pattern); a parallel inventory
    would duplicate it.  Partition gate 41 staged-only modules; axiom-clean;
    suite 32/32 PASS; Tier 0–3 + Rust green; trace fixture byte-identical.

  **WS-SM SM4.D audit-pass-3 LANDED at v0.31.33** (third deep audit; no
  correctness defect — closes one completeness gap + two doc-code mismatches):
  - **Last missed scheduler-reader (within / adjacent to SM4.D's
    subsystems)**: an exhaustive whole-tree re-scan (handling line-end
    `.runnable` + indirect readers) found one further scheduler-reading
    def adjacent to SM4.D's six subsystems with no per-core form:
    `registerContextStableCheck` (`Platform/RPi5/RuntimeContract.lean`, a
    `Bool` runtime contract reading `currentOnCore` + `.runnable`).
    Platform-layer (adjacent to SM4.D's six subsystems), so it fell outside
    §5.4's file list.  Migrated to `registerContextStableCheckOnCore` (+
    `registerContextStablePredOnCore`) in the new staged module
    `Platform/RPi5/RuntimeContractPerCore.lean` (boot-core bridge + idle /
    default witnesses); `budgetSufficientCheck` widened `private`→public
    (pure proof-side `Bool`, no runtime/TCB impact).  Now every
    `SchedulerState`-reading definition **within SM4.D's six subsystems
    plus the adjacent Platform/RPi5 runtime contract** has a per-core
    form or an explicit disposition.  (The Scheduler-subsystem
    `Liveness/*.lean` predicates also read scheduler state but are
    **SM4.C.11** scope, not SM4.D — flagged accurately by audit-pass-4
    below; audit-pass-3's "every def in the tree" phrasing was an
    overclaim.)  Partition gate: 42 staged-only modules.
  - **Doc-code fix #1**: audit-pass-1's "no `@[simp]` in the SM4.D modules"
    was stale — audit-pass-2 added two `@[simp]` `RetypeTargetSmp`
    id-projection lemmas (correct, mirroring single-core `mkRetypeTarget_id`);
    corrected the absent-constructs list.
  - **Doc-code fix #2**: the audit-pass-2 "132" suite-anchor count was
    actually 121; corrected.  Final suite: 127 `#check` anchors, 19
    examples, 34 runtime assertions (34/34 PASS).
  - Comprehensive `#print axioms` sweep over all SM4.D-module theorems:
    zero `sorryAx`/`native`/`unsafe`; zero warnings on clean rebuild; AK7
    all pass; Tier 0–3 + Rust green; trace fixture byte-identical.

  **WS-SM SM4.D audit-pass-4 LANDED at v0.31.34** (fourth deep audit; no
  code-soundness defect — the SM4.D per-core cross-subsystem surface is
  complete, faithful, and axiom-clean.  Closes one documentation
  completeness *overclaim* introduced by audit-pass-3, per the
  implement-the-improvement rule's honesty corollary: a forced deferral
  must be recorded as tracked debt with an explicit closure target, never
  absorbed into a falsely-strong public claim):
  - **Scope correction (the finding)**: audit-pass-3 asserted the
    whole-tree re-scan left "**every** `SchedulerState`-reading def in the
    tree" with a per-core form or disposition.  A re-enumeration of *every*
    `def`/`abbrev`/`structure` reading a scheduler accessor
    (`currentOnCore` / `runQueueOnCore` / `replenishQueueOnCore` /
    `activeDomainOnCore` / `domainTimeRemainingOnCore` / `.runnable`,
    direct or transitive) confirms SM4.D's six subsystems + the Platform/
    RPi5 runtime contract are fully covered — BUT the Scheduler-subsystem
    **Liveness** predicates (`SeLe4n/Kernel/Scheduler/Liveness/*.lean`:
    `eventuallyExits`, `higherBandExhausted`, `rpi5CanonicalConfig`,
    `CanonicalDeploymentProgress`, `stepPrecondition`, `stepPost`,
    `selectedAt`, `runnableAt`, `budgetAvailableAt`,
    `countHigherOrEqualEffectivePriority`, `maxBudgetInBand`,
    `maxPeriodInBand`, `bucketPosition`, `WCRTHypotheses`, `wcrtBound` —
    ~15 decls across `BandExhaustion`/`RPi5CanonicalConfig`/`TraceModel`/
    `WCRT`) read scheduler state pinned to `bootCoreId` and have **no**
    per-core form.  These are explicitly **SM4.C.11** scope
    (`Scheduler/Liveness/*.lean (incl. WCRT)` — plan §5.3 table), the
    Scheduler-subsystem migration, NOT the SM4.D cross-subsystem boundary
    (§5.4).  Migrating them inside the SM4.D cut would misattribute SM4.C
    work and break the one-coherent-slice rule.
  - **Tracked debt (explicit closure target = SM4.C.11)**: per-core
    Liveness forms remain open.  SMP liveness genuinely needs `∀ c`
    reasoning (a runnable thread may be selected on any core), so the
    bootCoreId-pinned predicates are correct *single-core* surface but
    incomplete for SMP.  Recorded as tracked debt against **SM4.C.11**
    (plan §5.3) — out of the SM4.D one-coherent-slice scope; not an SM4.D
    correctness gap.  The SM4.D modules are unchanged: no code edit, the
    per-core cross-subsystem surface is complete and axiom-clean.
  - **Re-verification (no new logic error — findings have converged)**:
    machine-checked semantic faithfulness (every per-core def body reads
    `c`, never a stray `bootCoreId`; the compiling `Iff.rfl` / `simp`
    boot-core bridges *prove* defeq/equivalence to the single-core forms;
    `getEndpoint?_eq_some_iff` / `getNotification?_eq_some_iff` are
    bidirectional, so the typed-accessor migration is semantically
    equivalent with zero security impact); zero warnings on a clean
    rebuild; the `budgetSufficientCheck` `private`→public widening broke no
    encapsulation test; `#print axioms` clean; suite 34/34; full
    `test_full.sh` green; trace fixture byte-identical.  Audit convergence:
    ap1 = `lowEquivalent`; ap2 = preservation layer; ap3 = one Platform
    `Bool` check + two doc typos; ap4 = one documentation overclaim
    (this), no code defect.

  **WS-SM SM4.E LANDED at v0.31.35 on branch
  `claude/gallant-darwin-zWsYi`** (single-core witness retirement + per-core
  SMP boot witness + retirement ledger; closes plan §5.5, all 5 sub-tasks,
  and the SMP-H2 finding — retired, per-core fields replace the singular
  ones).  Purely additive at the proof surface: **trace fixture
  byte-identical (227/227)**, zero new axioms (the new theorems depend only
  on `propext` / `Classical.choice` / `Quot.sound`).

  - **SM4.E.1**: `bootFromPlatform_singleCore_witness` **deleted** from
    `SeLe4n/Kernel/CrossSubsystem.lean`.  After SM4.B flipped
    `SchedulerState.current` to `Vector (Option ThreadId) numCores`, the
    boot-core-only witness was structurally too weak to characterise the
    per-core SMP shape.  A discoverability retirement note remains at the
    CX-M03 site pointing at the boot-side replacement (the replacement
    references `bootFromPlatform`, and
    `Platform.Boot → Kernel.API → Architecture.Invariant → CrossSubsystem`,
    so siting it in `CrossSubsystem` would cycle — same reason as the
    CX-M04 bundle note).
  - **SM4.E.2**: `bootFromPlatform_smp_witness` added to
    `SeLe4n/Platform/Boot.lean` (plan §3.8) — `∀ c : CoreId`, the booted
    scheduler's `currentOnCore c` is `none ∨ ∃ tid, = some tid`.  The
    `∀ c : CoreId` quantification is the genuine improvement over the
    boot-core-only form.  Forward-compatible: the `some tid` disjunct will be
    witnessed by `idleThreadId c` once SM4.G installs per-core idle threads,
    so it needs no second retirement (the §3.8 `some (idleThreadId c)` is
    adapted to `∃ tid, = some tid` since `idleThreadId` does not exist until
    SM4.G).  Substantive companion `bootFromPlatform_smp_currentAllNone`
    proves `currentOnCore c = none` on **every** core at boot (via
    `bootFromPlatform_scheduler_eq` + the SM4.B.9
    `default_state_perCoreInitialized`) — the non-vacuous content behind the
    disjunctive witness.
  - **SM4.E.3 / SM4.E.4**: AN12-B `smpLatentInventory` entries 7 + 8
    `smpDischarge` → "implemented in SM4 path-a"; `sourceTheorem`s repointed
    to `bootFromPlatform_smp_witness` (entry 7) and
    `bootFromPlatform_smp_currentAllNone` (entry 8 — kept distinct so
    `smpLatentInventory_sourceTheorems_nodup` still holds).  The
    `Architecture.ArchAssumption.singleCoreOperation` consumer mapping is
    repointed to `bootFromPlatform_smp_witness` (a `Lean.Name` literal, no
    import needed).
  - **SM4.E.5**: `smpRetiredInventory` retirement ledger added to
    `SeLe4n/Kernel/Concurrency/Assumptions.lean` — an 8-entry
    `SmpRetiredAssumption` list mirroring `smpLatentInventory` one-to-one by
    `identifier` (`smpRetiredInventory_covers_latent`), with a
    `SmpRetirementStatus` enum (`.pathARetired` / `.perCoreBracketGated`).
    Witnesses: `_count = 8` (size pin), `_identifiers_nodup`,
    `_retiredBy_nodup`, `_covers_latent`, and — per the honesty corollary —
    the disposition counts `_pathARetired_count = 2` /
    `_perCoreBracketGated_count = 6` (only the scheduler-state shape +
    boot-core current are genuinely path-a-retired; the other six are
    `perCoreBracketGated`, single-core property preserved per-core by the FFI
    bracket, full retirement gated on SM5+).  "All retired" is the ledger's
    *purpose* (tracking all 8 toward retirement); SM9 (release closure) flips
    the gated entries and proves `smpRetiredInventory_complete`.

  **Build-anchor + surface coverage**: `Concurrency.Anchors` (SMP-H3 gate)
  repoints the two inventory `@`-references and adds seven for the ledger;
  `tests/SmpFoundationsSuite.lean` + `tests/ModelIntegritySuite.lean` migrate
  their CX-M03 / consumer-mapping checks and add ledger checks (both suites
  green, 0 fails); `scripts/test_tier3_invariant_surface.sh` adds eight
  surface anchors.  Items deferred past v1.0.0 with correctness impact: NONE.
  Follow-on: SM4.C remaining sub-tasks (incl. the SM4.C.11 Liveness tracked
  debt) + SM4.G (per-core idle-thread bootstrap) + SM5 (per-core scheduler).

  **WS-SM SM4.G LANDED at v0.31.36 on branch
  `claude/gallant-darwin-zWsYi`** (per-core idle-thread bootstrap; follow-on
  to SM4.E per maintainer directive).  Upgrades the named SMP boot witness
  from a tautology to a substantive claim and closes the three SM4.E
  audit-gaps.  All in `SeLe4n/Platform/Boot.lean`; every new theorem
  axiom-clean; trace byte-identical (227/227 — `bootFromPlatform` is left
  unchanged; the trace harness never calls it anyway).

  - **Substantive witness**: `bootFromPlatform_smp_witness` is now
    `currentOnCore c = none ∨ currentOnCore c = some (idleThreadId c)` (was
    `∨ ∃ tid, = some tid`, a tautology over `Option`).  Naming the per-core
    idle thread *excludes* `current = some <non-idle>` — the plan §4.3 form,
    genuinely non-vacuous, still forward-compatible (proved via the `none`
    branch on `bootFromPlatform`).
  - **Idle machinery (§3.7)**: `idleThreadId` (reserved range
    `idleThreadIdBase = 0x1_0000`, `idleThreadId_injective`),
    `createIdleThread` (priority 0, domain 0, `.Running`, sentinel
    CSpace/VSpace — idle runs in kernel context, core bound by the
    `tid = idleThreadId c` identity since `TCB` has no `cpuAffinity`),
    `installIdleThread` (builder `createObject` + `setCurrentOnCore`, the
    `IntermediateState` invariants forwarded by defeq — the
    `applyMachineConfig` pattern), and `bootFromPlatformWithIdleThreads` (a
    wrapper over `bootFromPlatform`, like `bootFromPlatformWithInterrupts`, so
    the base boot path's entire verified invariant surface is untouched).
  - **Theorem 3.7.1**: `bootFromPlatformWithIdleThreads_all_cores_have_idle`
    (`∀ c`, current = `some (idleThreadId c)` + the idle TCB is present in the
    object store) — proved via a `Nodup` fold-install lemma + two frame
    lemmas (each install targets a distinct core); holds unconditionally.
  - **Soundness**: `bootFromPlatformWithIdleThreads_schedulerInvariantBundle`
    (the installed state is scheduler-valid — idle is a valid current TCB,
    dequeued, run queue duplicate-free) + `…_valid` (the four structural boot
    invariants, preserved because idle TCBs go through the same builder as
    platform objects).  No dangling current ref, no double-scheduling.
  - **SM4.E audit-gap closures** (per the implement-the-improvement rule):
    `SmpRetiredAssumption.retiredBy` renamed **`anchor`** (it overstated for
    the 6 `.perCoreBracketGated` entries, which point to their *current*
    per-core anchor, not a retirement witness; `…_retiredBy_nodup` →
    `…_anchor_nodup`); the `ModelIntegritySuite` boot test now exercises
    `foldObjects` (non-empty `initialObjects`) and runs the install fold;
    `SMP_FOUNDATIONS_PLAN.md` SM0 sketches get a post-retirement note.

  Surface: 7 `SmpFoundationsSuite` `#check` anchors + 4 tier-3 anchors +
  `model_integrity_suite` SM4.G runtime checks (idle current, per-core idle
  TCB present, empty run queue, distinct idle ids — all green).  Items
  deferred past v1.0.0 with correctness impact: NONE.  Follow-on: SM4.C.11
  Liveness tracked debt + SM5 (per-core scheduler).

  **WS-SM SM4.G audit-pass-1 LANDED at v0.31.37 on branch
  `claude/gallant-darwin-zWsYi`** (deeper-audit pass; the v0.31.36 landing was
  sound + axiom-clean — closes two optimality/honesty gaps per the
  implement-the-improvement rule, both in `SeLe4n/Platform/Boot.lean`; every
  new theorem axiom-clean; trace byte-identical 227/227; default build green
  320 jobs):
  - **Under-claim closed (base triad → FULL 9-conjunct bundle)**:
    `bootFromPlatformWithIdleThreads_schedulerInvariantBundleFull` proves the
    idle-thread state satisfies all 9 conjuncts (SM4.G proved only the base 3).
    Unlike the plain `bootFromPlatform` Full bundle (current-thread conjuncts
    vacuous via `current = none`), the idle path discharges
    `currentTimeSlicePositive` (idle `timeSlice = 5 > 0`) and
    `contextMatchesCurrent` (boot regs = idle `registerContext` = default
    `RegisterFile`, via `bootFromPlatform_machine_non_config_fields`)
    **substantively** against the live idle TCB.  Bonus
    `…_currentThreadInActiveDomain` (the idle thread resides in the boot active
    domain — the *extended* bundle's conjunct, again substantive where plain
    boot is vacuous).
  - **Phantom `idleSlotsFreshAt` implemented**: the `idleThreadIdBase`
    docstring referenced a nonexistent freshness hypothesis "that the canonical
    platforms discharge".  Per implement-the-improvement the symbol is now
    built, closing the latent silent-overwrite concern (`ObjId` wraps an
    unbounded `Nat`, so the 16-bit disjointness was convention not structure,
    and `createObject`'s `RHTable.insert` overwrites on collision):
    `idleSlotsFreshAt` predicate;
    `foldl_installIdleThread_objects_frame_of_not_idle` (general object frame);
    `bootFromPlatformWithIdleThreads_preserves_platform_objects` (under
    freshness the install is purely **additive** — no platform object
    clobbered); `idleSlotsFreshAt_of_initialObjects_below_base` (discharges
    freshness for any below-base config — the canonical RPi5/Sim case), making
    the disjointness a *proven* property.  The `idleThreadIdBase` docstring is
    rewritten to cite the real symbols.
  Surface: +5 tier-3 anchors + 5 `SmpFoundationsSuite` `#check`s (full bundle,
  active-domain, freshness predicate + preservation + discharge); 2 top-level
  elaboration `example`s + 3 substantive runtime checks in
  `model_integrity_suite` (idle `timeSlice > 0`, idle in active domain,
  below-base platform object survives the install + idle threads additively
  present).  Items deferred past v1.0.0 with correctness impact: NONE.

  **WS-SM SM5.A LANDED at v0.31.38 on branch
  `claude/sharp-mayer-tAap4`** (per-core `chooseThread`; opens SM5, the
  per-core scheduler phase).  All eight sub-tasks landed in one cut per
  [`docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md`](docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md)
  §3.1 / §5.  Every new theorem is axiom-clean (`propext` / `Quot.sound`
  only); the legacy single-core `chooseThread` migrates to delegate to the
  per-core form with **zero behavioural change** (default build green, 320
  jobs; trace fixture byte-identical).

  - **SM5.A.1 + SM5.A.5** (production, `Scheduler/Operations/Selection.lean`):
    `chooseThreadOnCore (st) (c : CoreId) : Except KernelError (Option
    ThreadId)` — the per-core analogue of `chooseThread`, selecting the
    highest-priority runnable thread in core `c`'s active domain by reading
    **only** core `c`'s run-queue + active-domain slots.  Plan §3.1's bare
    `Option ThreadId` is adapted to `Except KernelError (Option ThreadId)` so
    the underlying `chooseBestInBucket`'s `schedulerInvariantViolation`
    (corrupted run queue) is preserved, not silently collapsed to `none` (a
    richer, strictly-safer contract; `chooseThreadOnCore_ok_of_runnableTCBs`
    proves the error branch unreachable on valid states).  The legacy
    `chooseThread` is now *defined* as `chooseThreadOnCore` at `bootCoreId`
    lifted into the `Kernel` monad (`chooseThread_eq_chooseThreadOnCore_bootCore`,
    `rfl`); the five production proof sites that `unfold chooseThread` updated
    to also unfold `chooseThreadOnCore`.
  - **SM5.A.2** (staged, `Scheduler/Operations/PerCoreChooseThread.lean`):
    `RunQueueLockId` (a `CoreId`-keyed per-core run-queue lock — distinct from
    the SM0.I object-lock `LockId` hierarchy, since run queues are
    `SchedulerState` fields not kernel objects, so the 10-level `LockKind`
    pinning is untouched) + `chooseThreadOnCoreLockSet c = [(⟨c⟩, .read)]`
    reusing SM3.B's `AccessMode`, with four structural witnesses (singleton,
    read-only, guards-core-`c`, keys-`Nodup`).
  - **SM5.A.3**: per-core independence (Theorem 3.1.2).
    `chooseThreadOnCore_frame` (the selection on core `c` depends only on
    `(objects, runQueueOnCore c, activeDomainOnCore c)`) + four corollaries —
    independence under sibling-core run-queue / active-domain writes, under
    **any** core's `current` write (the selection never reads `current`), and
    the lock-set bridge `_independent_of_write_off_lockSet` tying the SM5.A.2
    lock-set to the actual read footprint.
  - **SM5.A.4**: idle-fallback completeness.  Three induction lemmas on
    `chooseBestRunnableBy` (`_some_ne_ok_none`, `_none_no_eligible`,
    `_ok_of_allTcb`) lift through `chooseBestInBucket` to:
    `chooseThreadOnCore_ok_of_runnableTCBs` (never errors on a well-formed
    all-TCB run queue — total on valid states),
    `chooseThreadOnCore_none_no_eligible` (returns `.ok none` only when no
    in-domain runnable thread exists — the idle fallback drops nothing), and
    `chooseThreadOnCore_some_of_eligible` (an in-domain runnable thread
    guarantees a `some` selection — the conditional SM5.E discharges with the
    per-core idle thread for the unconditional
    `chooseThreadOnCore_always_succeeds`).  Plus the
    `schedulerInvariant_perCore` corollary
    `chooseThreadOnCore_ok_of_schedulerInvariant`.
  - **SM5.A.6**: selection soundness.
    `chooseThreadOnCore_some_mem_runQueueOnCore` (a chosen thread is a genuine
    run-queue member — the substantive "respects well-formedness" content for
    a read-only selector) + the literal preservation form
    `chooseThread_preserves_runQueueOnCore_wellFormed` (`chooseThread` is a
    pure read) + the `schedulerInvariant_perCore` corollary.
  - **SM5.A.7**: `chooseThreadOnCoreSelects` / `chooseThreadOnCoreIdleFallback`
    decidable predicates (Lean core does not derive `DecidableEq (Except _ _)`,
    so decidability is by structural case analysis on the evaluated result) —
    what lets the unit tests `decide` concrete selection scenarios.
  - **SM5.A.8** (`tests/SmpSchedulerSelectionSuite.lean`): 22 surface anchors,
    8 elaboration-time theorem-application examples, 16 runtime assertions at
    landing (raised to 23 / 9 / 19 by audit-pass-1) across the six selection
    scenarios (empty ⇒ idle fallback; single in-domain selected;
    highest-priority wins; out-of-domain skipped; per-core independence;
    selection soundness) + the SM5.A.2 lock-set witnesses.
    Tier-2 + Tier-3 wired.

  **Production support**: `RunQueue.ofList_wellFormed` added to
  `Scheduler/RunQueue.lean` (`ofList` folds `insert` over `empty`, both
  well-formedness-preserving) to discharge `RunQueue.wellFormed` on concrete
  fixtures.  **Module reachability**: `Scheduler.Operations.PerCoreChooseThread`
  staged via `Platform.Staged` (`staged_module_allowlist.txt`, 43 staged-only
  modules); `chooseThreadOnCore` itself is production-reached (legacy
  `chooseThread` delegates to it).  SM5.B's per-core `switchToThread` is the
  first runtime exerciser of the SM5.A theorems.  Items deferred past v1.0.0
  with correctness impact: NONE.

  **Audit-pass-1 refinements** (post-initial-landing deep audit; ship inside
  v0.31.38 — the initial landing was sound + axiom-clean): added
  `chooseThreadOnCore_perCore_independence` (the plan §3.1.2 named per-core-
  independence statement, restating the run-queue-write corollary with the
  plan's `c₁ ≠ c₂` naming for traceability); corrected the
  `chooseThreadOnCoreSelects` docstring (it claimed decidability "flows from
  `DecidableEq (Except _ _)`" — a non-existent instance, which is why the
  `Decidable` instance uses manual case analysis); and added a 7th runtime
  test scenario exercising genuine per-core selection on a **non-boot** core
  (`c ≠ bootCoreId`) — the first runtime witness of the `(c : CoreId)`
  parameter beyond the boot core.  Suite: 23 anchors / 9 examples / 19 runtime
  assertions (counts verified against the source).  Axiom-clean; Tier 0–3 green.

  **WS-SM SM5.A completion + cross-domain unification (in the single
  v0.31.38 cut) on branch `claude/sharp-mayer-tAap4`** (closes the gaps from
  the SM5.A deep self-audit *and* the post-audit PR #804 cross-domain
  lock-set finding, bringing the per-core chooseThread phase to a complete +
  optimal implementation).  Axiom-clean; default build green (320 jobs);
  Tier 0–3 green.

  - **Selection optimality (`chooseThreadOnCore_selects_highest`, plan §3.1.1)**
    — the headline correctness property that the audit found missing: the
    selected thread is not `isBetterCandidate`-beaten by any active-domain
    thread in the run queue's **maximum-priority bucket**.  This is the
    *honest, correct* optimality — `chooseBestInBucket` buckets by *effective*
    priority (`max(base, pipBoost)`) and picks the best within the top bucket by
    *base* priority + EDF, so a global "highest base priority over the whole
    queue" claim is **false** (a lower-effective-bucket thread can have a higher
    base priority) and is deliberately not made.  Lifts the de-privatized
    single-core `chooseBestRunnableBy_optimal` / `_result_fields`.
  - **Budget-aware per-core selector `chooseThreadEffectiveOnCore`** (production
    def + legacy `chooseThreadEffective` migration in `Selection.lean`) — the
    CBS-budget-aware companion that rejects exhausted-budget threads.  Full
    mirrored suite: objects-congruence + frame + independence, non-erroring,
    completeness, soundness, and the unique-to-the-variant
    `chooseThreadEffectiveOnCore_selected_has_budget` (a dispatched thread
    genuinely has budget).
  - **`RunQueueLockId` total order (SM5.A.2)** — `le`/`lt` keyed by `CoreId`
    with `le_refl`/`_trans`/`_antisymm`/`_total`/`lt_irrefl`/`lt_asymm` +
    `Decidable` + `runQueueLockLevel = 10` +
    `objectLockLevels_lt_runQueueLockLevel` (plan §4.4).
  - **Cross-domain lock-set unification (post-audit, closing PR #804's P1
    under-locking finding)** — `chooseThreadOnCore` resolves every queued
    thread through `st.objects.get?`, so the run-queue-only footprint
    under-locked: a concurrent retype / delete / write of a queued TCB could
    change the selection (or force `schedulerInvariantViolation`) while only
    the run-queue lock was held.  Fixed by the unified `SchedLockId`
    (object-lock `LockId` ⊕ run-queue `RunQueueLockId`) with the plan §4.4
    total order (`le_total` / `le_antisymm` / … + `object_lt_runQueue`: every
    object lock before every run-queue lock — kept a *constructor* of
    `SchedLockId`, not an eleventh `LockKind`, preserving the pinned 10-level
    SM0.I hierarchy), and `chooseThreadOnCoreLockSet` now declaring the
    **complete two-domain** footprint
    `[(object schedObjStoreLockId, .read), (runQueue ⟨c⟩, .read)]` — the
    object-store read lock (`schedObjStoreLockId`, the SM3.A.10 table-level
    lock) guards the `st.objects` reads.  Runtime `withLockSet` acquisition
    wiring over `SchedLockId` is SM5.B.
  - **Budget selector footprint symmetry**: `chooseThreadEffectiveOnCoreLockSet`
    = `chooseThreadOnCoreLockSet` — the production-reached budget-aware selector
    reads the object store too (TCB resolutions + `hasSufficientBudget`
    SchedContext reads), both guarded by the single table read lock, so it
    carries the same complete footprint.
  - **`chooseThreadOnCore_preserves_wellFormed`** — the literal SM5.A.6
    plan-named anchor; 12 selection bridge lemmas de-privatized for SM5.B/E.
  - **Tests** grow to 54 anchors / 17 examples / 35 runtime assertions, incl.
    the **error path** (corrupt run queue ⇒ `.error`, the security path), **EDF**
    tie-break, the **budget guarantee** contrast (non-budget selects an
    exhausted-budget thread; budget-aware rejects it), and the **cross-domain
    footprint** witnesses (object-store + run-queue read locks; the §4.4
    object-before-run-queue acquisition order).  Items deferred past
    v1.0.0 with correctness impact: NONE.

  **WS-SM SM5.B LANDED at v0.31.39 on branch
  `claude/lucid-allen-6c48D`** (per-core `switchToThread` — the per-core
  context-switch transition; plan §3.2 / §5).  All nine sub-tasks landed in one
  cut; every new theorem axiom-clean (`propext` / `Quot.sound` /
  `Classical.choice` only); default build green (320 jobs); trace fixture
  byte-identical; Tier 0–3 green; full Rust HAL suite green (718) with zero
  clippy warnings.

  - **Foundation (SM5.B.4)**: `TCB.cpuAffinity : Option CoreId := none`
    (`none` = unbound, runs on any core; `some c` = pinned to core `c`) is
    pulled forward from the plan's nominal SM5.C.7 slot because reject-remote
    cannot be a non-vacuous theorem without a per-thread core binding (a stub
    would be a security/correctness shortcut, forbidden by the
    implement-the-improvement rule).  Default `none` keeps the single-core
    trace byte-identical; `BEq TCB` grows 23 → 24 conjuncts, `TCB.ext` gains the
    `cpuAffinity` hypothesis; TCBs pass `freezeObject` unchanged (no freeze
    cascade).  `KernelError.threadOnDifferentCore` (discriminant 53) added
    across the Lean enum + `KernelError.toUInt32` + the Rust `sele4n-types`
    enum (`from_u32` / `Display`) + the `sele4n-abi` decode layer + every
    discriminant-pinning test (54 variants, kernel range 0..=53, unknown-code
    fallback from 54).
  - **SM5.B.1/.3/.4** (production `Scheduler/Operations/Selection.lean`):
    `switchToThreadOnCore (st) (c) (tid) : Except KernelError SystemState` —
    preempt core `c`'s current thread (`preemptCurrentOnCore`: save its
    register context + re-enqueue at effective priority), dequeue `tid`
    (dequeue-on-dispatch), restore `tid`'s context, set current = `tid`.
    Fail-closed: non-TCB `tid` → `.schedulerInvariantViolation`; wrong-core
    affinity → `.threadOnDifferentCore` (the `affinityAdmitsCore` gate).
  - **SM5.B.2/.5/.6/.8** (staged
    `Scheduler/Operations/PerCoreSwitchToThread.lean`):
    `switchToThreadOnCoreLockSet` — the *complete* cross-domain footprint over
    SM5.A's `SchedLockId` (object-store **write** lock guarding the `getTcb?`
    resolutions + the preempted-thread register save, plus the per-core
    run-queue **write** lock; plan §4.4 object-before-run-queue order; the
    table lock subsumes the dynamic preempted-TCB write a static
    `LockId.tcb tid`-only set would under-lock — the class SM5.A's audit
    closed).  Switch-semantics theorems `_sets_current` (Thm 3.2.1),
    `_preempts_previous` (Thm 3.2.2), `_rejects_remote` / `_ok_of_admits`
    (Thm 3.2.3), `_runQueueOnCore_excludes_current` (SM5.B.5),
    `_independent_of_other_core` (SM5.B.6, via the `preemptCurrentOnCore`
    frame lemmas); totality + the decidable `switchToThreadOnCoreSucceeds` /
    `switchToThreadOnCoreRejectsRemote` (SM5.B.8).
  - **SM5.B.7** FFI seam: Rust `ffi_switch_to_thread` /
    `ffi_per_core_current_thread` (per-core `PER_CPU_CURRENT_THREAD` slot,
    fail-closed u64-before-cast bound check) + Lean `@[extern]`
    (`Platform.FFI.ffiSwitchToThread` / `ffiPerCoreCurrentThread`) + typed
    `Concurrency.switchToThreadHw` / `perCoreCurrentThreadHw` wrappers + marker
    theorems; new `build.rs` scanner `scan_ffi_rs_exposes_switch_to_thread_exports`
    pins both exports.  No Lean caller at SM5.B; SM5.C's per-core dispatch loop
    is the consumer.
  - **Tests**: `tests/SmpSwitchToThreadSuite.lean`
    (`lake exe smp_switch_to_thread_suite`) — 35 surface anchors, 9
    elaboration-time theorem-application examples, 25 runtime assertions over
    the real `switchToThreadOnCore` computation (the eight SM5.B.9 scenarios +
    the SM5.B.2 lock-set + the SM5.B.4 affinity algebra); 6 new Rust
    `ffi::tests::sm5b7_*` (HAL 712 → 718).  `PerCoreSwitchToThread` registered
    in `Platform/Staged.lean` + `staged_module_allowlist.txt` (44 staged-only
    modules; partition gate green).  Items deferred past v1.0.0 with
    correctness impact: NONE.  Follow-on: SM5.C (cross-core wake via SGI)
    consumes `switchToThreadOnCore` + `switchToThreadOnCoreLockSet`.

  **WS-SM SM5.B audit-pass-1 (also in v0.31.39)**: a deep self-audit closed the
  verification-completeness + documentation gaps of the SM5.B landing (sound +
  axiom-clean, but a state *mutation* had shipped with no preservation theorems
  plus a few dead-weight / under-documented spots).  All axiom-clean (full
  `#print axioms` sweep over *every* SM5.B theorem, not the initial 6):

  - **Invariant preservation** (the main gap): `switchToThreadOnCore_preserves_objects_invExt`
    (object-store `invExt`), `_preserves_runQueueOnCore_wellFormed` (run-queue
    `RunQueue.wellFormed`), `_establishes_queueCurrentConsistentOnCore` (the SM4.C
    invariant form of dequeue-on-dispatch), the object-footprint bridge
    `switchToThreadOnCore_objects_eq_preempt` (the switch writes only what the
    preempt does — at most the preempted thread's TCB), + preempt-side helpers
    `preemptCurrentOnCore_preserves_objects_invExt` / `_preserves_runQueueOnCore_wellFormed`.
    The full 10-conjunct `schedulerInvariant_perCore` preservation remains SM5.I.8
    ("preservation by every transition") per the plan; these are its foundations.
    The per-conjunct `currentThreadValidOnCore` establishment was initially
    left to SM5.I.8 here, then **closed in audit-pass-2 below** (the cited AK7
    blocker proved avoidable via a typed `.get?`-method-form frame).
  - **Defense-in-depth**: `preemptCurrentOnCore_active_under_valid` proves the
    "previous current isn't a TCB" no-op fallback is **unreachable** under
    `currentThreadValidOnCore` (mirrors `saveOutgoingContext_always_succeeds_under_currentThreadValid`).
  - **Dead-weight removed**: the vacuous `switchToThreadOnCore_total` (`∃ r, … = r`)
    is replaced by the substantive `switchToThreadOnCore_ok_iff` (succeeds **iff**
    `tid` is a TCB whose affinity admits the core).
  - **Acquisition-order completeness**: `switchToThreadOnCoreLockSet_pairwise_le`
    (the lock-set's keys are `SchedLockId`-ascending — a valid `withLockSet`
    acquisition sequence; the switch's part of the SM3.D deadlock-freedom ladder).
  - **Honest lock-set rationale (documented, not changed)**: the object-store
    **table** write lock is the *sound* SM3.A.10 choice (RobinHood structural
    safety is table-granularity — an insert can relocate slots — so per-object TCB
    locks would be unsound); the cross-core-switch serialization is recorded as a
    tracked post-SM5 optimization (per-slot RHTable concurrency), not presented as
    strictly superior.  `switchToThreadOnCore`'s docstring now documents its
    deliberate preempt-vs-drop distinction from `schedule` (no `rfl`-bridge) and
    the single-`machine.regs` per-core register-model assumption (per-core banks
    land with SM5, as `contextMatchesCurrentOnCore` notes); the FFI
    `PER_CPU_CURRENT_THREAD` docstring explains the cross-core-readable `AtomicU64`
    array vs the non-atomic owner-only `PerCpuData`.
  - **Tests**: the suite gains a self-switch scenario (the `prevTid == incoming`
    preempt no-op branch) + elaboration-time witnesses for every new theorem;
    tier-3 anchors updated.  Items deferred past v1.0.0 with correctness impact:
    NONE.

  **WS-SM SM5.B audit-pass-2 (also in v0.31.39)**: closes the one substantive
  deferral audit-pass-1 left open, per the implement-the-improvement rule (the
  deferral's stated AK7 blocker was avoidable, so the symmetric sibling theorem
  is materialised rather than postponed to SM5.I.8):
  - **`switchToThreadOnCore_establishes_currentThreadValidOnCore`** — the
    symmetric sibling of `_establishes_queueCurrentConsistentOnCore`: a
    successful switch establishes that core `c`'s new current thread resolves to
    a TCB.  Audit-pass-1 deferred it citing the AK7 `RAW_LOOKUP_TID` gate, but
    the metric counts only the raw `[·]?` bracket text while
    `RHTable.getElem?_insert_ne` is stated in the `.get?`-method form.  The new
    typed-accessor frame `preemptCurrentOnCore_getTcb?_incoming` (the preempt's
    only object write is the *previous* current's save at a *different* key, so
    the lookup at the switch target is unchanged) closes the proof with **zero**
    raw-bracket source — `RAW_LOOKUP_TID` stays at the 810 floor
    (`GETTCB_ADOPTION` 284 → 303).
  - **Documentation drift fixed**: the module docstring still listed the
    renamed-away `switchToThreadOnCore_total`; corrected to
    `switchToThreadOnCore_ok_iff` + both establishment theorems.
  - **Tests**: +2 surface anchors + 1 example + 2 runtime scenarios
    (`smp_switch_to_thread_suite` 28 → 30 PASS) + 2 tier-3 anchors; both new
    theorems axiom-clean.  Default build green (320 jobs); Tier 0–3 green; trace
    byte-identical.  Items deferred past v1.0.0 with correctness impact: NONE.

  **WS-SM SM5.B audit-pass-3 (PR #805 automated-review closure; also in
  v0.31.39)**: two valid P2 findings from the PR's automated reviewer, both in
  SM5.B's scope (the `TCB.cpuAffinity` field + the FFI seam this cut
  introduced), closed per the implement-the-improvement rule:
  - **Information-flow projection leak (P2-4)**: adding `TCB.cpuAffinity` made
    it survive `projectKernelObject`'s TCB record update, while the projection
    deliberately erases every other scheduler-only field (`registerContext`,
    `schedContextBinding`, `pipBoost`, `pendingMessage`, `timedOut`).  Per-thread
    CPU *placement* is the same class, so two states differing only by an
    affinity change would project to different low objects — a cross-domain
    placement leak once `setThreadCpuAffinity` (SM5.C) lands.  Fixed by stripping
    `cpuAffinity := none` in the `.tcb` projection arm (structurally, mirroring
    AK6-G) with the witness `projectKernelObject_erases_cpuAffinity`.
  - **FFI ThreadId encodability (P2-2)**: `switchToThreadHw` did
    `UInt64.ofNat tid.toNat` on an unbounded-`Nat` `ThreadId`, silently wrapping
    for values ≥ 2^64 and colliding with the HAL `NO_CURRENT_THREAD = u64::MAX`
    sentinel at 2^64−1.  Fixed fail-closed (SM1.I.4 u64-before-cast discipline):
    `tid.toNat < switchToThreadHwTidBound` (= 2^64−1) covers both overflow and
    sentinel; an out-of-range `tid` returns `switchToThreadHwRejected` (`1`)
    without touching the HAL.  Witnesses
    `switchToThreadHw_returns_baseio_uint64_marker` (now conditional passthrough)
    + `switchToThreadHw_rejects_unencodable`.
  - Both axiom-clean (`propext` / `Quot.sound`); AK7 `RAW_LOOKUP_TID` unchanged
    (810); default build green (320 jobs); Tier 0–3 green; trace byte-identical;
    `codebase_map.json` regenerated.  Three further P2 findings (reject-non-
    runnable targets, idle-thread re-enqueue, `syncThreadStates` per-core lift)
    are SM5.C / SM5.E / already-tracked future-phase concerns, not SM5.B
    defects.  Items deferred past v1.0.0 with correctness impact: NONE.

  **WS-SM SM5.C LANDED at v0.31.40 on branch
  `claude/brave-hawking-ueuMe`** (cross-core wake via SGI — the cross-core
  scheduler-notification phase; plan §3.3, §4.4, §5).  All 12 sub-tasks landed
  in one cut (SM5.C.7, the `TCB.cpuAffinity` field, was pulled forward to SM5.B.4
  and is recapped here).  Every new theorem is axiom-clean (`propext` /
  `Quot.sound` / `Classical.choice` only); the full production build (322 jobs)
  is green and the trace fixture is byte-identical (SM5.C is purely additive —
  the wake transitions have no single-core caller yet).  Production transitions
  live in `Scheduler/Operations/Selection.lean` (alongside SM5.A
  `chooseThreadOnCore` and SM5.B `switchToThreadOnCore`); the forward-looking
  theorems live in the new staged module
  `SeLe4n/Kernel/Scheduler/Operations/PerCoreWake.lean`.

  - **SM5.C.1** `enqueueRunnableOnCore (st) (c) (tid)` — the per-core "make
    `tid` runnable on core `c`" primitive (per-core analogue of
    `IPC.ensureRunnable`).  Sets `ipcState := .ready` (the exact field the
    per-core IPC↔scheduler invariants
    `runnableThreadIpcReady_perCore` / `blockedOn*NotRunnable_perCore` gate
    run-queue membership on — `threadState` is *not* gated by any run-queue
    invariant, so it is left unchanged) and inserts at
    `effectiveRunQueuePriority`.  Idempotent (`RunQueue.insert`), fail-closed on
    non-TCB.  Theorems: object-store-`invExt` + run-queue-`wellFormed`
    preservation, membership, make-ready, cross-core run-queue + current frames,
    AK7-clean per-thread `getTcb?` frame, no-TCB no-op.
  - **SM5.C.2** `wakeThread (st) (tid) (executingCore) : SystemState × Option
    (CoreId × SgiKind)` (plan §3.3, Theorem 3.3.1) — determine target
    (`determineTargetCore`) → make runnable (`enqueueRunnableOnCore`) → emit a
    `.reschedule` SGI iff the target is remote.  The pure state-plus-SGI form
    (the `executingCore` is an explicit parameter, not an FFI read) mirrors
    `chooseThreadOnCore` / `switchToThreadOnCore`; SM5.C's dispatch loop reads
    the executing core from `TPIDR_EL1` (`Concurrency.currentCoreId`) and passes
    it in.
  - **SM5.C.3** `wakeThreadLockSet` + `handleRescheduleSgiOnCoreLockSet` — the
    cross-domain (object-store table **write** + per-core run-queue **write**)
    footprints over SM5.A's unified `SchedLockId`, in plan §4.4 ascending order
    (object lock before run-queue lock; `_pairwise_le` certifies the canonical
    `withLockSet` acquisition order).  Same table-lock rationale as SM5.B
    (SM3.A.10: RHTable structural safety is table-granularity, so a per-object
    TCB lock would not protect the table).
  - **SM5.C.4** SGI emission under BKL discipline:
    `wakeThread_emits_sgi_if_remote` / `_no_sgi_if_local` / `_sgi_is_reschedule`,
    plus the typed FFI emission wrappers `coreIdTargetMask` / `sgiIntidU8` /
    `sendSgiToCore` / `sendRescheduleSgi` / `emitWakeSgi` in
    `Concurrency/Runtime.lean` routing the wake's optional SGI to
    `Platform.FFI.ffiSendSgi` (which emits `dsb ish` before `GICD_SGIR` per
    SM1.F.8 — the BKL-discipline ordering: emit *after* the state write is
    visible).
  - **SM5.C.5** `handleRescheduleSgiOnCore (st) (c)` — the target core's
    reschedule-SGI handler: re-choose (`chooseThreadOnCore`, SM5.A) + switch
    (`switchToThreadOnCore`, SM5.B), or idle when nothing is runnable.  Theorems:
    idle-when-none, eq-switch-when-some, `_switches_current`, object/run-queue
    preservation, cross-core independence.  Its lock-set coincides with
    `switchToThreadOnCoreLockSet`.
  - **SM5.C.6** `wakeThread_lossless` (plan §3.3, Theorem 3.3.2) — the woken
    thread is recoverable: there is a scheduler-reachable state (the post-wake
    state itself, via the new genuine `SchedStep` / `SchedReachable` RT-closure)
    in which it is current on or enqueued on its target core.  Non-vacuous via
    `wakeThread_target_runQueue_contains`; the conjunction form
    (`reachable ∧ disjunct`) is strictly stronger than the plan pseudocode's
    ambiguous `(reachable ∧ A) ∨ B` precedence.  Full eventually-scheduled
    liveness is SM5.J.
  - **SM5.C.8** `setThreadCpuAffinity (st) (targetTid) (affinity)` — the
    affinity-control op (bind/unbind), modelled on `setPriorityOp`; fail-closed
    with `.invalidArgument` on non-TCB.  Theorems: sets-affinity,
    object-store-`invExt` + scheduler preservation, per-thread frame, ok/error
    classification, and `_affects_determineTargetCore` (feeds the wake routing).
    The SchedContext / run-queue migration on an affinity change is the separate
    SM5.H.4 op.
  - **SM5.C.9** `determineTargetCore` — bound thread → its affinity core; unbound
    thread (`cpuAffinity = none`, the TCB default) → `bootCoreId` (the
    "boot-time default affinity = `bootCoreId`" rule, realised as the default
    wake *target* — the field stays `none`, preserving the SM5.B "unbound runs
    on every core" admission semantics of `affinityAdmitsCore`).
  - **SM5.C.10** `wakeThread_target_runQueue_contains` — the woken thread is in
    the target core's run queue immediately after the wake (it is not lost).
  - **SM5.C.11** SGI delivery latency bound: `wakeThread_emits_at_most_one_sgi`
    (bounded emission, no SGI storm) + `rescheduleSgi_lowest_intid` (the
    `.reschedule` SGI is INTID 0 — the lowest-INTID, hence highest-GIC-priority,
    kernel SGI, so it is never starved by another kernel coordination SGI) +
    `sgiDeliveryLatencyBound = 0` (no kernel SGI is serviced ahead of it).
  - **SM5.C.12** `tests/SmpWakeSuite.lean` (`lake exe smp_wake_suite`) — 80+
    surface anchors, 9 elaboration-time theorem-application examples, and 41
    runtime assertions across seven sections: determine-target affinity routing,
    enqueue + make-ready, local vs remote wake (SGI emission), the full
    wake→SGI→handle round-trip (core 1 receives the SGI and switches to the
    woken thread), the affinity-control op, the lock-set witnesses, and the
    latency-bound witnesses.  Tier-2 (negative) + Tier-3 (invariant surface)
    wired.

  **Module reachability**: `Scheduler.Operations.PerCoreWake` staged via
  `Platform.Staged` (`staged_module_allowlist.txt`, 44 staged-only modules);
  `Concurrency.Sgi` is promoted production-reached (production `Selection.lean`
  now imports it for `SgiKind`), so its `STATUS: staged` marker is dropped and it
  leaves the staged allowlist.  SM5.D's per-core timer tick (whose cross-core
  CBS-replenish wake calls `wakeThread`) is the first runtime exerciser.  Items
  deferred past v1.0.0 with correctness impact: NONE.  Follow-on: SM5.D (per-core
  timer tick), SM5.E (per-core idle threads), SM5.F (per-core PIP), SM5.G/H/I/J/K
  per the master overview.

  **WS-SM SM5.C audit-pass-1 (deep self-audit; also in v0.31.40)**: closed seven
  optimality gaps in the SM5.C landing — most importantly the soundness-adjacent
  invariant-preservation gap (the wake had shipped with strictly weaker invariant
  coverage than SM5.B's switch).  Every new theorem axiom-clean; default build
  green (322 jobs); trace byte-identical; Rust 718 HAL tests green; zero clippy
  warnings.

  - **Invariant preservation (§10, the SM5.B-parity coverage)** — proves the wake
    preserves SM4.C `currentThreadValidOnCore` (every core, unconditional) and
    `queueCurrentConsistentOnCore` (under the seL4-faithful
    "don't-wake-the-running-thread" precondition, stated explicitly not via a
    never-taken runtime guard), plus the **full SM4.D
    `ipcSchedulerContractPredicates_perCore` IPC↔scheduler-coherence bundle**
    (`wakeThread_preserves_ipcSchedulerContract`).  The pivotal soundness result:
    enqueuing a freshly-woken thread is coherent *because* the wake sets
    `ipcState := .ready` — it can never create a runnable-but-blocked thread.  A
    generic `enqueueRunnableOnCore_preserves_blockedNotRunnable_aux` discharges
    all five blocked-state conjuncts.  Corrects the original "deferred: NONE" by
    *proving* the safety obligation rather than folding it into SM5.I.
  - **Ghost-wake SGI guard (gap d)** — `wakeThread` emits the cross-core
    `.reschedule` SGI only when `tid` resolves to a TCB (so the enqueue was not a
    fail-closed no-op); a wake of a non-existent thread pokes no remote core
    (`wakeThread_no_sgi_if_no_tcb`).  `wakeThread_emits_sgi_if_remote` gains the
    `hTcb` hypothesis.
  - **Multi-step liveness (§6b, gap c)** —
    `wakeThread_then_handle_dispatches_current` /
    `wakeThread_roundtrip_reachable_current` prove the wake → reschedule-SGI-handler
    round-trip dispatches the woken thread to **current** in two real scheduler
    steps (an `enqueue` then a `switch`), walking the `SchedReachable` closure
    through `.tail`/`.switch` — which `wakeThread_lossless` (reflexive) left unused.
  - **Memory-model happens-before (§11, gap e)** — `wakeOrdering_happensBefore`
    models the wake's BKL ordering in SM2.A's operational memory model: the
    executing core's release-store synchronizes-with the target core's
    acquire-load, hence happens-before, in a well-formed two-event trace.  The
    prose "emit the SGI after the state write is visible" is now a theorem (the
    full SystemState↔MemoryTrace refinement is deferred to SM6/SM7).
  - **Honest latency-bound scoping (gap f)** —
    `sgiDeliveryLatencyBound_counts_higher_priority_kernel_sgis` makes the "= 0"
    precise: a kernel-SGI-ordering / non-starvation property (no kernel SGI
    outranks `.reschedule`, INTID 0), not an absolute hardware-delivery bound
    (SM5.J / GIC territory).
  - **Theorem inventory (gap m)** — NEW
    `Scheduler/Operations/Sm5CInventory.lean`: a 78-entry typed inventory in 7
    categories with the `s5ct!` compile-time identifier-validation macro +
    per-category counts + partition-sum + Nodup witnesses, mirroring the
    SM3.A/B/C/D/E inventories.
  - **Test + QEMU coverage** — `tests/SmpWakeSuite.lean` grows to 54 runtime
    assertions (+13) covering the new preservation / ghost-guard / multi-step
    liveness / full-mask (gaps k/l) / memory-model-HB / inventory scenarios; NEW
    `scripts/test_qemu_smp_wake.sh` (gap h) a `-smp 4` cross-core wake round-trip
    SKIP-stub wired into tier-4 (mirroring SM1.H / SM3.D); `Sm5CInventory` staged
    (45 staged-only modules); Rust suite confirmed unaffected (gap j).

  **WS-SM SM5.C audit-pass-2 (independent deep re-audit; also in v0.31.40)**: a
  second, independent deep audit verifying the *code* directly (not its
  docstrings) caught a real defect audit-pass-1 introduced, added two missing
  security theorems, and corrected documented counts.

  - **Inventory duplicate-identifier bug — FOUND AND FIXED.**
    `Sm5CInventory.lean`'s `.enqueue` section had a copy-paste error: an entry
    described as `enqueueRunnableOnCore` actually referenced
    `determineTargetCore_in_range` again — a duplicate identifier making
    `(sm5CTheorems.map (·.identifier)).Nodup` genuinely **false**, which
    `sm5CTheorems_identifiers_nodup := by native_decide` nonetheless "proved"
    (`native_decide` trusts the compiled `Lean.ofReduceBool` eval, which here
    disagreed with the kernel; kernel `decide` correctly rejects it).  Fixed the
    entry; switched both `_identifiers_nodup` / `_descriptions_nodup` from
    `native_decide` to **kernel-sound `decide`** under an elevated
    `set_option maxRecDepth 10000` (the 81-entry list's `Nodup` reduction
    recurses past the default `maxRecDepth` of 512 — the longer `description`
    strings overflow it first; the elevated limit only raises the recursion
    *cap*, adding no work and no axioms, so the proof stays a kernel-checked
    `of_decide_eq_true` with NO `Lean.ofReduceBool`, strictly stronger than the
    SM3 `native_decide` precedent); added two runtime `Nodup` assertions
    (identifiers + descriptions) to `SmpWakeSuite` as a second, compiled-`decide`
    guard.
  - **Two new security theorems** (implement-the-improvement):
    `determineTargetCore_admits_thread` / `wakeThread_target_admits_thread` (the
    no-liveness-stranding property — the wake target always admits the woken
    thread, so a wake never strands a thread on a core whose dispatch gate would
    reject it), and `enqueueRunnableOnCore_preserves_woken_thread_fields` (the
    field frame — the wake changes only `ipcState`; `priority` / `domain` /
    `cpuAffinity` / `threadState` preserved, so no silent thread-state corruption
    or placement leak).
  - **Documentation accuracy**: the §10b `IPC.ensureRunnable` comparison is made
    precise (`ensureRunnable` does not itself clear `ipcState`; `enqueueRunnableOnCore`
    bundles the clear; the IPC-dequeue is the caller's job for both).  Corrected
    counts: inventory is **81 entries** (was 78; +3 — the two new security
    theorems plus `enqueueRunnableOnCore_preserves_woken_thread_fields`);
    `SmpWakeSuite` has **59 runtime assertions / 103 surface anchors / 17
    examples** (over the audit-pass-1 baseline: +2 `assertBool` for the dual
    `Nodup` guards, +2 `#check` and +2 `example` for the three new theorems).
    All new theorems are axiom-clean and the two SM5.C modules build
    warning-clean; `smp_wake_suite` reports **59/59 PASS**; partition gate 45
    staged-only modules.  Items deferred past v1.0.0 with correctness impact:
    NONE.

- **WS-RC remediation workstream PARTIALLY LANDED (v0.30.11 → v0.31.0 → v0.31.2,
  branch `claude/audit-workstream-planning-XsmKS` and successors)**
  — historical detail retained for traceability:
  Remediates the v0.30.11 audit cycle (comprehensive + deep verification)
  via 15 phases (R0..R14); R0..R5 landed at v0.31.2; R6..R14 absorbed
  into WS-SM per the SM0.Q merge.  Plan:
  [`docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md`](docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md).
  Errata recording the audit-text corrections discovered during planning:
  [`docs/audits/AUDIT_v0.30.11_ERRATA.md`](docs/audits/AUDIT_v0.30.11_ERRATA.md).
  Release path: `v0.31.0` "verified specification release" (R0+R1+R8..R12)
  → `v1.0.0` "bootable verified microkernel" (+ R2..R6). The plan applies
  the implement-the-improvement rule uniformly: even false-positive
  audit findings receive structural enforcement gates (R12.B for
  production/staged partition, R12.C for ARM-ARM citations, R12.D for
  `_fields` consumer presence; R4.D for cspaceMutate witness theorem).
  Plan-author audit at WS-RC R0 prep landed: SPDX header on
  `SeLe4n.lean` (R10.1), audit errata file (R0.2), staged-module
  allowlist + partition gate (R12.B.1/2), orphan-fields gate (R12.D.1),
  contract-marker text correction (R12.B side effect — partition
  gate caught 2 stale "STATUS: staged" markers on production-wired
  contract files). **R1 (DEEP-IPC-03) LANDED on branch
  `claude/audit-ipc-symmetry-yhdIu`**: closes the call-path NI
  asymmetry by aligning `endpointCallWithCaps` with the AK1-I
  fail-closed shape — all three IPC capability-transfer paths
  (`endpointSendDualWithCaps`, `endpointReceiveDualWithCaps`,
  `endpointCallWithCaps` in
  `SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean`) now return
  `.error .invalidCapability` on the missing-CSpace-root
  structural fault. Proof discharge updated in
  `SeLe4n/Kernel/IPC/Invariant/CallReplyRecv/ReplyRecv.lean`;
  test coverage in `tests/InformationFlowSuite.lean` +
  `tests/NegativeStateSuite.lean::runR1IpcCallPathSymmetryChecks`.
  **R2 (DEEP-FFI-01/02/03 + DEEP-TEST-03) LANDED on branch
  `claude/review-hardware-syscall-phase-FfbvV`**: closes the
  hardware-syscall-dispatch gap by replacing the
  `suspend_thread_inner` and `syscall_dispatch_inner` `@[export]`
  stubs (previously returning `KernelError::NotImplemented = 17`)
  with substantive bodies that route through
  `Kernel.Lifecycle.Suspend.suspendThread` and the verified
  `syscallEntryChecked` entry point.  R2.A: kernel-state IO.Ref
  threading (`kernelStateRef`, `kernelLabelingContextRef`,
  `initialiseKernelState`, `getKernelState`, `updateKernelState`,
  `bootAndInitialiseFromPlatform` boot wrapper).  R2.B: pure typed-ABI
  entry point `syscallDispatchFromAbi` (writes FFI register values
  into the current TCB, invokes `syscallEntryChecked`, encodes the
  result via the bit-63 error-flag UInt64 contract); replaced bodies
  for the two `@[export]` declarations.  Adds `KernelError.toUInt32`
  (mirroring `rust/sele4n-types/src/error.rs` discriminants 0..51),
  `encodeError` / `encodeOk` UInt64 encoding helpers, an ABI
  consistency gate that rejects with `.invalidSyscallArgument` if
  `msgInfo ≠ x1` (both must equal `frame.x1()` per the Rust caller's
  `SyscallArgs::from_trap_frame`) without spilling registers or
  mutating kernel state, and nine correctness theorems
  (`encodeError_high_bit_set`,
  `encodeOk_high_bit_clear`,
  `syscallDispatchFromAbi_total`,
  `syscallDispatchFromAbi_ok_of_syscallEntryChecked_ok`,
  `syscallDispatchFromAbi_error_of_syscallEntryChecked_error`,
  `syscallDispatchFromAbi_illegalState_when_no_current`,
  `syscallDispatchFromAbi_abiMismatch_rejected`,
  `writeFfiRegistersToTcb_id_when_not_tcb`,
  `readReturnValue_zero_when_not_tcb`).  Aligns the Rust comments at
  `rust/sele4n-hal/src/svc_dispatch.rs:237-244,305-312` and
  `rust/sele4n-hal/src/ffi.rs:247-254` with the actual
  `syscall_dispatch_inner` / `suspend_thread_inner` symbol names.
  R2.C: makes the FFI docstring's gating claim honest (link-time, not
  preprocessor); adds the dedicated `tests/SyscallDispatchSuite.lean`
  regression suite (195 assertions across 18 test functions covering
  all 52 `KernelError` discriminants pinned 1:1 against the Rust enum,
  `encodeError` low-32-bits-match-discriminant proofs, `encodeOk`
  identity-when-bit-63-clear and bit-63-truncation properties, the
  IO.Ref bootstrap path, `suspendThreadInner` integration,
  `syscallDispatchInner` integration, the ABI-mismatch reject path,
  and sequential dispatch state evolution) wired into
  `scripts/test_tier2_negative.sh` and
  `scripts/test_tier3_invariant_surface.sh`.  Audit follow-up
  refactored the Rust `DispatchError` enum to wrap the raw kernel-
  error discriminant via `Kernel(u32)` instead of coarsening to
  `NotImplemented`, so user-mode now sees the exact `KernelError`
  the Lean kernel emitted (pre-fix: 49 of 52 variants were silently
  collapsed to `17 = NotImplemented`).
  **R3 (DEEP-BOOT-01) LANDED on branch
  `claude/vspace-threading-boot-G0GAp`**: closes the boot-VSpace
  threading gap by admitting boot-safe VSpaceRoots into the
  `bootSafeObject` / `bootSafeObjectCheck` predicates and threading
  the canonical `rpi5BootVSpaceRoot` through `bootFromPlatformChecked`
  via the new `installBootVSpaceRoot` builder operation.  Pre-R3 the
  `.vspaceRoot _ => false` arm rendered the proven-W^X-compliant
  data structure inert; per the implement-the-improvement rule, the
  verified structure is the better state and the boot path now
  consumes it.  R3.0a-b: `bootSafeVSpaceRootCheck` (Bool mirror)
  and `bootSafeVSpaceRootCheck_iff` equivalence in
  `Platform/RPi5/VSpaceBoot.lean`; `installBootVSpaceRoot` builder
  in `Platform/Boot.lean` composing `Builder.createObject` with
  `asidTable` insertion so the boot VSpace is resolvable by ASID;
  `rpi5BootVSpaceRoot_mappings_invExt` discharge witness.  R3.1:
  rewrote `.vspaceRoot` arm of `bootSafeObjectCheck` (Bool) and
  `bootSafeObject` (Prop) to admit boot-safe VSpaceRoots.  R3.2:
  added witness theorems `bootSafeObjectCheck_admits_rpi5BootVSpaceRoot`
  and `bootSafeObject_admits_rpi5BootVSpaceRoot`.  R3.3: added
  `bootVSpaceRoot : Option BootVSpaceRootEntry := none` to
  `PlatformConfig`, two runtime gates
  (`bootVSpaceRootObjIdDistinct`, `bootVSpaceRootSafe`), and
  threaded through `bootFromPlatformChecked`.  R3.4: wired
  `rpi5BootVSpaceRootEntry` into the RPi5 `PlatformBinding`
  instance via the new typeclass `bootVSpaceRoot` field.  R3.5:
  defined `simBootVSpaceRoot` (single-mapping boot-safe root) and
  wired into both `simPlatformBinding` and
  `simRestrictivePlatformBinding` for parity.  R3.6:
  `bootFromPlatformChecked_eq_bootFromPlatform` gains a
  `bootVSpaceRoot = none` precondition; sibling theorem
  `bootFromPlatformChecked_admits_bootVSpace` covers the
  `some entry` case.  R3.7: added 8 TPH-015 tests in
  `tests/TwoPhaseArchSuite.lean` exercising the end-to-end
  threading.  R3.8: extended `tests/An9HardwareBindingSuite.lean`
  with 5 new boot-VSpace assertions.  Removed
  `Platform.RPi5.VSpaceBoot` and `Architecture.AsidManager` from
  `scripts/staged_module_allowlist.txt` — they enter production
  via Boot.lean's import.  Pre-R3 theorem
  `bootFromPlatform_proofLayerInvariantBundle_general` gains a
  `hNoVSpaceInInitial` precondition; boot VSpaceRoots are now
  exclusively introduced via the gated `bootFromPlatformChecked`
  path.
  **WS-RC R3 audit pass** (post-LANDING audit):
  closed two HIGH security/correctness issues (#2 VSpaceRoots in
  `initialObjects` bypass `asidTable` update — fixed by adding
  `noVSpaceRootsInInitialObjects` gate; #3 boot VSpace ObjId was
  the reserved `ObjId.sentinel` (`⟨0⟩`) — changed to
  `ObjId.ofNat 1` and added defense-in-depth
  `bootVSpaceRootObjIdNonSentinel` gate).  Plus four LOW
  documentation accuracy fixes (#1 sim binding docstring, #4 P-L9
  resolved status in MmioAdapter, #5 RPi5 Contract Status section,
  #7 speculative reference to unimplemented sibling theorem).
  Three new regression tests (TPH-015i/j/k) cover the new gates.
  All theorem proofs that traverse `bootFromPlatformChecked`'s
  gates updated for the two new splits
  (`bootFromPlatformChecked_eq_bootFromPlatform`,
  `bootFromPlatformChecked_admits_bootVSpace`,
  `bootFromPlatformChecked_ok_implies_*`,
  `bootFromPlatformChecked_ok_interruptsEnabled`).
  **WS-RC R3 third-audit pass** (post-LANDING audit, v0.30.11
  hardening):  closed a defense-in-depth gap in
  `bootSafeVSpaceRootCheck` that did not verify the canonical-form
  bound on virtual addresses (`vaddr.val < 2^48`).  Pre-fix the
  predicate verified four conjuncts (asid bounded, W^X compliant,
  non-empty mappings, paddr < 2^44); a third-party
  `BootVSpaceRootEntry` constructed with a vaddr in the ARMv8-A
  reserved gap `[2^48, 2^64 - 2^48)` would pass the gate yet
  translation-fault on hardware before the kernel could intercept
  the misconfiguration.  Per implement-the-improvement, added a
  fifth `VSpaceRootVaddrCanonical` predicate to the
  `VSpaceRootWellFormed` conjunction and threaded it through both
  Bool (`bootSafeVSpaceRootCheck`) and Prop (`bootSafeVSpaceRoot`)
  forms, the equivalence theorem (`bootSafeVSpaceRootCheck_iff`),
  the canonical RPi5 boot root proof
  (`rpi5BootVSpaceRoot_vaddrCanonical` discharge witness and the
  five-conjunct `rpi5BootVSpaceRoot_wellFormed` refine), the
  simulation boot root proof (`simBootVSpaceRoot_bootSafe` — fifth
  `decide`), and the `Platform.Boot.bootSafeObjectCheck` `.vspaceRoot`
  arm docstring.  New regression test
  `TPH-015l_nonCanonicalVAddrRejected` exercises the gate with a
  malformed entry at `vaddr = 2^48` (the first non-canonical
  address); the existing `TPH-015a..k` tests continue to pass
  because canonical vaddrs (rpi5BootVSpaceRoot via insertIdentity
  with paddr<2^44, simBootVSpaceRoot at vaddr=0x1000) trivially
  satisfy the new conjunct via `decide`.
  **WS-RC R5 (DEEP-SUSP-01/02, DEEP-SCH-02..06) LANDED on branch
  `claude/audit-scheduler-phase-r5-nWFdz`**: closes the seven
  scheduler/lifecycle behaviour-symmetry findings.  R5.A splits the
  monolithic `cancelDonation` (suspend G3) into the two named arms
  `cancelBoundDonation` (in-place SchedContext unbind) and
  `cancelDonatedDonation` (return-to-original-owner via
  `cleanupDonatedSchedContext`); the original name survives as a thin
  dispatcher that preserves closure-form proof discharge.  R5.B adds
  PIP recomputation at the resume H3b step: `resumeThread` re-derives
  the resumed thread's `pipBoost` from the post-suspend blocking graph
  via `PriorityInheritance.computeMaxWaiterPriority`, with three
  structural witnesses (`restoreToReady_objectIndex_eq`,
  `restoreToReady_objects_eq_at_tid`,
  `resumeThread_pipBoost_consistent_post_restore`).  R5.C introduces
  the total `effectiveSchedParams` (returning a `(Priority, Deadline,
  DomainId)` triple) alongside the existing partial
  `effectivePriority`, with two bridge witnesses
  (`effectiveSchedParams_priority_deadline_eq_resolve` agreeing with
  `resolveEffectivePrioDeadline`; `effectivePriority_some_eq_effectiveSchedParams`
  agreeing with the partial form when the partial form succeeds).
  R5.D consolidates the shared IPC-state-clearing transition between
  `cancelIpcBlocking` (suspend G2) and `resumeThread` (H3) under the
  named helper `restoreToReady` (the original private
  `clearTcbIpcFields` becomes a `@[inline]` back-compat alias).
  R5.E surfaces `KernelError.missingSchedContext` (new discriminant
  52) in the bound-budget branch of `timerTickBudget` when the
  bound TCB's SchedContext is missing — replacing the pre-R5 silent
  `(state, false)` no-preempt fallback; the Rust `KernelError` enum
  and every discriminant-pinning test grow in lock-step (range
  extends to 0..=52, sentinel range starts at 53).  The same
  surfacing is mirrored in `FrozenOps.frozenTimerTickBudget` for
  cross-phase consistency.  R5.F promotes `RunQueue.rotateToBack`'s
  membership precondition to two formal assertion theorems
  (`rotateToBack_requires_membership`,
  `rotateToBack_priority_eq_threadPriority`) without changing the
  function definition.  R5.G adds a domain-propagation block to
  `schedContextConfigure` that mirrors the existing priority-
  propagation block: when the SC's bound TCB has a domain that
  differs from the new SC domain, the TCB's `domain` field is
  rewritten — closing a silent
  `boundThreadDomainConsistent`-invariant-violation path; two new
  witness theorems
  (`schedContextConfigure_bound_tcb_domain_eq`,
  `schedContextConfigure_domain_noop_when_eq`).  Tests:
  4 + 3 + 2 new regression tests in `tests/SuspendResumeSuite.lean`
  for R5.A, R5.B, R5.D (30 tests total — R5.B gains the substantive
  audit-pass test `sr027b_resumeRecomputesPipBoostWithWaiters`
  exercising the with-waiter PIP recomputation path); 3 new
  regression tests in `tests/PriorityManagementSuite.lean` for R5.G
  (30 tests total); 1 new regression test in
  `tests/NegativeStateSuite.lean` for R5.E
  (`runR5EOrphanedSchedContextChecks`); 1 new discriminant pin in
  `tests/SyscallDispatchSuite.lean` (`sd001_52_missingSchedContext`,
  variant count is now 53); 24 new surface-anchor `#check`s in
  `tests/LivenessSuite.lean` (R5.A/B/C/D/G witness theorems +
  closure-form preservation); 1 new Rust unit test
  (`decode_missing_sched_context_error`) and 1 new Rust integration
  test (`missing_sched_context_decode`).  Audit-pass additions land
  `cancelBoundDonation_preserves_projection` /
  `cancelDonatedDonation_preserves_projection` closure-form helpers
  in `InformationFlow/Invariant/Operations.lean` for IF discharge
  symmetry with the AK6-F.17 retained dispatcher helper, and
  `schedContextConfigure_preserves_boundThreadDomainConsistent`
  closure-form preservation in
  `SchedContext/Invariant/Preservation.lean` for caller-site
  invariant discharge.  The R5.E error-branch docstring is
  corrected (pre-audit version misclaimed "timer still advances on
  the rejection path"; the `.error` short-circuit returns before
  any state update, so the timer is NOT advanced and the error
  propagates to the caller without committing the partial budget
  accounting).  AK7 cascade monotonicity baseline retained at the
  v0.30.11 floor (the new lookup site in `resumeThread` routes
  through `getTcb?`, preventing `raw_match_tcb` drift).
  R5 deferred-work completion (follow-up audit pass): R5.F.1 fully
  landed — `RunQueue.rotateToBack`'s body now routes through the
  private helper `lookupPriorityOrPanic` which explicitly `panic!`s
  on the invariant-unreachable branch (pre-this-commit the branch
  silently defaulted to priority 0); the existing
  `rotateToBack_preserves_wellFormed` proof is updated to use
  `lookupPriorityOrPanic_of_some` under the pre-existing
  `wellFormed`+`contains` hypotheses.  R5.C.1 fully landed for the
  prominent caller — `computeMaxWaiterPriority` is migrated from
  `effectivePriority` (Option) to `effectiveSchedParams` (total),
  removing the Option propagation in the priority-inheritance fold;
  the migration is semantics-preserving under
  `schedContextStoreConsistent`.

  **WS-RC R5 deferred-work SUBSTANTIVE COMPLETION (v0.31.2, branch
  `claude/review-closeout-plan-UCrc7`)**: the deferred-work plan
  ([`docs/dev_history/audits/WS_RC_R5_DEFERRED_COMPLETION_PLAN.md`](docs/dev_history/audits/WS_RC_R5_DEFERRED_COMPLETION_PLAN.md)
  — archived to dev_history per WS-SM SM0.Q.2)
  completes the four "AVOIDED" / "UNDER-DELIVERED" items from the
  initial R5 landing.  Phase P (foundational lemmas):
  `blockingAcyclic_of_subgraph` + `blockingChain_subgraph_prefix`
  (`Scheduler/PriorityInheritance/BlockingGraph.lean`);
  `computeMaxWaiterPriority_frame` + `waitersOf_frame` +
  `effectiveSchedParams_frame` + `effectiveSchedParams_frame_per_field`
  + `getSchedContext?_frame` (`Scheduler/PriorityInheritance/Compute.lean`);
  `objects_insert_non_tcb_non_sc_preserves_boundThreadDomainConsistent`
  + `objects_update_sync_domain_preserves_boundThreadDomainConsistent`
  (`Scheduler/Invariant.lean`).  Phase Q (R5.B.2 substantive):
  `restoreToReady_invExt`, `restoreToReady_blockingServer_subgraph`,
  `restoreToReady_preserves_blockingAcyclic`, `ensureRunnable_objects_eq`,
  `ensureRunnable_objectIndex_eq`, `ensureRunnable_blockingServer_eq`,
  `ensureRunnable_preserves_computeMaxWaiterPriority`,
  `resumeThread_postState_shape` (structural shape Prop),
  `resumeThread_preserves_blockingAcyclic` (SUBSTANTIVE — no `hProp`),
  `resumeThread_pipBoost_consistent_with_blocking_graph` (SUBSTANTIVE
  — no `hProp`).  Phase R (R5.G.3 substantive):
  `schedContextConfigure_preserves_boundThreadDomainConsistent_caseC`,
  `schedContextConfigure_preserves_boundThreadDomainConsistent_scOnly`,
  `schedContextConfigure_preserves_boundThreadDomainConsistent`
  (SUBSTANTIVE — no `hProp`).  Phase S (R5.C.1 full deprecation):
  `effectivePriority` def + 3 helper theorems + bridge theorem all
  deleted; remaining callers migrated to `effectiveSchedParams`.
  Phase V: surface anchors added; discharge index §3.H rows H.19–H.25
  added; H.16 marked SUBSTANTIVE; H.9 marked RETIRED.  ERRATA-R5-1
  (plan pseudocode references nonexistent
  `scheduler.blockingGraph` field) and ERRATA-R5-2 (plan signature
  missing `schedContextBindingConsistent`) recorded in errata.
  Items deferred past v1.0.0 with correctness impact: NONE.
  The substantive `resumeThread_*` proofs use a structural-shape
  hypothesis (`resumeThread_postState_shape`) characterising the
  post-state's `objects` table.  The shape is concrete (not a
  closure of the conclusion) and is dischargeable at call sites
  from `resumeThread = .ok st'` plus the runtime invariants in
  `crossSubsystemInvariant`; a `_full` variant that internally
  unfolds `resumeThread` is a post-1.0 hardening candidate.

  **WS-RC R4 close-out COMPLETE (v0.31.0, branch
  `claude/review-closeout-plan-HToSk`)**:  the 9-sub-PR close-out
  ([`docs/dev_history/audits/WS_RC_R4_CLOSEOUT_PLAN.md`](docs/dev_history/audits/WS_RC_R4_CLOSEOUT_PLAN.md)
  — archived to dev_history per WS-SM SM0.Q.2)
  plus an audit-driven deep cleanup completes the four R4 sub-tasks
  left open after the v0.30.11 partial landing and **fully retires**
  the historical state-level `cspaceSlotUnique` and `uniqueWaiters`
  predicates per the plan's A2.c4 / C2.c4 deletion mandate.  Phase
  P1: the close-out plan's 6 plan-named witnesses are landed (4 of
  them survive the deep cleanup — `cnode_slots_unique`,
  `notification_waiters_nodup`,
  `cspaceSlotUnique_promoted_to_structural`,
  `uniqueWaiters_promoted_to_structural` — and the 2 transitional
  `_trivial` helpers are deleted in A2/C2).  Phases A1/A2/deep
  cleanup: `cspaceSlotUnique` retired (state-level predicate
  removed entirely from the codebase; per-CNode discharge is now
  via the structural `UniqueSlotMap.hWF` carried by every
  `CNode.slots`; 22 vestigial hypothesis parameters and 8 transfer
  theorems deleted; `cspaceLookupSound_of_cspaceSlotUnique` renamed
  to the unconditional `cspaceLookupSound_holds`).  Phases B1/B2/B3:
  `ScrubTokenImpl` made `private structure` with privacy verified by
  external probe (`#check` of `ScrubTokenImpl` from outside the file
  fails with "Unknown identifier"; `{...}` construction fails with
  "constructor is marked as private");
  `lifecyclePreRetypeCleanupWithToken` wrapper threading the token
  through cleanup; `mkRetypeTarget` smart constructor.  Phases
  C1/C2/deep cleanup: `uniqueWaiters` retired (state-level predicate
  removed entirely; `ipcInvariantFull` 16→15 conjuncts; per-Notification
  discharge is now via the structural `NoDupList.hNodup` carried by
  every `Notification.waitingThreads`; the
  `notificationWait_preserves_uniqueWaiters`,
  `notification_waitingThreads_nodup_witness`,
  `coreIpcInvariantBundle_to_uniqueWaiters`, and
  `default_uniqueWaiters` helpers are deleted).  Phase V1: version
  bumped 0.30.11 → 0.31.0 across `lakefile.toml`, `README.md`,
  `CHANGELOG.md`, `CLAUDE.md`, `docs/spec/SELE4N_SPEC.md`,
  `rust/Cargo.{toml,lock}`, `rust/sele4n-hal/src/boot.rs`, all 10
  `docs/i18n/<lang>/README.md`, `docs/codebase_map.json`.  No
  `True`-alias shims remain after the deep cleanup; the codebase is
  free of backwards-compat hacks per CLAUDE.md's structural
  enforcement rule.  Items deferred past v1.0.0 with correctness
  impact: NONE.

- **WS-AN portfolio COMPLETE (v0.30.11, branch `claude/review-codebase-phase-an12-JBPQN`)**:
  Phase AN12 — Documentation, themes, closure — landed the cross-cutting
  Theme 4.1 closure-form discharge index
  (`docs/dev_history/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md`, archived at
  WS-AN closure; marker theorem
  `closureForm_discharge_index_documented` in `SeLe4n/Kernel/CrossSubsystem.lean`),
  Theme 4.4 SMP-latent assumption inventory
  (`SeLe4n/Kernel/Concurrency/Assumptions.lean` with `smpLatentInventory`
  aggregator + `_count : length = 8` size witness, wired into
  `Platform.Staged`; mirrored at `docs/spec/SELE4N_SPEC.md` §6.8),
  the DOC-M01..M08 batch (SPDX-License-Identifier headers added to all
  247 `.lean`/`.rs` source files; `CONTRIBUTING.md` rewritten),
  the DOC LOW batch (`docs/audits/README.md` documenting the
  "one active audit at a time" lifecycle convention; `docs/CLAUDE_HISTORY.md`
  archive convention established), in-place RESOLVED annotations on
  14 of 15 absorbed `AUDIT_v0.29.0_DEFERRED.md` rows (now archived under
  `docs/dev_history/audits/`; DEF-F-L9 retained
  as a post-1.0 readability/maintainability refactor with no correctness
  impact), and the closure summary in `docs/WORKSTREAM_HISTORY.md`.
  Version bumped 0.30.10 → 0.30.11. Items deferred past v1.0.0 with
  correctness impact: NONE.

- **Older WS-AN entries (AN0..AN11) and pre-WS-AN portfolios (WS-AK
  through WS-AA)** — archived to
  [`docs/CLAUDE_HISTORY.md`](docs/CLAUDE_HISTORY.md). Canonical
  per-phase record:
  [`docs/WORKSTREAM_HISTORY.md`](docs/WORKSTREAM_HISTORY.md) +
  [`CHANGELOG.md`](CHANGELOG.md).

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
