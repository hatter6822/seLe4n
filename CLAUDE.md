# CLAUDE.md — seLe4n project guidance

> A mirror of this file lives at `AGENTS.md` so that non-Claude coding
> agents (and any tool that follows the AGENTS.md convention) get the
> same project rules. If you edit one, edit the other in the same PR —
> the two files must stay byte-identical apart from this header.

## What this project is

seLe4n is a production-oriented microkernel written in Lean 4 with machine-checked
proofs, improving on seL4 architecture. Every kernel transition is an executable
pure function with zero `sorry`/`axiom`. First hardware target: Raspberry Pi 5.
Lean 4.28.0 toolchain, Lake build system, version 0.31.9.

> The version line above is **CI-enforced** by
> `scripts/check_version_sync.sh` (a Tier 0 gate). When you bump
> `lakefile.toml`, you must bump that line in the same PR, on a single
> line, with the canonical trigger phrase intact. Do not reword the
> sentence and do not split it across a line wrap — the script greps
> for the literal phrase on one line.

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
- `CHANGELOG.md` (~14336 lines)
- `docs/WORKSTREAM_HISTORY.md` (~5243 lines)
- `docs/dev_history/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md` (~4721 lines)
- `docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md` (~4130 lines)
- `tests/NegativeStateSuite.lean` (~4029 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~3908 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` (~3783 lines)
- `SeLe4n/Kernel/CrossSubsystem.lean` (~3390 lines)
- `docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md` (~3388 lines)
- `SeLe4n/Testing/MainTraceHarness.lean` (~3159 lines)
- `docs/dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md` (~3140 lines)
- `docs/dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md` (~3134 lines)
- `docs/gitbook/12-proof-and-invariant-map.md` (~3040 lines)
- `SeLe4n/Model/Object/Structures.lean` (~2809 lines)
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean` (~2672 lines)
- `SeLe4n/Platform/Boot.lean` (~2591 lines)
- `SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean` (~2505 lines)
- `docs/dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md` (~2476 lines)
- `docs/dev_history/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md` (~2472 lines)
- `SeLe4n/Kernel/API.lean` (~2374 lines)
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` (~2369 lines)
- `docs/dev_history/audits/AUDIT_v0.25.14_WORKSTREAM_PLAN.md` (~2340 lines)
- `docs/dev_history/audits/AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md` (~2339 lines)
- `docs/audits/AUDIT_v0.30.11_DEEP_VERIFICATION.md` (~2326 lines)
- `SeLe4n/Model/State.lean` (~2237 lines)
- `docs/spec/SELE4N_SPEC.md` (~2216 lines)
- `tests/OperationChainSuite.lean` (~2208 lines)
- `docs/planning/SMP_RUST_HAL_PLAN.md` (~2204 lines)
- `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean` (~2187 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/DualQueueMembership.lean` (~2065 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/StoreObjectFrame.lean` (~1991 lines)
- `docs/dev_history/planning/V3_PROOF_CHAIN_HARDENING_E_G6_PLAN.md` (~1966 lines)
- `tests/ModelIntegritySuite.lean` (~1950 lines)
- `docs/dev_history/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md` (~1917 lines)
- `docs/dev_history/planning/V3E_IPC_UNWRAP_CAPS_LOOP_COMPOSITION_PLAN.md` (~1891 lines)
- `docs/dev_history/audits/AUDIT_v0.30.6_COMPREHENSIVE.md` (~1889 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/PerOperation.lean` (~1885 lines)
- `SeLe4n/Kernel/Capability/Operations.lean` (~1868 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/QueueNextTransport.lean` (~1860 lines)
- `SeLe4n/Prelude.lean` (~1830 lines)
- `docs/dev_history/audits/AUDIT_v0.27.6_WORKSTREAM_PLAN.md` (~1801 lines)
- `docs/dev_history/audits/AUDIT_v0.25.21_WORKSTREAM_PLAN.md` (~1800 lines)
- `SeLe4n/Model/Object/Types.lean` (~1794 lines)
- `SeLe4n/Kernel/IPC/Invariant/QueueMembership.lean` (~1792 lines)
- `docs/dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md` (~1776 lines)
- `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` (~1753 lines)
- `docs/dev_history/audits/AUDIT_v0.25.14_COMPREHENSIVE.md` (~1739 lines)
- `docs/dev_history/audits/WORKSTREAM_PLAN_WS_O_SYSCALL_RUST_WRAPPERS.md` (~1725 lines)
- `docs/dev_history/AUDIT_v0.22.10_WORKSTREAM_PLAN.md` (~1674 lines)
- `SeLe4n/Model/FreezeProofs.lean` (~1663 lines)
- `docs/planning/SMP_FOUNDATIONS_PLAN.md` (~1646 lines)
- `tests/InformationFlowSuite.lean` (~1623 lines)
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` (~1590 lines)
- `SeLe4n/Kernel/Architecture/Invariant.lean` (~1520 lines)
- `docs/dev_history/audits/AUDIT_v0.28.0_WORKSTREAM_PLAN.md` (~1480 lines)
- `docs/dev_history/planning/V3B_LOAD_FACTOR_BOUNDED_MIGRATION_PLAN.md` (~1457 lines)
- `docs/dev_history/audits/AUDIT_v0.25.3_WORKSTREAM_PLAN.md` (~1452 lines)
- `docs/dev_history/audits/WS_RC_R5_DEFERRED_COMPLETION_PLAN.md` (~1414 lines)
- `docs/dev_history/AUDIT_v0.23.21_WORKSTREAM_PLAN.md` (~1411 lines)
- `docs/dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md` (~1382 lines)
- `docs/dev_history/audits/AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md` (~1357 lines)
- `docs/dev_history/audits/AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md` (~1342 lines)
- `docs/dev_history/audits/AUDIT_v0.22.17_WORKSTREAM_PLAN.md` (~1252 lines)
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean` (~1243 lines)
- `docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md` (~1237 lines)
- `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` (~1211 lines)
- `SeLe4n/Kernel/Scheduler/Invariant.lean` (~1210 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` (~1180 lines)
- `docs/dev_history/audits/AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md` (~1178 lines)
- `SeLe4n/Platform/DeviceTree.lean` (~1154 lines)
- `SeLe4n/Platform/RPi5/MmioAdapter.lean` (~1153 lines)
- `tests/KernelErrorMatrixSuite.lean` (~1139 lines)
- `SeLe4n/Kernel/RobinHood/Bridge.lean` (~1111 lines)
- `docs/planning/WS_RC_R4_TYPE_LEVEL_PROMOTION_PLAN.md` (~1111 lines)
- `docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md` (~1098 lines)
- `docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md` (~1071 lines)
- `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean` (~1043 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Core.lean` (~1039 lines)
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean` (~1032 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean` (~1027 lines)
- `SeLe4n/Kernel/InformationFlow/Policy.lean` (~1023 lines)
- `SeLe4n/Kernel/FrozenOps/Operations.lean` (~999 lines)
- `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean` (~984 lines)
- `docs/dev_history/audits/AUDIT_v0.19.6_WORKSTREAM_PLAN.md` (~984 lines)
- `SeLe4n/Machine.lean` (~977 lines)
- `SeLe4n/Kernel/Scheduler/RunQueue.lean` (~969 lines)
- `docs/dev_history/planning/WS_X_LEAN_ETHEREUM_FORMALIZATION_PLAN.md` (~958 lines)
- `docs/dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md` (~930 lines)
- `docs/dev_history/audits/AUDIT_v0.28.0_COMPREHENSIVE.md` (~921 lines)
- `SeLe4n/Platform/FFI.lean` (~917 lines)
- `docs/dev_history/audits/AUDIT_H3_HARDWARE_BINDING_v0.25.27.md` (~911 lines)
- `docs/dev_history/audits/AUDIT_v0.25.10_WORKSTREAM_PLAN.md` (~909 lines)
- `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/Signal.lean` (~887 lines)
- `docs/dev_history/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md` (~884 lines)
- `docs/dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md` (~859 lines)
- `SeLe4n/Kernel/IPC/Operations/SchedulerLemmas.lean` (~836 lines)
- `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean` (~827 lines)
- `docs/dev_history/audits/WS_RC_R4_CLOSEOUT_PLAN.md` (~818 lines)
- `tests/TwoPhaseArchSuite.lean` (~811 lines)
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
  lines, 36 decidable examples, and 41 runtime `assertBool`
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

  Follow-on: SM3.B (`LockId.fromObject`, `LockId.lookup`,
  per-transition `lockSet`, `lockAcquireSequence` ordering
  theorems) consumes the SM3.A.10 `objectLockOf` projection; SM3.C
  (`withLockSet` 2PL discipline) consumes both SM3.A and SM3.B;
  SM3.D/SM3.E close with deadlock-freedom and serializability
  theorems.  See
  [`docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md`](docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md)
  §§5.2..5.5.

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
