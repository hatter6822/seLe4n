# CLAUDE.md — seLe4n project guidance

> A mirror of this file lives at `AGENTS.md` so that non-Claude coding
> agents (and any tool that follows the AGENTS.md convention) get the
> same project rules. If you edit one, edit the other in the same PR —
> the two files must stay byte-identical apart from this header.

## What this project is

seLe4n is a production-oriented microkernel written in Lean 4 with machine-checked
proofs, improving on seL4 architecture. Every kernel transition is an executable
pure function with zero `sorry`/`axiom`. First hardware target: Raspberry Pi 5.
Lean 4.28.0 toolchain, Lake build system, version 0.31.5.

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

- **WS-SM SMP multi-core completion workstream IN FLIGHT (v0.31.2 → v0.31.3 → v0.31.4 → v0.31.5 → v0.32.x → v1.0.0,
  branch `claude/review-codebase-secondary-core-PgqGR`)**:
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
