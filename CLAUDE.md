# CLAUDE.md — seLe4n project guidance

> A mirror of this file lives at `AGENTS.md` so that non-Claude coding
> agents (and any tool that follows the AGENTS.md convention) get the
> same project rules. If you edit one, edit the other in the same PR —
> the two files must stay byte-identical apart from this header.

## What this project is

seLe4n is a production-oriented microkernel written in Lean 4 with machine-checked
proofs, improving on seL4 architecture. Every kernel transition is an executable
pure function with zero `sorry`/`axiom`. First hardware target: Raspberry Pi 5.
Lean 4.28.0 toolchain, Lake build system, version 0.31.2.

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
- `CHANGELOG.md` (~13479 lines)
- `docs/dev_history/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md` (~4721 lines)
- `docs/WORKSTREAM_HISTORY.md` (~4617 lines)
- `docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md` (~4130 lines)
- `tests/NegativeStateSuite.lean` (~3940 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~3857 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` (~3779 lines)
- `SeLe4n/Kernel/CrossSubsystem.lean` (~3309 lines)
- `docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md` (~3303 lines)
- `SeLe4n/Testing/MainTraceHarness.lean` (~3159 lines)
- `docs/dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md` (~3140 lines)
- `docs/dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md` (~3134 lines)
- `docs/gitbook/12-proof-and-invariant-map.md` (~3002 lines)
- `SeLe4n/Model/Object/Structures.lean` (~2772 lines)
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean` (~2745 lines)
- `SeLe4n/Platform/Boot.lean` (~2584 lines)
- `SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean` (~2505 lines)
- `docs/dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md` (~2476 lines)
- `docs/dev_history/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md` (~2472 lines)
- `SeLe4n/Kernel/API.lean` (~2374 lines)
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` (~2369 lines)
- `docs/dev_history/audits/AUDIT_v0.25.14_WORKSTREAM_PLAN.md` (~2340 lines)
- `docs/dev_history/audits/AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md` (~2339 lines)
- `docs/audits/AUDIT_v0.30.11_DEEP_VERIFICATION.md` (~2326 lines)
- `SeLe4n/Model/State.lean` (~2226 lines)
- `tests/OperationChainSuite.lean` (~2208 lines)
- `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean` (~2187 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/DualQueueMembership.lean` (~2071 lines)
- `docs/spec/SELE4N_SPEC.md` (~2051 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/StoreObjectFrame.lean` (~1983 lines)
- `docs/dev_history/planning/V3_PROOF_CHAIN_HARDENING_E_G6_PLAN.md` (~1966 lines)
- `docs/dev_history/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md` (~1917 lines)
- `docs/dev_history/planning/V3E_IPC_UNWRAP_CAPS_LOOP_COMPOSITION_PLAN.md` (~1891 lines)
- `docs/dev_history/audits/AUDIT_v0.30.6_COMPREHENSIVE.md` (~1889 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/PerOperation.lean` (~1885 lines)
- `SeLe4n/Kernel/Capability/Operations.lean` (~1868 lines)
- `SeLe4n/Kernel/IPC/Invariant/Structural/QueueNextTransport.lean` (~1860 lines)
- `SeLe4n/Prelude.lean` (~1830 lines)
- `docs/dev_history/audits/AUDIT_v0.27.6_WORKSTREAM_PLAN.md` (~1801 lines)
- `docs/dev_history/audits/AUDIT_v0.25.21_WORKSTREAM_PLAN.md` (~1800 lines)
- `SeLe4n/Kernel/IPC/Invariant/QueueMembership.lean` (~1785 lines)
- `docs/dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md` (~1776 lines)
- `SeLe4n/Model/Object/Types.lean` (~1775 lines)
- `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` (~1753 lines)
- `docs/dev_history/audits/AUDIT_v0.25.14_COMPREHENSIVE.md` (~1739 lines)
- `docs/dev_history/audits/WORKSTREAM_PLAN_WS_O_SYSCALL_RUST_WRAPPERS.md` (~1725 lines)
- `docs/dev_history/AUDIT_v0.22.10_WORKSTREAM_PLAN.md` (~1674 lines)
- `SeLe4n/Model/FreezeProofs.lean` (~1661 lines)
- `tests/ModelIntegritySuite.lean` (~1643 lines)
- `tests/InformationFlowSuite.lean` (~1623 lines)
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` (~1590 lines)
- `SeLe4n/Kernel/Architecture/Invariant.lean` (~1524 lines)
- `docs/dev_history/audits/AUDIT_v0.28.0_WORKSTREAM_PLAN.md` (~1480 lines)
- `docs/dev_history/planning/V3B_LOAD_FACTOR_BOUNDED_MIGRATION_PLAN.md` (~1457 lines)
- `docs/dev_history/audits/AUDIT_v0.25.3_WORKSTREAM_PLAN.md` (~1452 lines)
- `docs/dev_history/AUDIT_v0.23.21_WORKSTREAM_PLAN.md` (~1411 lines)
- `docs/dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md` (~1382 lines)
- `docs/dev_history/audits/AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md` (~1357 lines)
- `docs/dev_history/audits/AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md` (~1342 lines)
- `docs/dev_history/audits/AUDIT_v0.22.17_WORKSTREAM_PLAN.md` (~1252 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` (~1181 lines)
- `docs/dev_history/audits/AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md` (~1178 lines)
- `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` (~1162 lines)
- `SeLe4n/Platform/DeviceTree.lean` (~1154 lines)
- `SeLe4n/Platform/RPi5/MmioAdapter.lean` (~1153 lines)
- `tests/KernelErrorMatrixSuite.lean` (~1139 lines)
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean` (~1111 lines)
- `SeLe4n/Kernel/RobinHood/Bridge.lean` (~1111 lines)
- `docs/planning/WS_RC_R4_TYPE_LEVEL_PROMOTION_PLAN.md` (~1102 lines)
- `docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md` (~1071 lines)
- `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean` (~1043 lines)
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean` (~1032 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Core.lean` (~1025 lines)
- `SeLe4n/Kernel/InformationFlow/Policy.lean` (~1023 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean` (~1018 lines)
- `docs/dev_history/audits/AUDIT_v0.19.6_WORKSTREAM_PLAN.md` (~984 lines)
- `SeLe4n/Kernel/FrozenOps/Operations.lean` (~983 lines)
- `SeLe4n/Machine.lean` (~977 lines)
- `docs/dev_history/planning/WS_X_LEAN_ETHEREUM_FORMALIZATION_PLAN.md` (~958 lines)
- `docs/dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md` (~930 lines)
- `SeLe4n/Kernel/Scheduler/Invariant.lean` (~922 lines)
- `docs/dev_history/audits/AUDIT_v0.28.0_COMPREHENSIVE.md` (~921 lines)
- `SeLe4n/Platform/FFI.lean` (~916 lines)
- `docs/dev_history/audits/AUDIT_H3_HARDWARE_BINDING_v0.25.27.md` (~911 lines)
- `docs/dev_history/audits/AUDIT_v0.25.10_WORKSTREAM_PLAN.md` (~909 lines)
- `docs/dev_history/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md` (~884 lines)
- `SeLe4n/Kernel/Scheduler/RunQueue.lean` (~883 lines)
- `docs/dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md` (~859 lines)
- `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/Signal.lean` (~851 lines)
- `SeLe4n/Kernel/IPC/Operations/SchedulerLemmas.lean` (~834 lines)
- `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean` (~827 lines)
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

- **WS-RC remediation workstream IN FLIGHT (v0.30.11 → v0.31.0 → v1.0.0,
  branch `claude/audit-workstream-planning-XsmKS`)**:
  Remediates the v0.30.11 audit cycle (comprehensive + deep verification)
  via 15 phases (R0..R14). Plan:
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
  ([`docs/audits/WS_RC_R5_DEFERRED_COMPLETION_PLAN.md`](docs/audits/WS_RC_R5_DEFERRED_COMPLETION_PLAN.md))
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
  ([`docs/audits/WS_RC_R4_CLOSEOUT_PLAN.md`](docs/audits/WS_RC_R4_CLOSEOUT_PLAN.md))
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
