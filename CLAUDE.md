# CLAUDE.md — seLe4n project guidance

## What this project is

seLe4n is a production-oriented microkernel written in Lean 4 with machine-checked
proofs, improving on seL4 architecture. Every kernel transition is an executable
pure function with zero `sorry`/`axiom`. First hardware target: Raspberry Pi 5.
Lean 4.28.0 toolchain, Lake build system, version 0.25.23.

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

For example, if you modified `SeLe4n/Kernel/RobinHood/Bridge.lean`:
```bash
lake build SeLe4n.Kernel.RobinHood.Bridge
```

**`lake build` (default target) is NOT sufficient.** The default target only
builds modules reachable from `Main.lean` and test executables. Modules that
are not yet imported by the main kernel (e.g., `RobinHood` before N4
integration) will silently pass `lake build` even with broken proofs.

A pre-commit hook enforces this automatically. Install it:
```bash
cp scripts/pre-commit-lean-build.sh .git/hooks/pre-commit
```

The hook:
1. Detects staged `.lean` files
2. Builds each modified module via `lake build <Module.Path>`
3. Checks for `sorry` in staged content
4. **Blocks the commit** if any build fails or sorry is found

Do NOT bypass the hook with `--no-verify`.

## Source layout

```
SeLe4n/Prelude.lean              Typed identifiers, monad foundations
SeLe4n/Machine.lean              Machine state primitives
SeLe4n/Model/Object.lean         Kernel objects (re-export hub)
  Object/Types.lean              Core data types, TCB, Endpoint, Notification
  Object/Structures.lean         VSpaceRoot, CNode, KernelObject, CDT helpers
SeLe4n/Model/State.lean          Kernel/system state representation
SeLe4n/Model/IntermediateState.lean  Q3-A: Builder-phase state with invariant witnesses
SeLe4n/Model/Builder.lean        Q3-B: Builder operations (invariant-preserving state construction)
SeLe4n/Model/FrozenState.lean    Q5: FrozenMap, FrozenSet, FrozenSystemState, freeze function
SeLe4n/Model/FreezeProofs.lean   Q6: Freeze correctness proofs (lookup equiv, radix equiv, invariant transfer)
SeLe4n/Kernel/Scheduler/*        Scheduler transitions + invariants
  Operations.lean                Re-export hub
    Operations/Selection.lean    EDF predicates, thread selection
    Operations/Core.lean         Core transitions (schedule, handleYield, timerTick)
    Operations/Preservation.lean Scheduler invariant preservation theorems
  PriorityInheritance.lean       Re-export hub (D4)
    PriorityInheritance/BlockingGraph.lean   Blocking relation, chain walk, acyclicity, depth bound
    PriorityInheritance/Compute.lean         computeMaxWaiterPriority
    PriorityInheritance/Propagate.lean       updatePipBoost, propagate/revert priority inheritance
    PriorityInheritance/Preservation.lean    Frame lemmas (scheduler, IPC, cross-subsystem)
    PriorityInheritance/BoundedInversion.lean Parametric WCRT bound, determinism
  Liveness.lean                  Re-export hub (D5)
    Liveness/TraceModel.lean     Trace model types, query predicates, counting functions
    Liveness/TimerTick.lean      Timer-tick budget monotonicity, preemption bounds
    Liveness/Replenishment.lean  CBS replenishment timing bounds
    Liveness/Yield.lean          Yield/rotation semantics, FIFO progress bounds
    Liveness/BandExhaustion.lean Priority-band exhaustion analysis
    Liveness/DomainRotation.lean Domain rotation bounds
    Liveness/WCRT.lean           WCRT hypotheses, main theorem, PIP enhancement
SeLe4n/Kernel/Capability/*       CSpace/capability ops + invariants
  Invariant.lean                 Re-export hub
    Invariant/Defs.lean          Core invariant definitions, transfer theorems
    Invariant/Authority.lean     Authority reduction, badge routing
    Invariant/Preservation.lean  Operation preservation, lifecycle integration
SeLe4n/Kernel/IPC/*              IPC subsystem
  Operations.lean                Re-export hub
    Operations/Endpoint.lean     Core endpoint/notification ops
    Operations/CapTransfer.lean  IPC capability transfer (WS-M3)
    Operations/Timeout.lean      Z6 timeout-driven IPC unblocking
    Operations/Donation.lean     Z7: SchedContext donation wrappers + preservation proofs
    Operations/SchedulerLemmas.lean Scheduler preservation lemmas
  DualQueue.lean                 Re-export hub
    DualQueue/Core.lean          Dual-queue operations
    DualQueue/Transport.lean     Transport lemmas
    DualQueue/WithCaps.lean      DualQueue with capability transfer
  Invariant.lean                 Re-export hub
    Invariant/Defs.lean          Core IPC invariant definitions
    Invariant/EndpointPreservation.lean Endpoint preservation proofs
    Invariant/CallReplyRecv.lean Call/ReplyRecv preservation proofs
    Invariant/WaitingThreadHelpers.lean Primitive waitingThreadsPendingMessageNone helpers
    Invariant/NotificationPreservation.lean Notification preservation proofs
    Invariant/QueueNoDup.lean    V3-K: No self-loops, send/receive head disjointness
    Invariant/QueueMembership.lean V3-J: Queue membership consistency proofs
    Invariant/QueueNextBlocking.lean V3-J-cross: queueNext blocking consistency proofs
    Invariant/Structural.lean    Structural invariants, composition theorems
SeLe4n/Kernel/Lifecycle/*        Lifecycle/retype transitions + invariants
  Suspend.lean                   D1: Thread suspension/resumption operations
  Invariant/SuspendPreservation.lean  D1: Transport lemmas for suspend/resume
SeLe4n/Kernel/Service/*          Service orchestration + policy
  Interface.lean                 Service interface definitions
  Operations.lean                Service operations
  Registry.lean                  Service registry
  Registry/Invariant.lean        Registry invariant proofs
  Invariant.lean                 Re-export hub
    Invariant/Policy.lean        Policy surface, bridge theorems
    Invariant/Acyclicity.lean    Dependency acyclicity proofs
SeLe4n/Kernel/Architecture/*     Architecture assumptions + VSpace + VSpaceBackend + RegisterDecode
  VSpace.lean                    VSpace HashMap map/unmap/lookup, W^X enforcement
  VSpaceBackend.lean             VSpace backend operations
  VSpaceInvariant.lean           VSpace invariant proofs
  TlbModel.lean                  TLB flush model
  Adapter.lean                   Architecture adapter
  Assumptions.lean               Architecture assumptions
  Invariant.lean                 Architecture invariant re-export hub
  RegisterDecode.lean            Total deterministic decode: raw registers → typed kernel IDs
  SyscallArgDecode.lean          Per-syscall typed argument decode (msgRegs → typed structs)
  IpcBufferValidation.lean       D3: IPC buffer address validation and setIPCBufferOp
SeLe4n/Kernel/InformationFlow/*  Security labels, projection, non-interference
  Enforcement.lean               Re-export hub
    Enforcement/Wrappers.lean    Policy-gated operation wrappers
    Enforcement/Soundness.lean   Correctness theorems, declassification
  Invariant.lean                 Re-export hub
    Invariant/Helpers.lean       Shared NI proof infrastructure
    Invariant/Operations.lean    Per-operation NI proofs
    Invariant/Composition.lean   Trace composition, declassification
SeLe4n/Kernel/RobinHood/*        Robin Hood hash table verified implementation
  Core.lean                      Types, operations, proofs (N1 complete)
  Set.lean                       RHSet type (hash-set wrapper over RHTable)
  Bridge.lean                    Kernel API bridge: instances, bridge lemmas, filter (N3)
  Invariant.lean                 Re-export hub (N2)
    Invariant/Defs.lean          Invariant definitions, empty table proofs, probeChainDominant
    Invariant/Preservation.lean  WF, distCorrect, noDupKeys, PCD preservation (all ops), helpers
    Invariant/Lookup.lean        Functional correctness (get after insert/erase), key absence
SeLe4n/Kernel/SchedContext/*      Scheduling context types, CBS budget engine, replenishment queue, operations (Z1–Z5)
  Types.lean                     Budget, Period, SchedContext, SchedContextBinding, BEq instances
  Budget.lean                    CBS budget operations: consume, replenish, admission control
  ReplenishQueue.lean            System-wide replenishment queue: sorted insert, popDue, remove, invariants (Z3)
  Operations.lean                Capability-controlled SchedContext operations: configure, bind, unbind, yieldTo (Z5)
  PriorityManagement.lean        D2: setPriorityOp, setMCPriorityOp, MCP authority validation, run queue migration
  Invariant.lean                 Re-export hub (Z2)
    Invariant/Defs.lean          Invariant definitions, preservation proofs, bandwidth theorems
    Invariant/Preservation.lean  Per-operation preservation theorems for SchedContext operations (Z5)
    Invariant/PriorityPreservation.lean  D2: Transport lemmas, authority non-escalation proofs for priority ops
SeLe4n/Kernel/SchedContext.lean  Re-export hub
SeLe4n/Kernel/RadixTree/*        CNode radix tree verified flat array (Q4)
  Core.lean                      CNodeRadix type, extractBits, O(1) lookup/insert/erase/fold/toList
  Invariant.lean                 24 correctness proofs (lookup, WF, size, toList, fold)
  Bridge.lean                    buildCNodeRadix (RHTable → CNodeRadix), freezeCNodeSlots, bridge lemmas
SeLe4n/Kernel/FrozenOps/*        Frozen kernel operations (Q7, experimental — not in production chain)
  Core.lean                      FrozenKernel monad, lookup/store primitives
  Operations.lean                15 per-subsystem frozen operations
  Commutativity.lean             FrozenMap set/get? roundtrip proofs, frame lemmas
  Invariant.lean                 frozenStoreObject preservation theorems
SeLe4n/Kernel/CrossSubsystem.lean Cross-subsystem invariants (R4-E)
SeLe4n/Kernel/API.lean           Public kernel interface + syscall wrappers
SeLe4n/Platform/Contract.lean    PlatformBinding typeclass (H3-prep)
SeLe4n/Platform/DeviceTree.lean  FDT parsing with bounds-checked helpers
SeLe4n/Platform/Sim/*            Simulation platform contracts + proof hooks
  Sim/RuntimeContract.lean       Permissive + restrictive runtime contracts
  Sim/BootContract.lean          Boot + interrupt contracts (all True)
  Sim/ProofHooks.lean            AdapterProofHooks for restrictive contract
  Sim/Contract.lean              PlatformBinding instance (re-export hub)
SeLe4n/Platform/Boot.lean        Q3-C: Boot sequence (PlatformConfig → IntermediateState)
SeLe4n/Platform/RPi5/*           Raspberry Pi 5 platform (BCM2712)
  RPi5/Board.lean                BCM2712 addresses, MMIO, MachineConfig
  RPi5/RuntimeContract.lean      Substantive runtime + restrictive contract
  RPi5/BootContract.lean         Boot + interrupt contracts (GIC-400)
  RPi5/MmioAdapter.lean           MMIO adapter for RPi5
  RPi5/ProofHooks.lean           AdapterProofHooks for restrictive contract
  RPi5/Contract.lean             PlatformBinding instance (re-export hub)
SeLe4n/Testing/*                 Test harness, state builder, fixtures
  Helpers.lean                   Shared test helpers (expectError, expectOk, expectCond)
  StateBuilder.lean              Test state construction
  InvariantChecks.lean           Runtime invariant check helpers
  MainTraceHarness.lean          Main trace test harness
  RuntimeContractFixtures.lean   Platform contract test fixtures
Main.lean                        Executable entry point
tests/                           Executable test suites + fixtures
  DecodingSuite.lean             T-03/AC6-A: 40 tests for RegisterDecode + SyscallArgDecode
  LivenessSuite.lean             D5: 58 surface anchor tests for liveness/WCRT theorems
```

Note: Files marked "Re-export hub" are thin import-only files that preserve
backward compatibility. All existing `import` statements continue to work
unchanged. Actual implementations live in the listed submodules.

## Reading large files

Several files in this repo exceed 500 lines (invariant suites, audit plans,
specs). When reading any file, always use `offset` and `limit` parameters to
read in chunks rather than attempting the entire file at once:

```
Read(file_path, offset=1,   limit=500)   # lines 1-500
Read(file_path, offset=501, limit=500)   # lines 501-1000
```

**Known large files** (read in ≤500-line chunks):
- `SeLe4n/Kernel/IPC/Invariant/Structural.lean` (~7591 lines)
- `CHANGELOG.md` (~5285 lines)
- `tests/NegativeStateSuite.lean` (~3589 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` (~3466 lines)
- `SeLe4n/Testing/MainTraceHarness.lean` (~3114 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~2671 lines)
- `SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean` (~2504 lines)
- `SeLe4n/Model/Object/Structures.lean` (~2454 lines)
- `SeLe4n/Kernel/Capability/Invariant/Preservation.lean` (~2407 lines)
- `docs/dev_history/audits/AUDIT_v0.25.14_WORKSTREAM_PLAN.md` (~2340 lines)
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` (~2300 lines)
- `SeLe4n/Kernel/CrossSubsystem.lean` (~2211 lines)
- `tests/OperationChainSuite.lean` (~2208 lines)
- `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean` (~2186 lines)
- `docs/WORKSTREAM_HISTORY.md` (~1926 lines)
- `SeLe4n/Kernel/API.lean` (~1895 lines)
- `SeLe4n/Kernel/IPC/Invariant/QueueMembership.lean` (~1767 lines)
- `docs/dev_history/audits/AUDIT_v0.25.14_COMPREHENSIVE.md` (~1739 lines)
- `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` (~1653 lines)
- `SeLe4n/Model/State.lean` (~1569 lines)
- `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation.lean` (~1490 lines)
- `SeLe4n/Kernel/Capability/Operations.lean` (~1384 lines)
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` (~1380 lines)
- `SeLe4n/Model/FreezeProofs.lean` (~1372 lines)
- `SeLe4n/Prelude.lean` (~1355 lines)
- `SeLe4n/Kernel/Lifecycle/Operations.lean` (~1350 lines)
- `SeLe4n/Model/Object/Types.lean` (~1290 lines)
- `SeLe4n/Platform/Boot.lean` (~1270 lines)
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean` (~1084 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` (~1076 lines)
- `SeLe4n/Kernel/IPC/Invariant/CallReplyRecv.lean` (~1069 lines)
- `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean` (~1012 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean` (~1006 lines)
- `SeLe4n/Kernel/RobinHood/Bridge.lean` (~994 lines)
- `docs/spec/SELE4N_SPEC.md` (~969 lines)
- `tests/InformationFlowSuite.lean` (~969 lines)
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean` (~949 lines)
- `SeLe4n/Kernel/FrozenOps/Operations.lean` (~939 lines)
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean` (~895 lines)
- `SeLe4n/Kernel/Scheduler/RunQueue.lean` (~869 lines)
- `docs/gitbook/12-proof-and-invariant-map.md` (~2714 lines)
- `docs/dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md` (~2476 lines)
- `docs/dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md` (~3140 lines)
- `docs/dev_history/audits/AUDIT_v0.19.6_WORKSTREAM_PLAN.md` (~984 lines)

When editing large files, read the specific region around the target lines
first (e.g., `offset=380, limit=40`) rather than the whole file. This avoids
context-window pressure and "file too large" errors.

## Writing and editing large files

The Write tool replaces an entire file in one call. For files over ~100 lines
this is error-prone: the tool call **times out**, content gets silently
truncated, sections are accidentally dropped, and the context window fills up.
**Prefer the Edit tool for all changes to existing files**, regardless of size.

**Hard limit — Write tool timeout prevention:**

The Write tool will time out if the inline content is too large. To avoid this:

- **Never pass more than 100 lines of content in a single Write call.** Files
  at or above this threshold must be built incrementally (skeleton + Edit
  appends) or written via Bash `cat <<'HEREDOC'` to a file.
- **For existing files, never use Write at all.** Always use Edit with targeted
  `old_string`/`new_string` pairs. Edit calls do not carry the full file
  content and therefore do not time out.
- **If a Write call times out or fails**, do not retry with the same large
  content. Switch to the incremental approach below.

**Rules for large-file changes:**

1. **Never rewrite a large file with Write.** Use Edit with a precise
   `old_string`/`new_string` pair targeting only the lines that change. This is
   safer, faster, and avoids timeouts.
2. **One logical change per Edit call.** If you need to change three separate
   functions, make three Edit calls rather than one giant replacement that spans
   the whole file.
3. **Read before you edit.** Always Read the specific region first
   (e.g., `offset=350, limit=50`) so the `old_string` matches exactly,
   including indentation and whitespace.
4. **Adding large new sections.** If you must insert more than ~80 new lines
   into an existing file, break the insertion into multiple sequential Edit
   calls (each ≤80 lines), anchoring each one to context already present in the
   file.
5. **Creating new large files.** When a new file must exceed ~100 lines, build
   it incrementally:
   - Write an initial skeleton (imports, structure, first section) with Write,
     keeping the content **under 100 lines**.
   - Use successive Edit calls to append remaining sections, using the end of
     the previously written content as the `old_string` anchor.
   - Each Edit append should add no more than ~80 lines at a time.
   - Verify the final line count with `wc -l` via Bash.
   - **Alternative**: use Bash with a heredoc to write the full file in one
     shot (`cat <<'EOF' > path/to/file.lean`). Bash does not have the same
     content-size timeout as the Write tool.
6. **Post-write verification.** After any large write or series of edits, spot-
   check the result by reading the modified region (and the file's last few
   lines) to confirm nothing was truncated or duplicated.

**Example — appending a new theorem block to an invariant file:**

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

**Example — creating a new 300-line file without timing out:**

```
# Step 1: Write skeleton (under 100 lines)
Write("SeLe4n/Kernel/NewModule/Operations.lean", "<imports + first ~80 lines>")

# Step 2: Append next section via Edit
Edit(file_path="SeLe4n/Kernel/NewModule/Operations.lean",
     old_string="<last 2-3 lines from step 1>",
     new_string="<those same lines>\n<next ~80 lines>")

# Step 3: Repeat Edit appends until complete

# Step 4: Verify
Bash("wc -l SeLe4n/Kernel/NewModule/Operations.lean")
```

## Handling large search and command output

Grep and other search tools can return oversized results in this codebase.
Always constrain output to avoid truncation and context-window pressure:

- **Grep**: Use `head_limit` to cap results (e.g., `head_limit=30`). If more
  results exist, paginate with `offset` (e.g., `offset=30, head_limit=30` for
  the next batch). Prefer `output_mode: "files_with_matches"` first to identify
  relevant files, then switch to `output_mode: "content"` on specific files.
- **Glob**: Use `path` to narrow the search directory instead of searching the
  entire repo. If results are numerous, combine with Grep on specific matches.
- **Bash commands** (`lake build`, test scripts, etc.): Pipe through `head` or
  `tail` when output may be large (e.g., `lake build 2>&1 | tail -80`). For
  very large output, redirect to a temp file and read in chunks:
  ```bash
  lake build 2>&1 > /tmp/build.log
  ```
  Then use `Read("/tmp/build.log", offset=1, limit=500)` to page through it.

**Rule of thumb**: if a command or search might return more than ~100 lines,
limit it upfront. Paginate through results rather than requesting everything
at once.

## Background agent file-change protection

Background agents (launched via the Task tool with `run_in_background: true`)
run concurrently and may finish after the foreground agent has already modified
the same files. When this happens the background agent's stale writes silently
overwrite the foreground agent's progress. **You must prevent this.**

**Rules:**

1. **Never delegate file writes to a background agent for files you may also
   edit.** Before launching a background agent, identify every file it might
   create or modify. If there is any chance the foreground agent (you) will
   touch the same file while the background agent runs, do **not** run that
   agent in the background — run it in the foreground instead, or restructure
   the work so there is no file overlap.
2. **Partition files strictly.** When parallel work is genuinely needed, assign
   each agent a disjoint set of files. Document the partition in your task
   prompt to the background agent (e.g., "You own `Foo.lean` and `Bar.lean`
   only — do not modify any other file"). The foreground agent must not touch
   those files until the background agent completes.
3. **Use background agents only for read-only or independent-file tasks.** Safe
   uses include: running builds/tests, searching the codebase, reading files
   for research, or writing to files that the foreground agent will never edit
   during this session. Unsafe uses include: editing shared source files,
   modifying configuration files, or any task where the output files overlap
   with foreground work.
4. **Check background results before acting on shared state.** When a background
   agent finishes, read its output and verify whether it touched any files. If
   it wrote to a file you have since modified, discard the background agent's
   version and redo that work on top of your current file state.
5. **When in doubt, run in foreground.** The performance benefit of background
   execution is never worth the risk of silently lost work. Prefer sequential
   correctness over parallel speed.

**Example — safe background usage:**

```
# Background agent runs tests (read-only, no file writes)
Task(subagent_type="Bash", run_in_background=true,
     prompt="Run ./scripts/test_smoke.sh and report results")

# Meanwhile, foreground edits Operations.lean — no conflict
Edit("SeLe4n/Kernel/Scheduler/Operations.lean", ...)
```

**Example — unsafe pattern to avoid:**

```
# WRONG: background agent will edit Invariant.lean
Task(subagent_type="general-purpose", run_in_background=true,
     prompt="Add theorem X to Invariant.lean")

# Foreground also edits Invariant.lean — background will overwrite!
Edit("SeLe4n/Kernel/Scheduler/Invariant.lean", ...)
```

## Key conventions

- **Invariant/Operations split**: each kernel subsystem has `Operations.lean`
  (transitions) and `Invariant.lean` (proofs). Keep this separation.
- **No axiom/sorry**: forbidden in production proof surface. Tracked exceptions
  must carry a `TPI-D*` annotation.
- **Deterministic semantics**: all transitions return explicit success/failure.
  Never introduce non-deterministic branches.
- **Fixture-backed evidence**: `Main.lean` output must match
  `tests/fixtures/main_trace_smoke.expected`. Update fixture only with rationale.
- **Typed identifiers**: `ThreadId`, `ObjId`, `CPtr`, `Slot`, `DomainId`, etc.
  are wrapper structures, not `Nat` aliases. Use explicit `.toNat`/`.ofNat`.
- **Internal-first naming**: theorem/function/definition names must describe
  semantics (state update shape, preserved invariant, transition path). Do **not**
  encode workstream IDs (`WS-*`, `wsH*`, etc.) in identifier names.

## Documentation rules

When changing behavior, theorems, or workstream status, update in the same PR:
1. `README.md` — metrics sync from `docs/codebase_map.json` (`readme_sync` key)
2. `docs/spec/SELE4N_SPEC.md`
3. `docs/DEVELOPMENT.md`
4. Affected GitBook chapter(s) — canonical root docs take priority over GitBook
5. `docs/CLAIM_EVIDENCE_INDEX.md` if claims change
6. `docs/WORKSTREAM_HISTORY.md` if workstream status changes
7. Regenerate `docs/codebase_map.json` if Lean sources changed

Canonical ownership: root `docs/` files own policy/spec text. GitBook chapters
under `docs/gitbook/` are mirrors that summarize and link to canonical sources.
`docs/WORKSTREAM_HISTORY.md` is the single canonical source for workstream
planning, status, and history.

## Website link protection

The project website ([sele4n.org](https://github.com/hatter6822/hatter6822.github.io))
links to source files, documentation, scripts, assets, and directories in this
repository.  Renaming or deleting any of these paths will produce 404 errors on
the website.

**Protected paths** are listed in `scripts/website_link_manifest.txt`.  The
Tier 0 hygiene check (`scripts/check_website_links.sh`, called from
`test_tier0_hygiene.sh`) verifies that every listed path still exists.  This
runs on every PR and push to main via CI.

**If you need to rename or remove a protected path:**
1. Update the website (`hatter6822.github.io`) to use the new path first.
2. Then update `scripts/website_link_manifest.txt` to match.
3. CI will pass only when the manifest and the repo tree are consistent.

## Ignoring dev_history

The `docs/dev_history/` directory contains milestone closeouts, prior audit reports
(v0.8.0–v0.9.32), completed workstream plans, and legacy GitBook chapters
retained only for historical traceability. **Do not read or reference files in
`docs/dev_history/` unless explicitly instructed.** All active documentation lives
under `docs/` and `docs/gitbook/`.

## Active workstream context

- **WS-AF Phase AF2 COMPLETE** (v0.25.23): Pre-Release Comprehensive Audit Remediation — Phase AF2: State & Model Hardening. 7 sub-tasks (AF2-A through AF2-G). Machine-checked `storeObject` capacity safety: `storeObject_existing_preserves_objectIndex_length` + `retypeFromUntyped_capacity_gated` + `storeObject_capacity_safe_of_existing` (AF-03), `SchedContextId.ofObjIdChecked` sentinel guard (AF-22), W^X proof obligation in builder-phase `mapPage` with `mapPage_wxCompliant` theorem (AF-24), `apiInvariantBundle_frozenDirect` scope documentation (AF-25), `RegisterFile` non-lawful BEq documentation (AF-23), CDT `descendantsOf` transitive closure completeness deferral documentation (AF-34). Zero sorry/axiom. See `docs/audits/AUDIT_v0.25.21_WORKSTREAM_PLAN.md`
- **WS-AF Phase AF1 COMPLETE** (v0.25.22): Pre-Release Comprehensive Audit Remediation — Phase AF1: Scheduler Correctness & Proof Gaps. 10 sub-tasks (AF1-A through AF1-J). `blockingAcyclic` added as 10th predicate of `crossSubsystemInvariant` (AF-01/HIGH-1), `bounded_scheduling_latency` renamed to `wcrtBound_unfold` (AF-02/HIGH-2), `pip_deterministic` renamed to `pip_congruence` (AF-13), `eventuallyExits` hypothesis documentation (AF-14), priority/domain fallback documentation (AF-10/AF-11), RunQueue.size and FIFO documentation (AF-40/AF-49), blockingServer pre-mutation read documentation (AF-29). New theorems: `blockingChain_step`, `blockingChain_congr`, `blockingAcyclic_frame`. Zero sorry/axiom. See `docs/audits/AUDIT_v0.25.21_WORKSTREAM_PLAN.md`
- **WS-AE Phase AE6 COMPLETE** (v0.25.21): Production Audit Remediation — Phase AE6: Testing, Documentation & Closure. 8 sub-tasks (AE6-A through AE6-H). PIP suite execution in test scripts (U-25), `buildChecked` upgrade for 4 test suites (T-07/T-F02/T-F03), `test_rust.sh` CI skip logging (T-F17), Rust ABI register comment fix (R-F01), CLAUDE.md large-file list refresh, documentation synchronization, fixture verification. Zero sorry/axiom. WS-AE portfolio complete. See `docs/dev_history/audits/AUDIT_v0.25.14_WORKSTREAM_PLAN.md`
- **WS-AE Phase AE5 COMPLETE** (v0.25.20): Production Audit Remediation — Phase AE5: Platform, Service & Cross-Subsystem. 7 sub-tasks (AE5-A through AE5-G). `collectQueueMembers` fuel-safe `Option` return (U-22), `registryEndpointUnique` invariant with duplicate endpoint rejection (U-20), `registryInterfaceValid` added to 9-predicate `crossSubsystemInvariant` (SVC-04), boot invariant bridge limitation documentation (U-21), NI boundary service orchestration documentation (U-10), `LabelingContextValid` deployment requirement documentation (IF-14). Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.25.14_WORKSTREAM_PLAN.md`
- **WS-AE Phase AE4 COMPLETE** (v0.25.19): Production Audit Remediation — Phase AE4: Capability, IPC & Architecture Hardening. 10 sub-tasks (AE4-A through AE4-J). CPtr masking in resolveCapAddress (U-17), VAddr canonicity in decodeVSpaceUnmapArgs (U-26), CDT acyclicity preservation proof with freshChild_not_reachable bridge (U-18), cdtMintCompleteness lifted to cross-subsystem composition (U-36), endpointQueueRemove fallback unreachability proofs (U-24), timeout sentinel dual-condition documentation (U-23), TLB targeted flush H3 preparation documentation (U-27), ipcBuffer_within_page theorem (U-32), receiverSlotBase plumbing documentation (U-37). Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.25.14_WORKSTREAM_PLAN.md`
- **WS-AE Phase AE3 COMPLETE** (v0.25.18): Production Audit Remediation — Phase AE3: Scheduler & SchedContext Correctness. 12 sub-tasks (AE3-A through AE3-L). Domain consistency enforcement (U-11), cancelDonation isActive+replenish queue fix (U-15), effective priority in resumeThread (U-16), handleYield gap documentation (S-03), schedContextConfigure replenishment queue reset (U-14), CBS bandwidth documentation (U-12/U-13), dead Budget.refill deletion (SC-06), frame theorem with full invExt threading (S-01), schedContextBind documentation (SC-09), timeoutBlockedThreads documentation (S-05). Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.25.14_WORKSTREAM_PLAN.md`
- **WS-AE Phase AE2 COMPLETE** (v0.25.16): Production Audit Remediation — Phase AE2: Data Structure Hardening & Production Reachability. 8 sub-tasks (AE2-A through AE2-H). RobinHood `4 ≤ capacity` enforcement (U-28), RadixTree checked build with key-bounds validation (U-29), fuel exhaustion documentation (U-30), FrozenOps partial mutation fix (U-31), FrozenOps experimental status documentation (U-02), Liveness production reachability via CrossSubsystem import (U-05), PIP transitive import verification (AE2-G). Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.25.14_WORKSTREAM_PLAN.md`
- **WS-AE Phase AE1 COMPLETE** (v0.25.15): Production Audit Remediation — Phase AE1: API Dispatch & NI Composition. 8 sub-tasks (AE1-A through AE1-H). Dispatch parity fixes (U-01/U-06), wildcard unreachability (U-07), switchDomain NI composition (IF-01/U-03), donation/PIP NI proofs (IF-02/U-04), master dispatch NI theorem (U-08). KernelOperation 32→34 constructors. Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.25.14_WORKSTREAM_PLAN.md`
- **WS-AD PORTFOLIO COMPLETE** (v0.25.11–v0.25.14): Pre-Release Audit Remediation — 5 phases (AD1–AD5). 21 findings (7 actionable, 2 already addressed, 12 no-action). Phase AD4 (F-08): 35 cross-subsystem bridge lemmas (2 core + 33 per-operation) covering ALL 33 kernel operations that modify `objects`. Phase AD5: documentation sync & closure. Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.25.10_WORKSTREAM_PLAN.md`
- **WS-AC PORTFOLIO COMPLETE** (v0.25.3–v0.25.10): Comprehensive Audit Remediation — 6 phases (AC1–AC6), 42 sub-tasks. 3 HIGH, 9 MEDIUM, 9 LOW findings addressed. Phase AC6 COMPLETE (documentation, testing & closure: T-03 DecodingSuite, audit errata, workstream history). Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.25.3_WORKSTREAM_PLAN.md`
- **WS-AB PORTFOLIO COMPLETE** (v0.24.0–v0.25.5): Deferred Operations & Liveness Completion — 6 phases, 90 sub-tasks. All 5 deferred seL4 operations implemented: suspend/resume (D1), setPriority/setMCPriority (D2), setIPCBuffer (D3). Priority Inheritance Protocol (D4). Bounded Latency Theorem WCRT = D*L_max + N*(B+P) (D5). API Surface Integration & Closure (D6). Rust ABI synchronized (SyscallId 25, KernelError 44). Zero sorry/axiom. See `docs/dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md`
- **WS-AA Phase AA2 COMPLETE**: CI & Infrastructure Hardening — 6 sub-tasks (AA2-A through AA2-F), all complete (v0.23.23). Zero sorry/axiom. See `docs/dev_history/AUDIT_v0.23.21_WORKSTREAM_PLAN.md`
- **Next milestone**: Raspberry Pi 5 hardware binding
- **Hardware target**: Raspberry Pi 5 (ARM64)

## PR checklist

- [ ] Workstream ID identified
- [ ] Scope is one coherent slice
- [ ] Transitions are explicit and deterministic
- [ ] Invariant/theorem updates paired with implementation
- [ ] `test_smoke.sh` passes (minimum); `test_full.sh` for theorem changes
- [ ] Documentation synchronized
- [ ] No website-linked paths renamed or removed (see `scripts/website_link_manifest.txt`)

## Vulnerability reporting

While executing any task in this codebase, if you discover a possible software
vulnerability that could reasonably warrant a CVE (Common Vulnerabilities and
Exposures) designation, you **must** immediately report it to the user before
continuing. This applies to vulnerabilities found in:

- **This project's code** — logic errors in transition semantics, capability
  checks, information-flow enforcement, or any other component that could lead
  to privilege escalation, information leakage, denial of service, or violation
  of security invariants.
- **Dependencies and toolchain** — known or suspected vulnerabilities in Lean,
  Lake, elan, or any vendored/imported library encountered during builds,
  updates, or code review.
- **Build and CI infrastructure** — insecure script patterns (e.g., command
  injection in shell scripts, unsafe file permissions, unvalidated inputs in
  test harnesses) that could be exploited in a development or CI environment.
- **Model/specification gaps** — cases where the formal model fails to capture
  a security-relevant behavior of the real seL4 kernel, creating a false
  assurance gap that could mask a real-world vulnerability.

**What to report:**

1. **Summary** — a concise description of the vulnerability.
2. **Location** — file path(s) and line number(s) where the issue exists.
3. **Severity estimate** — your assessment of impact (Critical / High / Medium
   / Low) and exploitability.
4. **Reproduction or evidence** — how the issue manifests or could be triggered.
5. **Suggested remediation** — if apparent, a recommended fix or mitigation.

**How to report:**

- Stop current work and surface the finding in your response immediately.
- Do **not** silently fix a CVE-worthy vulnerability — always flag it explicitly
  so it can be tracked, triaged, and disclosed appropriately.
- If the vulnerability is in a third-party dependency, note whether an upstream
  advisory already exists.

This requirement applies regardless of whether the vulnerability is directly
related to the current task. Vigilance during routine work is one of the most
effective ways to catch security issues early.
