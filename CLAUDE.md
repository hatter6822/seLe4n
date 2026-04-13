# CLAUDE.md — seLe4n project guidance

## What this project is

seLe4n is a production-oriented microkernel written in Lean 4 with machine-checked
proofs, improving on seL4 architecture. Every kernel transition is an executable
pure function with zero `sorry`/`axiom`. First hardware target: Raspberry Pi 5.
Lean 4.28.0 toolchain, Lake build system, version 0.28.0.

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
  VSpaceBackend.lean             VSpace backend operations + HashMap instance (AG3-H)
  VSpaceInvariant.lean           VSpace invariant proofs
  TlbModel.lean                  TLB flush model + hardware adapter integration (AG6-F/G)
  CacheModel.lean                AG8-B: Cache coherency model (D-cache/I-cache states, maintenance ops)
  PageTable.lean                 AG6-A/B: ARMv8 4-level page table types, walk, W^X bridge
  VSpaceARMv8.lean               AG6-C/D: VSpaceBackend ARMv8 instance, shadow-based refinement
  AsidManager.lean               AG6-H: ASID pool allocator, rollover, uniqueness proof
  Adapter.lean                   Architecture adapter
  Assumptions.lean               Architecture assumptions
  Invariant.lean                 Architecture invariant re-export hub
  RegisterDecode.lean            Total deterministic decode: raw registers → typed kernel IDs
  SyscallArgDecode.lean          Per-syscall typed argument decode (msgRegs → typed structs)
  IpcBufferValidation.lean       D3: IPC buffer address validation and setIPCBufferOp
  ExceptionModel.lean            AG3-C/F: ARM64 exception types, ESR classification, dispatch, EL0/EL1
  InterruptDispatch.lean         AG3-D: GIC-400 interrupt dispatch (acknowledge→handle→EOI)
  TimerModel.lean                AG3-E: Hardware timer binding (54 MHz RPi5, monotonicity proof)
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
tests/                           Executable test suites + fixtures (17 suites)
  DecodingSuite.lean             T-03/AC6-A: 40 tests for RegisterDecode + SyscallArgDecode
  BadgeOverflowSuite.lean        AG9-E: 22 tests for Badge Nat↔UInt64 round-trip
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

- **WS-AI Phase AI7 COMPLETE** (v0.28.0): Post-Audit Comprehensive Remediation — Phase AI7: Testing, Closure & Final Gate. 6 sub-tasks (AI7-A through AI7-F). AI7-A (L-17/LOW): Documented CBS admission truncation tolerance in `Budget.lean` and `Types.lean` — per-context error ≤ 1 per-mille, RPi5 impact ≤ 0.1 ms/context, aggregate ≤ 6.4% for ≤64 contexts; truncation-down matches seL4 MCS. AI7-B (L-26/LOW): Documented `lifecycleRetypeObject` public visibility rationale — 13+ proof chain files prevent `protected`; explicit L-26 annotation. AI7-C: Fixture verification — 225 trace lines match `main_trace_smoke.expected`. AI7-D: Version bump 0.27.11 → 0.28.0 (16 files, `check_version_sync.sh` passes). AI7-E: WORKSTREAM_HISTORY.md + CHANGELOG.md updated. AI7-F: CLAUDE.md active workstream context updated. Gate: `test_full.sh` + `cargo test --workspace` + `check_version_sync.sh` + zero sorry/axiom. **WS-AI PORTFOLIO COMPLETE** (v0.27.7–v0.28.0, 7 phases, 37 sub-tasks). See `docs/dev_history/audits/AUDIT_v0.27.6_WORKSTREAM_PLAN.md`
- **WS-AI Phase AI6 COMPLETE** (v0.27.12): Post-Audit Comprehensive Remediation — Phase AI6: Documentation & Proof Gaps. 7 sub-tasks (AI6-A through AI6-G). AI6-A: Scheduler documentation batch — M-02 `resolveExtraCaps` silent-drop spec cross-reference (API.lean), M-03 `RunQueue.size` proof-linking deferral note, M-23 `blockingChain` fuel-exhaustion cycle behavior (BlockingGraph.lean), M-24 `eventuallyExits` deployment scope with WCRT.lean cross-reference (BandExhaustion.lean), M-25 WCRT `hDomainActiveRunnable`/`hBandProgress` deployment obligation documentation (WCRT.lean). AI6-B: Platform & boot documentation batch — M-07 boot invariant bridge empty-config scope (Boot.lean), M-08 `fromDtb` H3 DTB parsing placeholder status (DeviceTree.lean), M-10 MMIO read RAM semantics sequential model limitation (RPi5/MmioAdapter.lean), M-11 VSpaceRoot boot exclusion traceability tag (Boot.lean). AI6-C: Architecture documentation batch — M-13 `physicalAddressBound` 2^52 proof-layer default clarification (VSpace.lean), M-16 D-cache→I-cache pipeline ordering hardware protocol requirement (CacheModel.lean), M-17 context switch TLB/ASID maintenance gap (Adapter.lean), M-18 cross-module TLB+cache+page table composition gap (Invariant.lean). AI6-D: Model & SchedContext documentation batch — M-21 `descendantsOf` fuel sufficiency TPI-DOC cross-reference with `edgeWellFounded` foundation (Structures.lean), L-02 `allTablesInvExtK` 17-deep tuple projection fragility with AF-26 design rationale (State.lean), L-13 `schedContextBind` thread-state gap seL4 MCS semantics rationale (Operations.lean). AI6-E: Stale reference fixes — L-15 removed nonexistent `maxBlockingDepth`/`blockingDepthBound` references, replaced with `objectIndex.length` bound explanation (BlockingGraph.lean); L-24 replaced stale "H3-prep stub" with substantive 6-condition contract description (RPi5/RuntimeContract.lean). AI6-F: SELE4N_SPEC.md sync — 4 new sections: §8.10.4 IPC Extra Capability Resolution silent-drop semantics (M-02), §8.14.1 WCRT Externalized Hypotheses (M-24/M-25), §8.14.2 Boot Invariant Bridge Scope (M-07), §8.14.3 MMIO Model Limitations (M-10). Gate: `test_full.sh` + doc sync + zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.27.6_WORKSTREAM_PLAN.md`
- **WS-AI Phase AI5 COMPLETE** (v0.27.11): Post-Audit Comprehensive Remediation — Phase AI5: Platform & Simulation Safety. 3 sub-tasks (AI5-A through AI5-C). AI5-A (H-01/HIGH): Replaced vacuously-true simulation boot contract predicates with substantive checks — `objectTypeMetadataConsistent` validates empty default object store, `capabilityRefMetadataConsistent` validates empty default capability reference table; 2 correctness proofs (proven by `rfl`). AI5-B (H-02/HIGH): Replaced accept-all simulation interrupt contract with GIC-400 range-bounded predicates — `irqLineSupported` restricts to INTIDs 0–223 (`irq.toNat < simMaxIrqId`), `irqHandlerMapped` requires handler registration for supported IRQs; `simMaxIrqId := 224`. AI5-C (M-19/MEDIUM): Added `isInsecureDefaultContext` runtime detector (Policy.lean) with sentinel-based O(1) check; `testLabelingContext` helper; guard wired into `syscallEntryChecked` (API.lean) returning `.error .policyDenied`; 2 correctness theorems; test sites updated. Gate: `lake build` + `test_smoke.sh` + `test_full.sh`. Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.27.6_WORKSTREAM_PLAN.md`
- **WS-AI Phase AI4 COMPLETE** (v0.27.10): Post-Audit Comprehensive Remediation — Phase AI4: IPC & SchedContext Hardening. 4 sub-tasks (AI4-A through AI4-D). AI4-A (M-01/MEDIUM): Wired `cleanupPreReceiveDonation` into `endpointReceiveDual` no-sender branch (Transport.lean) — prevents SchedContext leaks on abnormal receive-without-reply path; moved function from Donation.lean to Endpoint.lean (import cycle fix); created frame lemma suite in Defs.lean (`cleanupPreReceiveDonation_scheduler_eq`, `cleanupPreReceiveDonation_preserves_objects_invExt`, `returnDonatedSchedContext_notification_backward`, `returnDonatedSchedContext_endpoint_backward`, `cleanupPreReceiveDonation_tcb_forward`, `cleanupPreReceiveDonation_tcb_ipcState_backward`); updated 16+ preservation theorems across EndpointPreservation.lean, Structural.lean, InformationFlow/Invariant/Operations.lean. AI4-B (M-09/MEDIUM): DTB parser fuel exhaustion now returns `Except DeviceTreeParseError` — added `DeviceTreeParseError` type (`.fuelExhausted`/`.malformedBlob`); `parseFdtNodes` return type changed; sole caller `fromDtbFull` updated. AI4-C (L-05/LOW): Removed unused `_endpointId` parameter from `timeoutAwareReceive`; 2 test call sites updated. Gate: `lake build` + `test_smoke.sh`. Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.27.6_WORKSTREAM_PLAN.md`
- **WS-AI Phase AI3 COMPLETE** (v0.27.9): Post-Audit Comprehensive Remediation — Phase AI3: Scheduler & PIP Correctness. 4 sub-tasks (AI3-A through AI3-D). AI3-A (M-04/MEDIUM): Fixed `handleYield`, `timerTick`, `switchDomain` re-enqueue at base priority — now uses `effectiveRunQueuePriority` (base + PIP boost), preventing priority inversion on yield; added `effectiveRunQueuePriority` function, updated `schedulerPriorityMatch` invariant, updated `edfCurrentHasEarliestDeadline` with effective priority guard, updated 15+ preservation theorems and NI proofs. AI3-B (M-22/MEDIUM): Fixed `migrateRunQueueBucket` ignoring PIP boost — applies `max(newPriority, pipBoost)` on re-insert. AI3-C (L-09/LOW): Formally proved `saveOutgoingContext` silent-failure path unreachable under `currentThreadValid` — `saveOutgoingContext_always_succeeds_under_currentThreadValid` theorem. AI3-D (L-10/LOW): Added `configTimeSlicePositive` predicate + `default_configTimeSlicePositive` proof. Gate: `lake build` (256 jobs) + `test_smoke.sh`. Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.27.6_WORKSTREAM_PLAN.md`
- **WS-AI Phase AI2 COMPLETE** (v0.27.8): Post-Audit Comprehensive Remediation — Phase AI2: Interrupt & Architecture Safety. 5 sub-tasks (AI2-A through AI2-E). AI2-A (H-03/HIGH): Fixed missing EOI on interrupt dispatch error path in `InterruptDispatch.lean` — `interruptDispatchSequence` always sends `endOfInterrupt` regardless of handler outcome, preventing GIC lockup; new `interruptDispatchSequence_always_ok` theorem. AI2-B (M-14/MEDIUM): Surfaced error on VSpaceARMv8 `unmapPage` HW walk failure — added `VSpaceWalkError` type; changed return from `Option` to `Except VSpaceWalkError`; VSpaceBackend instance preserved via `unmapPageOpt` adapter. AI2-C (M-15/MEDIUM): Added TLB flush enforcement for ASID reuse — free-list reuse sets `requiresFlush := true`; new `asidAllocRequiresFlush` predicate + 3 theorems. AI2-D (M-20/MEDIUM): Documented `suspendThread` transient inconsistency window with H3-ATOMICITY annotation. Gate: `lake build` (256 jobs) + `test_smoke.sh` + `test_full.sh`. Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.27.6_WORKSTREAM_PLAN.md`
- **WS-AI Phase AI1 COMPLETE** (v0.27.7): Post-Audit Comprehensive Remediation — Phase AI1: Rust ABI & Trap Correctness. 5 sub-tasks (AI1-A through AI1-E). AI1-A (H-05/HIGH): Fixed exception error codes in `trap.rs` — alignment/unknown exceptions return discriminant 45 (`UserException`) instead of 43 (`AlignmentError`), matching Lean `ExceptionModel.lean:175-177`. Added `error_code` module with named constants. AI1-B (H-04/HIGH): SVC handler stub returns `NOT_IMPLEMENTED` (17) instead of success (0) — prevents userspace misinterpretation; TODO marker for WS-V/AG10 FFI wiring. AI1-C (M-26/MEDIUM): Eliminated dual timer reprogram — removed `increment_tick_count()` from `handle_irq()`; canonical tick path is `ffi_timer_reprogram()` in `ffi.rs`. AI1-D (M-27/MEDIUM): Made `BOOT_UART` safe with `AtomicBool`-based `UartLock` spinlock (disables interrupts before acquiring to prevent IRQ deadlock) — replaced `pub static mut` with module-private `BOOT_UART_INNER` + `UART_LOCK`; `kprint!` macro uses `with_boot_uart()`. Gate: `cargo test --workspace` (366 tests) + `cargo clippy --workspace` (0 warnings) + `test_smoke.sh`. Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.27.6_WORKSTREAM_PLAN.md`
- **WS-AH Phase AH5 COMPLETE** (v0.27.6): Pre-Release Comprehensive Audit Remediation — Phase AH5: Documentation, Testing & Closure. 6 sub-tasks (AH5-A through AH5-F). AH5-A (M-04/M-07): Design-rationale documentation — VSpaceRoot boot exclusion in `bootSafeObject` (Boot.lean), `pendingMessage` NI visibility in `projectKernelObject` (Projection.lean). AH5-B (M-05/M-06/L-13): Spec-level documentation in `SELE4N_SPEC.md` — Platform Testing Limitations (6.6), CNode Intermediate Rights (8.10.3), TPIDR_EL0/TLS (6.5.6). AH5-C (M-08/L-11/L-12): Defense-in-depth documentation — cross-subsystem composition (CrossSubsystem.lean), Badge constructor safety (Prelude.lean), MCP default rationale (Types.lean). AH5-D: Test fixture verification. AH5-E: Full documentation sync. AH5-F: Final gate. Gate: `test_full.sh` + `cargo test --workspace` + documentation sync. Zero sorry/axiom. **WS-AH PORTFOLIO COMPLETE** (v0.27.2–v0.27.6, 5 phases, 27 sub-tasks). See `docs/dev_history/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md`
- **WS-AH Phase AH4 COMPLETE** (v0.27.5): Pre-Release Comprehensive Audit Remediation — Phase AH4: Version Consistency & CI Automation. 6 sub-tasks (AH4-A through AH4-F). AH4-A (H-02/HIGH): Updated `KERNEL_VERSION` in `rust/sele4n-hal/src/boot.rs` from `0.26.8` to `0.27.5` — UART boot banner now prints correct version; Rust workspace version updated from `0.27.1` to `0.27.5`. AH4-B: CLAUDE.md version reference updated to `0.27.5`. AH4-C: `docs/spec/SELE4N_SPEC.md` package version updated to `0.27.5`. AH4-D: All 10 i18n README version badges updated to `0.27.5`. AH4-E: Created `scripts/check_version_sync.sh` — CI-safe script validating 15 version-bearing files against canonical `lakefile.toml` version. AH4-F: Integrated `check_version_sync.sh` into Tier 0 hygiene (`test_tier0_hygiene.sh`). Gate: `cargo test --workspace` + `test_smoke.sh` + `check_version_sync.sh`. Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md`
- **WS-AH Phase AH3 COMPLETE** (v0.27.4): Pre-Release Comprehensive Audit Remediation — Phase AH3: Capability, Architecture & Decode Hardening. 3 sub-tasks (AH3-A through AH3-C). AH3-A (L-04/LOW): Fixed `cspaceRevokeCdtStrict` CDT-orphan bug — error branch preserves CDT node instead of removing it on slot deletion failure; preservation theorem simplified. AH3-B (L-08/LOW): Refactored `setIPCBufferOp` to delegate to `storeObject` — eliminates manual struct-with replication; `setIPCBufferOp_capabilityRefs_eq` renamed to `setIPCBufferOp_capabilityRefs_cleaned`. AH3-C (L-14/LOW): Replaced hardcoded ASID limit `65536` with `maxASID : Nat` parameter in `decodeVSpaceMapArgs`/`decodeVSpaceUnmapArgs` — API dispatch passes `st.machine.maxASID`; 10+ theorems updated; delegation theorems restructured with `funext`; 12 test call sites updated. Gate: `lake build` (256 jobs) + `test_smoke.sh`. Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md`
- **WS-AH Phase AH2 COMPLETE** (v0.27.3): Pre-Release Comprehensive Audit Remediation — Phase AH2: IPC Donation Safety & Boot Pipeline. 7 sub-tasks (AH2-A through AH2-G). AH2-A/B (M-02/MEDIUM): `applyCallDonation` and `applyReplyDonation` return type changed from `SystemState` to `Except KernelError SystemState` — donation errors propagated instead of silently swallowed. AH2-C: 7 call sites updated (4 API.lean, 3 Donation.lean) + 4 test call sites + `dispatchWithCap_call_uses_withCaps` theorem. AH2-D: 4 preservation theorems updated to conditional postconditions (`applyCallDonation_scheduler_eq`, `applyCallDonation_machine_eq`, `applyReplyDonation_machine_eq`, `applyCallDonation_preserves_projection`). AH2-E (M-03/L-16): `defaultMachineConfig` constant + `PlatformConfig.machineConfig` field. AH2-F: `applyMachineConfig` integrated as final step of `bootFromPlatform`; 8 new preservation lemmas; `bootFromPlatform_machine_eq` replaced with `bootFromPlatform_machine_physicalAddressWidth` and `bootFromPlatform_machine_non_config_fields`. AH2-G (L-02/LOW): `timeoutAwareReceive` returns `.error .endpointQueueEmpty` for missing `pendingMessage`. Gate: `lake build` (256 jobs) + `test_smoke.sh`. Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md`
- **WS-AH Phase AH1 COMPLETE** (v0.27.2): Pre-Release Comprehensive Audit Remediation — Phase AH1: Critical IPC Dispatch Correctness. 5 sub-tasks (AH1-A through AH1-E). AH1-A (H-01/HIGH): `endpointSendDualChecked` delegates to `endpointSendDualWithCaps` (was `endpointSendDual`) — checked `.send` performs IPC capability transfer, 3 new params, return type `Kernel CapTransferSummary`. AH1-B: Updated `dispatchWithCapChecked` `.send` arm. AH1-C: 8 NI theorems updated (Wrappers, Soundness, Operations). AH1-D (M-01/MEDIUM): `validateVSpaceMapPermsForMemoryKind` wired into `.vspaceMap` dispatch — device memory execute permission blocked. AH1-E: 10 test call sites updated. Gate: `lake build` (256 jobs) + `test_smoke.sh` + `test_full.sh`. Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md`
- **WS-AG Phase AG9 COMPLETE** (v0.27.0): H3 Hardware Binding Audit Remediation — Phase AG9: Testing + Validation. 7 sub-tasks (AG9-A through AG9-G). AG9-A: QEMU integration testing (`scripts/test_qemu.sh`, boot validation, CI-safe skip). AG9-B: Hardware constant cross-check (`scripts/test_hw_crosscheck.sh`, 15 BCM2712 constants, `docs/hardware_validation/rpi5_cross_check.md`). AG9-C: WCRT empirical validation (`profiling.rs`, `LatencyStats`, PMCCNTR_EL0 cycle counter, `docs/hardware_validation/wcrt_empirical_validation.md`). AG9-D: RunQueue cache performance profiling (`docs/hardware_validation/runqueue_cache_performance.md`). AG9-E: Badge overflow validation (`tests/BadgeOverflowSuite.lean` — 22 tests, 7 Rust tests in sele4n-types, `docs/hardware_validation/badge_overflow_validation.md`). AG9-F: Speculation barriers (CSDB/SB in `barriers.rs`, exception dispatch CSDB in `trap.rs`, GIC dispatch CSDB in `gic.rs`, `speculation_safe_bound_check`, `has_feat_csv2`, 7 tests, clippy fixes in `mmio.rs`, `docs/hardware_validation/speculation_barriers.md`). AG9-G: Full RPi5 hardware test suite (`scripts/test_hw_full.sh`, 5-phase orchestration, `docs/hardware_validation/rpi5_full_test_report.md`). Gate: `lake build` + `test_smoke.sh` + `cargo test --workspace` (362 tests) + `cargo clippy --workspace` (0 warnings). Zero sorry/axiom. See `docs/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md`
- **WS-AG Phase AG8 COMPLETE** (v0.26.9): H3 Hardware Binding Audit Remediation — Phase AG8: Integration + Model Closure. 7 sub-tasks (AG8-A through AG8-G). AG8-A: Timeout sentinel → explicit `timedOut : Bool` TCB field (eliminates GPR x0 sentinel collision risk). AG8-B: Cache coherency model (`CacheModel.lean` — `CacheLineState`, `CacheState`, 5 operations, 17 preservation theorems). AG8-C: Memory barrier semantics (`BarrierKind`, `barrierOrdered`, 4 theorems in `MmioAdapter.lean` — trivially satisfied in sequential model). AG8-D: FrozenOps deferred to WS-V (experimental status maintained). AG8-E: CDT `descendantsOf` fuel sufficiency placeholders (`maxCdtDepth := 65536`, 2 placeholder theorems — substantive proofs deferred to WS-V). AG8-F: Donation chain k>2 cycle prevention building blocks (`donationChainAcyclic_general` re-extracts from `donationOwnerValid`, `blockedOnReply_cannot_call` — formal bridge to `blockingAcyclic` deferred to WS-V). AG8-G: Donation atomicity under interrupt disable (`donationAtomicRegion`, `donateSchedContext_machine_eq`). Fixed pre-existing simp warnings in RPi5 `RuntimeContract.lean`/`ProofHooks.lean`. Gate: `lake build` (256 jobs) + `test_full.sh`. Zero sorry/axiom. See `docs/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md`
- **WS-AG Phase AG7 COMPLETE** (v0.26.8): H3 Hardware Binding Audit Remediation — Phase AG7: FFI Bridge + Proof Hooks. 6 sub-tasks (AG7-A through AG7-F). Lean `@[extern]` FFI declarations for 17 Rust HAL functions (`FFI.lean`). MMIO volatile primitives + `MmioAdapter.lean`. Production `AdapterProofHooks` (`rpi5ProductionAdapterProofHooks`) with substantive preservation proofs for all 4 adapter paths. `proofLayerInvariantBundle` extended to 11 conjuncts (`notificationWaiterConsistent` added). Key theorems: `contextSwitchState_preserves_proofLayerInvariantBundle` (11-conjunct preservation through atomic context switch), `contextSwitchState_preserves_ipcInvariantFull` (15-conjunct IPC invariant with `passiveServerIdle` transfer), `rpi5Production_adapterContextSwitch_preserves` (end-to-end production contract context-switch preservation), `registerContextStableCheck_budget` (boolean→proposition budget bridge). TLB composition theorems verified complete from AG6. Gate: `lake build` (256 jobs) + `cargo test --workspace` + `test_smoke.sh` + `test_full.sh`. Zero sorry/axiom. See `docs/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md`
- **WS-AG Phase AG6 COMPLETE** (v0.26.7): H3 Hardware Binding Audit Remediation — Phase AG6: Memory Management (ARMv8 Page Tables). 9 sub-tasks (AG6-A through AG6-I). Lean: `PageTable.lean` — ARMv8 4-level page table descriptor types (`PageTableLevel`, `Shareability`, `AccessPermission`, `PageAttributes`, `PageTableDescriptor`), encode/decode (`descriptorToUInt64`/`uint64ToDescriptor`), `pageTableWalk` via structural recursion (no fuel), `pageTableWalk_deterministic`, W^X bridge `hwDescriptor_wxCompliant_bridge`. `VSpaceARMv8.lean` — `ARMv8VSpace` with shadow `VSpaceRoot`, `VSpaceBackend` instance (all 7 obligations discharged), `simulationRelation` + `lookupPage_refines` + `vspaceProperty_transfer` refinement proofs. `AsidManager.lean` — `AsidPool` bump allocator with generation tracking, free list reuse, exhaustion guard, `wellFormed` predicate, 3 preservation theorems, `asidPoolUnique` invariant. `TlbModel.lean` extensions — hardware adapter functions, 3 equivalence theorems, 3 consistency preservation theorems, `tlbBarrierComplete`, composition. Rust: `tlb.rs` — TLBI VMALLE1/VAE1/ASIDE1/VALE1 with DSB ISH + ISB. `cache.rs` — DC CIVAC/CVAC/IVAC/ZVA, IC IALLU/IALLUIS, `cache_range` aligned iteration. ~1005 lines Lean + ~406 lines Rust + ~113 lines TlbModel extensions. Gate: `cargo test --workspace` (306 tests) + `cargo clippy --workspace` (0 warnings) + `lake build` (256 jobs) + `test_smoke.sh` + `test_full.sh`. Zero sorry/axiom. See `docs/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md`
- **WS-AG Phase AG5 COMPLETE** (v0.26.6): H3 Hardware Binding Audit Remediation — Phase AG5: Interrupts + Timer. 7 sub-tasks (AG5-A through AG5-G). GIC-400 full driver (`gic.rs`): distributor init (GICD_CTLR/IGROUPR/IPRIORITYR/ITARGETSR/ICPENDR/ISENABLER), CPU interface init (GICC_PMR/BPR/CTLR), acknowledge/dispatch/EOI sequence with `dispatch_irq<F>()` generic handler, `init_gic()` convenience. ARM Generic Timer driver (`timer.rs`): system register accessors (CNTPCT_EL0, CNTFRQ_EL0, CNTP_CVAL_EL0, CNTP_CTL_EL0), `AtomicU64` state, `init_timer(tick_hz)`, `reprogram_timer()` counter-relative, RPi5 54 MHz default 1000 Hz. Interrupt management (`interrupts.rs`): `disable_interrupts()`/`restore_interrupts()`/`enable_irq()`/`with_interrupts_disabled<F,R>()` via DAIF register. Lean: `TimerInterruptBinding` in `TimerModel.lean`, `timerInterruptHandler` in `InterruptDispatch.lean`, `MachineState.interruptsEnabled` field + 10 frame theorems (including `withInterruptsDisabled_restores`), AG5-G atomicity proofs (5 preservation theorems in `ExceptionModel.lean`). `handleInterrupt` NI step (35th `KernelOperation`) + cross-subsystem bridge. Boot sequence updated (Phase 3: GIC→timer→IRQ enable). ~1184 lines added. Gate: `cargo test --workspace` (288 tests) + `cargo clippy --workspace` (0 warnings) + `lake build` (256 jobs) + `test_smoke.sh`. Zero sorry/axiom. See `docs/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md`
- **WS-AG Phase AG4 COMPLETE** (v0.26.5): H3 Hardware Binding Audit Remediation — Phase AG4: HAL Crate + Boot Foundation. 7 sub-tasks (AG4-A through AG4-G). New `sele4n-hal` Rust crate (4th workspace crate): ARM64 HAL with CPU instructions (WFE/WFI/NOP/ERET), memory barriers (DMB/DSB/ISB), system register accessors (MRS/MSR), PL011 UART driver (0xFE201000, 115200 8N1), MMU initialization (identity-mapped L1 block descriptors, MAIR/TCR/SCTLR), exception vector table (16 entries, 2048-byte aligned), trap entry/exit assembly (272-byte TrapFrame, full GPR save/restore), kernel linker script (0x80000 entry), boot sequence (BSS zero, stack setup, UART→MMU→VBAR). GIC-400 and timer stubs for AG5. ~900 lines Rust + ~300 lines assembly. Gate: `cargo test --workspace` (267 tests) + `cargo clippy --workspace` (0 warnings) + `lake build` + `test_smoke.sh`. Zero sorry/axiom. See `docs/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md`
- **WS-AG Phase AG3 COMPLETE** (v0.26.4): H3 Hardware Binding Audit Remediation — Phase AG3: Platform Model Completion. 8 sub-tasks (AG3-A through AG3-H). `classifyMemoryRegion` platform memory map classification (P-01). `applyMachineConfig` full field application with 6 new `MachineState` fields (P-04). ARM64 exception model with ESR classification and SVC→syscall dispatch (FINDING-04). Interrupt dispatch with GIC-400 acknowledge→handle→EOI sequence (FINDING-06). Hardware timer model binding at 54 MHz for RPi5 (FINDING-08). Exception level EL0/EL1 model with privilege predicates (H3-ARCH-05). System register file with read/write operations and frame lemmas (H3-ARCH-06). VSpaceBackend HashMap instance with all typeclass laws proven (H3-ARCH-10). KernelError 44→49 variants. Rust ABI synchronized: `error.rs` 5 new variants (VmFault=44..InvalidIrq=48), all conformance tests updated, 239 Rust tests pass. Gate: `lake build` + `test_full.sh` + `cargo test --workspace`. Zero sorry/axiom. See `docs/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md`
- **WS-AG Phase AG2 Audit COMPLETE** (v0.26.2): Post-implementation audit of AG2. Fixed critical `sched_context_configure` IPC buffer overflow bug — 5th parameter (domain) was never written to IPC buffer overflow slot, would cause stale domain read on ARM64 hardware. Added `&mut IpcBuffer` parameter matching `service_register` pattern. Clarified `DomainId::MAX_VALID` type-level vs ABI-level comment. Fixed CHANGELOG AG2-C version text. Gate: `cargo test --workspace` (239 tests), `cargo clippy --workspace` (0 warnings). Zero sorry/axiom.
- **WS-AG Phase AG2 COMPLETE** (v0.26.1): H3 Hardware Binding Audit Remediation — Phase AG2: Pre-Hardware Rust ABI Fixes. 3 sub-tasks (AG2-A through AG2-C). `MAX_DOMAIN` constant fix 255→15 matching Lean `numDomainsVal = 16` (R-05). `sele4n-sys/src/sched_context.rs` typed wrappers for syscalls 17-19 completing all 25 syscall coverage (R-01). Rust workspace version sync 0.25.6→0.26.1 (RUST-04). Bonus clippy fix in `tcb.rs`. Gate: `cargo test --workspace` (239 tests), `cargo clippy --workspace` (0 warnings). Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md`
- **WS-AG Phase AG1 COMPLETE** (v0.26.0): H3 Hardware Binding Audit Remediation — Phase AG1: Pre-Hardware Lean Code Fixes. 6 sub-tasks (AG1-A through AG1-F). CBS re-enqueue at effective priority with `resolveInsertPriority` helper, 5 call sites fixed (S-04). `timeoutBlockedThreads` diagnostic error collection (S-05). `uniqueWaiters` composed as 15th conjunct of `ipcInvariantFull` (F-T02). `bootFromPlatformWithWarnings` duplicate detection (P-03). `FrozenSchedulerState` `replenishQueue` field + 2 freeze proofs (F-F04). Runtime `crossSubsystemInvariant` checks — 10 decidable predicates (full coverage) integrated into test harness (T-01). Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md`
- **WS-AF PORTFOLIO COMPLETE** (v0.25.22–v0.25.27): Pre-Release Comprehensive Audit Remediation — 6 phases (AF1–AF6), 49 sub-tasks. Phase AF6 (v0.25.27): Rust ABI Fixes & Documentation Closure — `UnknownKernelError` variant (AF-20), `endpoint_reply_recv_checked` truncation detection (AF-21), stale comment fixes (AF-35/AF-36), `SchedContext` capability marker (AF-37), `IpcMessage.length` privacy (AF-38), shellcheck CI enforcement (AF-46), full documentation sync. Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.25.21_WORKSTREAM_PLAN.md`
- **WS-AF Phase AF5 COMPLETE** (v0.25.26): Pre-Release Comprehensive Audit Remediation — Phase AF5: IPC, Capability, Lifecycle & Documentation. 10 sub-tasks (AF5-A through AF5-J). Fixed stale `pendingMessage = none` documentation (AF-12), timeout sentinel H3 migration documentation (AF-04), `endpointQueueRemove` direct insert rationale (AF-06), Badge Nat round-trip safety documentation (AF-15), `donationChainAcyclic` 2-cycle scope documentation (AF-39), tuple projection maintenance burden documentation (AF-26), CSpace resolution layers documentation (AF-27), `suspendThread` re-lookup rationale (AF-28), FrozenOps operation count fix 21→24 with 4 missing table entries (AF-43), duplicate `cdt_only_preserves_projection` removal (AF-48), high-heartbeat proof fragility documentation (AF-31). Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.25.21_WORKSTREAM_PLAN.md`
- **WS-AF Phase AF4 COMPLETE** (v0.25.25): Pre-Release Comprehensive Audit Remediation — Phase AF4: Information Flow, Cross-Subsystem & SchedContext. 8 sub-tasks (AF4-A through AF4-H). All `native_decide` eliminated from codebase (TCB reduction): `enforcementBoundary_is_complete` upgraded to `decide` (AF-16), `crossSubsystem_pairwise_coverage_complete` upgraded to `decide` (AF-17), bonus `crossSubsystemInvariant_default` fix. Fuel-sufficiency formal argument sketch for `collectQueueMembers` (AF-07). `serviceHasPathTo` conservative fuel-exhaustion documentation (AF-18). `LabelingContextValid` seL4 separation kernel design cross-reference with `labelingContextValid_is_deployment_requirement` witness theorem (AF-33). CBS 8× bandwidth bound precision gap documentation (AF-08). `schedContextYieldTo` kernel-internal design documentation (AF-30/AF-47). Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.25.21_WORKSTREAM_PLAN.md`
- **WS-AF Phase AF3 COMPLETE** (v0.25.24): Pre-Release Comprehensive Audit Remediation — Phase AF3: Platform & DeviceTree Hardening. 7 sub-tasks (AF3-A through AF3-G). `parseFdtNodes` fuel-exhaustion fix: `go` and `parseNodeContents` return `none` on fuel exhaustion instead of silent truncation (AF-05), full MMIO write byte-range validation for `mmioWrite32` (`addr+3`), `mmioWrite64` (`addr+7`), and `mmioWrite32W1C` (`addr+3`) with 3 `_rejects_range_overflow` supplementary theorems (AF-09a), MMIO write-semantics model documentation (AF-09b), `extractPeripherals` 2-level depth limitation documentation (AF-32), `natKeysNoDup` opaque HashSet design tradeoff documentation (AF-19), four DTB/boot stub annotations: `classifyMemoryRegion` always-RAM (AF-41), `fromDtb` stub (AF-42), `bootFromPlatform` empty-config (AF-44), `applyMachineConfig` partial-copy (AF-45). Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.25.21_WORKSTREAM_PLAN.md`
- **WS-AF Phase AF2 COMPLETE** (v0.25.23): Pre-Release Comprehensive Audit Remediation — Phase AF2: State & Model Hardening. 7 sub-tasks (AF2-A through AF2-G). Machine-checked `storeObject` capacity safety: `storeObject_existing_preserves_objectIndex_length` + `retypeFromUntyped_capacity_gated` + `storeObject_capacity_safe_of_existing` (AF-03), `SchedContextId.ofObjIdChecked` sentinel guard (AF-22), W^X proof obligation in builder-phase `mapPage` with `mapPage_wxCompliant` theorem (AF-24), `apiInvariantBundle_frozenDirect` scope documentation (AF-25), `RegisterFile` non-lawful BEq documentation (AF-23), CDT `descendantsOf` transitive closure completeness deferral documentation (AF-34). Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.25.21_WORKSTREAM_PLAN.md`
- **WS-AF Phase AF1 COMPLETE** (v0.25.22): Pre-Release Comprehensive Audit Remediation — Phase AF1: Scheduler Correctness & Proof Gaps. 10 sub-tasks (AF1-A through AF1-J). `blockingAcyclic` added as 10th predicate of `crossSubsystemInvariant` (AF-01/HIGH-1), `bounded_scheduling_latency` renamed to `wcrtBound_unfold` (AF-02/HIGH-2), `pip_deterministic` renamed to `pip_congruence` (AF-13), `eventuallyExits` hypothesis documentation (AF-14), priority/domain fallback documentation (AF-10/AF-11), RunQueue.size and FIFO documentation (AF-40/AF-49), blockingServer pre-mutation read documentation (AF-29). New theorems: `blockingChain_step`, `blockingChain_congr`, `blockingAcyclic_frame`. Zero sorry/axiom. See `docs/dev_history/audits/AUDIT_v0.25.21_WORKSTREAM_PLAN.md`
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
- **Next milestone**: Raspberry Pi 5 hardware binding (WS-AG Phase AG10)
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
