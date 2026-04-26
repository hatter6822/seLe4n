# CLAUDE.md — seLe4n project guidance

## What this project is

seLe4n is a production-oriented microkernel written in Lean 4 with machine-checked
proofs, improving on seL4 architecture. Every kernel transition is an executable
pure function with zero `sorry`/`axiom`. First hardware target: Raspberry Pi 5.
Lean 4.28.0 toolchain, Lake build system, version 0.30.11.

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

A pre-commit hook enforces this automatically. Install it by running
`./scripts/install_git_hooks.sh` (invoked automatically by `setup_lean_env.sh`
and by the Lean Action CI workflow, so fresh clones and CI-cloned checkouts
are guarded without manual action). For CI contexts, `--check` verifies the
installer has run:

```bash
./scripts/install_git_hooks.sh          # install (idempotent no-op if present)
./scripts/install_git_hooks.sh --check  # verify installation (non-zero if absent/diverging)
./scripts/install_git_hooks.sh --force  # overwrite; backs up any diverging hook first
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
  TlbModel.lean                  TLB flush model + hardware adapter integration (AG6-F/G; AN9-B substantive `tlbBarrierComplete`)
  CacheModel.lean                AG8-B: Cache coherency model (D-cache/I-cache states, maintenance ops)
  BarrierComposition.lean        AN9-C: BarrierKind algebra + page-table / MMIO ordering theorems (DEF-A-M08/M09)
  TlbCacheComposition.lean       AN9-A: TLB+Cache composition theorem `pageTableUpdate_full_coherency` (DEF-A-M04)
  PageTable.lean                 AG6-A/B: ARMv8 4-level page table types, walk, W^X bridge
  VSpaceARMv8.lean               AG6-C/D: VSpaceBackend ARMv8 instance, shadow-based refinement
  AsidManager.lean               AG6-H: ASID pool allocator, rollover, uniqueness proof
  Adapter.lean                   Architecture adapter
  Assumptions.lean               Architecture assumptions
  Invariant.lean                 Architecture invariant re-export hub
  RegisterDecode.lean            Total deterministic decode: raw registers → typed kernel IDs
  SyscallArgDecode.lean          Per-syscall typed argument decode (msgRegs → typed structs)
  IpcBufferRead.lean             AK4-A: IPC-buffer overflow read helper (R-ABI-C01)
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
SeLe4n/Kernel/CrossSubsystem.lean Cross-subsystem invariants (R4-E; AN12-A discharge index marker)
SeLe4n/Kernel/Concurrency/Assumptions.lean  AN12-B SMP-latent assumption inventory (Theme 4.4)
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
tests/                           Executable test suites + fixtures (18 suites)
  DecodingSuite.lean             T-03/AC6-A + AK4-A: 57 tests for RegisterDecode + SyscallArgDecode + IPC-buffer merge
  AbiRoundtripSuite.lean         AK4-G: End-to-end ABI encode/decode integration (25 assertions)
  BadgeOverflowSuite.lean        AG9-E: 22 tests for Badge Nat↔UInt64 round-trip
  An9HardwareBindingSuite.lean   AN9: 23 surface-anchor tests for hardware-binding closure (DEF-A-M04..M09, DEF-C-M04, DEF-R-HAL-L14..L20)
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

**Known large files** (read in ≤500-line chunks) — refreshed v0.30.11 (AN12-I):
- `CHANGELOG.md` (~12592 lines)
- `tests/InformationFlowSuite.lean` (~1479 lines, AN11-D AK6 named tests)
- `tests/KernelErrorMatrixSuite.lean` (~957 lines, AN11-A new suite)
- `SeLe4n/Kernel/IPC/Invariant/Structural/DualQueueMembership.lean` (~2070 lines, AN3-C child)
- `SeLe4n/Kernel/IPC/Invariant/Structural/StoreObjectFrame.lean` (~1984 lines, AN3-C child)
- `SeLe4n/Kernel/IPC/Invariant/Structural/PerOperation.lean` (~1885 lines, AN3-C child)
- `SeLe4n/Kernel/IPC/Invariant/Structural/QueueNextTransport.lean` (~1859 lines, AN3-C child)
- `docs/dev_history/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md` (~4721 lines)
- `docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md` (~4130 lines, WS-AN canonical plan, archived at WS-AN closure)
- `docs/WORKSTREAM_HISTORY.md` (~4200 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~3857 lines)
- `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` (~3779 lines, AN5-B SCH-M03)
- `tests/NegativeStateSuite.lean` (~3660 lines)
- `SeLe4n/Kernel/CrossSubsystem.lean` (~3309 lines, AN12-A marker)
- `SeLe4n/Testing/MainTraceHarness.lean` (~3159 lines)
- `docs/gitbook/12-proof-and-invariant-map.md` (~2821 lines)
- `SeLe4n/Model/Object/Structures.lean` (~2772 lines)
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean` (~2745 lines)
- `SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean` (~2505 lines)
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` (~2369 lines)
- `SeLe4n/Kernel/API.lean` (~2374 lines)
- `tests/OperationChainSuite.lean` (~2208 lines)
- `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean` (~2186 lines)
- `SeLe4n/Model/State.lean` (~2226 lines)
- `SeLe4n/Platform/Boot.lean` (~2115 lines)
- `SeLe4n/Kernel/IPC/Invariant/QueueMembership.lean` (~1785 lines)
- `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` (~1753 lines)
- `SeLe4n/Model/Object/Types.lean` (~1759 lines)
- `SeLe4n/Model/FreezeProofs.lean` (~1661 lines)
- `SeLe4n/Kernel/Capability/Operations.lean` (~1858 lines)
- `SeLe4n/Prelude.lean` (~1830 lines)
- `docs/spec/SELE4N_SPEC.md` (~1904 lines)
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` (~1590 lines)
- `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/Signal.lean` (~850 lines, AN3-D child)
- `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/Wait.lean` (~688 lines, AN3-D child)
- `SeLe4n/Kernel/Capability/Invariant/Preservation/BadgeIpcCapsAndCdtMaps.lean` (~675 lines, AN4-F.3 child)
- `SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean` (~622 lines, AN4-F.3 child)
- `SeLe4n/Kernel/Capability/Invariant/Preservation/Revoke.lean` (~459 lines, AN4-F.3 child)
- `SeLe4n/Kernel/Capability/Invariant/Preservation/CopyMoveMutate.lean` (~353 lines, AN4-F.3 child)
- `SeLe4n/Kernel/Capability/Invariant/Preservation/Delete.lean` (~284 lines, AN4-F.3 child)
- `SeLe4n/Kernel/Capability/Invariant/Preservation/Insert.lean` (~229 lines, AN4-F.3 child)
- `SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean` (~764 lines, AN4-G.5 child)
- `SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean` (~460 lines, AN4-G.5 child)
- `SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean` (~279 lines, AN4-G.5 child)
- `SeLe4n/Kernel/Lifecycle/Operations/Cleanup.lean` (~204 lines, AN4-G.5 child)
- `docs/dev_history/audits/AUDIT_v0.28.0_WORKSTREAM_PLAN.md` (~1480 lines)
- `SeLe4n/Kernel/IPC/Invariant/CallReplyRecv/Call.lean` (~530 lines, AN3-D child)
- `SeLe4n/Kernel/IPC/Invariant/CallReplyRecv/ReplyRecv.lean` (~558 lines, AN3-D child)
- `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` (~1181 lines)
- `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean` (~1043 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean` (~1018 lines)
- `SeLe4n/Kernel/RobinHood/Bridge.lean` (~1111 lines)
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean` (~1032 lines)
- `SeLe4n/Kernel/FrozenOps/Operations.lean` (~983 lines)
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean` (~1056 lines)
- `SeLe4n/Kernel/Scheduler/RunQueue.lean` (~883 lines)
- `docs/dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md` (~2476 lines)
- `docs/dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md` (~3140 lines)

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
- **Internal-first naming**: every identifier in the codebase — theorems,
  functions, definitions, structures, fields, test runners, file names, and
  directory names — must describe the semantics of what it is (state update
  shape, preserved invariant, transition path, test subject). Workstream IDs,
  audit IDs, phase codes, and sub-task numbers (`WS-*`, `wsH*`, `AN3-*`, `AK7-*`,
  `ak9ce_01`, `an3b_02`, `I-H01`, etc.) **must not** appear in any identifier
  or file name. Example: rename a test from `an3b_02_projection_typing` to
  `ipc_invariant_full_projection_signatures`; rename a theorem from
  `ak7_cdt_hypothesis_discharge_index` to `cdt_hypothesis_discharge_index`.
  Rationale: workstream IDs are commit-time labels and age out as soon as a
  workstream closes — encoding them in identifiers creates documentation debt
  (every rename on workstream closure) and hides what the code actually
  means from anyone reading it outside the audit's temporal window.
  Legitimate places to reference a workstream ID: docstrings, commit messages,
  CHANGELOG entries, and `CLAUDE.md` / `docs/WORKSTREAM_HISTORY.md` prose.
  Historical identifiers that already encode workstream IDs (`ak8a_*`,
  `an2f3_*`, etc.) stay as-is until touched by a workstream that can rename
  them in the same commit; new code must comply with this rule from day one.

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

## Third-party attribution

seLe4n is GPLv3+ licensed (see `LICENSE`). The Rust workspace pulls a small
set of **build-time only** crates (`cc`, `find-msvc-tools`, `shlex`) to
assemble ARM64 boot assembly; no third-party code is linked into the
runtime kernel binary. Their upstream MIT copyright and permission notices
are reproduced verbatim in `THIRD_PARTY_LICENSES.md` at repo root. Rules:

1. If you add a runtime dependency (`[dependencies]` of any crate under
   `rust/`), update `THIRD_PARTY_LICENSES.md` in the same PR with the
   verbatim upstream MIT/Apache copyright lines and add the path to
   `scripts/website_link_manifest.txt` if it's not already there.
2. If you bump an existing external crate, re-check the upstream
   `LICENSE-MIT` and upstream Cargo.toml for authorship/copyright changes
   and sync `THIRD_PARTY_LICENSES.md` accordingly. Also re-check for a
   new upstream `NOTICE` file (Apache-2.0 § 4(d) propagation).
3. Prefer `core::*` and hand-written minimal code over pulling in a crate.
   A microkernel's trusted computing base must stay small.

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
