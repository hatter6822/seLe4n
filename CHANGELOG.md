## v0.27.9 — WS-AI Phase AI3: Scheduler & PIP Correctness

Phase AI3 of WS-AI Post-Audit Comprehensive Remediation. Fixes priority
inheritance consistency in `handleYield`, `timerTick`, `switchDomain`, and
`migrateRunQueueBucket` by using effective priority (base + PIP boost) instead
of static base priority. Proves `saveOutgoingContext` silent-failure path
unreachable under `currentThreadValid`. Adds `configTimeSlicePositive` guard.
4 sub-tasks (AI3-A through AI3-D). Gate: `lake build` (256 jobs) +
`test_smoke.sh`. Zero sorry/axiom.

### Changes

- **AI3-A** (M-04/MEDIUM): Fixed `handleYield` re-enqueue at base priority in
  `Core.lean`. Now re-enqueues at `effectiveRunQueuePriority tcb` (max of base
  and PIP boost) instead of `tcb.priority`. `timerTick` and `switchDomain` also
  updated to use `effectiveRunQueuePriority`. Added `effectiveRunQueuePriority`
  function to `Invariant.lean` (PIP-boost aware priority computation). Updated
  `schedulerPriorityMatch` invariant to track effective priority. Updated
  `edfCurrentHasEarliestDeadline` with effective priority guard. Updated
  `schedulerPriorityMatch_insert` helper theorem. Updated 15+ preservation
  theorems in `Preservation.lean`. Updated NI proofs in
  `InformationFlow/Invariant/Operations.lean` and EDF proofs in
  `Architecture/Invariant.lean`.
- **AI3-B** (M-22/MEDIUM): Fixed `migrateRunQueueBucket` ignoring PIP boost in
  `PriorityManagement.lean`. Now applies PIP boost (`max(newPriority, pipBoost)`)
  when re-inserting threads. All 5 transport lemmas pass unchanged (function only
  modifies `scheduler.runQueue`).
- **AI3-C** (L-09/LOW): Added `saveOutgoingContext_always_succeeds_under_currentThreadValid`
  theorem to `Selection.lean`. Formally proves the TCB-miss error path in
  `saveOutgoingContext` is unreachable under the `currentThreadValid` invariant.
  Design rationale documented: keeping `SystemState` return type (not `Except`)
  avoids 100+ proof site cascade; unreachability proof provides equivalent formal
  assurance.
- **AI3-D** (L-10/LOW): Added `configTimeSlicePositive` predicate and
  `default_configTimeSlicePositive` theorem to `Invariant.lean`. Enforces
  `configDefaultTimeSlice > 0` at the invariant level. Default value of 5
  serves as the positivity guarantee.

### Infrastructure

- New `effectiveRunQueuePriority` function for PIP-boost aware priority computation
- `schedulerPriorityMatch` invariant updated to track effective priority
- `edfCurrentHasEarliestDeadline` updated with effective priority guard
- `configTimeSlicePositive` predicate + default theorem
- `saveOutgoingContext_always_succeeds_under_currentThreadValid` unreachability proof

---

## v0.27.8 — WS-AI Phase AI2: Interrupt & Architecture Safety

Phase AI2 of WS-AI Post-Audit Comprehensive Remediation. Fixes architecture-layer
issues affecting correctness on hardware: missing EOI on interrupt error path,
silent shadow/HW divergence in VSpaceARMv8 unmapPage, missing TLB flush
enforcement for ASID reuse, and transient metadata inconsistency in suspendThread.
5 sub-tasks (AI2-A through AI2-E). Gate: `lake build` (256 jobs) +
`test_smoke.sh` + `test_full.sh`. Zero sorry/axiom.

### Changes

- **AI2-A** (H-03/HIGH): Fixed missing EOI on interrupt dispatch error path in
  `InterruptDispatch.lean`. `interruptDispatchSequence` now always sends
  `endOfInterrupt` regardless of handler outcome, preventing GIC lockup on real
  hardware. Error path changed from `.error e` to `.ok ((), endOfInterrupt st intId)`.
  New theorem `interruptDispatchSequence_always_ok` proves the dispatch sequence
  always returns `.ok`. Matches Linux's unconditional EOI pattern.
- **AI2-B** (M-14/MEDIUM): Surfaced error on VSpaceARMv8 `unmapPage` HW walk
  failure. Added `VSpaceWalkError` type (`shadowUnmapFailed`, `walkFailedAtLevel`)
  in `VSpaceARMv8.lean`. Changed `ARMv8VSpace.unmapPage` return type from
  `Option ARMv8VSpace` to `Except VSpaceWalkError ARMv8VSpace`. Three wildcard
  arms that silently succeeded with shadow-only updates now return level-specific
  errors. VSpaceBackend instance preserved via `unmapPageOpt` adapter. Theorems
  `unmapPage_preserves_asid` and `unmapPage_shadow_eq` updated to `.ok` matching.
- **AI2-C** (M-15/MEDIUM): Added TLB flush enforcement for ASID reuse in
  `AsidManager.lean`. Free-list reuse path now sets `requiresFlush := true`
  (was `false`), forcing callers to perform TLB flush via `adapterFlushTlbByAsid`
  before reusing an ASID. New `asidAllocRequiresFlush` predicate and 3 theorems:
  `allocate_reuse_requires_flush` (free-list reuse requires flush),
  `allocate_rollover_requires_flush` (rollover requires flush),
  `allocate_fresh_no_flush` (fresh bump allocation is safe without flush).
- **AI2-D** (M-20/MEDIUM): Documented transient metadata inconsistency window
  in `suspendThread` (Suspend.lean). Added H3-ATOMICITY annotation documenting
  that the G2→G3→G4→G5→G6 sequence must execute atomically with interrupts
  disabled on hardware. Cross-references Rust HAL's `with_interrupts_disabled`.
- **AI2-E**: Phase gate — `lake build` (256 jobs), `test_smoke.sh`,
  `test_full.sh` all pass. Version sync verified.

### Infrastructure

- New `VSpaceWalkError` inductive type for architecture-layer error reporting
- New `asidAllocRequiresFlush` predicate + 3 theorems for type-level flush enforcement
- `interruptDispatchSequence_always_ok` theorem for interrupt dispatch correctness
- Codebase map regenerated
- Version bumped to 0.27.8 across 15 version-bearing files

---

## v0.27.7 — WS-AI Phase AI1: Rust ABI & Trap Correctness

Phase AI1 of WS-AI Post-Audit Comprehensive Remediation. Fixes all Rust-side
defects affecting the Lean–Rust ABI contract: wrong exception error codes, no-op
syscall handler, dual timer reprogram, and unsafe UART static. 5 sub-tasks
(AI1-A through AI1-E). Gate: `cargo test --workspace` (366 tests) +
`cargo clippy --workspace` (0 warnings). Zero sorry/axiom.

### Changes

- **AI1-A** (H-05/HIGH): Fixed exception error codes in `rust/sele4n-hal/src/trap.rs`.
  Alignment (PC_ALIGN, SP_ALIGN) and unknown exception handlers now return
  discriminant 45 (`UserException`) instead of 43 (`AlignmentError`). Aligns Rust
  trap handler with Lean `ExceptionModel.lean:175-177` mapping of `pcAlignment`,
  `spAlignment`, and `unknownReason` to `.error .userException`. Added `error_code`
  module with named constants (`VM_FAULT`, `USER_EXCEPTION`, `NOT_IMPLEMENTED`)
  replacing bare numeric literals for maintainability.
- **AI1-B** (H-04/HIGH): Updated SVC handler stub in `rust/sele4n-hal/src/trap.rs`.
  Changed return value from 0 (success) to `error_code::NOT_IMPLEMENTED` (17),
  preventing userspace from interpreting the no-op stub as success. Added TODO
  marker for WS-V/AG10 FFI wiring. Added tests verifying error code constants
  match `sele4n-types::KernelError` discriminants.
- **AI1-C** (M-26/MEDIUM): Eliminated dual timer reprogram path. Removed
  `increment_tick_count()` call from `handle_irq()` in `trap.rs` — canonical
  tick-increment path is `ffi_timer_reprogram()` (ffi.rs) which calls both
  `reprogram_timer()` and `increment_tick_count()`. IRQ handler now only
  re-arms the hardware timer. Prevents double-counting of ticks when both the
  IRQ handler and FFI bridge fire.
- **AI1-D** (M-27/MEDIUM): Made `BOOT_UART` safe with spinlock synchronization.
  Replaced `pub static mut BOOT_UART` (uart.rs) with `AtomicBool`-based
  `UartLock` — IRQ-safe spinlock that disables interrupts before acquiring the
  lock and restores them after release, preventing IRQ-handler deadlock on
  single-core systems. Updated `with_boot_uart()`, `init_boot_uart()`,
  `boot_puts()`, and `kprint!` macro to use lock-mediated access.
  `BOOT_UART_INNER` is now module-private. Eliminates undefined behavior from
  unsynchronized mutable static access after interrupts are enabled.
- **AI1-E**: Phase gate — `cargo test --workspace` (366 tests pass),
  `cargo clippy --workspace` (0 warnings), `test_smoke.sh` passes.

### Infrastructure

- 4 new unit tests in trap.rs (error code verification, SVC stub assertion)
- All Lean smoke tests continue to pass (no Lean changes in this phase)

---

## v0.27.6 — WS-AH Phase AH5: Documentation, Testing & Closure

Phase AH5 of WS-AH Pre-Release Comprehensive Audit Remediation. Documents all
findings requiring specification or code-comment updates (M-04, M-05, M-06, M-07,
M-08, L-11, L-12, L-13), synchronizes all project documentation, and passes the
full test gate. 6 sub-tasks (AH5-A through AH5-F). WS-AH PORTFOLIO COMPLETE.
Gate: `test_full.sh` + `cargo test --workspace` + documentation sync. Zero sorry/axiom.

### Changes

- **AH5-A** (M-04, M-07): Design-rationale documentation in source code.
  M-04: VSpaceRoot boot exclusion rationale added to `bootSafeObject` doc comment
  in `Platform/Boot.lean` — explains ASID manager dependency, tradeoff, and WS-V
  integration timeline. M-07: `pendingMessage` NI visibility analysis added to
  `projectKernelObject` TCB case in `InformationFlow/Projection.lean` — explains
  unreachability under `runnableThreadIpcReady`, `currentNotEndpointQueueHead`,
  and domain scheduling invariants.
- **AH5-B** (M-05, M-06, L-13): Specification-level documentation in
  `docs/spec/SELE4N_SPEC.md`. M-05: Platform Testing Limitations section (6.6) —
  simulation contract `True` propositions, RPi5 `registerContextStable` 6-condition
  gap, recommendation for `Sim.Restrictive` contract. M-06: CNode Intermediate
  Rights Divergence section (8.10.3) — `resolveCapAddress` skips intermediate
  `Read` rights, impact analysis, U-M25 reference. L-13: TPIDR_EL0 / TLS Gap
  section (6.5.6) — `RegisterFile` scope, integration timeline, `TrapFrame`
  space note.
- **AH5-C** (M-08, L-11, L-12): Defense-in-depth documentation in source code.
  M-08: Cross-subsystem composition coverage assessment in
  `Kernel/CrossSubsystem.lean` — 10-predicate, 45-pairwise analysis, remaining
  gap scenarios, WS-V deferral. L-11: Badge constructor safety analysis in
  `Prelude.lean` — 5 safety layers from `Badge.valid` to Rust ABI truncation.
  L-12: `maxControlledPriority` default rationale in `Model/Object/Types.lean` —
  seL4 divergence, `setPriorityOp` MCP enforcement, production recommendation.
- **AH5-D**: Test fixture verification — trace output matches expected fixture
  (documentation-only changes do not affect trace output).
- **AH5-E**: Full documentation synchronization — CHANGELOG, WORKSTREAM_HISTORY,
  DEVELOPMENT, README, CLAUDE.md, CLAIM_EVIDENCE_INDEX, SELE4N_SPEC, GitBook.
- **AH5-F**: Final gate — `test_full.sh` + `cargo test --workspace` + sorry/axiom
  scan + version sync + website link check.

### Infrastructure

- Version bump: `lakefile.toml` 0.27.5 → 0.27.6
- All 15 version-bearing files synchronized to 0.27.6
- WS-AH portfolio marked COMPLETE in all documentation surfaces

---

## v0.27.5 — WS-AH Phase AH4: Version Consistency & CI Automation

Phase AH4 of WS-AH Pre-Release Comprehensive Audit Remediation. Synchronizes
all version-bearing files to match the canonical `lakefile.toml` version (H-02/HIGH)
and adds automated CI enforcement to prevent future version drift. 6 sub-tasks
(AH4-A through AH4-F). Gate: `cargo test --workspace` + `test_smoke.sh` +
`check_version_sync.sh`. Zero sorry/axiom.

### Changes

- **AH4-A** (H-02 fix): Updated `KERNEL_VERSION` in `rust/sele4n-hal/src/boot.rs`
  from `0.26.8` to `0.27.5` — UART boot banner now prints the correct version.
  Updated Rust workspace version in `rust/Cargo.toml` from `0.27.1` to `0.27.5`
  (propagates to all 4 crates via workspace inheritance).
- **AH4-B**: Updated CLAUDE.md project description version reference from
  `0.26.9` to `0.27.5`.
- **AH4-C**: Updated `docs/spec/SELE4N_SPEC.md` "Package version" table entry
  from `0.27.0` to `0.27.5`.
- **AH4-D**: Updated all 10 i18n README version badges from `0.26.6` to `0.27.5`
  (ar, de, es, fr, hi, ja, ko, pt-BR, ru, zh-CN).
- **AH4-E**: Created `scripts/check_version_sync.sh` — CI-safe shell script
  that validates 15 version-bearing files (Rust HAL, Cargo workspace, spec,
  CLAUDE.md, 10 i18n READMEs) against the canonical `lakefile.toml` version.
  Follows project style (GPL header, `set -euo pipefail`, `SCRIPT_DIR`/
  `REPO_ROOT` pattern).
- **AH4-F**: Integrated `check_version_sync.sh` into Tier 0 hygiene
  (`scripts/test_tier0_hygiene.sh`) via `run_check "HYGIENE"` — version
  sync is now enforced on every PR and push to main.

### Infrastructure

- New file: `scripts/check_version_sync.sh`
- Version bump: `lakefile.toml` 0.27.4 → 0.27.5
- Main `README.md` badge updated to 0.27.5
- GitBook version references updated

---

## v0.27.4 — WS-AH Phase AH3: Capability, Architecture & Decode Hardening

Phase AH3 of WS-AH Pre-Release Comprehensive Audit Remediation. Fixes
CDT-orphaned capabilities on revocation failure (L-04/LOW), eliminates manual
`storeObject` replication in IPC buffer operations (L-08/LOW), and replaces
hardcoded ASID limits with platform-configured values (L-14/LOW). 3 sub-tasks
(AH3-A through AH3-C). Gate: `lake build` + `test_smoke.sh`. Zero sorry/axiom.

### Changes

- **AH3-A** (L-04 fix): Fixed `cspaceRevokeCdtStrict` CDT-orphan bug in
  `Capability/Operations.lean`. Error branch (slot deletion failure) now
  preserves CDT node (`stAcc`) instead of removing it
  (`{ stAcc with cdt := stAcc.cdt.removeNode node }`). Prevents orphaned
  capabilities that would violate `cdtMapsConsistent`. Preservation theorem
  in `Capability/Invariant/Preservation.lean` simplified — unchanged state
  trivially preserves invariants (`exact ih _ stAcc hI hKAcc`).
- **AH3-B** (L-08 fix): Refactored `setIPCBufferOp` in
  `Architecture/IpcBufferValidation.lean` to delegate TCB update to
  `storeObject` instead of manual struct-with replication of `objects`,
  `objectIndex`, `objectIndexSet`, `lifecycle` fields. Eliminates maintenance
  divergence risk as `storeObject` evolves. Updated 3 preservation theorems:
  `setIPCBufferOp_machine_eq` (storeObject unfold), `setIPCBufferOp_asidTable_eq`
  (simp with lookup hypothesis). Renamed `setIPCBufferOp_capabilityRefs_eq` to
  `setIPCBufferOp_capabilityRefs_cleaned` — conclusion now reflects canonical
  `storeObject` cleanup semantics (filter on cnode ≠ tid). Cross-subsystem
  bridge (`setIPCBuffer_crossSubsystemInvariant_bridge`) verified unchanged.
- **AH3-C** (L-14 fix): Added `(maxASID : Nat)` parameter to
  `decodeVSpaceMapArgs` and `decodeVSpaceUnmapArgs` in
  `Architecture/SyscallArgDecode.lean`, replacing hardcoded `65536`. API
  dispatch arms in `API.lean` pass `st.machine.maxASID`. Updated 10+ theorems
  with parameter threading. Delegation theorems (`dispatchWithCap_vspaceMap_delegates`,
  `dispatchWithCap_vspaceUnmap_delegates`) restructured from function-level to
  state-specific equality with `(st : SystemState)` parameter.
  `dispatchWithCap_layer2_decode_pure` proof uses `funext` for function
  extensionality. 12 test call sites updated across 3 files (6 DecodingSuite,
  5 NegativeStateSuite, 1 MainTraceHarness) with `65536` for backward
  compatibility.

### Infrastructure

- Regenerated `docs/codebase_map.json`

---

## v0.27.3 — WS-AH Phase AH2: IPC Donation Safety & Boot Pipeline

Phase AH2 of WS-AH Pre-Release Comprehensive Audit Remediation. Eliminates
silent error swallowing in IPC donation wrappers (M-02/MEDIUM), integrates
machine configuration into the boot pipeline (M-03/MEDIUM, L-16/LOW subsumed),
and fixes empty-message masking in timeout-aware receive (L-02/LOW). 7 sub-tasks
(AH2-A through AH2-G). Gate: `lake build` + `test_smoke.sh`. Zero sorry/axiom.

### Changes

- **AH2-A** (M-02 fix): Changed `applyCallDonation` return type from
  `SystemState` to `Except KernelError SystemState`. All 5 control-flow paths
  updated: 4 no-op paths return `.ok st`, error path (donation failure) now
  returns `.error e` instead of silently swallowing to `st`.
- **AH2-B** (M-02 fix): Changed `applyReplyDonation` return type from
  `SystemState` to `Except KernelError SystemState`. Same error propagation
  pattern as AH2-A, with additional `removeRunnable` on success path.
- **AH2-C** (M-02 fix): Updated 7 call sites (4 in API.lean, 3 in
  Donation.lean) from direct value binding (`let st'' := applyCallDonation ...`)
  to match-based error propagation (`match ... with | .error e => .error e |
  .ok st'' => ...`). Updated `dispatchWithCap_call_uses_withCaps` theorem RHS.
  Updated 4 test call sites in `MainTraceHarness.lean`.
- **AH2-D** (M-02 fix): Updated 4 preservation theorems to conditional
  postconditions: `applyCallDonation_scheduler_eq`,
  `applyCallDonation_machine_eq`, `applyReplyDonation_machine_eq` (all in
  Donation.lean), and `applyCallDonation_preserves_projection` (in
  InformationFlow/Invariant/Operations.lean). Each now takes an explicit
  `h : applyCallDonation/applyReplyDonation ... = .ok st'` hypothesis.
- **AH2-E** (M-03 fix): Added `defaultMachineConfig` constant to `Machine.lean`
  with ARM64 defaults (registerWidth=64, virtualAddressWidth=48,
  physicalAddressWidth=52, pageSize=4096, maxASID=65536, registerCount=32).
  Added `machineConfig : MachineConfig := defaultMachineConfig` field to
  `PlatformConfig`.
- **AH2-F** (M-03/L-16 fix): Integrated `applyMachineConfig` as final step of
  `bootFromPlatform`, ensuring machine state fields are always set from platform
  configuration. Moved `applyMachineConfig` definition before `bootFromPlatform`
  to resolve forward reference. Added 8 new `applyMachineConfig_*_eq`
  preservation lemmas (cdt, services, serviceRegistry, interfaceRegistry,
  asidTable, tlb, lifecycle, cdtNodeSlot). Updated 10+ `bootFromPlatform_*_eq`
  theorem proofs. Replaced `bootFromPlatform_machine_eq` with two new theorems:
  `bootFromPlatform_machine_physicalAddressWidth` and
  `bootFromPlatform_machine_non_config_fields`.
- **AH2-G** (L-02 fix): Changed `timeoutAwareReceive` to return
  `.error .endpointQueueEmpty` instead of `.ok (.completed IpcMessage.empty, st)`
  when `pendingMessage = none`, surfacing protocol violations instead of
  silently returning empty messages.

### Infrastructure

- Updated trace fixture (`main_trace_smoke.expected`) line 197: SCO-030 now
  shows `error SeLe4n.Model.KernelError.endpointQueueEmpty`
- Regenerated fixture SHA256 hash
- Regenerated `docs/codebase_map.json`

---

## v0.27.2 — WS-AH Phase AH1: Critical IPC Dispatch Correctness

Phase AH1 of WS-AH Pre-Release Comprehensive Audit Remediation. Fixes the two
most security-critical dispatch path issues: the checked `.send` path silently
dropping capability transfer (H-01/HIGH) and the device-memory execute
permission validation gap (M-01/MEDIUM). 5 sub-tasks (AH1-A through AH1-E).
Gate: `lake build` + `test_smoke.sh` + `test_full.sh`. Zero sorry/axiom.

### Changes

- **AH1-A** (H-01 fix): `endpointSendDualChecked` now delegates to
  `endpointSendDualWithCaps` (with capability transfer) instead of
  `endpointSendDual` (without). Three new parameters added: `endpointRights`,
  `senderCspaceRoot`, `receiverSlotBase`. Return type changed from
  `Kernel Unit` to `Kernel CapTransferSummary`. Checked `.send` path now
  performs IPC capability transfer on rendezvous, matching the unchecked path.
- **AH1-B** (H-01 fix): Updated `dispatchWithCapChecked` `.send` arm in
  API.lean to pass `cap.rights`, `gate.cspaceRoot`, and `decoded.capRecvSlot`
  to the updated `endpointSendDualChecked`.
- **AH1-C** (H-01 fix): Updated 8 theorems across 3 files:
  - `endpointSendDualChecked_eq_endpointSendDualWithCaps_when_allowed` (renamed
    from `*_eq_endpointSendDual_*`): equivalence with new WithCaps target
  - `endpointSendDualChecked_flowDenied`: added 3 new parameters
  - `endpointSendDualChecked_denied_preserves_state`: existential updated to
    `CapTransferSummary × SystemState`
  - `enforcement_sufficiency_endpointSendDual`: disjunction updated for WithCaps
  - `enforcementSoundness_endpointSendDualChecked`: added 3 params + result
  - `checkedDispatch_flowDenied_preserves_state`: conjunct 1 updated
  - `enforcementBridge_to_NonInterferenceStep`: conjunct 1 updated
  - `endpointSendDualChecked_NI`: updated to use WithCaps projection hypothesis
- **AH1-D** (M-01 fix): Wired `validateVSpaceMapPermsForMemoryKind` into the
  `.vspaceMap` dispatch arm in `dispatchCapabilityOnly`. Device regions with
  execute permission now return `.error .policyDenied` before reaching the
  map operation. Updated `dispatchWithCap_vspaceMap_delegates` theorem to
  reflect the two-step validation.
- **AH1-E** (H-01 fix): Updated 10 call sites across 3 test files
  (`MainTraceHarness.lean`, `InformationFlowSuite.lean`, `TraceSequenceProbe.lean`)
  to pass the new parameters with `default` values (test messages have no caps).
  Updated match patterns from `(.ok ((), st'))` to `(.ok (_, st'))` where needed
  for `CapTransferSummary` return type.

### Infrastructure

- Regenerated `docs/codebase_map.json` with updated metrics
- Documentation: WORKSTREAM_HISTORY.md, CHANGELOG.md, SELE4N_SPEC.md updated

---

## v0.27.1 — WS-AG Phase AG10: Documentation + Closure

Phase AG10 of WS-AG H3 Hardware Binding Audit Remediation. Closes the H3
workstream with comprehensive documentation of hardware binding architecture,
platform integration, and multi-core limitations. Synchronizes all documentation
surfaces (spec, README, GitBook, workstream history). 7 sub-tasks (AG10-A
through AG10-G). **WS-AG PORTFOLIO COMPLETE** (10 phases, 67 sub-tasks,
v0.26.0–v0.27.1).
Gate: `lake build` + `test_full.sh` + documentation sync. Zero sorry/axiom.

### Changes

- **AG10-A** (FINDING-05, Multi-Core Limitation Documentation): New
  "Hardware Limitations" section (6.4) in `SELE4N_SPEC.md` documenting
  single-core operation (core 0 only, 3 cores in WFE loop), SMP deferral
  to WS-V with requirements list (per-core run queues, IPI, spinlocks,
  MOESI cache coherency, per-core TLB coordination), sequential memory
  model note, and absence of multi-core invariants
- **AG10-B** (FINDING-07, IPC Buffer Alignment Documentation): New
  Section 8.5.1 in `SELE4N_SPEC.md` documenting 512-byte alignment (Lean),
  960-byte `#[repr(C)]` struct (Rust ABI), Cortex-A76 cache line justification,
  `ipcBuffer_within_page` theorem (1472 < 4096 page boundary)
- **AG10-C** (Architecture Assumptions Update): Extended
  `Architecture/Assumptions.lean` with comprehensive documentation for all
  AG3–AG8 architecture modules: exception model (AG3-C), interrupt dispatch
  (AG3-D), timer binding (AG3-E), exception levels (AG3-F), ARMv8 page tables
  (AG6-A/B), VSpace ARMv8 instance (AG6-C/D), ASID manager (AG6-H), TLB model
  (AG6-F/G), cache coherency model (AG8-B), and ARM64-specific constraints
- **AG10-D** (SELE4N_SPEC.md Major Update): New "Hardware Binding Architecture"
  section (6.5) with layered diagram and 5 subsections: Exception Handling
  (6.5.1), Interrupt Dispatch (6.5.2), Timer Binding (6.5.3), Memory Management
  ARMv8 (6.5.4), FFI Bridge (6.5.5). Updated H3 status to COMPLETE in Path to
  Hardware table. Updated NI constructor count 34→35
- **AG10-E** (Codebase Map Regeneration): Regenerated `docs/codebase_map.json`
  with updated version 0.27.1, 141 production files, 91,466 LoC
- **AG10-F** (WORKSTREAM_HISTORY.md Update): Added AG10 entry, changed WS-AG
  status from IN PROGRESS to PORTFOLIO COMPLETE
- **AG10-G** (README.md Metrics Sync): Updated metrics table (version, LoC,
  Rust crates, hardware binding status, single-core note), updated completed
  workstreams table with WS-AG and WS-AF, updated next milestone to WS-V

### Infrastructure

- Version bump: `lakefile.toml` and `rust/Cargo.toml` 0.27.0→0.27.1
- Documentation: SELE4N_SPEC.md (+206 lines), Assumptions.lean (+114 lines),
  WORKSTREAM_HISTORY.md, DEVELOPMENT.md, CLAIM_EVIDENCE_INDEX.md, GitBook
  chapters 01/05/10 updated
- Codebase map regenerated with updated metrics

---

## v0.27.0 — WS-AG Phase AG9: Testing + Validation

Phase AG9 of WS-AG H3 Hardware Binding Audit Remediation. Validates the H3
implementation through QEMU integration testing, hardware constant cross-checks,
empirical measurement infrastructure, Badge overflow validation, speculation
barrier hardening (Spectre v1/v2), and full RPi5 test suite orchestration.
7 sub-tasks (AG9-A through AG9-G).
Gate: `lake build` + `test_smoke.sh` + `cargo test --workspace` +
`cargo clippy --workspace` (0 warnings). Zero sorry/axiom.

### Changes

- **AG9-A** (QEMU Integration Testing): New `scripts/test_qemu.sh` automated
  test infrastructure for QEMU-based kernel validation. Builds kernel binary
  via `cargo build --release --target aarch64-unknown-none`, launches QEMU
  `raspi4b` machine, validates UART boot output, checks for fatal exceptions.
  Graceful skip when QEMU unavailable (CI-safe). Boot expected fixture at
  `tests/fixtures/qemu_boot_expected.txt`
- **AG9-B** (H3-PLAT-07, Hardware Cross-Check): New `scripts/test_hw_crosscheck.sh`
  validation script for physical RPi5 hardware constant verification. Validates
  15 BCM2712 constants from `Board.lean` — automated PASS/FAIL for architecture,
  PA width, page size, timer frequency; device tree probes for GIC and UART
  addresses; remaining MMIO constants pending bare-metal boot. Documentation at
  `docs/hardware_validation/rpi5_cross_check.md`
- **AG9-C** (H3-SCHED-05, WCRT Empirical Validation): New `profiling` module
  in `rust/sele4n-hal/src/profiling.rs` providing cycle-accurate measurement
  via PMCCNTR_EL0 (CPU cycle counter). `LatencyStats` accumulator for min/max/
  mean statistics across 10,000+ samples. `enable_cycle_counter()` PMU setup.
  Documentation at `docs/hardware_validation/wcrt_empirical_validation.md`
- **AG9-D** (H3-SCHED-03, RunQueue Cache Performance): Profiling infrastructure
  for RunQueue insert/remove/selection operations. Uses AG9-C `LatencyStats`
  for cycle counting at various queue sizes (1, 10, 50, 100 threads).
  Two-stage selection hit rate analysis documented at
  `docs/hardware_validation/runqueue_cache_performance.md`
- **AG9-E** (H3-IPC-03, Badge Overflow Validation): New Lean test suite
  `tests/BadgeOverflowSuite.lean` (22 tests) validating `Badge.ofNatMasked`
  round-trip identity, overflow/truncation semantics, bor preservation, and
  boundary values. 7 new Rust tests in `sele4n-types` for ARM64 u64 register
  width confirmation. Registered as `lake exe badge_overflow_suite` and
  integrated into Tier 2 negative tests. Documentation at
  `docs/hardware_validation/badge_overflow_validation.md`
- **AG9-F** (Speculation Barriers): CSDB (Conditional Speculation Dependency
  Barrier) added to `barriers.rs` for Spectre v1 mitigation on Cortex-A76.
  `speculation_safe_bound_check()` generic bounds-check pattern. `sb()` full
  speculation barrier. `has_feat_csv2()` Spectre v2 hardware mitigation check.
  CSDB deployed at exception dispatch (`trap.rs`) and GIC interrupt dispatch
  (`gic.rs`). 7 unit tests. Pre-existing clippy warnings in `mmio.rs` fixed
  (`is_multiple_of`). Documentation at
  `docs/hardware_validation/speculation_barriers.md`
- **AG9-G** (Full RPi5 Test Suite): New `scripts/test_hw_full.sh` orchestrating
  5-phase hardware validation: Lean tiered tests (Tier 0-3), Rust workspace
  tests, Badge overflow validation, hardware cross-check, QEMU integration.
  Report template at `docs/hardware_validation/rpi5_full_test_report.md`

### Infrastructure

- Badge overflow suite registered in `lakefile.toml` and integrated into
  `test_tier2_negative.sh` (Tier 2 gate)
- Hardware validation documentation directory: `docs/hardware_validation/`
  (6 reports covering AG9-B through AG9-G)
- Rust workspace: 362 tests pass (0 failures), 0 clippy warnings

## v0.26.9 — WS-AG Phase AG8: Integration + Model Closure

Phase AG8 of WS-AG H3 Hardware Binding Audit Remediation. Closes remaining
Lean model gaps exposed by hardware integration: timeout sentinel migration,
cache coherency model, memory barrier semantics, FrozenOps production decision,
CDT fuel sufficiency, donation chain cycle prevention, and donation atomicity.
7 sub-tasks (AG8-A through AG8-G).
Gate: `lake build` (256 jobs) + `test_full.sh`. Zero sorry/axiom.

### Changes

- **AG8-A** (H3-IPC-01/I-01): Migrated timeout signaling from fragile sentinel
  value `0xFFFFFFFF` in GPR x0 to explicit `timedOut : Bool` TCB field.
  `timeoutThread` sets `timedOut := true`, `timeoutAwareReceive` checks
  `tcb.timedOut` and clears on success. Eliminates collision risk with
  legitimate IPC data. Updated BEq instance (22 field comparisons).
  Removed `timeoutErrorCode` constant
- **AG8-B** (H3-ARCH-07): Cache coherency model in new
  `Architecture/CacheModel.lean`. `CacheLineState` (invalid/clean/dirty),
  `CacheState` structure with D-cache and I-cache function fields. Operations:
  `dcClean`, `dcInvalidate`, `dcCleanInvalidate`, `icInvalidateAll`, `dcZeroByVA`.
  17 preservation theorems including `empty_cacheCoherent`,
  `icInvalidateAll_coherent`, and `pageTableUpdate_icache_coherent` composition
- **AG8-C** (H3-ARCH-08): Memory barrier semantics formalization in
  `MmioAdapter.lean`. `BarrierKind` (dmb_ish/dsb_ish/isb), `barrierOrdered`
  predicate. 4 theorems: `barrierOrdered_trivial`,
  `dsb_isb_guarantees_tlb_visibility`, `dmb_guarantees_mmio_ordering`,
  `dsb_guarantees_mmio_completion`. Sequential model: barriers trivially ordered
- **AG8-D** (H3-PROOF-05): FrozenOps production decision — deferred to WS-V.
  Evaluation: 24 operations have preservation theorems, `FrozenSchedulerState`
  includes `replenishQueue` (AG1-E), commutativity proofs complete. However,
  frozen-phase type gap (e.g., `FrozenTCB` vs `TCB` field mismatches after
  AG8-A `timedOut` addition) and partial mutation concerns (AE2-D) warrant
  continued experimental status. All 4 FrozenOps files annotated with
  "Experimental — deferred to WS-V (AG8-D)"
- **AG8-E** (F-S05): CDT `descendantsOf` fuel sufficiency and depth bounds.
  `maxCdtDepth : Nat := 65536` constant based on RPi5 maximum kernel objects.
  `childrenOf_to_edge` bridges `childMap` membership to proof-anchor edge list.
  `CdtChildReachable_implies_cdtReachable` converts inductive reachability to
  path-based reachability (induction on CdtChildReachable with List path
  extension). `edgeWellFounded_no_self_reachable` proves no CDT self-cycles
  under `edgeWellFounded` + `cdtMapsConsistent`. `addEdge_edges_length` proves
  `addEdge` increments `edges.length` by exactly 1. `addEdge_maintains_depth_bound`
  proves depth bound preserved through `addEdge`
- **AG8-F** (H3-PROOF-03): Donation chain cycle prevention — substantive proofs.
  `donationOwnerValid_implies_donationChainAcyclic` proves that `donationOwnerValid`
  structurally implies `donationChainAcyclic` via `.bound ≠ .donated` constructor
  disjointness (SchedContextBinding mutually exclusive constructors with
  DecidableEq). `donationChain_no_extension` proves donated threads' owners
  cannot themselves be in `.donated` state. `blockedOnReply_cannot_call` proves
  blocked threads cannot initiate new calls
- **AG8-G** (H3-IPC-04): Donation atomicity under interrupt disable —
  substantive composed proofs. `donationAtomicRegion` predicate asserting
  `interruptsEnabled = false` for both pre- and post-states.
  `donateSchedContext_machine_eq` / `returnDonatedSchedContext_machine_eq`
  theorems proving machine state preserved through donation.
  `donateSchedContext_atomicRegion` / `returnDonatedSchedContext_atomicRegion`
  compose pre-condition + `machine_eq` to derive atomicity (non-vacuous:
  post-condition derived, not assumed). Wrapper proofs:
  `applyCallDonation_machine_eq`, `applyReplyDonation_machine_eq`,
  `cleanupPreReceiveDonation_machine_eq`, `removeRunnable_machine_eq`

### Additional fixes

- Fixed pre-existing unused simp argument warnings in
  `Platform/RPi5/RuntimeContract.lean` (hBind, hSc) and
  `Platform/RPi5/ProofHooks.lean` (hCurr, hObj)

### Post-implementation audit fixes

- **AG8-B audit**: Added `dcClean_preserves_dcacheCoherent` and
  `dcCleanInvalidate_preserves_dcacheCoherent` — missing preservation theorems
  proving D-cache coherency is maintained through clean and clean+invalidate
  operations (first audit). Second audit added 7 more theorems for
  `dcInvalidate` (4) and `dcZeroByVA` (3), bringing total to 17 theorems
- **AG8-E audit (substantive)**: Replaced both placeholder theorems with
  substantive proofs. `descendantsOf_fuel_sufficient` (Nat ≥ 0 tautology) →
  `edgeWellFounded_no_self_reachable` (no CDT node reaches itself under
  edgeWellFounded + cdtMapsConsistent). `cdtDepth_bounded_by_maxCdtDepth`
  (P → P identity) → `addEdge_edges_length` + `addEdge_maintains_depth_bound`
  (addEdge increments edges by 1, preserves depth bound). New bridge theorems:
  `childrenOf_to_edge` (childMap membership → edge existence),
  `CdtChildReachable_implies_cdtReachable` (inductive reachability → path-based
  reachability via path extension with List getElem? index manipulation)
- **AG8-F audit (substantive)**: Replaced weak `donationChainAcyclic_general`
  (unused `_hDCA` hypothesis) with two substantive theorems:
  `donationOwnerValid_implies_donationChainAcyclic` (owners have `.bound` binding
  → `.bound ≠ .donated` constructor disjointness prevents 2-cycles) and
  `donationChain_no_extension` (donated threads' owners cannot themselves be
  donated). Both proofs use `Option.some` injectivity on `st.objects` lookup
  followed by constructor disjointness contradiction
- **AG8-G audit**: Added `returnDonatedSchedContext_machine_eq` — symmetric
  machine state preservation theorem for the return path. Mirrors
  `donateSchedContext_machine_eq` with 3-step `storeObject` transitivity chain.
  Closes asymmetric coverage gap between donate and return paths
- **AG8-C audit**: Updated barrier theorem docstrings
  (`dsb_isb_guarantees_tlb_visibility`, `dmb_guarantees_mmio_ordering`,
  `dsb_guarantees_mmio_completion`) to explicitly state they are trivially
  satisfied in the sequential model (`barrierOrdered := True`). Prevents
  readers from mistaking vacuous proofs for substantive hardware guarantees
- **AG8-F audit**: Refined `blockedOnReply_cannot_call` docstring to describe
  it as a "building block" of the cycle prevention argument rather than "the
  structural invariant that prevents k>2 donation cycles"
- **AG8-G audit (round 2, substantive)**: Added wrapper-level machine state
  preservation proofs: `applyCallDonation_machine_eq`,
  `applyReplyDonation_machine_eq`, `cleanupPreReceiveDonation_machine_eq`,
  `removeRunnable_machine_eq`. Replaced vacuous `donationAtomicRegion_of_disabled`
  (hypothesis packaging) with composed atomicity proofs:
  `donateSchedContext_atomicRegion` and `returnDonatedSchedContext_atomicRegion`
  — each derives post-condition `interruptsEnabled = false` from pre-condition +
  `machine_eq` theorem, proving donation is atomic under interrupt disable

### Key theorems

- `donateSchedContext_machine_eq`: machine state preserved through SchedContext
  donation
- `returnDonatedSchedContext_machine_eq`: machine state preserved through
  SchedContext return (symmetric with donate)
- `applyCallDonation_machine_eq`: wrapper-level machine preservation (call path)
- `applyReplyDonation_machine_eq`: wrapper-level machine preservation (reply path)
- `cleanupPreReceiveDonation_machine_eq`: wrapper-level machine preservation
  (pre-receive cleanup path)
- `dcClean_preserves_dcacheCoherent`: D-cache coherency preserved through clean
- `dcCleanInvalidate_preserves_dcacheCoherent`: D-cache coherency preserved
  through clean+invalidate
- `donationOwnerValid_implies_donationChainAcyclic`: `donationOwnerValid` →
  `donationChainAcyclic` via `.bound ≠ .donated` constructor disjointness
- `donationChain_no_extension`: donated threads' owners cannot be donated
- `donateSchedContext_atomicRegion`: donation atomic under interrupt disable
  (composed from pre-condition + `donateSchedContext_machine_eq`)
- `returnDonatedSchedContext_atomicRegion`: return-donation atomic under
  interrupt disable (composed from pre-condition +
  `returnDonatedSchedContext_machine_eq`)
- `blockedOnReply_cannot_call`: blocked threads cannot initiate calls
- `empty_cacheCoherent`: empty cache is trivially coherent
- `pageTableUpdate_icache_coherent`: I-cache coherence after page table update
  + flush
- `childrenOf_to_edge`: `childrenOf` membership → edge existence (under
  `cdtMapsConsistent`)
- `CdtChildReachable_implies_cdtReachable`: inductive reachability → path-based
  reachability (path extension with List index manipulation)
- `edgeWellFounded_no_self_reachable`: no CDT self-cycles under
  `edgeWellFounded` + `cdtMapsConsistent`
- `addEdge_edges_length`: `addEdge` increments `edges.length` by exactly 1
- `addEdge_maintains_depth_bound`: depth bound preserved through `addEdge`

### New files

- `SeLe4n/Kernel/Architecture/CacheModel.lean` — cache coherency model

### Modified files

- `SeLe4n/Model/Object/Types.lean` — `timedOut : Bool` TCB field, BEq update
- `SeLe4n/Kernel/IPC/Operations/Timeout.lean` — sentinel → `timedOut` migration
- `SeLe4n/Kernel/IPC/Operations/Donation.lean` — atomicity predicate + theorems
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean` — k>2 cycle prevention theorems
- `SeLe4n/Model/Object/Structures.lean` — `maxCdtDepth`, fuel sufficiency proofs
- `SeLe4n/Platform/RPi5/MmioAdapter.lean` — barrier semantics formalization
- `SeLe4n/Kernel/FrozenOps/Core.lean` — WS-V deferral annotation
- `SeLe4n/Kernel/FrozenOps/Operations.lean` — WS-V deferral annotation
- `SeLe4n/Kernel/FrozenOps/Commutativity.lean` — WS-V deferral annotation
- `SeLe4n/Kernel/FrozenOps/Invariant.lean` — WS-V deferral annotation
- `SeLe4n/Platform/RPi5/RuntimeContract.lean` — simp warning fixes
- `SeLe4n/Platform/RPi5/ProofHooks.lean` — simp warning fixes
- `SeLe4n/Testing/MainTraceHarness.lean` — timeout field test updates

## v0.26.8 — WS-AG Phase AG7: FFI Bridge + Proof Hooks

Phase AG7 of WS-AG H3 Hardware Binding Audit Remediation. Lean-to-Rust FFI
bridge with `@[extern]` declarations, MMIO volatile primitives, system register
accessors, and production `AdapterProofHooks` for the RPi5 runtime contract.
Key deliverable: substantive (non-vacuous) proof hooks for both register writes
and atomic context switches on the production contract.
6 sub-tasks (AG7-A through AG7-F).
Gate: `lake build` (256 jobs) + `cargo test --workspace` + `test_smoke.sh` +
`test_full.sh`. Zero sorry/axiom.

### Changes

- **AG7-A** (H3-FFI-01): Lean `@[extern]` declarations in `FFI.lean` for 17
  Rust HAL functions across 6 groups (Timer, GIC, TLB, MMIO, UART, Interrupts).
  Corresponding `#[no_mangle] pub extern "C"` implementations in
  `rust/sele4n-hal/src/ffi.rs`
- **AG7-B** (H3-FFI-02): System register accessor extensions in
  `rust/sele4n-hal/src/registers.rs`. MRS/MSR wrappers for SCTLR_EL1,
  TCR_EL1, MAIR_EL1, TTBR0_EL1, VBAR_EL1, ESR_EL1, ELR_EL1, FAR_EL1
- **AG7-C** (H3-FFI-03): MMIO volatile read/write primitives in
  `rust/sele4n-hal/src/mmio.rs`. 32/64-bit volatile operations, debug
  UART output via PL011 MMIO, Lean-side `MmioAdapter.lean` with
  `mmioAccessAllowed` predicate and region disjointness proof
- **AG7-D** (H3-PROOF-01): Production `AdapterProofHooks` for
  `rpi5RuntimeContract`. `rpi5ProductionAdapterProofHooks` with substantive
  (non-vacuous) preservation proofs for all 4 adapter paths:
  - `preserveAdvanceTimer`: delegates to generic timer preservation lemma
  - `preserveWriteRegister`: extracts `contextMatchesCurrent` from
    production `registerContextStablePred` via boolean decomposition
  - `preserveReadMemory`: state-preserving identity
  - `preserveContextSwitch`: extracts all 6 TCB conditions (register match,
    dequeue-on-dispatch, time-slice positivity, IPC readiness, EDF
    compatibility, budget sufficiency) from `registerContextStablePred` and
    delegates to `contextSwitchState_preserves_proofLayerInvariantBundle`.
    Key helper: `contextSwitchState_preserves_ipcInvariantFull` handles
    `passiveServerIdle` transfer via `currentThreadIpcReady` contrapositive.
  `proofLayerInvariantBundle` extended to 11 conjuncts (added
  `notificationWaiterConsistent` as 11th) to close context-switch proof gap
- **AG7-E** (H3-PROOF-02): TLB flush composition theorems verified complete
  from AG6-F/G: `hardwareFlushAll_equiv_modelFlush`,
  `hardwareFlushByAsid_equiv_modelFlush`, `hardwareFlushByVAddr_equiv_modelFlush`,
  `vspaceUnmapPageWithFlush_preserves_tlbConsistent`
- **AG7-F** (H3-PROOF-03): End-to-end context switch proof hooks.
  `rpi5Production_adapterContextSwitch_preserves`: when `adapterContextSwitch`
  succeeds under the production runtime contract, `proofLayerInvariantBundle`
  holds for the post-state. `registerContextStableCheck_budget` bridge theorem
  connecting boolean budget check to `currentBudgetPositive` proposition

### Key theorems

- `contextSwitchState_preserves_proofLayerInvariantBundle`: 11-conjunct
  invariant bundle preserved through atomic context switch
- `contextSwitchState_preserves_ipcInvariantFull`: 15-conjunct IPC invariant
  preserved with `passiveServerIdle` transfer via old-current-thread IPC
  readiness
- `rpi5Production_adapterContextSwitch_preserves`: end-to-end production
  contract context-switch preservation
- `registerContextStableCheck_budget`: boolean budget check → proposition
  bridge

### Modified files

- `SeLe4n/Kernel/Architecture/Invariant.lean` — `proofLayerInvariantBundle`
  11th conjunct, context-switch + IPC preservation theorems
- `SeLe4n/Platform/RPi5/RuntimeContract.lean` — budget bridge theorem,
  import update
- `SeLe4n/Platform/RPi5/ProofHooks.lean` — production `AdapterProofHooks`
  instance + end-to-end theorems
- `SeLe4n/Platform/Boot.lean` — 11th conjunct in boot proof

## v0.26.7 — WS-AG Phase AG6: Memory Management (ARMv8 Page Tables)

Phase AG6 of WS-AG H3 Hardware Binding Audit Remediation. ARMv8-A 4-level
page table implementation with shadow-based refinement proofs, TLB and cache
maintenance HAL wrappers, and ASID generation/management with uniqueness proofs.
9 sub-tasks (AG6-A through AG6-I) closing 7 findings from the H3 hardware
binding audit.
Gate: `cargo test --workspace` (306 tests) + `cargo clippy --workspace`
(0 warnings) + `lake build` (256 jobs) + `test_smoke.sh` + `test_full.sh`.
Zero sorry/axiom.

### Changes

- **AG6-A** (H3-ARCH-01): ARMv8 page table descriptor types in `PageTable.lean`.
  `PageTableLevel` (L0–L3), `Shareability`, `AccessPermission` (kernelRW/RO,
  userRW/RO), `PageAttributes`, `PageTableDescriptor` (invalid/block/table/page).
  `descriptorToUInt64`/`uint64ToDescriptor` encode/decode with round-trip.
  `encodePageAttributes`/`decodePageAttributes`. W^X bridge proof
  `hwDescriptor_wxCompliant_bridge` linking hardware AP/PXN/UXN to
  `PagePermissions.wxCompliant`
- **AG6-B** (H3-ARCH-01): 4-level page table walk in `PageTable.lean`.
  Index extraction via div/mod (omega-compatible). `readUInt64` little-endian
  memory read. `pageTableWalk` via structural recursion on `PageTableLevel`
  (no fuel). `pageTableWalk_deterministic` proof. `pageTableWalkPerms` wrapper
- **AG6-C** (H3-ARCH-01): `VSpaceBackend` ARMv8 instance in `VSpaceARMv8.lean`.
  `ARMv8VSpace` with shadow `VSpaceRoot` + hardware page tables + `Memory`.
  Shadow-first design: `mapPage`/`unmapPage` update shadow then hardware.
  `lookupPage` delegates to shadow for proof tractability. `ensureTable`
  allocates L0→L3 chain. All 7 VSpaceBackend obligations discharged
- **AG6-D** (H3-ARCH-01): Shadow-based refinement proof. `simulationRelation`
  linking hardware walk to shadow HashMap. `lookupPage_refines` and
  `hwLookupAddr_refines` refinement theorems. `vspaceProperty_transfer`
  master invariant transfer theorem
- **AG6-E** (H3-RUST-05): TLB flush wrappers in `tlb.rs`. `tlbi_vmalle1()`,
  `tlbi_vae1(asid, vaddr)`, `tlbi_aside1(asid)`, `tlbi_vale1(asid, vaddr)`.
  Each followed by DSB ISH + ISB per ARM ARM D8.11. 7 tests
- **AG6-F** (H3-ARCH-02): TLB flush model integration in `TlbModel.lean`.
  Hardware adapter functions + 3 equivalence theorems + 3 consistency
  preservation theorems + unmap-flush composition theorem
- **AG6-G** (H3-ARCH-03): TLB barrier model. `tlbBarrierComplete` predicate.
  Barrier completion theorems. `adapterFlushTlbHw_safe` combined safety
- **AG6-H** (H3-ARCH-04): ASID management in `AsidManager.lean`. `AsidPool`
  bump allocator with generation tracking, free list, and exhaustion guard.
  `wellFormed` predicate with 3 preservation theorems. `asidPoolUnique`
  uniqueness invariant with allocation/free preservation
- **AG6-I** (H3-RUST-06): Cache maintenance in `cache.rs`. DC CIVAC/CVAC/IVAC/
  ZVA, IC IALLU/IALLUIS. `cache_range` aligned iteration. Convenience wrappers.
  11 tests

### New files

- `SeLe4n/Kernel/Architecture/PageTable.lean` (433 lines)
- `SeLe4n/Kernel/Architecture/VSpaceARMv8.lean` (341 lines)
- `SeLe4n/Kernel/Architecture/AsidManager.lean` (231 lines)
- `rust/sele4n-hal/src/tlb.rs` (153 lines)
- `rust/sele4n-hal/src/cache.rs` (253 lines)

### Modified files

- `SeLe4n/Kernel/Architecture/TlbModel.lean` (+113 lines)
- `rust/sele4n-hal/src/lib.rs` (+2 lines: `pub mod tlb; pub mod cache;`)

### Post-implementation audit fixes

- **FINDING-01** (MEDIUM): `uint64ToDescriptor` now treats bits[1:0]=0b10 as
  invalid per ARM ARM D8.3 (bit[0]=0 → fault). Previously fell through to
  table/page decode, creating model-hardware disagreement
- **FINDING-02** (MEDIUM): `cache_range` loop uses `saturating_add` instead of
  `+=` to prevent integer overflow infinite loop near u64::MAX
- **FINDING-03** (LOW): `pageTableWalk_deterministic` strengthened from bare
  existence to unique existence (`∃ result, ... ∧ ∀ result', ... → result' = result`)
- **FINDING-04** (INFO): Documented simulation relation preservation gap —
  `mapPage_refines`/`unmapPage_refines` deferred to AG7 FFI integration
- **FINDING-05** (INFO): Documented ASID freshness connection gap — formal
  connection between `AsidPool.allocate` and uniqueness precondition deferred
  to AG8 kernel integration

---

## v0.26.6 — WS-AG Phase AG5: Interrupts + Timer

Phase AG5 of WS-AG H3 Hardware Binding Audit Remediation. Full GIC-400
interrupt controller and ARM Generic Timer bring-up, connecting hardware
interrupts to the Lean kernel model. Rust HAL upgraded from stubs to complete
drivers. Lean model extended with interrupt-disabled region semantics,
timer interrupt binding, and handleInterrupt information-flow proof.
7 sub-tasks (AG5-A through AG5-G) closing 7 findings from the H3 hardware
binding audit.
Gate: `cargo test --workspace` (288 tests) + `cargo clippy --workspace`
(0 warnings) + `lake build` (256 jobs) + `test_smoke.sh`. Zero sorry/axiom.

### Changes

- **AG5-A** (H3-PLAT-02): GIC-400 distributor initialization in `gic.rs`.
  `init_distributor()`: disable GICD_CTLR, configure GICD_IGROUPR (Group 0),
  set GICD_IPRIORITYR (default 0xA0), route GICD_ITARGETSR to CPU 0, clear
  pending via GICD_ICPENDR, enable via GICD_ISENABLER, re-enable GICD_CTLR.
  GIC-400 distributor base 0xFF841000 (BCM2712). All register offsets and MMIO
  helpers modeled with `cfg(target_arch = "aarch64")` guards
- **AG5-B** (H3-PLAT-02): GIC-400 CPU interface initialization in `gic.rs`.
  `init_cpu_interface()`: set GICC_PMR = 0xFF (accept all priorities),
  GICC_BPR = 0 (no grouping), GICC_CTLR = 1 (enable). CPU interface base
  0xFF842000 (BCM2712)
- **AG5-C** (H3-RUST-04): GIC-400 acknowledge/dispatch/EOI in `gic.rs`.
  `acknowledge_irq() -> u32` reads GICC_IAR. `end_of_interrupt(intid)` writes
  GICC_EOIR. `dispatch_irq<F>(handler)` composes acknowledge → spurious check
  (INTID ≥ 1020) → dispatch → EOI. `init_gic()` convenience function
  initializes both distributor and CPU interface. 14 unit tests
- **AG5-D** (H3-PLAT-03): ARM Generic Timer driver in `timer.rs`.
  `read_counter() -> u64` (CNTPCT_EL0), `read_frequency() -> u32`
  (CNTFRQ_EL0), `set_comparator(u64)` (CNTP_CVAL_EL0), `enable_timer()`/
  `disable_timer()` (CNTP_CTL_EL0), `is_timer_pending() -> bool`. Static state
  via `AtomicU64` (`TICK_COUNT`, `TIMER_INTERVAL`). `init_timer(tick_hz)`:
  compute interval from frequency, set first comparator, enable.
  `reprogram_timer()`: counter-relative advancement. `increment_tick_count()`/
  `get_tick_count()`. RPi5 54 MHz, default 1000 Hz tick. 8 unit tests
- **AG5-E** (H3-SCHED-01): Timer interrupt → `timerTick` binding in Lean.
  `TimerInterruptBinding` structure in `TimerModel.lean` with `config` and
  `tickCount` fields. `handleTimerInterrupt` composes acknowledge → timerTick →
  reprogram. 4 preservation theorems (all `rfl`). `rpi5TimerBinding` default
  instance. `timerInterruptHandler` in `InterruptDispatch.lean` delegates to
  `timerTick`; `handleInterrupt_timer` theorem proves timer INTID dispatch
- **AG5-F** (FINDING-06): `handleInterrupt` kernel integration.
  `NonInterferenceStep.handleInterrupt` constructor added to `Composition.lean`
  with `hCurrentHigh`/`hCurrentObjHigh`/`hAllRunnable`/`hProj` hypotheses.
  `KernelOperation.handleInterrupt` added (35th constructor). Coverage proof
  `niStepCoverage_count` updated 34→35. `step_preserves_projection` extended.
  `handleInterrupt_crossSubsystemInvariant_bridge` in `CrossSubsystem.lean`
  delegates to `crossSubsystemInvariant_objects_change_bridge`
- **AG5-G** (H3-DAIF): Interrupt-disabled region model (Rust + Lean).
  Rust: `interrupts.rs` with `disable_interrupts() → u64` (saves DAIF),
  `restore_interrupts(saved)`, `enable_irq()`, `are_interrupts_enabled()`,
  `with_interrupts_disabled<F,R>()`. 4 unit tests.
  Lean: `interruptsEnabled : Bool` field on `MachineState`. `disableInterrupts`,
  `enableInterrupts`, `withInterruptsDisabled` (save/restore semantics)
  operations with 10 frame/preservation theorems including
  `withInterruptsDisabled_restores`. AG5-G atomicity proofs in
  `ExceptionModel.lean`:
  `saveOutgoingContext_preserves_interruptsEnabled`,
  `restoreIncomingContext_preserves_interruptsEnabled`,
  `setCurrentThread_preserves_interruptsEnabled`,
  `interruptDispatchSequence_preserves_interruptsEnabled_spurious`,
  `chooseThread_preserves_interruptsEnabled`,
  `schedule_preserves_interruptsEnabled`,
  `timerTick_preserves_interruptsEnabled`,
  `handleInterrupt_timer_preserves_interruptsEnabled`

### Metrics

- **New files**: 1 (`rust/sele4n-hal/src/interrupts.rs`)
- **Modified files**: 11 (6 Lean, 5 Rust)
- **Lines changed**: ~1184 added, ~106 removed
- **Rust workspace**: 4 crates, 288 tests, 0 clippy warnings
- **Lean**: 256 build jobs, zero sorry/axiom
- **NI coverage**: 35 kernel operations (was 34)

---

## v0.26.5 — WS-AG Phase AG4: HAL Crate + Boot Foundation

Phase AG4 of WS-AG H3 Hardware Binding Audit Remediation. Creates the
kernel-side Rust/assembly infrastructure for Raspberry Pi 5 — the first phase
producing hardware-executable code. New `sele4n-hal` crate with ARM64 boot
sequence, PL011 UART driver, MMU initialization, exception vector table, and
trap entry/exit assembly. 7 sub-tasks (AG4-A through AG4-G) closing 7 findings
from the H3 hardware binding audit. Rust workspace now has 4 crates.
Gate: `cargo test --workspace` (267 tests) + `cargo clippy --workspace`
(0 warnings) + `lake build` + `test_smoke.sh`. Zero sorry/axiom.

### Changes

- **AG4-A** (FINDING-01/RUST-03): `sele4n-hal` crate created. `#![no_std]`,
  ARM64 HAL for seLe4n kernel. Modules: `cpu` (WFE, WFI, NOP, ERET,
  `current_core_id`), `barriers` (DMB ISH/SY, DSB ISH/SY, ISB), `registers`
  (MRS/MSR macros, 11 system register accessors), `uart`, `mmu`, `trap`,
  `boot`, `gic` (stub), `timer` (stub). All AArch64-specific code gated behind
  `cfg(target_arch = "aarch64")` for cross-platform compilation. `build.rs`
  assembles `.S` files via `cc` crate. Added to workspace members
- **AG4-B** (H3-PLAT-04/RUST-01): ARM64 exception vector table in `vectors.S`.
  16 entries (4 exception types × 4 source states), 2048-byte aligned for
  VBAR_EL1. Current EL SPx routes: sync → `__el1_sync_entry`, IRQ →
  `__el1_irq_entry`, SError → `__el1_serror_entry`. Lower EL AArch64 routes:
  sync → `__el0_sync_entry` (SVC syscall path), IRQ → `__el0_irq_entry`.
  Unused entries branch to WFE stub. AArch32 lower EL not supported
- **AG4-C** (H3-RUST-02): Trap entry/exit assembly in `trap.S`. `save_context`
  macro: saves 31 GPRs (x0-x30) + SP_EL0 + ELR_EL1 + SPSR_EL1 into 272-byte
  `TrapFrame` on kernel stack. `restore_context` macro: reverse restore + ERET.
  `TrapFrame` Rust struct in `trap.rs` with ABI register accessors (x0-x5, x7)
  matching seLe4n syscall convention. `handle_synchronous_exception`: ESR EC
  dispatch (SVC → syscall stub, data/instruction abort → vmFault, alignment →
  userException). `handle_irq`: GIC stub (AG5). `handle_serror`: fatal halt.
  Compile-time assertion: `TrapFrame` is exactly 272 bytes
- **AG4-D** (H3-RUST-10): Kernel linker script `link.ld`. Entry at `_start`,
  load address 0x80000 (standard RPi5 kernel entry). Sections: `.text.boot` →
  `.text.vectors` (2048-aligned) → `.text` → `.rodata` → `.data` → `.bss` →
  `.bss.page_tables` (4096-aligned) → `.stack` (64 KiB). Exports `__bss_start`,
  `__bss_end`, `__stack_top`, `__page_tables_start` linker symbols. RAM origin
  at 0x80000 with 0xFBF80000 length
- **AG4-E** (H3-PLAT-08): Boot sequence in `boot.S` + `boot.rs`. Assembly
  entry `_start`: MPIDR core ID check (park non-core-0), DTB pointer save
  (x19), BSS zeroing (16-byte stride STP), stack setup (`__stack_top`), branch
  to `rust_boot_main`. Rust boot: Phase 1 (UART init, boot banner), Phase 2
  (MMU init, VBAR set), Phase 3 (hardware init summary, idle loop). Secondary
  cores enter WFE spin loop (SMP deferred to WS-V)
- **AG4-F** (H3-PLAT-05): MMU initialization in `mmu.rs`. MAIR_EL1: 3
  attribute indices (Normal WB-WA-RA at idx 0, Device-nGnRnE at idx 1, Normal
  NC at idx 2). TCR_EL1: T0SZ/T1SZ = 16 (48-bit VA), TG0/TG1 = 4 KiB
  granule, IPS = 44-bit PA (BCM2712), Inner Shareable, WB cacheable. Boot page
  tables: L1 identity map with 1 GiB block descriptors — 3 entries Normal RAM
  (0x00-0xBF_FFFF_FFFF) + 1 entry Device (0xC0-0xFF_FFFF_FFFF covering
  peripherals). SCTLR_EL1: M + C + I bits set. DSB ISH + ISB barriers around
  MMU enable
- **AG4-G** (H3-PLAT-06): PL011 UART driver in `uart.rs`. Base address
  0xFE201000 (BCM2712 UART0, matching Board.lean `uart0Base`). 48 MHz UART
  clock, 115200 baud (IBRD=26, FBRD=3). 8N1 line control with FIFO enabled.
  Blocking `putc` (polls TXFF), `puts` with CR/LF conversion, non-blocking
  `getc`. `core::fmt::Write` implementation for `write!`/`writeln!` macros.
  `kprint!`/`kprintln!` global macros using `&raw mut` for safe static access.
  Global `BOOT_UART` instance with `init_boot_uart()` initializer

### Metrics

- **New Rust crate**: `sele4n-hal` (4th workspace crate)
- **New files**: 13 (10 Rust `.rs`, 3 assembly `.S`, 1 `build.rs`, 1 `link.ld`,
  1 `Cargo.toml`)
- **Lines added**: ~900 Rust + ~300 assembly + linker script
- **Rust workspace**: 4 crates, 267 tests, 0 clippy warnings
- **Lean**: Zero changes to production proofs (zero sorry/axiom maintained)

---

## v0.26.4 — WS-AG Phase AG3: Platform Model Completion + Audit

Phase AG3 of WS-AG H3 Hardware Binding Audit Remediation. Completes all Lean
model gaps that block hardware bring-up. Post-implementation audit found and
fixed critical Rust ABI desynchronization (5 missing KernelError variants),
misleading DeviceTree docstring, and documentation gaps. 8 sub-tasks
(AG3-A through AG3-H) closing 8 findings from the H3 hardware binding audit.
Gate: `lake build` + `test_full.sh` + `cargo test --workspace`. Zero sorry/axiom.

### Changes

- **AG3-A** (P-01): `classifyMemoryRegion` now accepts a platform memory map
  (`List MemoryRegion`) for address-based classification. `classifyAddress`
  standalone function added. Two correctness theorems proven
- **AG3-B** (P-04): `applyMachineConfig` copies all 7 `MachineConfig` fields
  (was: only `physicalAddressWidth`). 6 new `MachineState` fields added:
  `registerWidth`, `virtualAddressWidth`, `pageSize`, `maxASID`, `memoryMap`,
  `registerCount`. `MemoryKind`/`MemoryRegion` moved before `MachineState` to
  enable `memoryMap` field. 6 new preservation theorems proven
- **AG3-C** (FINDING-04): ARM64 exception model in `ExceptionModel.lean`.
  `ExceptionType` (4 variants), `ExceptionSource` (4 variants),
  `SynchronousExceptionClass` (6 variants), `ExceptionContext` structure.
  ESR classification via EC field extraction (bits [31:26]). SVC dispatch
  wired to `syscallEntry`. 6 dispatch/preservation theorems
- **AG3-D** (FINDING-06): Interrupt dispatch in `InterruptDispatch.lean`.
  `InterruptId` (GIC-400 bounded `Fin 224`), `timerInterruptId` (PPI 30).
  Acknowledge→handle→EOI sequence. Timer interrupt → `timerTick`, mapped
  IRQ → `notificationSignal`, unmapped → `.invalidIrq`. IRQ dispatch wired
  into `dispatchException` IRQ branch. 3 theorems proven
- **AG3-E** (FINDING-08): Timer model binding in `TimerModel.lean`.
  `HardwareTimerConfig` with `counterFrequencyHz`, `tickIntervalNs`,
  `comparatorValue`. `hardwareTimerToModelTick` conversion with monotonicity
  proof. `reprogramComparator` for evenly-spaced interrupts. RPi5 config at
  54 MHz with 54000 counts/tick proven via `decide`
- **AG3-F** (H3-ARCH-05): Exception level model in `ExceptionModel.lean`.
  `ExceptionLevel` (el0/el1), `exceptionLevelFromSpsr`,
  `exceptionLevelFromSource`, `canAccessSystemRegisters`, `canExecutePrivileged`
- **AG3-G** (H3-ARCH-06): System register model in `Machine.lean`.
  `SystemRegisterFile` structure (10 registers: ELR, ESR, SPSR, FAR, SCTLR,
  TCR, TTBR0, TTBR1, MAIR, VBAR). `SystemRegisterIndex` enum.
  `readSystemRegister`/`writeSystemRegister` with 4 frame lemmas proven
- **AG3-H** (H3-ARCH-10): `hashMapVSpaceBackend` instance for `VSpaceRoot`.
  All 8 typeclass obligations discharged: ASID preservation (2), round-trip
  correctness (2), non-interference (4). `rootWF = invExtK`
- `KernelError` extended from 44 to 49 variants: `vmFault`, `userException`,
  `hardwareFault`, `notSupported`, `invalidIrq`
- **Rust ABI sync**: `KernelError` in `sele4n-types/src/error.rs` updated with
  5 new variants (VmFault=44, UserException=45, HardwareFault=46,
  NotSupported=47, InvalidIrq=48). All conformance tests updated
  (discriminant count 44→49, gap assertions 44→49, roundtrip range 0-48).
  `sele4n-abi/src/decode.rs` unknown error threshold updated (44→49).
  239 Rust tests pass, zero clippy warnings
- **Second audit pass**: Fixed 2 stale Rust comments referencing pre-AG3
  error range (decode.rs "0–43"→"0–48", error.rs "0–43"→"0–48"). All
  documentation verified accurate. Full test suite re-validated

---

## v0.26.2 — WS-AG Phase AG2 Audit: IPC Buffer Correctness Fix

Post-implementation audit of Phase AG2. Found and fixed a critical correctness
bug in `sched_context_configure`: the 5th parameter (domain) was never written
to the IPC buffer overflow slot, meaning the kernel would read a stale/zero
value on real ARM64 hardware. All tests pass (cargo test --workspace: 239 tests,
cargo clippy: zero warnings). Zero sorry/axiom.

### Changes

- **AG2-B fix**: `sched_context_configure` in `sele4n-sys/src/sched_context.rs` now takes `&mut IpcBuffer` and writes `buf.set_mr(4, encoded[4])?` before `invoke_syscall`, matching the `service_register` pattern for 5-register syscalls. Without this fix, on ARM64 hardware the kernel's `requireMsgReg decoded.msgRegs 4` (SyscallArgDecode.lean:962) would read a stale IPC buffer value for the domain field
- **AG2-C fix**: Corrected CHANGELOG v0.26.1 entry — AG2-C version sync target was `0.26.1` not `0.26.0`
- **DomainId comment**: Clarified `DomainId::MAX_VALID = 255` in `sele4n-types/src/identifiers.rs` is a type-level bound (seL4 8-bit domain space), distinct from the ABI-level `MAX_DOMAIN = 15` enforced by `sele4n-abi`
- Conformance test `ag2b_sys_sched_context_module_exports` updated to verify `&mut IpcBuffer` in function signature
- GitBook chapter 15: Added IPC buffer overflow documentation for 5-register syscalls
- **CI fix**: Reverted `is_multiple_of()` in `tcb.rs` to `% != 0` with `#[allow(clippy::manual_is_multiple_of)]` — `u64::is_multiple_of()` requires Rust 1.87+ but CI pins toolchain 1.82.0

---

## v0.26.1 — WS-AG Phase AG2: Pre-Hardware Rust ABI Fixes

Phase AG2 of WS-AG H3 Hardware Binding Audit Remediation. Fixes Rust ABI
domain validation mismatch, adds missing SchedContext typed syscall wrappers,
synchronizes workspace version, and resolves pre-existing clippy warning.
All tests pass (cargo test --workspace: 239 tests, cargo clippy: zero warnings).
Zero sorry/axiom.

### Changes

- **AG2-A** (R-05): Fixed `MAX_DOMAIN` constant from 255 to 15 in `sele4n-abi/src/args/sched_context.rs` — now matches Lean `numDomainsVal = 16` (zero-indexed 0..=15). Domain values 16-255 previously accepted by Rust ABI but rejected by kernel with `invalidArgument`. Updated decode boundary validation, 2 existing unit tests, 2 existing conformance tests, and added 4 new AG2-A conformance tests (boundary validation, exhaustive valid/invalid domain coverage)
- **AG2-B** (R-01): Created `rust/sele4n-sys/src/sched_context.rs` with 3 typed wrapper functions (`sched_context_configure`, `sched_context_bind`, `sched_context_unbind`) for syscalls 17-19 — completes sele4n-sys coverage for all 25 syscalls. `sched_context_configure` correctly writes the 5th parameter (domain) to the IPC buffer overflow slot via `buf.set_mr(4, encoded[4])`, matching the `service_register` pattern for 5-register syscalls. Module registered in `sele4n-sys/src/lib.rs`. AG2-B conformance test verifies function signature exports
- **AG2-C** (RUST-04): Synchronized Rust workspace version from `0.25.6` to `0.26.1` in `rust/Cargo.toml` — now tracks Lean `lakefile.toml` version. Added version-tracking comment
- **Bonus**: Suppressed `manual_is_multiple_of` clippy lint in `sele4n-abi/src/args/tcb.rs:123` via `#[allow]` — `u64::is_multiple_of()` requires Rust 1.87+ but CI pins 1.82.0

### Metrics

| Metric | Value |
|--------|-------|
| Rust workspace version | 0.26.1 (synced with Lean) |
| Unit tests | 91 (sele4n-abi) + 13 (sele4n-sys) + 42 (sele4n-types) |
| Conformance tests | 93 (sele4n-abi/tests/conformance.rs) |
| Clippy warnings | 0 |
| Gate | `cargo test --workspace` + `cargo clippy --workspace` |

---

## v0.26.0 — WS-AG Phase AG1: Pre-Hardware Lean Code Fixes

Phase AG1 of WS-AG H3 Hardware Binding Audit Remediation. Fixes 6 verified
Lean-side code issues from the release audit before beginning hardware work.
Establishes a clean baseline. All tests pass (test_smoke.sh). Zero sorry/axiom.

---

## v0.25.27 — WS-AF Phase AF6: Rust ABI Fixes & Documentation Closure

Phase AF6 of WS-AF Pre-Release Comprehensive Audit Remediation. Fixes Rust ABI
error mapping semantics, adds checked truncation detection, corrects stale
variant counts, adds missing SchedContext marker type, enforces IpcMessage.length
privacy, and installs shellcheck in CI. All tests pass (test_full.sh Tier 0-3,
cargo test). Zero sorry/axiom. **WS-AF PORTFOLIO COMPLETE** (6 phases, 49 sub-tasks).

### Changes

- **AF6-A** (AF-20): Added `UnknownKernelError` variant (discriminant 255) — unrecognized error codes now map to semantically correct fallback instead of `InvalidSyscallNumber`
- **AF6-B** (AF-21): Added `endpoint_reply_recv_checked` with `IpcTruncationError` — rejects messages longer than 3 registers instead of silent truncation
- **AF6-C** (AF-35, AF-36): Fixed stale doc comments — "43-variant" → "45-variant", "20-variant" → "25-variant", decode range "0–42" → "0–43"
- **AF6-D** (AF-37): Added `SchedContext` marker type to `sele4n-sys/src/cap.rs` for phantom-typed capability handles
- **AF6-E** (AF-38): Made `IpcMessage.length` private — added `length()` accessor and `new_with_length()` validated constructor
- **AF6-F** (AF-46): Added shellcheck installation to CI workflow (`lean_action_ci.yml`)
- **AF6-G**: Full documentation synchronization — version bump 0.25.26 → 0.25.27 across all 7+ documentation files

### Metrics

| Metric | Value |
|--------|-------|
| Production LoC | 87,132 across 133 files |
| Test LoC | 11,359 across 16 suites |
| Proved declarations | 2,581 theorem/lemma (zero sorry/axiom) |
| Gate | `test_full.sh` Tier 0-3, `cargo test --workspace` |

---

## v0.25.26 — WS-AF Phase AF5: IPC, Capability, Lifecycle & Documentation

Phase AF5 of WS-AF Pre-Release Comprehensive Audit Remediation. Fixes stale
documentation, corrects FrozenOps operation count, removes duplicate NI
definitions, and adds design rationale documentation across IPC, capability,
lifecycle, and scheduler subsystems. All tests pass (test_full.sh Tier 0-3).
Zero sorry/axiom.

### Changes

- **AF5-A** (AF-12): Fixed stale `pendingMessage = none` documentation in `notificationSignal` — now cross-references proven `waitingThreadsPendingMessageNone` invariant (AC1-A)
- **AF5-B** (AF-04): Documented timeout sentinel H3 migration path (`timedOut : Bool` on TCB)
- **AF5-C** (AF-06): Documented `endpointQueueRemove` direct `RHTable.insert` rationale with AE4-E unreachability proof cross-references
- **AF5-D** (AF-15): Documented Badge Nat round-trip safety via `ofNatMasked` 64-bit masking
- **AF5-E** (AF-39): Documented `donationChainAcyclic` 2-cycle scope with IPC protocol structural argument
- **AF5-F** (AF-26): Documented tuple projection maintenance burden in Builder.lean and Capability/Invariant/Defs.lean (deferred to WS-V)
- **AF5-G** (AF-27): Documented `cspaceResolvePath` vs `resolveCapAddress` CSpace resolution layers
- **AF5-H** (AF-28): Documented `suspendThread` TCB re-lookup rationale after `cancelIpcBlocking`
- **AF5-I** (AF-43): Fixed FrozenOps operation count from stale "21" to correct "24" with 4 missing table entries (frozenCspaceLookupSlot, frozenSetPriority, frozenSetMCPriority, frozenSetIPCBuffer)
- **AF5-I** (AF-48): Removed duplicate `cdt_only_preserves_projection` and `ensureCdtNodeForSlot_preserves_projection` definitions — consolidated to primed canonical versions
- **AF5-J** (AF-31): Documented high-heartbeat proof fragility (1.6M/800K) with mitigation strategies

### Metrics

| Metric | Value |
|--------|-------|
| Production LoC | 87,132 across 133 files |
| Test LoC | 11,359 across 16 suites |
| Proved declarations | 2,581 theorem/lemma (zero sorry/axiom) |
| Gate | `test_full.sh` Tier 0-3 |

---

## v0.25.25 — WS-AF Phase AF4: Information Flow, Cross-Subsystem & SchedContext

Phase AF4 of WS-AF Pre-Release Comprehensive Audit Remediation. Eliminates all
`native_decide` from the codebase (TCB reduction), expands fuel-sufficiency
documentation, and adds deployment requirement cross-references across
information flow, cross-subsystem, service, and SchedContext modules. All tests
pass (test_full.sh Tier 0-3). Zero sorry/axiom.

### Changes

- **AF4-A** (AF-16): Replaced `native_decide` with `decide` in `enforcementBoundary_is_complete` (Wrappers.lean) — removes Lean runtime evaluator from TCB for 25-element SyscallId enumeration
- **AF4-B** (AF-17): Replaced `native_decide` with `decide` in `crossSubsystem_pairwise_coverage_complete` (CrossSubsystem.lean) — 15-element pairwise disjointness proof now kernel-checked
- **AF4-B+**: Replaced bonus `native_decide` in `crossSubsystemInvariant_default` (CrossSubsystem.lean:378) — zero `native_decide` remains in production code
- **AF4-C** (AF-07): Expanded `collectQueueMembers` fuel-sufficiency formal argument sketch with `tcbQueueChainAcyclic` connection
- **AF4-D** (AF-18): Documented `serviceHasPathTo` conservative fuel-exhaustion semantics (returns `true` on fuel=0 for safe cycle detection)
- **AF4-E** (AF-33): Added seL4 separation kernel design cross-reference for `LabelingContextValid` deployment requirement; created `labelingContextValid_is_deployment_requirement` witness theorem (AE5-F gap closure)
- **AF4-F** (AF-08): Documented CBS 8× bandwidth bound precision gap analysis with future proof-tightening roadmap
- **AF4-G** (AF-30, AF-47): Documented `schedContextYieldTo` kernel-internal design rationale (operates below capability layer, pure function with identity fallback)

## v0.25.24 — WS-AF Phase AF3: Platform & DeviceTree Hardening

Phase AF3 of WS-AF Pre-Release Comprehensive Audit Remediation. Addresses 7
findings across platform, DeviceTree, and MMIO subsystems — DTB parser
fuel-exhaustion fix (`parseFdtNodes` returns `none` on fuel exhaustion instead
of silent truncation), full MMIO write byte-range validation (`mmioWrite32`,
`mmioWrite64`, `mmioWrite32W1C`), MMIO write-semantics model documentation,
`extractPeripherals` depth limitation documentation, `natKeysNoDup` opacity
documentation, and four DTB/boot stub limitation annotations. All tests pass
(test_smoke.sh). Zero sorry/axiom.

### Changes

- **AF3-A** (AF-05): `parseFdtNodes` fuel exhaustion returns `none` (was `some []`)
- **AF3-B** (AF-09a): `mmioWrite32`/`mmioWrite64`/`mmioWrite32W1C` validate full byte range; 3 supplementary `_rejects_range_overflow` theorems prove end-of-range rejection when base address is valid but endpoint is not
- **AF3-C** (AF-09b): MMIO write-semantics model gap documented
- **AF3-D** (AF-32): `extractPeripherals` 2-level depth limitation documented
- **AF3-E** (AF-19): `natKeysNoDup` opaque HashSet design tradeoff documented
- **AF3-F** (AF-41/42/44/45): DTB/boot stubs documented (deferred to WS-V)

## v0.25.19 — WS-AE Phase AE4: Capability, IPC & Architecture Hardening

Phase AE4 of WS-AE Production Audit Remediation. Addresses 10 findings across
capability, IPC, and architecture subsystems — CPtr masking, VAddr canonicity,
CDT acyclicity preservation, mint completeness integration, queue remove
unreachability, timeout documentation, TLB flush preparation, IPC buffer
cross-page safety, and capability transfer slot generalization. All tests pass
(test_full.sh Tier 0-3). Zero sorry/axiom.

### Changes
- **AE4-A (U-17/CAP-01)**: Added CPtr masking (`addr.toNat % machineWordMax`)
  to `resolveCapAddress` for consistency with `CNode.resolveSlot` (S4-C). Updated
  `resolveCapAddress_guard_reject` and `resolveCapAddress_guard_match` theorem
  statements to reference masked address.
- **AE4-B (U-26/ARCH-03)**: Added VAddr canonicity check to
  `decodeVSpaceUnmapArgs` for defense-in-depth parity with `decodeVSpaceMapArgs`.
  Updated `decodeVSpaceUnmapArgs_error_iff` (3-way disjunction) and
  `decodeVSpaceUnmapArgs_roundtrip` (new `hVAddr` hypothesis).
  `decode_layer2_roundtrip_all` updated.
- **AE4-C (U-18/CAP-02)**: Added `cdtReachable` propositional reachability
  predicate and `freshChild_not_reachable` bridging theorem. Added
  `cspaceMintWithCdt_cdtAcyclicity_of_freshDst` — proves CDT acyclicity
  preservation for mint operations with fresh destination nodes, eliminating
  the need for `hCdtPost` hypothesis in the fresh-child case.
- **AE4-D (U-36/C-CAP06)**: Defined `capabilityInvariantBundleWithMintCompleteness`
  (standard 7-tuple + `cdtMintCompleteness`). Added extraction and composition
  theorems. Integrated into `CrossSubsystem.lean` as
  `crossSubsystemInvariantWithCdtCoverage` for full CDT coverage at the
  composition layer.
- **AE4-E (U-24/IPC-02)**: Proved `queueRemove_predecessor_exists` and
  `queueRemove_successor_exists` — under `tcbQueueLinkIntegrity`, the fallback
  `| _ => objs` branches in `endpointQueueRemove` are unreachable. Added
  documentation annotations.
- **AE4-F (U-23/IPC-01)**: Documented timeout sentinel `0xFFFFFFFF` dual-condition
  mitigation strategy in `Timeout.lean`. gpr x0 AND ipcState=.ready composite
  check prevents false positives. H3 migration path: dedicated `timedOut : Bool`
  TCB field.
- **AE4-G (U-27/A-T01)**: Added H3 preparation documentation for targeted TLB
  flush composition theorems in `VSpace.lean`. Documents required theorems
  (`targetedFlushByAsid_sufficient`, `targetedFlushByVAddr_sufficient`,
  `targetedFlush_crossAsid_isolation`) and building blocks from `TlbModel.lean`.
- **AE4-H (U-32/A-IB01)**: Proved `ipcBuffer_within_page` — IPC buffer cross-page
  safety is guaranteed by 512-byte alignment (512 divides 4096). Defense-in-depth
  for H3 hardware binding.
- **AE4-I (U-37/I-WC01)**: Documented complete slot targeting plumbing:
  `capRecvSlot` flows from `SyscallDecodeResult` through API dispatch to
  `ipcUnwrapCaps` → `ipcTransferSingleCap`. Per-slot CDT tracking is already
  in place. Receiver-side extraction deferred to H3 IPC buffer layout.
- **AE4-J**: Gate verification — `lake build` (256 jobs), `test_full.sh` Tier 0-3,
  zero sorry/axiom in all modified files.
- Version bump 0.25.18 → 0.25.19.

## v0.25.18 — WS-AE Phase AE3: Scheduler & SchedContext Correctness

Phase AE3 of WS-AE Production Audit Remediation. Addresses 12 findings across
the scheduler, SchedContext, and lifecycle subsystems — domain consistency,
CBS budget accounting, donation cleanup, effective priority, and PIP frame
theorems. All tests pass (test_full.sh Tier 0-3). Zero sorry/axiom.

### Changes
- **AE3-A (U-11)**: Enforced `sc.domain == tcb.domain` invariant in
  `schedContextBind` — rejects cross-domain binding with `.invalidArgument`.
  Added `boundThreadDomainConsistent` predicate and boot state theorem.
  `schedulerInvariantBundleExtended` expanded from 15-tuple to 16-tuple.
- **AE3-B/C (U-15, SC-07)**: Fixed `cancelDonation` for `.bound` case — checks
  `isActive` before enqueuing replenishment, clears replenishment queue on unbind
  to prevent stale entry accumulation. Added 3 transport lemmas for lifecycle and
  serviceRegistry preservation. `cancelDonation_scheduler_eq` refined to
  `cancelDonation_scheduler_runQueue_eq` (reflects replenishQueue modification).
- **AE3-D (U-16)**: Changed `resumeThread` preemption check from `tcb.priority`
  to `resolveEffectivePriority` for PIP-aware priority comparison.
- **AE3-E (S-03)**: Documented `handleYield` effective priority gap — re-enqueue
  uses base `tcb.priority` (correct for yield semantics; PIP boost applied at
  selection time).
- **AE3-F (U-14)**: Reset replenishment list in `schedContextConfigure` to
  `[{ amount := budget, eligibleAt := st.machine.timer }]`. Prevents stale
  entries from prior configuration referencing outdated budget/period values.
- **AE3-G (U-12, U-13)**: Documented CBS bandwidth bound 8× precision gap
  (`maxReplenishments × budget`) and admission control per-mille rounding
  (aggregate error ≤ n/1000).
- **AE3-H (SC-06)**: Deleted dead `Budget.refill` function (inverted semantics,
  unreachable, superseded by `applyRefill`).
- **AE3-I (S-01)**: Strengthened PIP frame theorems with full `invExt` threading.
  Proved `updatePipBoost_self_ipcState`, `blockingServer_ipcState_congr`, and
  completed `updatePipBoost_preserves_blockingServer` (blocking graph invariant
  under PIP boost). Uses `suffices`/`refine`/`by_cases` pattern.
- **AE3-J (SC-09)**: Documented `schedContextBind` pre-update read pattern for
  run queue insertion priority.
- **AE3-K (S-05)**: Documented `timeoutBlockedThreads` O(n) performance with
  deferred optimization to per-SchedContext bound-thread index.
- **AE3-L**: Gate verification — `lake build` (256 jobs), `test_smoke.sh`, zero
  sorry/axiom. Trace fixture updated for AE3-F replenishment queue reset.
- Version bump 0.25.17 → 0.25.18.

## v0.25.17 — AE1 Audit Remediation: Stale Comment Fixes & Documentation Sync

Post-implementation audit of WS-AE Phase AE1. Fixed stale constructor count
comments (32→34) in NI composition proofs and README documentation. Synchronized
Spanish README enforcement boundary count (30→33). Zero sorry/axiom.

### Changes
- **Composition.lean**: Fixed two stale comments referencing "32 constructors"
  to correctly state "34 constructors" (matching `kernelOperation_count` theorem).
- **README.md**: Updated `NonInterferenceStep` constructor count from 32 to 34.
- **docs/i18n/es/README.md**: Updated `NonInterferenceStep` constructor count
  from 32 to 34 and enforcement boundary count from 30 to 33.
- Version bump 0.25.16 → 0.25.17.

## v0.25.16 — WS-AE Phase AE2: Data Structure Hardening & Production Reachability

Phase AE2 of WS-AE Production Audit Remediation. Addresses 6 audit findings
(U-28, U-29, U-30, U-31, U-02, U-05) with RobinHood capacity enforcement,
RadixTree key-bounds validation, FrozenOps partial mutation fix, and Liveness
production reachability. All tests pass (test_full.sh Tier 0-3). Zero sorry/axiom.

### Changes
- **AE2-A (U-28)**: Enforced `4 ≤ capacity` in `RHTable` struct and `RHTable.empty`.
  Changed struct field from `hCapPos : 0 < capacity` to `hCapGe4 : 4 ≤ capacity`,
  added backward-compatible `hCapPos` accessor. Prevents tables with capacity 1-3
  from bypassing `insert_size_lt_capacity` guard. Updated 13 downstream files.
- **AE2-B (U-29)**: Added `buildCNodeRadixChecked` with runtime key-bounds
  validation. Falls back to empty radix on out-of-bound keys. Connecting theorems
  prove equivalence when keys are bounded (defense-in-depth for `UniqueRadixIndices`
  precondition).
- **AE2-C (U-30)**: Added `AUDIT-NOTE: D-RH02` annotations to all 4 fuel
  exhaustion points (`insertLoop`, `getLoop`, `findLoop`, `backshiftLoop`)
  documenting consequence, WF property, and kernel-safe fallback.
- **AE2-D (U-31)**: Refactored `frozenQueuePushTailObjects` to two-phase design:
  validate all object keys exist before any mutation, preventing partial state
  corruption on intermediate lookup failure.
- **AE2-E (U-02)**: Documented FrozenOps as experimental/future infrastructure
  with explicit non-production status.
- **AE2-F (U-05)**: Imported `Scheduler.Liveness` into production proof chain via
  `CrossSubsystem.lean`. All 7+1 Liveness modules now type-checked against actual
  scheduler on every build (import-cycle resolved via CrossSubsystem boundary).
- **AE2-G**: Verified all 5 PriorityInheritance submodules transitively reachable
  via Liveness import chain.

## v0.25.15 — WS-AE Phase AE1: API Dispatch & NI Composition

Phase AE1 of WS-AE Production Audit Remediation. Addresses 7 audit findings
(U-01, U-03, U-04, U-06, U-07, U-08, IF-01, IF-02) with dispatch parity fixes,
wildcard unreachability proofs, and non-interference composition for PIP/donation
and domain switching. All tests pass (test_full.sh Tier 0-3). Zero sorry/axiom.

### Changes
- **AE1-A (U-01)**: Unified `.tcbSetPriority` and `.tcbSetMCPriority` into
  `dispatchCapabilityOnly` — fixes checked/unchecked dispatch parity bug where
  `dispatchWithCapChecked` lacked these arms and returned `.illegalState`.
- **AE1-B (U-06)**: Moved `.tcbSetIPCBuffer` into `dispatchCapabilityOnly` and
  removed duplicate arms from both `dispatchWithCap` and `dispatchWithCapChecked`.
  `dispatchCapabilityOnly` now has 14 capability-only arms (was 11).
- **AE1-C**: Updated wildcard comments in both dispatch functions to reflect
  14 capability-only arms. Added per-arm structural equivalence theorems:
  `checkedDispatch_tcbSetPriority_eq_unchecked`,
  `checkedDispatch_tcbSetMCPriority_eq_unchecked`,
  `checkedDispatch_tcbSetIPCBuffer_eq_unchecked`.
- **AE1-D (U-07)**: Added `dispatchWithCapChecked_wildcard_unreachable` —
  proves all 25 `SyscallId` variants are handled (14 cap-only + 11 explicit).
  Updated `checkedDispatch_capabilityOnly_eq_unchecked` for 14 disjuncts.
- **AE1-E (IF-01/U-03)**: Extended NI composition with
  `ComposedNonInterferenceStep.switchDomain` + `composedNI_withSwitchDomain`.
  `KernelOperation` extended from 32 to 34 variants with
  `endpointCallWithDonationHigh` and `endpointReplyWithReversionHigh`.
- **AE1-F (IF-02/U-04)**: Full NI proofs for call/reply with donation/PIP:
  `updatePipBoost_preserves_projection` (all 13 projection components),
  `applyCallDonation_preserves_projection`,
  `propagatePIP_preserves_projection` (inductive over fuel),
  `revertPIP_preserves_projection`,
  `endpointCallWithDonation_preserves_lowEquivalent`,
  `endpointReplyWithReversion_preserves_lowEquivalent`.
  Supporting frame lemmas in `PriorityInheritance/Preservation.lean`:
  `updatePipBoost_objects_ne`, `updatePipBoost_toList_filter_neg`,
  `updatePipBoost_preserves_objects_invExt`.
- **AE1-G (U-08)**: Master dispatch NI theorem:
  `projPreserving_preserves_lowEquivalent` (Composition.lean) +
  `dispatchSyscallChecked_preserves_projection` (API.lean) — structural
  decomposition through TCB lookup → CNode lookup → cap resolution → inner dispatch.

## v0.25.14 — WS-AD Phase AD4/AD5: Cross-Subsystem Composition Proofs & Closure (F-08)

Phase AD4 of WS-AD Pre-Release Audit Remediation + Phase AD5 closure. Addresses
1 MEDIUM finding (F-08) with cross-subsystem composition bridge lemmas. All tests
pass (test_full.sh Tier 0-3). Zero sorry/axiom. **WS-AD PORTFOLIO COMPLETE.**

### Changes
- **AD4-A (F-08)**: Coverage matrix audit — all 33 kernel operations that modify
  `objects` preserve `services` and `serviceRegistry`. 30 operations preserve
  `objectIndex` (in-place mutations); 3 lifecycle retype operations may grow
  `objectIndex`. The 2 services-reading predicates are always frame-preserved.
- **AD4-B (F-08)**: 7 IPC operation bridge lemmas — `ipcSend`, `ipcReceive`,
  `ipcReply`, `ipcCall`, `ipcReplyRecv`, `notificationSignal`, `notificationWait`.
- **AD4-C (F-08)**: 7 Scheduler/Lifecycle operation bridge lemmas — `schedule`,
  `handleYield`, `timerTick`, `switchDomain`, `scheduleDomain`, `suspendThread`,
  `resumeThread`.
- **AD4-D (F-08)**: 7 Capability operation bridge lemmas — `cspaceMint`,
  `cspaceCopy`, `cspaceMove`, `cspaceMutate`, `cspaceInsertSlot`,
  `cspaceDeleteSlot`, `cspaceRevoke`.
- **AD4-E (F-08)**: 4 SchedContext operation bridge lemmas — `schedContextConfigure`,
  `schedContextBind`, `schedContextUnbind`, `schedContextYieldTo`.
- **AD4-F (F-08)**: 2 Priority management bridge lemmas — `setPriorityOp`,
  `setMCPriorityOp`.
- **AD4-G (F-08)**: 2 VSpace operation bridge lemmas — `vspaceMapPage`,
  `vspaceUnmapPage`.
- **AD4-H (F-08)**: 1 IPC buffer bridge lemma — `setIPCBufferOp`.
- **AD4-I (F-08)**: 3 Lifecycle retype bridge lemmas using monotone objectIndex
  variant — `lifecycleRetypeObject`, `lifecycleRetypeWithCleanup`,
  `retypeFromUntyped`.
- **AD4 core**: 2 core bridge theorems:
  (1) `crossSubsystemInvariant_objects_change_bridge` — for operations preserving
  `objectIndex` (30 operations);
  (2) `crossSubsystemInvariant_retype_bridge` — for lifecycle operations that
  grow `objectIndex` (3 operations), using `serviceGraphInvariant_monotone`.
- **AD5-A**: Documentation sync — WORKSTREAM_HISTORY, CHANGELOG, CLAIM_EVIDENCE_INDEX,
  GitBook chapter 12, codebase_map.json, README version badge, workstream plan
  status updates. Version bump 0.25.13 → 0.25.14.
- **AD5-B**: Final validation — `test_full.sh` pass, zero sorry/axiom, all 21
  findings accounted for, all 19 sub-tasks complete.

## v0.25.13 — WS-AD Phase AD3: Production Deployment Documentation (F-04, F-05, F-06, F-07)

Phase AD3 of WS-AD Pre-Release Audit Remediation. 6 sub-tasks. Addresses 3 HIGH
+ 1 MEDIUM findings with deployment-facing documentation. All tests pass
(test_full.sh Tier 0-3). Zero sorry/axiom.

### Changes
- **AD3-A/B (F-04, F-05, F-06, F-07)**: Created `docs/DEPLOYMENT_GUIDE.md`
  (238 lines) — production deployment guide with security model overview
  (non-BIBA integrity, NI boundary scope, covert channel analysis), mandatory
  labeling context override with code example, platform binding requirements,
  and 7-item pre-deployment checklist.
- **AD3-C (F-05)**: Added §11.2 "Information Flow and Non-Interference
  Boundary" to `docs/spec/SELE4N_SPEC.md` — documents 32 `NonInterferenceStep`
  constructors and service orchestration exclusion with
  `serviceOrchestrationOutsideNiBoundary` cross-reference.
- **AD3-D (F-04, F-07)**: Added SA-4 (non-BIBA integrity model) to
  `docs/SECURITY_ADVISORY.md` with formal witnesses; added SA-2 cross-reference
  to deployment guide override instructions.
- **AD3-E**: Updated `docs/CLAIM_EVIDENCE_INDEX.md` with 4 deployment claims.
- **AD3-F**: Updated GitBook chapter 28 with deployment findings table.
- Version bump 0.25.12 → 0.25.13.

## v0.25.12 — WS-AD Phase AD2: Code Quality Hardening (F-02, F-03)

Phase AD2 of WS-AD Pre-Release Audit Remediation. 4 sub-tasks. All tests pass
(full build + test_smoke.sh). Zero sorry/axiom.

### Changes
- **AD2-A (F-02)**: Added `endpointQueuePopHeadFresh` convenience wrapper in
  `DualQueue/Core.lean` that returns the post-state TCB with cleared queue
  links, avoiding the stale-snapshot footgun documented under WS-L1/L1-A.
  The original `endpointQueuePopHead` returns the pre-dequeue TCB whose
  queue link fields are stale; the new variant re-fetches from post-state.
- **AD2-B (F-02)**: Added staleness annotations at all 3 call sites of
  `endpointQueuePopHead` in `DualQueue/Transport.lean` (`endpointSendDual`,
  `endpointReceiveDual`, `endpointCall`), noting that the returned TCB has
  stale queue links and callers should use `st'` for current state.
- **AD2-C (F-03)**: Enhanced module-level docstring in
  `IPC/Operations/CapTransfer.lean` with explicit F-03 error-to-noSlot
  conversion documentation. Clarifies that `ipcTransferSingleCap` errors
  are intentionally converted to `.noSlot` by `ipcUnwrapCapsLoop`, matching
  seL4's cursor-preservation semantics. No capability can be silently
  installed or lost.
- **AD2-D**: Gate verification — module builds (Core, CapTransfer, Transport),
  full build (236 jobs), and smoke tests all pass.
- Codebase map regenerated; version bump 0.25.11 → 0.25.12.

## v0.25.11 — WS-AD Phase AD1: Integration Fix (F-01)

Phase AD1 of WS-AD Pre-Release Audit Remediation. 3 sub-tasks. All tests pass
(full build + test_full.sh Tier 0-3). Zero sorry/axiom.

### Changes
- **AD1-A/B (F-01)**: Integrated 2 orphaned SchedContext preservation modules
  into the production proof chain. `Preservation.lean` (7 theorems: Z5-M,
  Z5-I, Z5-K, Z5-L, Z5-N1/N2) and `PriorityPreservation.lean` (14 theorems:
  D2-G/H/I/J transport lemmas + authority non-escalation) were fully proven
  but unreachable — not imported by any production module.
- **Import cycle resolution**: Direct import into `SchedContext/Invariant.lean`
  (the re-export hub) would create a dependency cycle via
  `Object/Types → SchedContext → Invariant → Preservation → Operations →
  Model.State → Object/Types`. Resolved by importing both modules from
  `CrossSubsystem.lean`, which sits downstream of the cycle boundary and is
  the natural integration point for cross-subsystem preservation theorem
  composition. Chain: `CrossSubsystem → Architecture/Invariant → API.lean`.
- **AD1-C**: Verified 21 theorems (7 + 14) reachable from production import
  chain. Module build (69 jobs), full build (236 jobs), smoke test, and
  full test suite (Tier 0-3) all pass.
- Workstream plan updated with import-cycle resolution documentation.
- Version bump 0.25.10 → 0.25.11.

## v0.25.10 — WS-AC Phase AC6: Documentation, Testing & Closure

Phase AC6 of WS-AC Comprehensive Audit Remediation. 7 sub-tasks. All tests pass
(full build + test_full.sh Tier 0-3). Zero sorry/axiom. **WS-AC PORTFOLIO
COMPLETE** (6 phases, 42 sub-tasks, v0.25.3-v0.25.10).

### Changes
- **T-03 (AC6-A)**: New `tests/DecodingSuite.lean` — 40 dedicated tests for
  Layer 1 (RegisterDecode: `decodeSyscallId`, `decodeMsgInfo`, `decodeCapPtr`,
  `validateRegBound`) and Layer 2 (SyscallArgDecode: 20 per-syscall decode
  functions across CSpace, VSpace, Lifecycle, Service, Notification,
  SchedContext, TCB families). Covers valid decode, insufficient registers,
  boundary conditions, domain-specific validation failures. Registered in
  `lakefile.toml` and `test_tier2_negative.sh`.
- **AC6-B**: Decode layer test coverage convention (#10) added to
  DEVELOPMENT.md §5b audit-driven coding conventions.
- **AC6-C**: WORKSTREAM_HISTORY.md updated with WS-AC completion entry.
- **AC6-D**: Corrected severity table addendum (Section 16) appended to
  AUDIT_v0.25.3_COMPREHENSIVE.md — 16 errata catalogued with corrected entries,
  reclassifications (A-01: Medium→Info, X-05: Medium→Low), and recommendation
  to use Sections 1-12 as authoritative source.
- **AC6-E**: `codebase_map.json` regenerated (16 test suites, 11,318 test LoC).
- Version bump 0.25.9 → 0.25.10.

## v0.25.9 — WS-AC Phase AC5: Cross-Cutting & Infrastructure

Phase AC5 of WS-AC Comprehensive Audit Remediation. 8 sub-tasks, 9 files
modified. All tests pass (full build + test_full.sh Tier 0-3). Zero sorry/axiom.

### Changes
- **X-05 (AC5-A)**: 18 new pairwise field-disjointness theorems for SchedContext
  predicates. Complete C(8,2)=28 pair coverage with compile-time `native_decide`
  summary theorem.
- **X-08 (AC5-B)**: GitBook content-hash drift detection in `test_docs_sync.sh`.
- **S-05 (AC5-C)**: `saveOutgoingContext_scheduler` theorem verified and
  cross-referenced.
- **F-04 (AC5-D)**: Codebase-wide catch-all audit — zero risky patterns on
  `KernelError`.
- **F-02 (AC5-E)**: `inter_valid` strengthened (only needs left operand valid),
  `subset_sound` (bitwise inclusion via `Nat.testBit_and`), `mem_bit_bounded`.
- **F-03 (AC5-F)**: `storeObjectChecked` coding convention verified.
- **IF-01 (AC5-G)**: `enforcementBoundary_is_complete` verified compiling.
- Version bump 0.25.8 → 0.25.9.

## v0.25.8 — WS-AC Phase AC4: Architecture & Platform Tightening

Phase AC4 of WS-AC Comprehensive Audit Remediation. 5 sub-tasks, 20 files
modified. All tests pass (full build + test_full.sh Tier 0-3). Zero sorry/axiom.

- **AC4-A (A-04)**: `physicalAddressBound` documented as proof-layer default
  only — production code uses `vspaceMapPageCheckedWithFlushFromState`
  (state-aware, reads `st.machine.physicalAddressWidth`). 2 regression tests:
  PA at 2^44 rejected on RPi5 (44-bit), PA at 2^44-1 accepted.
- **AC4-B (F-02)**: `AccessRightSet` constructor safety model documented —
  raw `mk` is TCB-internal, 5 safe constructors with validity theorems,
  operational safety argument for `mem`/`subset`/`inter`/`union`. AC4-B notes
  added to `union`/`inter` on raw `⟨bits⟩` return semantics.
- **AC4-C (F-01)**: Typed Identifier Safety Model added to Prelude.lean —
  unbounded `Nat` design rationale, ABI boundary validation chain, internal
  kernel trust model, hardware deployment contract.
- **AC4-D (IF-01)**: Enforcement boundary completeness witness —
  `SyscallId.all` (25 variants), `all_length` + `all_complete` compile-time
  checks, `syscallIdToEnforcementName` bridge, `enforcementBoundaryComplete`
  Bool check, `enforcementBoundary_is_complete` (`native_decide` theorem).
  Fails at compile time if any `SyscallId` is missing from enforcement boundary.
  Enforcement boundary expanded 30→33 entries with dedicated VSpace
  (`vspaceMapPageCheckedWithFlushFromState`, `vspaceUnmapPageWithFlush`) and
  service (`revokeService`) capability-only entries. All `syscallIdToEnforcementName`
  mappings verified against API dispatch for semantic accuracy.
- **AC4-E**: Full build + test_full.sh (Tier 0-3) pass.
- Audit-driven coding conventions extended (F-02, A-04, IF-01).
- Version bump 0.25.7 → 0.25.8.

## v0.25.7 — WS-AC Phase AC3: IPC Atomicity & Invariant Strengthening

Phase AC3 of WS-AC Comprehensive Audit Remediation. 6 sub-tasks, 7 files
modified. All tests pass (232-job build + smoke). Zero sorry/axiom.

- **AC3-A (I-02/I-03)**: Atomicity contracts documented for `donateSchedContext`
  and `returnDonatedSchedContext` — 3-step `storeObject` mutation sequences,
  monad-level atomicity (`.error` carries no state), hardware-level atomicity
  (interrupts disabled during kernel transitions).
- **AC3-B (I-02 proof)**: Two atomicity theorems in `SchedulerLemmas.lean`:
  `donateSchedContext_ok_implies_sc_bound` (precondition witness — SchedContext
  found and bound to client) and `donateSchedContext_ok_server_donated`
  (postcondition witness — server TCB has `.donated` binding in post-state,
  proving both `storeObject` calls succeeded).
- **AC3-C (I-04)**: `Badge.bor` unbounded-Nat intermediate documented —
  `ofNatMasked` applies `% machineWordMax`, `bor_valid` proves result validity.
- **AC3-D (API-01)**: `resolveExtraCaps` silent-drop semantics documented.
  New `chain34ResolveExtraCapsSilentDrop` test in OperationChainSuite (3
  addresses, 2 valid + 1 empty slot → resolved count = 2).
- **AC3-E (F-03)**: `storeObjectChecked` capacity-enforcing variant added to
  `State.lean`. Rejects new insertions at `maxObjects`, allows in-place updates.
  3 theorems: `storeObjectChecked_preserves_objectIndexBounded`,
  `storeObjectChecked_existing_eq_storeObject`,
  `storeObjectChecked_headroom_eq_storeObject`.
- **AC3-F**: Full build (232 jobs) + smoke tests pass.

## v0.25.6 — WS-AC Phase AC2: Scheduler & SchedContext Hardening

Phase AC2 of WS-AC Comprehensive Audit Remediation. 7 sub-tasks, 12 files
modified. All tests pass (232-job build + Tier 0–3). Zero sorry/axiom.

- **AC2-A (S-02/SC-01)**: `timeoutBlockedThreads` O(n) cost documented with
  quantified worst-case analysis (n ≤ 65536 objects, triggered once per CBS
  period). Future optimization path noted (per-SchedContext bound-thread index).
- **AC2-B (S-03)**: `blockingChain` fuel-truncation behavior documented —
  fuel default (`objectIndex.length`), `blockingAcyclic` invariant dependency,
  silent truncation on cycle, consequence analysis.
- **AC2-C (S-04)**: `timerTick` and `timerTickBudget` migrated from hardcoded
  `defaultTimeSlice` to configurable `st.scheduler.configDefaultTimeSlice`.
  18 proof sites in Preservation.lean updated. New `hConfigTS` hypothesis
  (`configDefaultTimeSlice > 0`) added to `timerTick_preserves_timeSlicePositive`,
  `timerTick_preserves_currentTimeSlicePositive`, and
  `timerTick_preserves_schedulerInvariantBundleFull`. TraceModel.lean and
  InformationFlow/Operations.lean updated.
- **AC2-D (S-05)**: `switchDomain` dual-state pattern documented — reads from
  `st`, returns `stSaved`, formal reference to `saveOutgoingContext_scheduler`.
- **AC2-E (S-06)**: RunQueue flat-list complexity documented (O(1)/O(k)/O(n)/O(p)
  breakdown with RPi5 acceptability rationale).
- **AC2-F (F-04)**: `KernelError` catch-all lint convention added (doc-comment
  on inductive + DEVELOPMENT.md coding convention).
- Audit-driven coding conventions and performance characteristics table added
  to DEVELOPMENT.md.
- Version bump 0.25.5 → 0.25.6.

## v0.25.5 — WS-AC Phase AC1: High-Severity Audit Fixes (Audit-Verified)

Phase AC1 of WS-AC Comprehensive Audit Remediation (v0.25.3 baseline).
End-to-end audit verified: all 9 sub-tasks complete, zero sorry/axiom.

- **AC1-A (S-01)**: `hasSufficientBudget` changed from fail-open to fail-closed.
  Missing SchedContext now returns `false` (defense-in-depth). Unreachable under
  `schedContextStoreConsistent` invariant. All preservation proofs pass unchanged.
- **AC1-B/C (I-01)**: `waitingThreadsPendingMessageNone` preservation proofs
  refactored to their semantic home. New `WaitingThreadHelpers.lean` extracts
  7 primitive helpers from Structural.lean, breaking a circular import dependency.
  3 operation-level theorems (`notificationSignal_preserves_*`,
  `notificationWait_preserves_*`, `notificationWake_pendingMessage_was_none`)
  moved from Structural.lean to NotificationPreservation.lean with full
  machine-checked proofs (replacing comment cross-references). Net ~330 lines
  removed from Structural.lean.
- **AC1-D (C-01)**: Production syscall dispatch now routes through
  `cspaceMintWithCdt` (CDT-tracked) — minted capabilities are revocable via
  `cspaceRevoke`. Change path: `dispatchWithCap` → `cspaceMintWithCdt`,
  `cspaceMintChecked` → `cspaceMintWithCdt`. Non-interference proof updated
  with CDT-pipeline preservation (`cdt_only_preserves_projection'`,
  `ensureCdtNodeForSlot_preserves_projection'`). Enforcement soundness and
  dispatch delegation theorems updated. `cspaceMint` retained as CDT-untracked
  base operation for internal composition and proof decomposition.
- **AC1-G**: 5 negative regression tests for budget fail-closed behavior.
- **AC1-H**: 2 regression tests verifying CDT edge tracking difference between
  `cspaceMint` (no edges) and `cspaceMintWithCdt` (adds edge).
- Cross-subsystem verification: Preservation.lean, WCRT, CrossSubsystem,
  PriorityInheritance all build unchanged. Zero sorry/axiom.
- Version bump 0.25.3 → 0.25.5.

## v0.25.3 — D5 Audit: Surface Anchor Count Correction

Comprehensive audit of Phase D5 (Bounded Latency Theorem) implementation.

- **Surface anchor count fix**: `LivenessSuite.lean` correctly has 58 `#check`
  surface anchors (was incorrectly documented as 38/46/48 across docs).
  Updated: LivenessSuite output string, CLAUDE.md, DEVELOPMENT.md, SPEC,
  CLAIM_EVIDENCE_INDEX, WORKSTREAM_HISTORY, GitBook chapter 12, workstream plan.
- **D5 proof audit**: All 7 Liveness submodules verified — zero sorry/axiom,
  no vacuous theorems, no shortcuts. `bounded_scheduling_latency_exists` uses
  genuine decomposition (domain rotation + band exhaustion). `countHigherOrEqual_mono_threshold`
  proved by induction with accumulator generalization. PIP integration sound.
- Version bump 0.25.2 → 0.25.3.

## v0.25.2 — D6: API Surface Integration & Closure (WS-AB Complete)

Phase D6 of WS-AB Deferred Operations workstream. Final integration phase
closing the WS-AB portfolio (6 phases, 90 sub-tasks, v0.24.0–v0.25.2).

- **D6-A**: Enforcement boundary completeness verified — 30 entries covering
  all 25 `SyscallId` variants (11 policy-gated, 5 capability-only base,
  3 read-only, 3 internal, 3 SchedContext, 2 lifecycle, 2 priority, 1 IPC buffer).
- **D6-B**: `dispatchWithCap_wildcard_unreachable` covers all 25 variants.
- **D6-C**: `frozenOpCoverage_count = 20` (20/25 syscalls have frozen
  equivalents; 5 builder-only excluded).
- **D6-D**: Rust ABI synchronized — `SyscallId` 20→25 variants
  (`TcbSuspend`=20, `TcbResume`=21, `TcbSetPriority`=22,
  `TcbSetMCPriority`=23, `TcbSetIPCBuffer`=24). `KernelError`
  +`AlignmentError`=43 (44 variants total). New `rust/sele4n-abi/src/args/tcb.rs`
  module: `SuspendArgs`, `ResumeArgs`, `SetPriorityArgs`, `SetMCPriorityArgs`,
  `SetIPCBufferArgs` with encode/decode/roundtrip tests.
  Updated conformance tests across all 3 Rust crates.
  New `rust/sele4n-sys/src/tcb.rs` module: `tcb_suspend`, `tcb_resume`,
  `tcb_set_priority`, `tcb_set_mcp`, `tcb_set_ipc_buffer` high-level wrappers.
- **D6-D audit fix**: Priority/MCP out-of-range error corrected from
  `InvalidSyscallArgument` (discriminant 41) to `InvalidArgument` (discriminant
  39), matching Lean `decodeSetPriorityArgs`/`decodeSetMCPriorityArgs`.
- **D6-E**: Comprehensive test suite green — Lean Tier 0-3 + Rust 231 tests,
  zero warnings.
- **D6-F**: Spec §5.14 updated with D4 (PIP) and D5 (WCRT) subsections.
- **D6-G**: Claims index updated with D6 closure claim.
- **D6-H**: CLAUDE.md workstream context updated to WS-AB COMPLETE.
- **D6-I**: README metrics, WORKSTREAM_HISTORY, CHANGELOG synchronized.
- **D6-J**: Website link manifest verified.
- Zero sorry/axiom. **WS-AB PORTFOLIO COMPLETE.**

## v0.25.1 — D5 Audit: Bounded Latency Theorem Refinement

- Strengthen `bounded_scheduling_latency_exists`: proper existential trace-level theorem with domain rotation + band exhaustion composition
- Replace trivial tautologies: `selectedAt_budget_witness` → `budget_always_available_unbound` + `budget_available_when_positive`
- Replace vacuous `higherBandExhausted` (conclusion was `True`) with substantive version using `eventuallyExits`
- Add `higherBandExhausted_when_no_higher`: vacuous case when no higher-priority threads exist
- Replace trivial `replenishment_queue_eligibility` (x=x) with `replenishment_within_period` + `replenishment_dead_time_exact`
- Add `fifo_head_zero_wait`: base case for FIFO progress at position 0
- Expand surface anchor tests from 38 to 46
- Zero sorry/axiom, all test_full.sh passes

## [0.23.23] — AA2: CI & Infrastructure Hardening

Phase AA2 of WS-AA Comprehensive Audit Remediation. Hardened CI supply chain,
fixed shell scripting vulnerabilities, and locked down test fixture injection.

- **AA2-A**: Replaced `curl | sh` Rust toolchain install in CI with SHA-pinned
  `dtolnay/rust-toolchain` action (v1, commit `a54c7afa`), toolchain `1.82.0`.
  Eliminates supply-chain risk from unverified installer script (H-4).
- **AA2-B**: Added `RUST_TOOLCHAIN_VERSION="1.82.0"` documentation variable in
  `setup_lean_env.sh` for consistency with existing Lean toolchain SHA-pinning.
- **AA2-C**: Fixed `$STAGED_LEAN_FILES` word-splitting vulnerability in
  `pre-commit-lean-build.sh`. Replaced unquoted variable with `mapfile -t`
  bash array and array-safe iteration `"${STAGED_LEAN_FILES[@]}"` (H-5).
- **AA2-D**: Made `verify_toolchain_sha256` fail-closed for unrecognized
  architectures. Changed `return 0` (silent skip) to `return 1` with error
  message (M-7).
- **AA2-E**: Added `git ls-files --error-unmatch` validation for
  `TRACE_FIXTURE_PATH` in `test_tier2_trace.sh` to reject non-tracked fixture
  files (M-8).
- **AA2-F**: JSON-escaped `$lane` variable in `ci_capture_timing.sh` via
  Python `json.dumps`, preventing invalid JSON from special characters (L-30).
- Findings addressed: H-4, H-5, M-7, M-8, L-30.
- Zero sorry/axiom. `test_smoke.sh` green.

## [0.23.22] — AA1: Rust ABI Type Synchronization

Phase AA1 of WS-AA Comprehensive Audit Remediation. Synchronized Rust ABI types
with the Lean model, closing three HIGH-severity Lean-Rust desync gaps that made
the entire SchedContext subsystem unreachable from Rust userspace.

- **AA1-A**: Added `SchedContextConfigure` (17), `SchedContextBind` (18),
  `SchedContextUnbind` (19) to `SyscallId` enum. COUNT updated 17→20.
  All three require `.write` access (matching Lean API.lean:381-383).
- **AA1-B**: 6 SyscallId conformance tests (roundtrip, boundary, required_rights).
- **AA1-C**: Added `IpcTimeout = 42` to `KernelError` enum (43 variants total).
  Updated `from_u32`, `Display`, decode boundary, all inline tests.
- **AA1-D**: Added `SchedContext = 6` to `TypeTag` enum (7 variants total).
  Updated `from_u64`, inline tests, lifecycle retype boundary tests (6→7).
- **AA1-E**: Updated `lib.rs` doc comments ("34-variant" → "43-variant",
  "14-variant" → "20-variant").
- **AA1-F**: Created `sched_context.rs` module with `SchedContextConfigureArgs`
  (5 fields: budget, period, priority, deadline, domain; priority/domain ≤ 255
  validation), `SchedContextBindArgs` (1 field: threadId),
  `SchedContextUnbindArgs` (empty). 7 inline + 9 conformance tests.
- **AA1-G**: 2 conformance tests for `TypeTag::SchedContext` retype integration.
- **AA1-H**: 4 conformance tests for `KernelError::IpcTimeout` (roundtrip,
  distinctness, result wrapping, boundary).
- **Audit fixes**: Stale comment in `lifecycle.rs` ("values > 5" → "> 6"),
  stale TypeTag count in `sele4n-abi/src/lib.rs` (6→7), stale syscall count
  in `sele4n-sys/src/lib.rs` (17→20), stale `decode.rs` boundary (42→43).
- Findings addressed: H-1, H-2, H-3, L-25, L-29.
- 200 Rust tests pass (77 abi + 76 conformance + 12 sys + 35 types).
- Zero sorry/axiom. `test_smoke.sh` green.

## [0.23.21] — Z10: Documentation & Closure — WS-Z PORTFOLIO COMPLETE

Final documentation synchronization for the WS-Z Composable Performance Objects
workstream. All 10 phases (Z1–Z10, 213 sub-tasks) delivered.

- **Z10-A1/A2**: Added 5 new subsections to `SELE4N_SPEC.md` (§8.12.2–§8.12.6):
  ReplenishQueue (Z3), Scheduler Integration (Z4), Capability Binding (Z5),
  API Surface (Z8), Cross-Subsystem Composition (Z9)
- **Z10-B**: Updated `DEVELOPMENT.md` with Z9/Z10 phase entries and
  ReplenishQueue/CrossSubsystem build targets
- **Z10-C**: Updated `WORKSTREAM_HISTORY.md` with Z10 closure entry
- **Z10-D**: Updated `CLAIM_EVIDENCE_INDEX.md` with 4 key verified claims:
  CBS bandwidth isolation, donation chain acyclicity, timeout termination,
  admission control soundness
- **Z10-E**: Regenerated `codebase_map.json` (v0.23.21, 113 files, 79,743 LoC,
  2,295 proved declarations)
- **Z10-F**: Added GitBook §30 (Documentation & Closure) to proof/invariant map
- **Z10-G**: Updated `README.md` metrics from `codebase_map.json`
- **Z10-H**: Updated `CLAUDE.md` source layout (Operations.lean,
  Invariant/Preservation.lean) and active workstream context
- **Z10-I**: Updated `website_link_manifest.txt` with Budget.lean,
  ReplenishQueue.lean, Operations.lean, Invariant.lean, Timeout.lean,
  Donation.lean, and SchedContext/ directory
- Zero sorry/axiom. All tests pass (full).

## [0.23.20] — Z9 Audit: Documentation Accuracy & Disjointness Completeness

Post-implementation audit of Z9 Invariant Composition & Cross-Subsystem phase.

- **AUD-1**: Module docstring in `CrossSubsystem.lean` updated to list all 8
  predicates (was missing 3 new SchedContext predicates).
- **AUD-2**: `schedContextNotDualBound` docstring corrected — first sentence
  now accurately describes the predicate's semantics (prevents ANY two threads
  from referencing the same SchedContext, not just bound+donated).
- **AUD-3**: `crossSubsystemInvariant_composition_complete` extended from 14
  to 16 conjuncts — added 2 missing disjointness witnesses:
  `schedContextRunQueueConsistent` ↔ `registryDependencyConsistent` and
  `schedContextRunQueueConsistent` ↔ `serviceGraphInvariant`.
- **AUD-4**: Z9-N/O frame-lemma docstrings clarified as frame-case building
  blocks, documenting what full mutation-level preservation would require.
- Regenerated `docs/codebase_map.json`.
- Zero sorry/axiom. All tests pass (smoke + full).

## [0.23.19] — Z9: Invariant Composition & Cross-Subsystem

Complete cross-subsystem invariant integration for SchedContext objects.
Extends all invariant bundles, boot proofs, and operation preservation
to cover SchedContext consistency. **WS-Z PORTFOLIO COMPLETE.**

- **Z9-A/B/C**: 3 new cross-subsystem predicates: `schedContextStoreConsistent`
  (TCB→SC object exists), `schedContextNotDualBound` (unique SC binding),
  `schedContextRunQueueConsistent` (runnable threads have positive budget)
- **Z9-D**: `crossSubsystemInvariant` extended from 5 to 8 predicates
- **Z9-E**: Field-disjointness analysis: 14 pairwise witnesses for 8 predicates
- **Z9-F**: 3 frame lemmas for new predicates
- **Z9-G**: `proofLayerInvariantBundle` extended from 9 to 10 conjuncts
  (added `schedulerInvariantBundleExtended`)
- **Z9-I**: `bootSafeObject` extended with SchedContext wellFormedness (6th conjunct)
- **Z9-J**: Boot-time proofs for all 10 bundle components
- **Z9-L/M/N/O**: Operation preservation theorems (timerTick, schedule,
  donation, cleanup/destroy)
- Test fixture updated (`crossSubsystemFieldSets` 5→8)
- Zero sorry/axiom. All tests pass (smoke + full).

## [0.23.18] — Z8 Audit: Defense-in-Depth Hardening

Post-implementation audit of Z8 API Surface & Syscall Wiring phase.

- **AUD-1**: `frozenSchedContextUnbind` — replaced silent fallback on
  `FrozenMap.set` failure with explicit `.error .objectNotFound`. Prevents
  theoretical inconsistent state where TCB is unbound but SC retains stale
  binding. Aligns with `frozenSchedContextBind` error-handling pattern.
- Regenerated `docs/codebase_map.json`.
- Zero sorry/axiom. All tests pass (smoke + full).

## [0.23.17] — Z8: API Surface & Syscall Wiring

Complete public API surface for SchedContext operations. Wire new operations
through decode → dispatch → invoke pipeline. Add frozen operation variants.
Expand enforcement boundary. Update test harness and fixtures.

- **Z8-B**: 3 error-exclusivity theorems: `decodeSchedContextConfigureArgs_error_iff`
  (fails iff `< 5` MRs), `decodeSchedContextBindArgs_error_iff` (fails iff `< 1` MR),
  `decodeSchedContextUnbindArgs_error_iff` (never fails — no MRs required)
- **Z8-H**: 3 frozen SchedContext operations: `frozenSchedContextConfigure`,
  `frozenSchedContextBind`, `frozenSchedContextUnbind` — passthrough-frozen
  (no internal RHTables), operate via `FrozenMap.get?`/`FrozenMap.set`
- **Z8-I**: `frozenTimerTickBudget` — CBS budget-aware timer tick in frozen
  state, mirrors `timerTickBudget` (Z4-F) with dequeue-on-dispatch semantics
- **Z8-M**: `enforcementBoundary` expanded from 22 to 25 entries (3 new
  `.capabilityOnly` entries for schedContextConfigure/Bind/Unbind)
- **Z8-J**: 6 budget lifecycle trace scenarios (Z8J-001 through Z8J-006):
  create+configure, bind, per-tick decrement, 4-tick partial, exhaustion
  with preemption, replenishment with budget restoration
- **Z8-L**: 8 negative-state tests (Z8-L-01 through Z8-L-08): configure
  non-existent, zero period, budget>period, bind non-existent, double-bind,
  TCB already bound, unbind no bound thread, unbind non-existent
- **Frozen op coverage**: 12 → 15 SyscallId arms (SchedContext operations
  now frozen-phase capable); `frozenOpCoverage_count` updated
- **Test ripple**: InformationFlowSuite enforcement boundary count assertions
  updated (22→25 total, 7→10 capability-only)
- Zero sorry/axiom. All tests pass (smoke + full).

## [0.23.16] — Z7 Audit: Documentation Hardening + Verification

Comprehensive audit pass 2 of Phase Z7 SchedContext Donation.

- **Gitbook update**: Chapter 12 `ipcInvariantFull` count updated from
  10-conjunct to 14-conjunct; `coreIpcInvariantBundle` description updated
  to list all 14 sub-invariants including Z7 donation invariants
- **Spec update**: Section 8.7 added to `SELE4N_SPEC.md` documenting
  donation protocol, architecture, invariants, lifecycle integration,
  and defense-in-depth measures
- **Spec active workstream**: Updated to "WS-Z Phases Z1–Z7 COMPLETE"
- Zero sorry/axiom. All tests pass (smoke + full).

## [0.23.15] — Z7: SchedContext Donation / Passive Servers

Implement SchedContext lending during IPC Call/Reply, enabling passive servers
that consume zero CPU when idle (seL4 MCS passive server pattern).

- **Core operations**: `donateSchedContext`, `returnDonatedSchedContext`,
  `cleanupDonatedSchedContext`, `cleanupActiveDonation` (Endpoint.lean)
- **Post-processing helpers**: `applyCallDonation`, `applyReplyDonation`,
  `cleanupPreReceiveDonation` (Donation.lean)
- **Donation-aware wrappers**: `endpointCallWithDonation`,
  `endpointReplyWithDonation`, `endpointReplyRecvWithDonation` (Donation.lean)
- **API dispatch wiring**: Both unchecked and checked dispatch arms (`.call`,
  `.reply`, `.replyRecv`) apply donation post-processing
- **4 new invariants** (ipcInvariantFull extended from 10 to 14 conjuncts):
  `donationChainAcyclic`, `donationOwnerValid`, `passiveServerIdle`,
  `donationBudgetTransfer`
- **Lifecycle integration**: `cleanupDonatedSchedContext` in
  `lifecyclePreRetypeCleanup` ensures donated SchedContexts are returned
  before TCB destruction
- **Boot safety**: `bootObjectSafe` extended with `schedContextBinding = .unbound`
- **Proof ripple**: Structural.lean (10 composition theorems), Capability
  Invariant/Preservation.lean (5 extractors), Architecture/Invariant.lean
  (timer advancement + default state), Platform/Boot.lean (14-conjunct bundle)
- **Preservation theorems**: `donateSchedContext_scheduler_eq`,
  `returnDonatedSchedContext_scheduler_eq`, `applyCallDonation_scheduler_eq`,
  `cleanupDonatedSchedContext_scheduler_eq`
- **8 trace tests**: Z7D-001 through Z7D-008
- **New file**: `SeLe4n/Kernel/IPC/Operations/Donation.lean`
- Zero sorry/axiom

## [0.23.14] — Z6 Audit Pass 2: Edge Case Test Coverage

Second comprehensive audit of Phase Z6 Timeout Endpoints.

- **AUD-Z6-5**: 4 new edge-case trace tests (SCO-032 through SCO-035):
  - SCO-032: 3-thread mid-queue removal — validates predecessor/successor relinking
  - SCO-033: receiveQ removal — verifies sendQ remains unchanged
  - SCO-034: timeoutThread on `blockedOnCall` thread — confirms state reset + error code
  - SCO-035: multi-thread `timeoutBlockedThreads` — both threads timed out correctly
- Cross-subsystem ripple verified: all `ipcInvariantFull` 10-tuple construction/
  destructuring sites confirmed correct (Structural.lean, Boot.lean,
  Architecture/Invariant.lean, Capability/Invariant/Preservation.lean).
- Transport lemma coverage verified: 4 subsystem fields (scheduler, cdt, lifecycle,
  services) have explicit equality proofs.
- Documentation accuracy verified against code (SELE4N_SPEC.md, gitbook ch.12).
- Scenario registry updated (4 new entries).

Zero sorry/axiom. All tiers pass (0-3).

## [0.23.13] — Z6 Audit: Documentation Hardening + Test Coverage

Comprehensive audit of Phase Z6 Timeout Endpoints implementation.

- **AUD-Z6-1**: `endpointQueueRemove` defensive coding documented — `| _ => objs`
  fallback on predecessor/successor lookup explained as invariant-guaranteed dead
  code under `ipcStateQueueMembershipConsistent` and `queueNextBlockingConsistent`.
  Relationship to existing `endpointQueueRemoveDual` (Transport.lean) documented.
- **AUD-Z6-2**: `timeoutThread` precondition documented — caller
  `timeoutBlockedThreads` validates ipcState via `tcbBlockingInfo` before calling.
- **AUD-Z6-3**: 12 new trace tests (SCO-020 through SCO-031) covering:
  endpointQueueRemove head/tail/error paths, timeoutThread success/error/re-enqueue,
  timeoutBlockedThreads matching/non-matching SC, timeoutAwareReceive timeout
  detection/normal path.
- **AUD-Z6-4**: `timeoutAwareReceive` docstring corrected — describes actual
  timeout detection semantics, `_endpointId` reserved-for-future-use documented.
- Scenario registry updated (12 new entries in `scenario_registry.yaml`).
- `codebase_map.json` regenerated.

Zero sorry/axiom. All tiers pass (0-3).

## [0.23.12] — Z6: Timeout Endpoints

Phase Z6 implements budget-driven timeout for IPC blocking operations. When a
thread's SchedContext budget expires while blocked on send/receive/call/reply,
the thread is unblocked with a timeout error code and re-enqueued in the RunQueue.

- **Z6-A**: Added `timeoutBudget : Option SchedContextId` field to TCB struct
  for tracking which SchedContext governs a blocking IPC operation's timeout.
- **Z6-C**: `timeoutThread` operation: removes thread from endpoint queue,
  resets IPC state to `.ready`, clears pending message and timeout budget,
  writes timeout error code (`0xFFFFFFFF`) to register x0, re-enqueues via
  `ensureRunnable`. `timeoutAwareReceive` wrapper detects prior timeout.
- **Z6-D**: `endpointQueueRemove` mid-queue splice-out: O(1) removal of any
  thread from an intrusive dual-queue endpoint. Patches predecessor/successor
  links, updates head/tail pointers, clears removed thread's queue fields.
  `endpointQueueRemove_preserves_objects_invExt` proven.
- **Z6-E/F**: Integrated timeout into `timerTickBudget`: on budget exhaustion
  (Z4-F3 branch), calls `timeoutBlockedThreads` to unblock all threads bound
  to the exhausted SchedContext. `processReplenishmentsDue` documented as
  not requiring timeout action.
- **Z6-G**: Design optimization — timeout scan uses `schedContextBinding.scId?`
  match in timer tick handler instead of modifying IPC store functions. Zero
  changes to existing IPC operations, zero existing proof breakage.
- **Z6-H**: `IpcTimeoutResult` inductive type (`.completed msg | .timedOut`).
- **Z6-J**: `blockedThreadTimeoutConsistent` invariant: threads with
  `timeoutBudget = some scId` must reference a valid SchedContext and be in a
  blocking IPC state. Extended `ipcInvariantFull` from 9 to 10 conjuncts.
  Full ripple fix across Structural.lean (~12 sites), Boot.lean,
  Architecture/Invariant.lean, Capability/Invariant/Preservation.lean.
- **Z6-K/M**: Transport lemmas for `endpointQueueRemove`: scheduler, CDT,
  lifecycle, and services backward preservation theorems.
- **New file**: `SeLe4n/Kernel/IPC/Operations/Timeout.lean`
- **Boot safety**: Extended `bootSafeObject` TCB clause with
  `timeoutBudget = none` requirement.

Zero sorry/axiom. All tiers pass (0-3).

## [0.23.11] — Z5 Audit Pass 2: Test Coverage Completion

Second audit pass of Z5 Capability-Controlled Thread Binding. Found 7 untested
critical code paths (scheduler integration behaviors) and 1 stale doc comment.

- **AUD-8 (LOW)**: API.lean line 522 comment said "17 SyscallId variants"
  when the actual count is 20. Fixed.
- **AUD-9 (HIGH)**: 5 critical code paths had zero test coverage:
  - Z5-G3: `schedContextBind` RunQueue re-insertion (SCO-013)
  - Z5-H1: `schedContextUnbind` preemption guard when thread is current (SCO-014)
  - Z5-H2: `schedContextUnbind` RunQueue removal of bound thread (SCO-015)
  - Z5-I2: `schedContextYieldTo` budget-starved target enqueue (SCO-016)
  - Admission control failure path when bandwidth > 100% (SCO-017)
- **AUD-10 (MED)**: 2 additional untested error paths:
  - `schedContextBind` when TCB is already bound to different SC (SCO-018)
  - `schedContextYieldTo` when target has no bound thread (SCO-019)
- **Testing**: 7 new trace tests SCO-013 through SCO-019. All 19 SCO tests pass.
- **Operations.lean deep review**: No correctness or security issues found.
  All scheduler integration logic (RunQueue, preemption, admission) verified.

Zero sorry/axiom. All tiers pass (0-3). Metrics: 77,424 production LoC,
111 files, 2,251 proved declarations.

## [0.23.10] — Z5 Audit: SchedContext Operations Hardening

Post-implementation audit of Z5 Capability-Controlled Thread Binding. Seven
audit findings fixed, 4 new preservation theorems, 12 new trace tests.

- **AUD-1 (HIGH)**: `schedContextBind` missing RunQueue re-insertion (Z5-G3).
  After bind, thread in RunQueue is now removed and re-inserted at
  SchedContext-derived priority to maintain `effectiveParamsMatchRunQueue`.
- **AUD-2 (HIGH)**: `schedContextUnbind` missing preemption guard (Z5-H1).
  If bound thread is the current thread, `current` is now cleared to force
  rescheduling. Prevents unbinding the running thread without preemption.
- **AUD-3 (HIGH)**: `schedContextUnbind` missing RunQueue removal (Z5-H2).
  Runnable threads are now removed from RunQueue before unbinding.
- **AUD-4 (MED)**: `schedContextYieldTo` missing re-enqueue logic (Z5-I2).
  When budget transfer reactivates a budget-starved target, its bound thread
  is now enqueued in the RunQueue at the SchedContext's priority.
- **AUD-5 (MED)**: 4 missing preservation theorems added:
  `schedContextBind_output_bidirectional` (Z5-K),
  `schedContextUnbind_output_cleared` (Z5-L),
  `schedContextBind_runQueue_insert_uses_sc_priority` (Z5-N1/N2),
  `schedContextConfigure_admission_excludes_eq` (Z5-M admission).
- **AUD-6 (LOW)**: 4 stale doc comments in `API.lean` updated from "6
  capability-only arms" to "9 capability-only arms".
- **AUD-7 (MED)**: `schedContextConfigure` admission control double-counted
  the SchedContext being reconfigured. `collectSchedContexts` now accepts
  `excludeId` parameter; configure passes the SchedContext's own ObjId.
- **Testing**: 12 new `SCO-001` through `SCO-012` trace tests covering
  parameter validation (5 tests), configure success, bind/unbind
  success+rejection, yieldTo budget transfer, and admission exclusion.

Zero sorry/axiom. All tiers pass (0-3). 212 modules build.

## [0.23.9] — Z5: Capability-Controlled Thread Binding

Phase Z5 of WS-Z Composable Performance Objects. 25 sub-tasks (Z5-A through
Z5-P2) implementing capability-gated SchedContext operations.

- **Z5-A/B/C**: 3 new `SyscallArgDecode` structures
  (`SchedContextConfigureArgs`, `SchedContextBindArgs`,
  `SchedContextUnbindArgs`) with decode/encode functions and round-trip proofs.
- **Z5-D**: 3 new `SyscallId` variants (`.schedContextConfigure`,
  `.schedContextBind`, `.schedContextUnbind`). Codec and injectivity proofs
  updated. Count 17→20.
- **Z5-E/J**: API dispatch wiring — 3 new `syscallRequiredRight` entries
  (all `.write`), 3 new `dispatchCapabilityOnly` arms, 3 structural
  equivalence theorems.
- **Z5-F/G/H/I**: Core operations in new `Operations.lean` —
  `validateSchedContextParams`, `collectSchedContexts`, `checkAdmission`,
  `schedContextConfigure`, `schedContextBind`, `schedContextUnbind`,
  `schedContextYieldTo`.
- **Z5-K/L/M/N**: Preservation theorems in new `Preservation.lean` —
  `validateSchedContextParams_implies_wellFormed`,
  `schedContextConfigure_output_wellFormed`,
  `schedContextYieldTo_target_bounded`.
- **Z5-O**: Information-flow enforcement via `dispatchCapabilityOnly` shared
  path (capability-only, no separate wrappers needed). Structural equivalence
  proven.
- **Z5-P1/P2**: Build verification + smoke tests passing.

New files: `SchedContext/Operations.lean`, `SchedContext/Invariant/Preservation.lean`.
Zero sorry/axiom. All tiers pass (0-2). 212 modules build.

## [0.23.8] — Z4 Audit v2: Tier 3 Invariant Surface Anchors

Second audit pass on Z4 Scheduler Integration. Added comprehensive Tier 3
invariant surface anchors for Z4 definitions, operations, and preservation
theorems.

- **AUD-T3 (MED)**: Added 23 `#check` Tier 3 anchors to
  `test_tier3_invariant_surface.sh` covering all Z4 invariant definitions
  (`budgetPositive`, `currentBudgetPositive`, `schedContextsWellFormed`,
  `replenishQueueValid`, `schedContextBindingConsistent`,
  `effectiveParamsMatchRunQueue`, `schedulerInvariantBundleExtended`),
  operations (`effectivePriority`, `hasSufficientBudget`,
  `chooseThreadEffective`, `timerTickBudget`, `scheduleEffective`,
  `timerTickWithBudget`, `handleYieldWithBudget`, `processReplenishmentsDue`),
  and key preservation theorems (`chooseThreadEffective_state_unchanged`,
  `budgetPositive_subset`, `effectivePriority_unbound_legacy`,
  `hasSufficientBudget_unbound_legacy`,
  `consumeBudget_preserves_schedContextWellFormed_full`,
  `scheduleReplenishment_preserves_schedContextWellFormed_full`,
  `cbsUpdateDeadline_preserves_wf`).

Zero sorry/axiom. All tiers pass (0-3). 210 modules build.

## [0.23.7] — Z4 Audit: Scheduler Integration Verification

Post-implementation audit of Z4 Scheduler Integration (33 sub-tasks). Four
audit improvements:

- **AUD-1/2/3 (INFO)**: CBS semantics documentation. Added V5-L backward
  compatibility rationale to `timerTickBudget` unbound branch (uses global
  `defaultTimeSlice` to match legacy `timerTick` proof chain). Documented CBS
  `consumedAmount` semantics in exhaustion branch (full remaining budget, not
  1 tick). Documented pre-tick `now` capture for standard CBS timing.
- **AUD-4 (MED)**: Replaced trivial preservation theorems with substantive
  machine-checked proofs. Added: `budget_decrement_stays_positive`,
  `consumeBudget_positive_of_gt_one`, `timerTickBudget_unbound_nopreempt_objects_key`,
  `timerTickBudget_unbound_preempt_objects_key` (frame lemmas proving only `.tcb`
  objects are modified in unbound path), `consumeBudget_preserves_wf`,
  `consumeBudget_preserves_schedContextWellFormed_full` (4-conjunct composition),
  `scheduleReplenishment_preserves_schedContextWellFormed_full` (with preconditions),
  `chooseThreadEffective_state_unchanged`, `budgetPositive_subset`,
  `effectivePriority_unbound_legacy`, `hasSufficientBudget_unbound_legacy`,
  `cbsUpdateDeadline_preserves_wf`.

Zero sorry/axiom. All tiers pass (0-3). 210 modules build. 2,238 proved declarations.

## [0.23.4] — Z2 Audit v3: Build Graph Fix

Third audit pass on Z2 CBS Budget Engine. Root-cause fix for CI failure:

- **AUD-10 (HIGH)**: `Object/Types.lean` imported only `SchedContext.Types`,
  leaving `Budget.lean` and `Invariant/Defs.lean` outside the default build
  graph (`lake build` = executable target only). Changed import to the full
  re-export hub `SeLe4n.Kernel.SchedContext`, ensuring all Z2 modules compile
  as part of the default `lake build`. This fixes Tier 3 CI failures where
  `lake env lean` couldn't find SchedContext.Invariant olean files.
- Reverted fragile `lake build` workaround in `test_tier3_invariant_surface.sh`.

Verified via `lake clean && lake build` (208 jobs). Zero sorry/axiom. All tiers pass.

## [0.23.3] — Z2 Audit v2: Bundle Completion & Surface Anchors

Second audit pass on Z2 CBS Budget Engine. Four improvements:

- **AUD-6 (LOW)**: `schedContextWellFormed` promoted to 4-conjunct bundle
  incorporating `replenishmentAmountsBounded` as the 4th conjunct. The bundled
  preservation proof `cbsBudgetCheck_preserves_schedContextWellFormed` now
  composes all 4 sub-invariants in both exhausted and non-exhausted branches.
- **AUD-7 (LOW)**: Module doc header in `Invariant/Defs.lean` updated to
  accurately list all 4 invariants, all 16 per-operation preservation theorems,
  and both composite theorems.
- **AUD-8 (MED)**: Added 13 Tier 3 invariant surface anchors for Z2 proof
  surface (`#check` for all invariant definitions, composite preservation
  theorems, bandwidth theorems, and representative per-operation theorems).
  Prevents accidental theorem deletion.
- **AUD-9 (LOW)**: Documentation theorem counts corrected across spec, gitbook,
  and CLAUDE.md to reflect the precise inventory: 16 per-operation + 2
  composite + 2 bandwidth + 7 operation correctness = 27 public theorems.

Zero sorry/axiom. All tiers pass.

## [0.23.2] — Z2 Audit: CBS Budget Engine Correctness Fixes

Post-implementation audit of Z2 CBS Budget Engine. Three correctness fixes:

- **AUD-1 (MED)**: `applyRefill` now updates `isActive` after budget refill.
  Previously, `isActive` remained stale (`false`) after successful replenishment
  because only `consumeBudget` updated it. The `isActive` flag must reflect
  `budgetRemaining > 0` at all times for correct scheduler preemption decisions.
- **AUD-2 (MED)**: Added 6 preservation theorems for `replenishmentAmountsBounded`:
  `consumeBudget_preserves_replenishmentAmountsBounded`,
  `processReplenishments_preserves_replenishmentAmountsBounded`,
  `scheduleReplenishment_preserves_replenishmentAmountsBounded`,
  `cbsUpdateDeadline_preserves_replenishmentAmountsBounded`,
  `cbsBudgetCheck_preserves_replenishmentAmountsBounded`.
  Without these, the bandwidth theorems (`cbs_single_period_bound`,
  `cbs_bandwidth_bounded`) required an invariant hypothesis that was never
  proven to be maintained across CBS operations — now fully closed.
- **AUD-3 (LOW)**: Refactored `cbs_single_period_bound` and `cbs_bandwidth_bounded`
  to share a common `totalConsumed_le_max_budget` lemma and document the
  relationship between the proven bound (`maxReplenishments × budget`) and the
  tighter theoretical bound (`budget × ⌈window/period⌉`).

Zero sorry/axiom. All tiers pass.

## [0.23.1] — Z2: CBS Budget Engine

Phase Z2 of WS-Z Composable Performance Objects. Implements the Constant
Bandwidth Server budget management algorithm as pure functions with
machine-checked invariants. Budget engine in isolation — no scheduler
integration yet.

- **Z2-A**: `consumeBudget` operation with saturating decrement and
  `consumeBudget_budgetRemaining_le` proof.
- **Z2-B**: `isBudgetExhausted` predicate.
- **Z2-C1/C2/C3**: `mkReplenishmentEntry` constructor, `truncateReplenishments`
  (bounded list via `List.drop`), `scheduleReplenishment` composition. Proofs:
  `mkReplenishmentEntry_amount_eq`, `truncateReplenishments_length_le`.
- **Z2-D1/D2/D3/D4**: `partitionEligible` (partition by eligibility time),
  `sumReplenishments` (recursive sum), `applyRefill` (capped at budget ceiling),
  `processReplenishments` composition. Proofs: `partitionEligible_eligible_sublist`,
  `sumReplenishments_nil`/`_cons`, `applyRefill_le_budget`.
- **Z2-E**: `cbsUpdateDeadline` — CBS deadline assignment rule (deadline updated
  on replenishment after exhaustion).
- **Z2-F**: `cbsBudgetCheck` — combined per-tick budget accounting entry point
  returning `(updatedSc, wasPreempted)`.
- **Z2-G**: `admissionCheck` — CBS admission control predicate (total utilization
  ≤ 1000 per-mille).
- **Z2-H/I/J**: Invariant definitions: `budgetWithinBounds` (remaining ≤ budget ≤
  period), `replenishmentListWellFormed` (bounded length, no zero-amount entries),
  `schedContextWellFormed` bundle, `replenishmentAmountsBounded`.
- **Z2-K through Z2-N**: 12 preservation theorems: `consumeBudget`, `processReplenishments`,
  `scheduleReplenishment`, `cbsUpdateDeadline` each preserve `wellFormed`,
  `budgetWithinBounds`, and `replenishmentListWellFormed`. Composed into
  `cbsBudgetCheck_preserves_schedContextWellFormed`.
- **Z2-O1/O2/O3**: Bandwidth theorems: `totalConsumed` accumulator,
  `cbs_single_period_bound` (single-period consumption ≤ maxReplenishments × budget),
  `cbs_bandwidth_bounded` (multi-period isolation guarantee).
- **Z2-P/Q**: Re-export hubs, build verification. Zero sorry/axiom. All tiers pass.

## [0.23.0] — Z1: SchedContext Type Foundation

Phase Z1 of WS-Z Composable Performance Objects. Introduces the `SchedContext`
kernel object type and all supporting data structures for CBS (Constant Bandwidth
Server) scheduling. Pure type foundation — no behavioral changes.

- **Z1-A**: `SchedContextId` typed wrapper in `Prelude.lean` with full instance
  suite (`Hashable`, `LawfulHashable`, `EquivBEq`, `LawfulBEq`), `toObjId`/
  `ofObjId` conversions, `sentinel`/`isReserved`/`valid` predicates,
  `toObjId_injective` proof.
- **Z1-B/C/D/E**: CBS primitive types in `SchedContext/Types.lean`: `Budget`
  (saturating decrement, ceiling refill), `Period` (default 10k ticks),
  `Bandwidth` (per-mille utilization), `ReplenishmentEntry` (amount + eligibleAt).
- **Z1-F/G/H**: `SchedContext` structure (11 fields), `wellFormed` predicate
  (period > 0, budget ≤ period, budgetRemaining ≤ budget, bounded replenishments),
  `bandwidth`/`utilizationPerMille` accessors.
- **Z1-I/J**: `SchedContextBinding` enum (`unbound`/`bound`/`donated`), TCB
  `schedContextBinding` field (defaults `.unbound`).
- **Z1-K**: `KernelObject.schedContext` (7th variant, tag 6),
  `KernelObjectType.schedContext`. Pattern match exhaustiveness updated across
  ~24 files (~150 match arms).
- **Z1-L**: `objectTypeAllocSize` entry (256 bytes).
- **Z1-M**: `SchedContext.empty`/`mkChecked` constructors.
- **Z1-N**: `threadSchedulingParams` migration bridge accessor.
- **Z1-O**: `FrozenKernelObject.schedContext` (passthrough freeze).
- **Z1-P**: `BEq` instances for all new types.
- **Z1-Q/R**: Re-export hub, build verification. Zero sorry/axiom. All tiers pass.

## [0.22.26] — Y3: Test Infrastructure & Documentation

Phase Y3 of WS-Y final audit remediation. Resolves 3 findings (MED-02,
LOW-07, LOW-08) from the v0.22.22 comprehensive full-kernel audit.
**WS-Y PORTFOLIO COMPLETE.**

- **Y3-A (MED-02, part 1)**: All 15 `.build` calls in `InformationFlowSuite.lean`
  migrated to `.buildChecked`. Two states with non-TCB runnable entries fixed
  (runnable list removed — irrelevant to security projection tests).
- **Y3-B (MED-02, part 2)**: 35 of 38 `.build` calls in `NegativeStateSuite.lean`
  migrated to `.buildChecked`. 3 calls retained as `.build` with per-call
  annotations explaining the deliberate invariant violation:
  - 2× malformed runnable list (tid 77 references non-existent TCB) for
    scheduler error path testing (check 3).
  - 1× lifecycle metadata mismatch (TCB vs endpoint) for retype error path
    testing (check 2b).
- **Y3-C (MED-02, part 3)**: All 9 `.build` calls in `OperationChainSuite.lean`
  migrated to `.buildChecked` (1 pre-existing `.buildChecked` preserved).
- **Y3-D (LOW-07)**: Duplicate `awaitReceive` probe operation replaced with
  `capCopy` (`cspaceCopy`), exercising the CSpace copy subsystem. Probe now
  covers 7 truly distinct operation families: IPC send, IPC receive, capability
  copy, capability lookup, notification signal, notification wait, schedule.
  `classifyError` updated to handle `targetSlotOccupied` errors.
  `checkStateInvariants` fixed to call `syncThreadStates` before checking
  (matching `assertStateInvariantsFor` behavior).
- **Y3-E (LOW-08)**: `assertStateInvariantsFor` docstring added documenting
  V8-G7 design: validates inference self-consistency (idempotency of
  `syncThreadStates`), not operational drift. Companion function
  `assertStateInvariantsWithoutSync` added for drift detection when needed.
- **Y3-F**: MED-01 test fixture and documentation changes verified as already
  landed in Y1 (v0.22.23). `configDefaultTimeSlice` correctly used in
  `frozenTimerTick` tests (TPH-006c verifies custom value 12).

Zero sorry/axiom. All modules build. `test_full.sh` green.

## [0.22.25] — Y2-D+: VSpaceRoot BEq Reflexivity (Real Proof)

Replaces the `True := trivial` placeholder in `VSpaceRoot.beq_converse_limitation`
with a genuine machine-checked proof. Rigorous analysis confirms `LawfulBEq VSpaceRoot`
is provably impossible; BEq reflexivity under `invExt` is the strongest achievable result.

- **LawfulBEq PagePermissions**: New instance proving PagePermissions BEq is sound
  and reflexive. Required for value-type reflexivity in the VSpaceRoot fold proof.
  `eq_of_beq` via field-wise decomposition, `rfl` via field-wise `Bool` reflexivity.
- **RHTable.slot_entry_implies_get**: New public theorem (Lookup.lean) proving
  that if entry `(k, v)` occupies slot `j` and `invExt` holds, then `get? k = some v`.
  This is the reverse direction of `get_some_slot_entry` — proven via
  `getLoop_finds_present` using `distCorrect`, `probeChainDominant`, and `noDupKeys`.
- **VSpaceRoot.beq_refl**: Real proof that `(a == a) = true` when `a.mappings.invExt`
  holds. Uses `Array.foldl_induction` to show the fold accumulator stays `true`:
  each step applies `slot_entry_implies_get` to establish `get? e.key = some e.value`,
  then `beq_self_eq_true` for the value-type BEq comparison.
- **LawfulBEq impossibility documented**: Rigorous analysis proves `eq_of_beq` for
  `RHTable` is false in general — Robin Hood hashing does not produce canonical
  layouts (different insertion orders yield different backing arrays for identical
  logical content). L-FND-3 limitation closed with this analysis.

Zero sorry/axiom. All 198 modules build. All tests pass.

## [0.22.24] — Y2: Platform, Data Structures & Proof Hardening

Phase Y2 of WS-Y final audit remediation. Resolves 7 findings (LOW-04,
LOW-05, LOW-06, INFO-01, INFO-03, INFO-04, INFO-06) from the v0.22.22
comprehensive full-kernel audit.

- **Y2-A (LOW-04)**: `switchDomain` fallback `| none =>` branch documented as
  unreachable under `schedulerInvariantBundleFull`. Added
  `switchDomain_index_in_bounds` lemma proving modular index is always valid for
  non-empty schedules, and `switchDomain_index_lookup_isSome` corollary
  confirming the `List.getElem?` lookup always returns `some`.
- **Y2-B (LOW-05)**: `registerContextStableCheck` dead branching simplified —
  removed `if oldTid == tid` conditional with identical branches. Register
  context stability is now checked uniformly via single expression
  `st'.machine.regs == tcb.registerContext`.
- **Y2-C (LOW-06)**: `insertLoop` and `backshiftLoop` fuel-exhaustion branches
  documented with invariant-based unreachability argument. References `invExtK`
  load-factor bound guaranteeing sufficient fuel for all probe/backshift sequences.
- **Y2-D (INFO-01)**: `VSpaceRoot.beq_converse_limitation` documentation updated
  with current V7 `LawfulBEq` status. Clarifies that V7 added `LawfulBEq` as a
  *key-type constraint* but not a `LawfulBEq RHTable` instance. Identifies two
  closure paths (backing-array-independent equality or canonical representation).
- **Y2-E (INFO-03)**: `enforcementBridge_to_NonInterferenceStep` extended from
  6/11 to **11/11** checked wrappers. Added 5 new soundness theorems
  (`enforcementSoundness_endpointCallChecked`, `enforcementSoundness_endpointReplyChecked`,
  `enforcementSoundness_cspaceMintChecked`, `enforcementSoundness_notificationWaitChecked`,
  `enforcementSoundness_endpointReplyRecvChecked`) and integrated all into the
  unified bridge theorem. Complete enforcement-NI coverage.
- **Y2-F (INFO-04)**: `VSpaceBackend.lean` module status updated with explicit
  integration marker: "H3 forward declaration — not yet integrated into kernel
  dispatch. Milestone: Raspberry Pi 5 hardware binding (post-v1.0)."
- **Y2-G (INFO-06)**: `collectQueueMembers` fuel sufficiency gap annotated with
  `TPI-DOC` tracking marker. Added `collectQueueMembers_length_bounded` lemma
  proving result list length is bounded by fuel parameter (supports informal
  acyclicity argument without requiring `QueueNextPath` connection).

Zero sorry/axiom. All modules build. All tests pass.

## [0.22.23] — Y1: Frozen State & Foundation Fixes

Phase Y1 of WS-Y final audit remediation. Resolves 4 findings (MED-01,
LOW-01, LOW-02, LOW-03) from the v0.22.22 comprehensive full-kernel audit.

- **Y1-A/B (MED-01)**: `configDefaultTimeSlice` field added to
  `FrozenSchedulerState` and transferred in `freezeScheduler`. Platform-tuned
  time-slice value now survives the builder→frozen transition.
  `freeze_preserves_configDefaultTimeSlice` proof ensures round-trip correctness.
- **Y1-C (MED-01)**: `frozenTimerTick` updated to use
  `st.scheduler.configDefaultTimeSlice` instead of hardcoded
  `frozenDefaultTimeSlice` constant. The constant is retained but deprecated.
- **Y1-D (LOW-01)**: `AccessRightSet.mk` raw constructor documented as
  internal-only with prominent warning. External uses migrated to `ofNat`
  (safe, masked constructor). `eta` simp lemma added for proof reconstruction.
  `decodeCSpaceMintArgs` now uses `AccessRightSet.ofNat` at the decode boundary
  to mask untrusted register values to the valid 5-bit range. Roundtrip proof
  updated with `hRights : args.rights.valid` hypothesis.
- **Y1-E (LOW-02)**: `descendantsOf` BFS visited-set optimized from O(n²)
  `List.Mem` to O(1) `Std.HashSet` membership checks. All 12 supporting
  theorems updated with visited/acc sync invariant. `foldl_insert_contains`
  and `sync_after_extend` helper lemmas added.
- **Y1-F/G (LOW-03)**: 7 missing named accessors added to `allTablesInvExtK`
  decomposition (cdtSlotNode, cdtNodeSlot, cdtChildMap, cdtParentMap,
  byPriority, threadPriority, membership). All 16 conjuncts now have named
  accessors with completeness documentation and raw-projection warning.
- **Audit hardening**: TPH-006b test updated to verify time-slice reset against
  `configDefaultTimeSlice` field (not hardcoded constant). TPH-006c added with
  non-default config value (12) to semantically verify the MED-01 fix path.

Zero sorry/axiom. All tests pass.

## [0.22.22] — X5: Documentation, Hardening & Low-Severity

Phase X5 of WS-X pre-release audit remediation. Resolves 9 findings (H-1, H-9,
M-2, M-3, M-5, M-11, L-1, L-2, L-4/L-5/L-6/L-7) from the v0.22.17
comprehensive audit. **WS-X PORTFOLIO COMPLETE.**

- **X5-A (H-1)**: Created `docs/SECURITY_ADVISORY.md` with SA-1 (starvation
  freedom advisory), SA-2 (default labeling context), SA-3 (scheduling covert
  channel). Documents seL4 precedent and recommended user-level mitigations.
- **X5-B (H-9)**: `cnode_capacity_always_ge4` documentation theorem witnessing
  that CNode.empty uses `RHTable.empty 16` (capacity 16 ≥ 4), satisfying the
  `insert_size_lt_capacity` precondition at all creation sites.
- **X5-C (M-3)**: `schedulingCovertChannel_bounded_width` theorem with formal
  bandwidth analysis (≤ 400 bits/sec for typical configurations with N ≤ 16
  domain entries at F ≤ 100 Hz). Acceptance rationale documented per seL4
  precedent (Murray et al., CCS 2013).
- **X5-D (M-5)**: `contextMatchesCurrent` idle-state design rationale documented:
  vacuously true when `current = none` by design, re-established by `schedule`.
- **X5-E (M-11)**: `invalidSyscallArgument` KernelError variant added (Lean
  discriminant 41, Rust `InvalidSyscallArgument = 41`). Decode path in
  `SyscallArgDecode.lean` updated. Rust ABI synced (42 total variants). All
  conformance tests updated.
- **X5-F (L-1)**: `VSpaceRoot.beq_converse_limitation` documented — converse
  requires RHTable extensional equality; no kernel correctness impact.
- **X5-G (L-2)**: RegisterFile BEq safety analysis: 4-point argument that
  non-lawful edge case (functions agreeing on 0..31 but differing at 32+)
  cannot occur in real kernel execution.
- **X5-H (M-2)**: Default labeling context production warning confirmed and
  cross-referenced to SECURITY_ADVISORY.md SA-2.
- **X5-I (L-4/L-5/L-6/L-7)**: All 4 low-severity items confirmed with
  v0.22.17 audit trail cross-references in source code comments.

Zero sorry/axiom. All tests pass.

## [0.22.21] — X4: Platform & Architecture Completion

Phase X4 of WS-X pre-release audit remediation. Resolves 4 findings (H-7, M-8,
M-9, M-10) from the v0.22.17 comprehensive audit.

- **X4-A/B/C (H-7)**: Generic FDT device node traversal (`parseFdtNodes`,
  `FdtNode`, `FdtProperty` structures). Full node tree parsing with depth
  tracking and fuel bound. `extractInterruptController` discovers GIC-400 via
  `compatible` string matching and parses `reg` property for distributor/CPU
  interface bases. `extractTimerFrequency` discovers `/timer` node and extracts
  `clock-frequency` property. `extractPeripherals` walks device nodes with
  `compatible` + `reg` properties. `fromDtbFull` now performs complete device
  discovery (peripherals, interrupt controller, timer) instead of stubs.
- **X4-D (M-10)**: `mmioRegionsPairwiseDisjointCheck` and
  `mmioRegionsPairwiseDisjoint_holds` — proof that 3 RPi5 MMIO regions (UART
  PL011, GIC distributor, GIC CPU interface) have non-overlapping address ranges.
  Proven via `decide` on concrete address computation.
- **X4-E (M-9)**: `serviceBfsFuel_sufficient` and `serviceBfsFuel_sound` —
  bi-directional correctness of fuel-bounded graph traversal under
  `serviceCountBounded`. `serviceBfsFuel_has_margin` proves the `+ 256` margin
  is strictly conservative. Completes the fuel sufficiency proof chain.
- **X4-F (M-8)**: `arm64_regCount_valid` and
  `machineConfig_registerCount_default_eq_arm64GPRCount` — compile-time
  assertions confirming ARM64 register count (32) consistency between
  `decodeSyscallArgs` default, `RegName.arm64GPRCount`, and
  `MachineConfig.registerCount`.

Audit refinements:
- `extractTimerFrequency` now supports 64-bit `clock-frequency` values
  (checks `freqBytes.size >= 8` before falling back to 32-bit).
- `mmioRegionsPairwiseDisjointCheck` refactored to iterate over `mmioRegions`
  directly instead of duplicating region definitions in let bindings.

Zero sorry/axiom. All tests pass.

## [0.22.20] — X3: Information Flow & Composition Closure

Phase X3 of WS-X pre-release audit remediation. Resolves 4 findings (H-3, H-4,
H-5, M-1) from the v0.22.17 comprehensive audit.

- **X3-A (H-3)**: `serviceOrchestrationOutsideNiBoundary` exclusion boundary
  theorem formally documenting that service orchestration internals (dependency
  graphs, lifecycle transitions, restart policies) are outside the NI boundary.
  `serviceRegistryAffectsProjection` predicate. `serviceOrchestration_boundary_disjunction`.
- **X3-B (H-5)**: `enforcementBridge_to_NonInterferenceStep` unified 6-conjunct
  bridge theorem connecting all enforcement soundness theorems
  (`endpointSendDualChecked`, `notificationSignalChecked`, `cspaceCopyChecked`,
  `cspaceMoveChecked`, `endpointReceiveDualChecked`, `registerServiceChecked`)
  to the NI composition framework.
- **X3-C (H-4 part 1)**: 4 sharing predicate pair frame theorems covering all
  10 cross-subsystem predicate interaction pairs. `sharingPair1_objects_frame`,
  `sharingPair23_objects_frame`, `sharingPair4_services_frame`.
  `crossSubsystemInvariant_objects_frame` and `crossSubsystemInvariant_services_change`
  composite preservation.
- **X3-D (H-4 part 2)**: `crossSubsystemInvariant_composition_complete` 10-conjunct
  tightness theorem witnessing all 6 disjoint + 4 sharing pairs.
- **X3-E (M-1)**: `integrityFlowsTo_prevents_escalation` 4-conjunct privilege
  escalation prevention theorem. `securityFlowsTo_prevents_label_escalation`
  label-level confidentiality denial and authority receipt permission.

## [0.22.19] — X2: Runtime Invariant Enforcement

Phase X2 of WS-X pre-release audit remediation. Resolves 5 findings (H-2, H-6,
H-8, M-4, M-6) from the v0.22.17 comprehensive audit.

- **X2-A/B/C (H-2)**: `domainScheduleEntriesPositive` predicate added as 9th
  conjunct of `schedulerInvariantBundleFull`. `setDomainScheduleChecked` builder
  validation rejects zero-length entries. 7 frame lemmas prove `domainSchedule`
  immutability across all scheduler transitions. 4 bundle preservation theorems
  updated (`schedule`, `handleYield`, `timerTick`, `switchDomain`).
- **X2-D/E (H-6)**: `physicalAddressWidth : Nat := 52` field added to
  `MachineState`. `vspaceMapPageCheckedWithFlushFromState` reads PA width from
  live machine state. API dispatch updated to use state-aware PA bounds.
  `applyMachineConfig` post-boot function propagates platform `MachineConfig`
  (including PA width) to booted state. 3 correctness theorems.
- **X2-F (H-8)**: `listAllDistinct` transparent O(n²) duplicate detection
  function. `irqsUniqueTransparent`/`objectIdsUniqueTransparent` variants.
  3 `native_decide` proofs replaced with `decide` for kernel-evaluable
  duplicate detection.
- **X2-G/H (M-4)**: `revokeService_preserves_noStaleNotificationWaitReferences`
  frame lemma in `CrossSubsystem.lean`. Proof via `revokeService_preserves_objects`
  and `noStaleNotificationWaitReferences_frame`.
- **X2-I (M-6)**: 4 checked scheduler wrappers (`scheduleChecked`,
  `handleYieldChecked`, `timerTickChecked`, `switchDomainChecked`) using
  `saveOutgoingContextChecked` with `schedulerInvariantViolation` error
  propagation. Defense-in-depth at API boundary.

Audit: `applyMachineConfig` boot-to-runtime PA width propagation, X2 test
coverage (6 assertions: X2-B-01/02, X2-D-01/02, X2-I-01/02).

Zero sorry/axiom. All tests pass.

## [0.22.18] — X1: Hardware-Binding Critical Proofs

Phase X1 of WS-X pre-release audit remediation. Resolves all 4 CRITICAL
findings from the v0.22.17 comprehensive audit.

- **X1-D (C-2)**: `MmioReadOutcome` inductive replacing `hOutcome : True`
  placeholder in `MmioSafe`. Four constructors encode read-kind constraints:
  `ramIdempotent` (idempotent), `volatileAny` (unconstrained), `w1cStatus`
  (current status), `fifoConsume` (queue entry consumed). Prevents proofs from
  assuming idempotent reads for volatile device registers.
- **X1-E (C-2)**: Device-specific `MmioSafe` witness generators for RPi5:
  `mkMmioSafe_uart` (UART PL011 volatile), `mkMmioSafe_gicDist` (GIC-400
  distributor volatile), `mkMmioSafe_gicCpu` (GIC-400 CPU interface volatile).
  Private region definitions with `List.Mem` membership proofs.
- **X1-F (C-3)**: `contextSwitchState` atomic context-switch operation that
  simultaneously updates `machine.regs` and `scheduler.current`, eliminating
  the window where individual register writes violate `contextMatchesCurrent`.
  `adapterContextSwitch` kernel wrapper with contract guard.
- **X1-G (C-3)**: `AdapterProofHooks.preserveContextSwitch` field added to
  proof-carrying adapter hooks structure.
  `adapterContextSwitch_ok_preserves_proofLayerInvariantBundle` composition
  theorem and `adapterContextSwitch_error_unsupportedBinding_preserves_*`
  error-case theorem. Component preservation:
  `contextSwitchState_preserves_vspaceInvariantBundle`,
  `contextSwitchState_preserves_contextMatchesCurrent`,
  `contextSwitchState_preserves_currentThreadValid`. All platform ProofHooks
  (RPi5 restrictive, Sim restrictive, Sim substantive) updated.
  End-to-end `rpi5Restrictive_adapterContextSwitch_preserves` theorem.
- **X1-K (C-4)**: TPI-001 (VSpace determinism) closed. Documentation updated
  in VSpace.lean and VSpaceInvariant.lean referencing 4 round-trip theorems.
- **X1-A/B/C (C-1)**: Verified as pre-existing from V4-A2–A9 workstream.
- **X1-H/I/J (C-4)**: Verified as pre-existing from WS-D3/F-08 workstream.

Zero sorry/axiom. All tests pass. 2,087 proved declarations.

## [0.22.17] — W6: Code Quality & Documentation

Phase W6 of WS-W pre-release audit remediation. Addresses M-7, LOW-1, LOW-2,
L-4, L-6, L-8, L-11, L-13, LOW-01, LOW-04, H-3 (downgraded) from v0.22.10
audits. **WS-W PORTFOLIO COMPLETE.**

- **W6-A (M-7)**: Documented `removeThreadFromQueue` TCB existence invariant.
  Defensive `(none, none)` fallback explained — safe due to cleanup-before-retype
  ordering and `tcbQueueChainAcyclic` invariant.
- **W6-B (L-4)**: Factored redundant lifecycle preservation proofs into bundled
  theorems (`spliceOutMidQueueNode_preserves`, `removeFromAllEndpointQueues_preserves`,
  `removeFromAllNotificationWaitLists_preserves`). Individual accessors project
  from bundles, reducing 77 lines of near-identical proofs.
- **W6-C (L-6)**: Removed unused `crossSubsystemPredicates` list and
  `crossSubsystemPredicates_count` count witness. Replaced with documentation
  comment directing to canonical `crossSubsystemInvariant` definition.
- **W6-D (L-8)**: Documented two-tier dispatch design in API.lean. Explains
  `dispatchCapabilityOnly` + explicit match split, wildcard unreachability (W2-C),
  and shared checked/unchecked implementation (V8-H).
- **W6-E (L-11)**: Extracted `default_objects_none` and `default_objects_absurd`
  helper lemmas in Architecture/Invariant.lean and applied them across 24+
  default-state proofs, replacing verbose `RHTable_get?_empty 16 (by omega)`
  patterns with single `default_objects_absurd hObj` calls.
- **W6-F (L-13)**: Added `RHSet.insert_invExtK`, `RHSet.erase_invExtK`,
  `RHSet.empty_invExtK'` public API wrappers using `RHSet.invExtK` abstraction.
- **W6-G (LOW-1)**: Added compile-time `const_assert` block in `message_info.rs`
  ensuring `MAX_LABEL`, `MAX_MSG_LENGTH`, `MAX_EXTRA_CAPS` stay synchronized
  with Lean model values.
- **W6-H (LOW-2)**: Documented `set_mr`/`get_mr` API asymmetry in `ipc_buffer.rs`.
  Intentional design: `set_mr(0..3)` returns informational `Ok(false)`, while
  `get_mr(0..3)` returns `Err(InvalidArgument)`.
- **W6-I (LOW-04)**: Documented CDT edge theorem suite as specification surface
  in Model/Object/Structures.lean.
- **W6-J (LOW-01)**: Documented RHTable specification surface theorems (14
  theorems) in Prelude.lean with cross-reference to RobinHood/Invariant/.
- **W6-K (H-3 downgraded)**: Documented lifecycle metadata enforcement chain
  for `lifecycleCapabilityRefObjectTargetBacked`. 4-step contract discipline
  via `lifecyclePreRetypeCleanup` (`cleanupTcbReferences`,
  `cleanupEndpointServiceRegistrations`, `detachCNodeSlots`) with
  `lifecycleRetypeObject_preserves_lifecycleInvariantBundle` proof.
- **W6-L**: Synchronized documentation across README.md, CHANGELOG.md,
  WORKSTREAM_HISTORY.md, CLAUDE.md, codebase_map.json, and GitBook chapters.
  Version bump to 0.22.17.
- Zero sorry/axiom. All test suites pass.

## [0.22.16] — W5: Test Infrastructure & Coverage

Phase W5 of WS-W pre-release audit remediation. Addresses M-10, M-11,
L-17, L-18, L-7, L-2 from v0.22.10 audits.

- **W5-A (M-10)**: Consolidated `expectError`/`expectOk`/`expectOkState`
  implementations. Canonical shared helpers in `SeLe4n/Testing/Helpers.lean`
  with `msgPrefix` parameter for suite-specific formatting. `NegativeStateSuite`
  and `OperationChainSuite` now delegate to shared versions, eliminating 3
  duplicate implementations.
- **W5-B (L-17)**: Documented test fixture OID ranges in `Helpers.lean`.
  11-suite range table prevents accidental collisions between test suites.
- **W5-C (L-18)**: Added comprehensive service lifecycle tests (chain33).
  25 assertions covering `registerInterface` (success + duplicate rejection),
  `registerService` (success + 5 error paths: missing interface, non-endpoint
  target, missing write right, duplicate, non-existent endpoint),
  `serviceRegisterDependency` (acyclic success + cycle rejection + nonexistent
  source + nonexistent target), `revokeService` (success + registry removal +
  services graph removal + dependency cleanup + nonexistent error).
  3 `assertInvariants` calls after state-mutating operations.
- **W5-D (M-11)**: Improved `buildChecked` error reporting. All 8 validation
  checks now include their check number and failing entity details (e.g.,
  specific ObjId, ThreadId) for immediate debuggability.
- **W5-E**: Added weak mutation testing assertions to chain1 (retype→endpoint
  verification, mint slot population) and chain5 (copy/move/delete slot state
  verification). Operations now verify actual state mutations, not just success.
- **W5-F (L-2)**: Removed unused `_hCap : capabilityInvariantBundle st`
  parameter from `policyOwnerAuthoritySlotPresent_of_capabilityLookup`.
- **W5-G (L-7)**: Added `resolveExtraCaps` silent-drop documentation explaining
  seL4-matching behavior where failed capability resolutions are silently
  dropped rather than errored.
- Zero sorry/axiom. All test suites pass. `test_smoke.sh` and `test_full.sh` green.

## [0.22.15] — W4: Platform & Architecture Hardening

Phase W4 of WS-W pre-release audit remediation. Addresses M-8, M-9, MED-02,
LOW-02, L-15, L-16, L-12 from v0.22.10 audits.

- **W4-A (M-8)**: BCM2712 datasheet validation checklist completed. All 14
  address constants in S5-F table cross-referenced with S6-G citations and
  marked **Validated** with datasheet document, section, and date references.
- **W4-B (M-9)**: FDT parsing hardened against integer overflow. Added explicit
  bounds checks to `readBE32` (`offset + 4 > blob.size` guard), `readCString`
  (`offset ≥ blob.size` initial guard), and `readCells` (`offset + cells * 4`
  guard). All parsing functions now reject out-of-bounds input before any
  arithmetic.
- **W4-C (MED-02)**: Eliminated all 3 `native_decide` instances in Board.lean.
  `mmioRegionDisjoint_holds`, `rpi5MachineConfig_wellFormed`, and
  `rpi5DeviceTree_valid` now use `decide`, reducing TCB expansion. All
  `DecidableEq` instances properly derived for involved types.
- **W4-D (LOW-02)**: Fixed stale `@[implemented_by]` comment in DeviceTree.lean.
  `fromDtb` stub now correctly documents that `fromDtbFull` is a separate
  function, not an `@[implemented_by]` override.
- **W4-E (L-15)**: `bootFromPlatformUnchecked` deprecated via comprehensive
  docstring directing users to `bootFromPlatformChecked`. Retained as alias
  for backward compatibility with test code.
- **W4-F (L-16)**: Comprehensive MMIO formalization boundary documentation
  added to MmioAdapter.lean. Documents what is modeled (address validation,
  alignment enforcement, region bounds, frame properties, W1C semantics) vs.
  what is deferred to H3 (volatile non-determinism, memory ordering/barriers,
  device-specific register semantics, interrupt side effects, cache coherency).
- **W4-G (L-12)**: `encodeMsgRegs` already removed in W3-H (v0.22.14). No
  action needed.
- Zero sorry/axiom. All module builds pass. `test_fast.sh` (Tier 0+1) green.

## [0.22.14] — W3: Dead Code Elimination

Phase W3 of WS-W pre-release audit remediation. Addresses MED-1/MED-01
(dead code), MED-2 (FrozenOps status), LOW-03/06/07/08 from v0.22.10 audits.

- **Foundation layer (W3-B)**: Removed 7 dead KernelM helper theorems
  (`pure_bind_law`, `get_returns_state`, `set_replaces_state`,
  `modify_applies_function`, `liftExcept_ok`, `liftExcept_error`,
  `throw_errors`); 8 dead alignment predicates and proofs from Machine.lean
  (`wordAligned`, `pageAligned`, proofs, `totalRAM`, `addressInMap`); 9 dead
  `isPowerOfTwo_of_pow2_*` witness theorems and `isPowerOfTwo_spec/pos`;
  duplicate `maxLength`/`maxExtraCaps'` from Types.lean; 4 dead CDT helpers
  (`parentOf`, `removeAsChild`, `removeAsParent`, `isAncestor`,
  `makeObjectCap`) from Structures.lean; `observedCdtEdges` +
  `observedCdtEdges_eq_projection` from State.lean.
- **Kernel subsystems (W3-C)**: Removed `resolveCapAddressK`,
  `severDerivationEdge` from Capability/Operations.lean; `lookupUntyped` from
  Lifecycle/Operations.lean; `maxServiceFuel` from Service/Operations.lean.
- **Architecture & Info Flow (W3-D)**: Removed entire fast-projection cluster
  (~200 lines) from Projection.lean (`computeObservableSet`,
  `projectObjectsFast`, `projectIrqHandlersFast`, `projectObjectIndexFast`,
  `projectStateFast`, 6 helper theorems); `capabilityOnlyOperations`,
  `enforcementBoundaryComplete_counts`, `enforcementBoundary_names_nonempty`
  from Wrappers.lean; 3 orphaned `List.foldl` HashSet bridge lemmas from
  Prelude.lean.
- **Data structures (W3-E)**: Removed `deleteObject` from Builder.lean;
  `addServiceGraph` from Builder.lean.
- **Testing layer (W3-F)**: Removed `listLookup`, `withMachine` from
  StateBuilder.lean.
- **FrozenOps evaluation (W3-G)**: Retained with architectural status
  documentation in Core.lean explaining zero-production-consumer status and
  future integration plan for H3 hardware binding.
- **Type aliases (W3-H)**: Removed `encodeMsgRegs` + `decodeMsgRegs_roundtrip`
  from RegisterDecode.lean (simplified `decode_components_roundtrip` to
  3-component version); `RegisterWriteInvariant` + proof from
  RPi5/RuntimeContract.lean.
- **Additional Architecture (W3-D)**: Removed `asidBound`, `asidBoundForConfig`,
  `resolveAsidRootChecked` + proof, `tlbFlushByASIDPage`, `tlbFlushAll` + proof,
  `storeObject_objectIndex_eq_of_mem` from VSpace.lean.
- **Additional Kernel (W3-C)**: Removed 11 superseded scheduler invariant
  definitions from Invariant.lean (`runQueueThreadPriorityConsistent` chain,
  `threadPriority_membership_consistent` chain, `domainTimeRemainingPositive`
  dead lemmas, `runnableThreadsAreTCBs_of_scheduler_objects_eq`); 8 dead
  RunQueue rotation/membership theorems; 4 `lifecycleRetypeDirect_*` error
  theorems from Lifecycle/Operations.lean; `syscallLookupCap_state_unchanged`
  and `dispatchCapabilityOnly_some_iff` from API.lean;
  `crossSubsystemInvariantFolded` + `iff_folded` from CrossSubsystem.lean.
- **Additional Data structures (W3-E)**: Removed `beq_symmetric`,
  `ofList_invExt`/`ofList_size_lt_capacity`/`ofList_invExtK` chain from
  RobinHood/Bridge.lean; `fold`, `size`, `capacity`, 3 proof theorems from
  RobinHood/Set.lean; `extractBits_zero_width` from RadixTree/Core.lean.
- Zero `sorry`, zero `axiom`. `test_full.sh` green.

## [0.22.13] — W2 audit: completeness and accuracy fixes

Post-implementation audit of Phase W2. Ensures all deliverables are complete
and documentation accurately reflects code.

- **W2-H completeness**: Documented all 9 elevated `maxHeartbeats` settings
  (previously only 4 of 9 were documented). Newly documented: CDT acyclicity
  (2M, Structures.lean), filter fold induction (2×400K, RobinHood/Bridge.lean),
  combined insertLoop preservation (420K, RobinHood/Invariant/Preservation.lean),
  buildCNodeRadix lookup equivalence (800K, RadixTree/Bridge.lean).
- **W2-A accuracy**: Fixed `storeObject_modifiedFields` (added `.lifecycle`),
  `revokeService_modifiedFields` (added `.serviceRegistry`),
  `ipcEndpointOp_modifiedFields` and `capabilityOp_modifiedFields` (added
  `.lifecycle`). All four `modifiedFields` definitions now accurately reflect
  the fields each operation writes via `storeObject`.
- **Documentation sync**: Updated stale metrics in SELE4N_SPEC.md (v0.22.3
  → v0.22.13, 69,994 → 73,246 LoC, 2,008 → 2,153 proved declarations),
  README.md, and CLAUDE.md.
- Zero `sorry`, zero `axiom`.

## [0.22.12] — W2: Proof Formalism & Architecture

Phase W2 of WS-W pre-release audit remediation. Closes 2 HIGH, 4 MEDIUM,
1 LOW findings from the v0.22.10 comprehensive audits.

- **H-2 (field-disjointness formalism)**: Added `modifiedFields` definitions for
  6 operation categories, 3 new per-predicate frame lemmas
  (`noStaleEndpointQueueReferences_frame`, `noStaleNotificationWaitReferences_frame`,
  `registryEndpointValid_frame`), and `fieldDisjointness_frameIndependence_documented`
  theorem connecting all 6 disjoint predicate pairs to frame independence guarantees.
- **H-1 (composition gap)**: `crossSubsystemInvariant_composition_gap_documented`
  theorem with comprehensive documentation of partial mitigation via frame lemmas
  and remaining gap scope for the 4 sharing predicate pairs.
- **MED-04 (wildcard unreachability)**: `dispatchWithCap_wildcard_unreachable` proves
  all 17 `SyscallId` variants are handled by explicit dispatch arms, making the
  `| _ => .error .illegalState` wildcard dead code.
- **M-6 (fuel sufficiency)**: `collectQueueMembers_fuel_sufficiency_documented` with
  formal argument citing `tcbQueueChainAcyclic` invariant for traversal termination.
- **M-4 (fuel exhaustion)**: `serviceHasPathTo_fuel_exhaustion_conservative` proves
  fuel=0 returns `true` (conservative safety). `serviceBfsFuel_adequate` verifies
  fuel bound exceeds object index length.
- **M-5 (serviceCountBounded)**: `removeDependenciesOf_objectIndex_eq` frame lemma,
  `serviceCountBounded_preservation_chain_documented` comprehensive preservation chain.
- **M-3 (boundary unification)**: `enforcementBoundaryExtended` unified as
  definitional `abbrev` of `enforcementBoundary`, adding element-wise equality proof
  `enforcementBoundaryExtended_eq_canonical`.
- **L-3 (maxHeartbeats)**: Documented all 9 elevated `maxHeartbeats` settings with
  rationale for inherent complexity (nested induction, hash table modular arithmetic,
  scheduler composition).
- Zero `sorry`, zero `axiom`.

## [0.22.11] — W1: Critical Rust ABI Fixes

- **CRIT-1/CRIT-2 fixed**: `notification_signal` dispatched `SyscallId::Send`
  instead of `SyscallId::NotificationSignal`; `notification_wait` dispatched
  `SyscallId::Receive` instead of `SyscallId::NotificationWait`. Both corrected.
- **HIGH-02 fixed**: `notification_signal` now accepts a `Badge` parameter and
  passes it via message register 0, matching the Lean kernel's
  `decodeNotificationSignalArgs` which reads badge from `MR[0]`.
- **HIGH-1 fixed**: Added `MmioUnaligned` error variant (discriminant 40) to
  Rust `KernelError`, matching Lean `KernelError.mmioUnaligned`.
- **MED-03 fixed**: New `endpoint_reply_recv` wrapper implementing the compound
  reply+receive syscall (`SyscallId::ReplyRecv`).
- **MED-05 fixed**: Updated `sele4n-sys` crate documentation from "14 syscalls"
  to "17 syscalls" and listed all 7 IPC wrappers.
- Fixed XVAL-015 conformance test which was validating the bug (asserting badge
  comes from capability, contradicting the Lean decode layer).
- Added 8 new W1 conformance tests: variant count assertions (KernelError=41,
  SyscallId=17), ABI constant assertions, encoding verification for all three
  new/fixed wrappers, MmioUnaligned discriminant, endpoint\_reply\_recv register
  layout validation.
- Fixed `decode_unknown_error_code` test boundary (40→41).
- **Audit fix**: `endpoint_reply_recv` had two bugs — (a) user `msg.regs[0]`
  was silently dropped (MR layout started at `regs[1]` instead of `regs[0]`),
  (b) `MessageInfo.length` did not account for the reply\_target slot in MR\[0\]
  (must be `user_len + 1`). Both corrected.
- Added `MmioUnaligned` to `new_variants_discriminants` test for explicit
  discriminant cross-validation.
- Fixed stale comment in `decode.rs` referencing old 0–39 error range (now 0–40).
- Bumped Lean project version to 0.22.11, Rust workspace version to 0.22.11.
- 168 Rust tests pass, zero `cargo doc` warnings.
- Zero `sorry`, zero `axiom`.

## [0.22.10] — V8 Audit: Semantic Correctness & Fixture Hardening

- **AUDIT-1**: Added `BlockedReply` as 8th `ThreadState` variant — `blockedOnReply`
  was incorrectly mapped to `.BlockedRecv`, collapsing two semantically distinct
  IPC states (server-side reply wait vs client-side receive wait).
- **AUDIT-2**: V8-A1 pipeline fixture expanded from 1 capability to 3 (endpoint,
  notification, CNode) per V8 spec. Notification object added with idle state.
- **AUDIT-3**: Fixed remaining dequeue-on-dispatch violations in
  `InformationFlowSuite.lean` — threads that are `current` must not appear in
  the runnable list.
- **AUDIT-4**: Added design-note documentation to `threadStateConsistentChecks`
  clarifying that it validates inference-logic consistency after `syncThreadStates`,
  not operational drift detection.
- Updated `ThreadState` enum from 7 to 8 variants in CHANGELOG V8-G entry.
- Fixture and SHA-256 hash regenerated for expanded pipeline output.
- Zero `sorry`, zero `axiom`. All smoke and full tests pass.

## [0.22.9] — V8: Test Coverage & Documentation

- **V8-A** (M-TST-1): End-to-end `syscallEntryChecked` pipeline test covering
  register decode (A2), argument extraction (A3), checked dispatch (A4),
  invariant preservation (A5), and trace equivalence vs unchecked path (A6).
- **V8-B** (M-TST-2): `cspaceMove` end-to-end test: register decode →
  move operation → verify source empty, dest populated, target preserved.
- **V8-C** (M-TST-3): Post-mutation invariant checks added for 5 operations
  (vspace map/unmap, service store/dep, cspace copy, timer tick expiry).
  Removed raw `lifecycleRetypeObject` check (use cleanup variant instead).
- **V8-D** (M-TST-4): `buildValidated` Check 8 fixed for dequeue-on-dispatch
  semantics — current thread must NOT be in run queue. Propagated to 7 test
  states across MainTraceHarness and OperationChainSuite.
- **V8-E** (M-TST-5): `partial` removed from `intrusiveQueueReachable` — uses
  fuel-based termination instead.
- **V8-F** (M-TST-6): Fixture drift detection via SHA-256 hash companion file.
  Verified in `test_tier2_trace.sh` before fixture comparison.
- **V8-G** (M-TST-9): `ThreadState` enum (8 variants) added to model:
  - G1: `ThreadState` inductive + `threadState` field on `TCB`.
  - G3: `inferThreadState`, `syncThreadStates`, `threadStateConsistent` —
    non-invasive design that preserves all existing operational proofs.
  - G7: `threadStateConsistentChecks` in `InvariantChecks.lean`;
    `assertStateInvariantsFor` auto-syncs before checking.
- **V8-H** (M-API-4): Shared `dispatchCapabilityOnly` extracts 6 capability-only
  syscall arms used by both checked and unchecked dispatch. ~120 lines of
  duplication removed. `dispatchCapabilityOnly_some_iff` theorem added.
- Zero `sorry`, zero `axiom`. All 38 inter-transition invariant checks pass.

## [0.22.8] — V7: Performance & Data Structure Optimization

- **V7-C** (M-DS-3): `LawfulBEq` made explicit API-level requirement for all
  `RHTable` public operations. Ripple fixes across 18 files including
  FrozenState.lean, FreezeProofs.lean, and Commutativity.lean.
- **V7-D** (M-DS-5): General `filter_preserves_key` theorem proved for arbitrary
  predicates via `filter_fold_present` / `filter_fold_absent_by_pred`.
- **V7-A** (M-DS-1): `filter_fold_present` proof refactored with
  `filter_fold_present_step` helper. Heartbeat budget reduced from 3.2M to 400K.
- **V7-B** (M-DS-2): `insertLoop_preserves_noDupKeys` and
  `insertLoop_preserves_pcd` proofs refactored with `noDupKeys_after_set` and
  `distCorrect_after_set` helpers. Heartbeat budgets reduced from 800K to
  420K (noDupKeys) and 400K (pcd).
- **V7-G** (L-DS-1): `CNodeRadix.toList` refactored from O(n²) to O(n)
  cons+reverse with updated `toList_eq_collectEntries` proof.
- **V7-I** (L-PLAT-2): `irqKeysNoDup`/`objIdKeysNoDup` replaced with O(n)
  `natKeysNoDup` using `Std.HashSet`.
- **V7-E** (M-RS-6): `native_decide` replaced with `decide` in
  `RegisterFile.not_lawfulBEq`.
- **V7-F** (M-TST-8): Non-lawful `BEq RegisterFile` documented in Machine.lean
  and test code.
- **V7-H** (L-DS-2): Robin Hood `erase` size decrement safety documented.
- **V7-J** (L-SCH-3): `RunQueue.wellFormed` design rationale and `ofList`
  validated constructor documented.

## [0.22.5] — V5 Audit: domainTimeRemainingPositive bundle integration

- V5-H (M-HW-7): **Audit fix** — `domainTimeRemainingPositive` is now the 8th
  conjunct of `schedulerInvariantBundleFull`. Added per-operation preservation
  proofs for `schedule`, `handleYield`, `timerTick`, `switchDomain`, and
  `scheduleDomain`. Updated `default_schedulerInvariantBundleFull` (Architecture)
  and `bootFromPlatform_proofLayerInvariantBundle_general` (Boot). All proofs
  machine-checked, zero sorry.
- V5-C (M-DEF-3): Test code updated to use `bootFromPlatformUnchecked` alias.
- V5-D/E (M-DEF-4/5): Added design note to `schedule` documenting checked vs
  unchecked context save/restore usage rationale.

## [0.22.4] — V5: Defensive Coding & Robustness

- V5-A (M-DEF-1): Replaced panicking `ByteArray.get!` with safe `data[·]?`
  in `readBE32` and `readCString` DTB parsing functions.
- V5-B (M-DEF-2): Added internal-only documentation warnings to
  `lifecycleRetypeObject` and `lifecycleRetypeDirect`.
- V5-C (M-DEF-3): Added `bootFromPlatformUnchecked` alias and promoted
  `bootFromPlatformChecked` as the recommended boot entry point.
- V5-D (M-DEF-4): Added `saveOutgoingContextChecked` with explicit success
  indicator and equivalence theorem.
- V5-E (M-DEF-5): Added `restoreIncomingContextChecked` with explicit success
  indicator and equivalence theorem.
- V5-F (M-DEF-6): `handleYield` now returns `.invalidArgument` when
  `current = none` instead of falling through to `schedule`. Updated 10
  preservation proofs in Preservation.lean and 1 in Operations.lean.
- V5-G (M-DEF-7): Added comprehensive revocation routing guide documenting
  `cspaceRevoke`, `cspaceRevokeCdt`, `cspaceRevokeCdtStrict`, and
  `cspaceRevokeCdtStreaming` entry points.
- V5-H (M-HW-7): Added `domainTimeRemainingPositive` invariant with default
  state theorem and frame preservation lemma.
- V5-I (H-SVC-1): Added fuel bounds documentation for `serviceHasPathTo` and
  `maxServiceFuel` constant.
- V5-J (L-FND-1): Added `ThreadId.toObjIdVerified` with TCB type verification
  via caller-supplied predicate.
- V5-K (L-FND-1): Documented `storeObject` infallibility design rationale.
- V5-L (L-SCH-1): Added configurable `configDefaultTimeSlice` field to
  `SchedulerState` (default 5).
- V5-M (L-SCH-2): Documented `timerTick` pre-reset priority correctness.
- V5-N (L-CAP-1): Removed redundant `detachSlotFromCdt` from `processRevokeNode`
  and `cspaceRevokeCdtStrict`. Updated Capability Invariant Preservation proofs.
- V5-O (L-DS-3): Added queue direction consistency check to `frozenQueuePopHead`.
- V5-P (L-DS-4): Added occupied-slot guard to `frozenCspaceMint`.

## [0.22.3] — V3-J/K: IPC Queue Invariant Completion

- V3-J (L-IPC-3): `ipcStateQueueMembershipConsistent` — strengthened version of
  `ipcStateQueueConsistent` with TCB queue reachability predicates. Primitive
  frame lemmas in `QueueMembership.lean`: `storeObject_non_ep_non_tcb_preserves_*`,
  scheduler helpers (`ensureRunnable`/`removeRunnable`), and pointwise lookup
  transfer helper `ipcStateQueueMembershipConsistent_of_objects_eq`. Integrated
  as 7th conjunct of `ipcInvariantFull`. Definition moved from `Structural.lean`
  to `Defs.lean` for forward-reference resolution.
- V3-K (L-LIFE-1): `endpointQueueNoDup` — no self-loops in intrusive queue
  chains, sendQ/receiveQ head disjointness. Primitive frame lemmas in
  `QueueNoDup.lean`: `storeObject_non_ep_non_tcb_preserves_*`,
  `storeTcbQueueLinks_preserves_*`, `storeObject_endpoint_preserves_*`.
  Integrated as 6th conjunct of `ipcInvariantFull`.
- V3-J-cross: `queueNextBlockingConsistent` — new invariant ensuring that if
  `a.queueNext = some b`, then `a` and `b` are blocked on the same endpoint with
  compatible queue types (send/call share sendQ, receive uses receiveQ).
  Extracted `queueNextBlockingMatch` helper predicate. Integrated as 8th
  conjunct of `ipcInvariantFull` (was 7). Primitive preservation proofs in
  new `QueueNextBlocking.lean`: `ensureRunnable`, `removeRunnable`,
  `storeObject_endpoint`, `storeObject_non_ep_non_tcb`, `storeTcbQueueLinks`
  (conditional), `storeTcbIpcStateAndMessage` (general + `.ready` + no-links
  variants). Resolves cross-endpoint PopHead frame gap in V3-J-op-2d.
  QHBC primitive preservation proofs: `ensureRunnable`, `removeRunnable`,
  `storeTcbIpcStateAndMessage` (with `hNotHead` precondition),
  `storeTcbPendingMessage`.
- V3-J compound proofs: `queueHeadBlockedConsistent` (QHBC) invariant added —
  queue heads must be in correct blocking state (`blockedOnReceive` for receiveQ
  heads, `blockedOnSend ∨ blockedOnCall` for sendQ heads). Integrated as 9th
  conjunct of `ipcInvariantFull` (was 8). `storeTcbIpcState_general_preserves_ipcStateQueueMembershipConsistent`
  added — general variant allowing blocking states with reachability callbacks.
  4 compound V3-J preservation proofs in `Structural.lean`:
  `endpointSendDual_preserves_ipcStateQueueMembershipConsistent`,
  `endpointReceiveDual_preserves_ipcStateQueueMembershipConsistent`,
  `endpointCall_preserves_ipcStateQueueMembershipConsistent`,
  `endpointReplyRecv_preserves_ipcStateQueueMembershipConsistent`.
  Uses `tcbQueueChainAcyclic_no_self_loop` for prev≠sender derivation
  and QHBC for `.blockedOnReply` hNotHead derivation.
- V3-J/K/J-cross bundle integration: `ipcInvariantFull` expanded from 5 to 9
  conjuncts. All 10 `_preserves_ipcInvariantFull` theorems updated. New
  extractors: `coreIpcInvariantBundle_to_endpointQueueNoDup`,
  `coreIpcInvariantBundle_to_ipcStateQueueMembershipConsistent`,
  `coreIpcInvariantBundle_to_queueNextBlockingConsistent`,
  `coreIpcInvariantBundle_to_queueHeadBlockedConsistent`. Default state
  proofs, lifecycle integration, and `advanceTimerState` preservation updated.
- Zero `sorry`, zero `axiom`. All 182 build targets pass. `test_full.sh` green.

## [0.22.2] — WS-V Phase V3: Proof Chain Hardening

- V3-A (H-RH-1): Added `invExtFull` bundle (`invExt ∧ loadFactorBounded`) and
  `invExtFull_implies_size_lt_capacity` lemma proving strict size bound from
  load factor. Eliminates redundant `hSize` hypothesis for erase operations.
- V3-B (H-RH-1): Added `erase_preserves_invExtFull` — erase preserves the full
  extended invariant without a separate `hSize` parameter. Load factor bound
  derived internally via V3-A lemma.
- V3-C (H-RAD-1): Added `uniqueRadixIndices_sufficient` machine-checked theorem
  proving that bounded keys + `UniqueRadixIndices` imply the `hNoPhantom`
  precondition for `buildCNodeRadix_lookup_equiv`.
- V3-D1-D5 (M-PRF-1): CDT acyclicity discharge chain.
  `cdtExpandingOp_preserves_bundle_with_hypothesis` (machine-checked, returns
  caller-supplied `hCdtPost`). `cdtShrinkingOps_preserve_acyclicity_note`
  (documentation-only) documents that shrinking ops prove via `edgeWellFounded_sub`.
- V3-E1-E5 (M-PRF-2): `ipcUnwrapCapsLoop_capInvariant` predicate defined.
  Per-step theorem (`ipcTransferSingleCap_preserves_capabilityInvariantBundle`)
  fully proved (machine-checked). Loop composition proofs (E1–E5) documented
  but not yet machine-checked.
- V3-F (M-PRF-3): `resolveCapAddress_callers_check_rights_note`
  (documentation-only) — documents that all 17 `SyscallId` dispatch arms pass
  through `syscallLookupCap` rights gate. No machine-checked dispatch analysis.
- V3-G1-G6 (M-PRF-5): Added `waitingThreadsPendingMessageNone` invariant
  (threads blocked on receive/notification have `pendingMessage = none`).
  Machine-checked primitive preservation lemmas for `removeRunnable`,
  `ensureRunnable`, `storeObject` (non-TCB), `storeTcbIpcState`,
  `storeTcbIpcStateAndMessage`, `storeTcbQueueLinks`, and
  `storeTcbPendingMessage` in `Structural.lean`. Full operation-level
  machine-checked proofs for all 7 IPC operations. V3-G6: integrated as
  5th conjunct of `ipcInvariantFull` (was 4-conjunct). Updated all bundle
  preservation theorems, extractors, and default proofs.
- V3-H (M-DS-4): `buildCNodeRadix_hNoPhantom_auto_discharge_note`
  (documentation-only) — documents auto-discharge pattern for bounded-key
  CNodes. Requires `extractBits_identity` lemma not yet formally proven.
- V3-I (L-IPC-1): `notificationWake_pendingMessage_was_none` documentation
  theorem (documentation-only) — wake path overwrites `none` (no data loss)
  under the V3-G invariant.
- Zero `sorry`, zero `axiom`. All 182 build targets pass. `test_full.sh` green.

## [0.22.0] — WS-V Phase V1: Rust ABI Hardening

- V1-A (H-RS-1): Added u64 range guard in `decode_response` — values exceeding
  `u32::MAX` now return `InvalidSyscallNumber` instead of silently truncating
  (e.g., `0x1_0000_0000` no longer yields false success).
- V1-B (L-RS-1): Fixed stale comment in decode.rs — error codes "0–37" updated
  to "0–39" reflecting the actual 40-variant `KernelError` enum.
- V1-C (M-RS-1): Changed `LifecycleRetypeArgs.new_type` from raw `u64` to
  validated `TypeTag` enum. Decode now rejects invalid type tag values > 5
  with `InvalidTypeTag`.
- V1-D (M-RS-2): Replaced all 13 `MessageInfo::new(...).unwrap()` calls in
  `sele4n-sys` with `MessageInfo::new_const()` — a compile-time validated
  infallible constructor that eliminates runtime panic risk for known-valid
  constant arguments.
- V1-E (M-RS-3): Fixed `IpcBuffer::get_mr()` to return `InvalidArgument`
  (not `InvalidMessageInfo`) for inline register indices 0–3. The message
  structure is valid; the argument is semantically wrong.
- V1-F (M-RS-4): Fixed `CSpaceMintArgs::decode()` and `PagePerms::TryFrom<u64>`
  to return `InvalidArgument` (not `InvalidMessageInfo`) for invalid argument
  values. The message structure is correct; the argument value is invalid.
- V1-G (M-RS-5): Added `PagePerms::checked_bitor()` that validates W^X at
  combine time, returning `PolicyDenied` if write + execute are both set.
  Standard `BitOr` still available for data composition (W^X enforced at
  point of use in `vspace_map()`).
- V1-H (M-RS-7): Added `is_reserved()`, `is_valid()`, and `MAX_VALID`
  constants to `Slot` (max 2^32), `DomainId` (max 255), and `Priority`
  (max 255) identifier types.
- V1-I (L-RS-2): Added bounds validation to `ServiceRegisterArgs::decode()`:
  `method_count` capped at 1024, `max_message_size`/`max_response_size`
  capped at 960 bytes (120 registers × 8 bytes).
- V1-J (L-RS-3): Aligned `IpcBuffer::get_mr()` error variant with V1-E fix.
- V1-K (M-TST-7): Added 10 new conformance tests covering all V1 changes:
  u64 overflow, TypeTag validation, error variant correctness, W^X
  checked_bitor, identifier validation, bounds enforcement.
- V1-L: Full Rust test suite: 157 tests pass, 0 failures, 0 warnings.

## [0.21.7] — WS-U Phase U8: Documentation & Closure (WS-U PORTFOLIO COMPLETE)

- U8-A (U-L16): Eliminated `simSubstantiveMemoryMap` duplication — made
  `simMachineConfig.memoryMap` reference the shared definition directly from
  `RuntimeContract.lean`. Added compile-time consistency theorem
  `simSubstantiveMemoryMap_eq_machineConfig` in `Contract.lean`.
- U8-B (U-L18, U-L19): Documented IRQ/INTID range limitations in
  `RPi5/BootContract.lean` (SGIs are IPI-only, not hardware interrupts) and
  `RPi5/Board.lean` (GIC-400 SPI cap at INTID 223, BCM2712 extended
  peripherals beyond 223 not covered).
- U8-C (U-L24): Documented notification word overflow in
  `IPC/Operations/Endpoint.lean` — model uses unbounded Lean Nat for
  notification badge merge, WS-V hardware binding must enforce 64-bit
  word width at platform boundary.
- U8-D (U-L26): Documented scheduler design decisions in `RunQueue.lean`
  (`recomputeMaxPriority` O(p) complexity for ≤256 priorities) and
  `Operations/Core.lean` (starvation freedom not guaranteed — matches seL4
  fixed-priority preemptive design).
- U8-E (U-M35): Documented hash collision assumption in
  `RobinHood/Invariant/Lookup.lean` — proofs assume `LawfulBEq` and
  deterministic `Hashable`, collision resistance not formally modeled
  (kernel uses typed system-assigned IDs, not adversary-controlled keys).
- U8-F: Synchronized all documentation to v0.21.7 — README badges and
  metrics, SELE4N_SPEC, DEVELOPMENT, WORKSTREAM_HISTORY, CLAIM_EVIDENCE_INDEX,
  GitBook chapters, i18n READMEs, CLAUDE.md, codebase_map.json, CHANGELOG.
- U8-G: Comprehensive validation — `test_full.sh` and `test_nightly.sh` pass.
- U8-H: WS-U closure report documenting all 97 sub-tasks across 8 phases
  (U1–U8), 12 erroneous findings identified, and items deferred to WS-V.
- **WS-U PORTFOLIO COMPLETE**: All 8 phases (U1–U8), 97+ sub-tasks delivered.

## [0.21.6] — WS-U Phase U7: Dead Code & Proof Hygiene

- U7-A: Deleted dead `KMap.lean` module (219 lines, never imported).
- U7-B: Removed dead types from `Assumptions.lean` (`TransitionSurface`,
  `InvariantSurface`, `ContractRef`, `ExceptionLevel`, `ExtendedBootBoundaryContract`
  and 6 associated functions/theorems), `MmioAdapter.lean` (`MemoryBarrier`,
  `MmioOpKind`, `MmioOp` and associated functions), `Policy.lean`
  (`defaultGenericLabelingContext`, `threeDomainExample`, `bibaPolicy` and
  9 associated theorems/definitions).
- U7-C: Removed dead functions across `Prelude.lean` (`Deadline.none/immediate`),
  `Machine.lean` (`alignedRead/Write`), `FrozenState.lean` (`FrozenSet.mem`,
  `minObjectSize`, `objectCapacity` and proofs), `RunQueue.lean`
  (`rotateHead`, `filterToList`, `maxPriorityValue`, `mem_rotateHead`),
  `VSpaceBackend.lean` (`hashMapVSpaceBackend` instance).
- U7-D: Removed trivial `_deterministic` tautology theorems across all
  subsystems (adapter, register decode, syscall arg decode, lifecycle,
  object type, page permissions, message register extraction).
- U7-E: Removed superseded invariant bundles: `kernelInvariant` (4-tuple),
  `canonicalSchedulerInvariantBundle`, 4 `kernelInvariant` preservation
  theorems from scheduler, `capabilityInvariantBundleWithMintCompleteness`,
  `capabilityInvariantBundleWithCdtMaps`, `capabilityInvariantBundleFull`
  and associated extraction theorems from capability.
- U7-G/H: Fixed `BEq RHTable` symmetry — added reverse fold to ensure
  `(a == b) = (b == a)`. Added `RHTable.beq_symmetric` theorem.
- U7-I: Migrated 5 `native_decide` to `decide` in `Object/Types.lean` and
  `Object/Structures.lean`, reducing TCB surface for small-domain proofs.
- U7-J: Refactored high-heartbeat Robin Hood proofs in `Lookup.lean` —
  removed all `maxHeartbeats` overrides (previously 800K–3.2M).
- U7-L: Added builder/frozen commutativity proofs in `FreezeProofs.lean`:
  `freezeMap_store_commutes_at_key`, `freezeMap_store_commutes_other_key`,
  `freezeMap_store_commutes_all`, thread/CDT store commutativity,
  `freezeMap_sequential_stores_commute`, `freezeMap_insert_step`.
- Updated tier 3 invariant surface anchors for all removed definitions.
- Updated `FrozenStateSuite.lean` test suite (14 tests, down from 15).

## [0.21.5] — WS-U Phase U6: Architecture & Platform Fidelity

- U6-A (U-M08): Added formal MMIO abstraction boundary with `MmioReadKind`
  (ram/volatile/writeOneClear/fifo), `MmioWriteKind` (normal/writeOneClear/
  setOnly), and `MmioRegionDesc` structure. Prevents unsound proofs about
  device register reads by classifying MMIO read/write semantics per region.
  Added `MmioSafe` hypothesis type requiring platform-specific justification.
- U6-B (U-M08): Added `notInMmioRegion` predicate and proof guidance for
  VSpace page-table walk proofs to exclude MMIO-mapped addresses from
  idempotency assumptions.
- U6-C (U-M09): Strengthened `registerContextStable` in RPi5 runtime contract
  from permissive `sp preserved OR context switch` to require machine register
  file matches scheduled thread's TCB `registerContext` field. TCB lookup
  failure (missing object or non-TCB type) is a contract violation (`false`),
  preventing malformed scheduler states from being silently accepted.
- U6-D (U-M09): Updated RPi5 proof hooks documentation for strengthened
  contract. Restrictive contract unchanged (still vacuously correct).
- U6-E (U-M12): Added `irqsUnique` duplicate IRQ detection for boot config
  validation. Documented last-wins semantics of `foldIrqs`.
- U6-F (U-M13): Added `objectIdsUnique` duplicate object ID detection for
  boot config validation. Added `PlatformConfig.wellFormed` predicate and
  `bootFromPlatformChecked` enforcement variant that rejects configs with
  duplicate IRQs or object IDs.
- U6-G (U-M15): Proved boot-to-runtime invariant bridge for empty config:
  `bootToRuntime_invariantBridge_empty` composes boot validity through freeze
  to establish both `proofLayerInvariantBundle` and `apiInvariantBundle_frozen`.
  General config bridge deferred to WS-V (requires builder operation extension).
- U6-H (U-M10): Added `mmioWrite32` and `mmioWrite64` operations for ARM64
  GIC register access with little-endian byte ordering and frame theorems.
- U6-I (U-M22): Documented non-standard BIBA integrity direction as deliberate
  design choice in Policy.lean with full rationale (capability authority flow).
- U6-J (U-M24): Documented service registry NI projection gap in Projection.lean
  — service orchestration state not captured by non-interference proofs.
- U6-K (U-M23): Documented accepted covert channels (scheduling state, TCB
  metadata, machine timer exclusion, object store metadata) in Projection.lean.
- U6-L (U-M14): Documented cross-subsystem invariant composition gap in
  CrossSubsystem.lean — conjunction may not be the strongest composite.

## [0.21.4] — WS-U Phase U5: API & Dispatch Integrity

- U5-A (U-M02): Verified structural equivalence of checked/unchecked dispatch
  for all 6 capability-only syscalls (cspaceDelete, lifecycleRetype, vspaceMap,
  vspaceUnmap, serviceRevoke, serviceQuery) with machine-checked proofs. Added
  `checkedDispatch_capabilityOnly_eq_unchecked` theorem covering all shared arms.
- U5-B (U-M01): Routed `.call` syscall through `endpointCallChecked` enforcement
  wrapper instead of an inline `securityFlowsTo` guard. This ensures `.call`
  uses the same enforcement layer as all other policy-gated operations.
- U5-C (U-M04): Routed `.reply` syscall through `endpointReplyChecked` enforcement
  wrapper for defense-in-depth. Reply caps are single-use authority, but the
  wrapper ensures auditability and consistency with the enforcement layer.
- U5-D (U-L20): Replaced trivial `checkedDispatch_subsumes_unchecked_documentation
  : True := trivial` with 7 machine-checked structural equivalence theorems proving
  the checked and unchecked paths are identical for capability-only operations.
- U5-E (U-M07): Changed `decodeVSpaceMapArgs` error from `.policyDenied` to
  `.invalidArgument` for invalid permission bits. Added `invalidArgument`
  variant to `KernelError` enum. This correctly classifies the error as a
  decode failure rather than a policy violation.
- U5-F/G (U-M21): Added `capabilityOnlyOperations` definition and comprehensive
  documentation in `Enforcement/Wrappers.lean` explaining why 7 operations have
  no runtime flow check (NI relies on proof soundness + capability authority).
- U5-H (U-M03): Documented badge-0 semantics in API dispatch — badge value 0
  is treated as "no badge" by design, matching seL4 semantics.
- U5-I (U-M28): Documented IPC message handling semantics in `endpointSendDual` —
  seLe4n rejects oversized messages with explicit errors rather than seL4's
  silent truncation.
- U5-J (U-M29): Documented `notificationSignal` wake-path overwrite — safe
  because `ipcStateQueueConsistent` invariant guarantees waiters have no
  pending message.
- U5-K/M (U-M30/U-L06): Documented CSpace root slot 0 simplification and
  cap transfer CDT tracking in `WithCaps.lean` — imprecise but safe,
  over-revokes rather than under-revokes.
- U5-L (U-L05): Documented `AccessRight.grantReply` (bit 3) as spec fidelity —
  no operational effect in current model, `.grant` governs all grant operations.
- U5-N (U-L27): Added note that `notificationSignalChecked` is defined but
  not wired into syscall dispatch (deferred to WS-V hardware binding).

## [0.21.3] — WS-U Phase U4: Proof Chain & Invariant Composition

- U4-A/B/C/D: Discharged `hProjection` preconditions for all four IPC endpoint
  operations (`endpointSendDual`, `endpointReceiveDual`, `endpointCall`,
  `endpointReplyRecv`), making scheduler preservation self-contained.
- U4-K: Made `endpointSendDual/ReceiveDual/Call/ReplyRecv_preserves_ipcInvariantFull`
  self-contained by deriving `allPendingMessagesBounded` and `badgeWellFormed`
  internally. Added 3 primitive `badgeWellFormed` preservation helpers
  (`storeTcbQueueLinks`, `storeTcbPendingMessage`, `storeObject_endpoint`) and
  8 composed endpoint-level preservation theorems.
- U4-N: Proved BFS positional queue lemma (`descendantsOf_go_queue_pos_children_found`)
  and queue membership variant (`descendantsOf_go_mem_children_found`) for CDT
  `descendantsOf`. These establish that if a node is anywhere in the BFS queue
  with sufficient fuel, all its children appear in the result — key infrastructure
  for transitive closure fuel sufficiency.

## [0.21.2] — WS-U Phase U3: Rust ABI Hardening

- U3-A (U-H11): Added `clobber_abi("C")` to `svc #0` inline assembly in
  `trap.rs`. The compiler now knows all caller-saved registers (x8–x18, x29,
  x30, NZCV, SIMD/FP) may be modified by the kernel during the exception,
  preventing silent register corruption.
- U3-B (U-M32): Made `MessageInfo` fields private. All construction must go
  through `new()` or `decode()`, both of which validate bounds. Added
  `length()`, `extra_caps()`, and `label()` accessor methods.
- U3-C (U-M32): Updated all `MessageInfo` call sites across `sele4n-abi`,
  `sele4n-sys`, and conformance tests to use `MessageInfo::new()` instead of
  struct literal construction.
- U3-D (U-M33): Replaced `From<u8> for AccessRights` with `TryFrom<u8>`.
  Values with bits 5–7 set (> 0x1F) are now rejected with `AccessRightsError`.
  Updated all call sites including CSpace argument decode.
- U3-E (U-M33): Added AccessRights roundtrip conformance tests covering all
  valid values (0–31), all invalid values (32–255), and bitmask operation
  validity preservation.
- U3-F (U-L08): Added `#[non_exhaustive]` to `KernelError` enum, ensuring
  future error variant additions are non-breaking for downstream crates.
- U3-G (U-L09): Added `RegisterFile` type with safe bounds-checked `get()`/
  `set()` methods returning `Option`. Out-of-bounds access returns `None`
  instead of panicking.
- U3-H (U-L10): Added bit-layout ASCII diagrams as doc-comments for
  `MessageInfo::encode` and `MessageInfo::decode` showing the 64-bit packing
  (bits 0–6 = length, 7–8 = extra_caps, 9–63 = label).
- U3-I (U-M34): Added compile-time `const` layout assertions for `IpcBuffer`
  `#[repr(C)]` verifying size (960 bytes) and alignment (8 bytes). Documented
  Lean-side correspondence.
- U3-J (U-L13): Added `scripts/test_rust_conformance.sh` — dedicated Rust ABI
  conformance test runner with unsafe containment verification and optional
  test vector fixture dump for Lean cross-validation.
- Rust workspace version bump to 0.21.2. All 135 Rust tests pass.
- Version bump to 0.21.2.

## [0.21.1] — WS-U Phase U2: Safety Boundary Hardening

- U2-A/B/C (U-H06): Added `VAddr.isCanonical` / `VAddr.canonical` predicates.
  Canonical address check in `vspaceMapPageChecked`, `vspaceMapPageCheckedWithFlush`,
  and `decodeVSpaceMapArgs`. Canonical address rejection theorem proved.
- U2-D/E/F (U-H07): Parameterized physical address width via
  `MachineConfig.physicalAddressWidth`. Added `physicalAddressBoundForConfig`,
  `vspaceMapPageCheckedWithFlushPlatform`, and PA-width-aware
  `DeviceTree.fromDtbWithRegions`.
- U2-G/H (U-H08): Added `ASID.isValidForConfig` / `ASID.validForConfig`
  predicates. ASID validation in `decodeVSpaceMapArgs` and
  `decodeVSpaceUnmapArgs`. Updated roundtrip and error-iff proofs with ASID
  preconditions.
- U2-I/J (U-H05): Documented `vspaceMapPage` and `lifecycleRetypeObject` as
  internal proof helpers with "do not use directly" docstrings. Updated test
  harness references to use public API.
- U2-K (U-L03): Added `AccessRightSet.mk_checked` proof-carrying constructor
  with `bits < 2^5` obligation. Added `empty_valid`, `singleton_valid`,
  `mk_checked_valid`, `union_valid`, `inter_valid`, and `isWord5_of_valid`
  lemmas. Closure proofs use `Nat.or_lt_two_pow` and `Nat.and_le_left`.
- U2-L (U-M18): Audited all `storeObject` call sites. Documented three
  categories: allocation-guarded (lifecycle retype), in-place mutation (VSpace,
  CSpace, IPC, scheduler), and builder/boot.
- U2-M (U-M20): Added `allTablesInvExt_witness` compile-time completeness
  theorem. Any mismatch between `allTablesInvExt` conjuncts and the 16-field
  witness type produces a build error.
- U2-N (U-M17): Added `RegisterFile.not_lawfulBEq` and `TCB.not_lawfulBEq`
  negative `LawfulBEq` instances via counterexample (out-of-range GPR index 32).
- **Audit refinements**: Extended `vspaceInvariantBundle` from 6-conjunct to
  7-conjunct with `canonicalAddressInvariant` (U2-C). Added
  `resolveAsidRootChecked` layered wrapper with ASID bounds guard (U2-H).
  Added `asidBound`/`asidBoundForConfig` constants. Preservation proofs
  updated for map and unmap success paths, default state, and timer/register
  helpers.
- Version bump to 0.21.1. Metrics: 62,154 production LoC, 1,867 theorems.

## [0.21.0] — WS-U Phase U1: Correctness Fixes

- U1-A/B/C (U-H01): Fixed `frozenQueuePopHead` to clear `queuePPrev` field,
  enabling multi-round IPC re-enqueue. Regression test FO-021 validates
  three-phase IPC cycle.
- U1-D/E (U-H02): Added post-allocation page-alignment re-verification in
  `retypeFromUntyped`. Updated `retypeFromUntyped_ok_decompose` theorem.
- U1-F/G (U-H04): Replaced `lifecycleRetypeDirect` with
  `lifecycleRetypeWithCleanup` in API dispatch. Updated doc comments.
- U1-H/I (U-H14): Aligned `lifecycleRetypeAuthority` from `.write` to
  `.retype`, matching `requiredRight` mapping. Updated authority preservation
  and scheduler preservation theorems.
- U1-J/K (U-H13): Changed `endpointReceiveDual` CSpace root fallback from
  silent `senderId.toObjId` to explicit `.invalidCapability` error. Updated
  IPC preservation theorems.
- U1-L (U-H03): Extracted `cspaceDeleteSlotCore` (non-private core) with
  `cspaceDeleteSlot` as thin guard wrapper (`hasCdtChildren` check). Migrated
  6 preservation theorems to core+wrapper pattern across 3 proof files.
  Internal callers (`processRevokeNode`, `cspaceMove`, `cspaceRevokeCdtStrict`)
  use core directly.
- U1-M (U-M39): Added defensive `saveOutgoingContext` in `switchDomain`
  before clearing `current`. Updated scheduler preservation theorems.
- Fixed scenario registry format parser to handle bracket-format fixtures.
- Updated scenario registry and catalog for new trace lines (LEP-006/008/017/
  018/020/024/026/028/030/034, UMT-002/003/004/007, ELC-003/004).
- Version bump to 0.21.0. All documentation and GitBook synchronized.

## [0.20.7] — WS-T Phase T8: Documentation & Closure (WS-T PORTFOLIO COMPLETE)

- T8-A: Synchronized `README.md` metrics from `docs/codebase_map.json` —
  version badge updated to 0.20.7, production LoC 61,538, 1,846 proved
  declarations.
- T8-B: Updated `docs/spec/SELE4N_SPEC.md` with all spec changes from T1–T7:
  frozen IPC queue semantics (§8.8), object well-formedness validation (§8.9),
  checked dispatch and MMIO adapter (§8.10), buildChecked runtime validation
  (§8.11). Metrics updated to current values.
- T8-C: Updated `docs/DEVELOPMENT.md` — WS-T marked PORTFOLIO COMPLETE.
- T8-D: Updated `docs/CLAIM_EVIDENCE_INDEX.md` with WS-T Phase T2–T8 claims:
  CDT access control, Rust ABI hardening, IPC proof closure, lifecycle safety,
  MMIO adapter, checked dispatch, test infrastructure, documentation closure.
- T8-E: Updated `docs/WORKSTREAM_HISTORY.md` with T8 completion summary and
  closure report link. WS-T marked PORTFOLIO COMPLETE (94 sub-tasks, 8 phases).
- T8-F: Verified `docs/codebase_map.json` — up to date (101 files, 1,846
  theorems, source digest current).
- T8-G: Updated 8 GitBook chapters to current metrics:
  - `README.md` — version 0.20.7, 61,538 LoC, 1,846 theorems.
  - `01-project-overview.md` — current LoC and theorem counts.
  - `05-specification-and-roadmap.md` — WS-T COMPLETE section, updated table.
  - `07-testing-and-ci.md` — updated stage context metrics.
  - `12-proof-and-invariant-map.md` — T4–T7 proof additions.
  - `17-project-usage-value.md` — current LoC and theorem counts.
  - `31-claim-vs-evidence-index.md` — WS-T portfolio claim.
- T8-H: Verified `scripts/website_link_manifest.txt` — all 93 protected paths
  present. `check_website_links.sh` passes.
- T8-I/J/K: All test tiers validated (build, smoke, trace, invariant surface).
- T8-L: Zero `sorry`, zero `axiom` in production Lean. 20 `native_decide`
  usages documented (finite enumeration, default state properties, platform
  configuration validation).
- T8-M: This changelog entry.
- T8-N: Produced WS-T closure report
  (`docs/dev_history/audits/WS_T_CLOSURE_REPORT.md`).

**WS-T Portfolio Summary**: 8 phases (T1–T8), 94 sub-tasks, v0.20.0–v0.20.7.
Addressed 72 findings from dual v0.19.6 deep-dive audits (4 HIGH, 52 MEDIUM,
16 selected LOW). All findings resolved. Zero sorry, zero axiom. Next
milestone: WS-U Raspberry Pi 5 hardware binding.

## [0.20.6] — WS-T Phase T7: Test Coverage & Build Infrastructure

- T7-A (S2-F): Migrated all `BootstrapBuilder.build` calls to `buildChecked` in
  MainTraceHarness (10 states) and OperationChainSuite (16 states). Ensures
  runtime structural invariant validation on every test state: no duplicate
  ObjIds, lifecycle type-tag matching, runnable threads reference existing TCBs,
  CNode capacity bounds, current thread in runnable list.
- T7-B (S2-F): Added 7 post-mutation invariant checks to trace harness (24→31
  total): post-vspace-unmap-mutated, post-register-write-mutated,
  post-lifecycle-retype-with-cleanup-mutated, post-ipc-handshake-chain-mutated,
  post-domain-switch-mutated, post-ipc-rendezvous-mutated,
  post-untyped-double-retype-mutated. Updated trace fixture (T7-J).
- T7-D/F (M-FRZ-1/2/3, L-P01): Added 3 frozen IPC queue enqueue tests
  (FO-016/017/018) to FrozenOpsSuite: frozenEndpointSend no-receiver enqueue,
  frozenEndpointReceive no-sender enqueue, frozenEndpointCall no-receiver
  enqueue. Validates `.blockedOnSend`/`.blockedOnReceive`/`.blockedOnCall` state
  and intrusive sendQ/receiveQ head/tail linkage.
- T7-E (L-P02): Added deep CDT cascade test with 4-level derivation tree
  (root→child→grandchild→great-grandchild) across separate CNodes, mid-chain
  `cspaceRevokeCdtStrict` at child level, verifies root preserved and
  descendants removed with `deletedSlots.length == 2`.
- T7-G (M-NEW-12): Hardened pre-commit hook temp file handling — replaced
  PID-based `/tmp/lake-precommit-$.log` with `mktemp` and `trap`-based cleanup.
- T7-H (M-NEW-13): Added SHA-256 verification for Lean toolchain downloads with
  architecture-aware hash selection (x86/ARM × ZST/ZIP) and skip-on-empty.
- T7-I (L-P03): Added Rust ABI test job to CI pipeline — `cargo test --workspace`
  with Cargo registry caching, independent of Lean test tiers.
- T7-K (L-P06/L-P07): Added handleYield empty-queue re-selection test (single
  thread yields and re-selects itself) and IRQ handler dispatch test (register
  handler + notification signal).
- T7-L (L-P08): Added boot sequence integration test using `bootFromPlatform`
  with 4 invariant witness type-checks, object and IRQ handler verification, and
  determinism check.
- T7 Audit Remediation:
  - T7-C (M-TST-4): Added syscall dispatch tests (chains 27–32) exercising full
    `syscallEntry → decode → dispatchWithCap` path for all 14 SyscallId variants:
    cspaceMint, cspaceDelete, cspaceCopy, cspaceMove (chain27), vspaceMap,
    vspaceUnmap (chain28), lifecycleRetype (chain29), serviceRegister,
    serviceQuery, serviceRevoke (chain30), reply (chain31), call (chain32).
  - T7-D (M-FRZ-4/5): Added FO-019 `frozenSchedule` (highest-priority thread
    selection) and FO-020 `frozenCspaceMint` (capability insertion into frozen
    CNode) tests to FrozenOpsSuite.
  - T7-E (L-P02): Extended chain23 with root-level revocation (4-level tree,
    `cspaceRevokeCdtStrict` at root, `deletedSlots == 3`) and mid-tree
    revoke+delete (`cspaceRevokeCdtStrict` at grandchild cascading
    great-grandchild removal, then `cspaceDeleteSlot` for the grandchild).
  - T7-K (L-P06): Added empty-queue edge case to chain24 — `handleYield` with
    `current = none` and empty run queue returns `.ok` with `current = none`.
  - T7-L (L-P08): Strengthened chain26 — explicit access to all 4
    `IntermediateState` invariant witness fields (`hAllTables`,
    `hPerObjectSlots`, `hPerObjectMappings`, `hLifecycleConsistent`).
  - Added `decodeVSpaceMapArgs_error_iff` theorem to SyscallArgDecode (Tier 3
    invariant surface anchor).

## [0.20.5] — WS-T Phase T6: Architecture & Hardware Preparation

- T6-A/B (M-NEW-6): Changed `vspaceMapPage` default permissions from `default`
  to explicit `PagePermissions.readOnly`. Enforces least-privilege: callers must
  explicitly request write or execute permissions. All callers audited.
- T6-C/D (M-ARCH-1): Changed `VSpaceMapArgs.perms` from raw `Nat` to typed
  `PagePermissions` with decode-time validation via `PagePermissions.ofNat?`.
  Values ≥ 32 (undefined permission bits) now rejected at the ABI boundary
  with `policyDenied` error. Round-trip proof updated for all 32 valid values.
- T6-E/H (M-NEW-7, M-NEW-8): Defined MMIO adapter operations in new file
  `Platform/RPi5/MmioAdapter.lean`: `mmioRead`/`mmioWrite` with device-region
  validation, `MemoryBarrier` inductive (DMB, DSB, ISB), `MmioOp` with barrier
  annotations. 4 correctness theorems (reject non-device, read preserves state,
  write frame).
- T6-F (M-NEW-7): Extended RPi5 runtime contract with `mmioAccessAllowed`
  predicate gating MMIO on device-region membership. Proven kind-disjoint from
  RAM access predicate.
- T6-G (M-NEW-8): Documented cache coherency assumptions in
  `docs/spec/SELE4N_SPEC.md` §6.3: single-core eliminates most coherency,
  MMIO requires barriers, DMA out of scope.
- T6-I (M-IF-1): Wired information-flow-checked dispatch into API. Created
  `dispatchWithCapChecked`, `dispatchSyscallChecked`, `syscallEntryChecked` —
  all 7 policy-gated operations now use `securityFlowsTo` wrappers at runtime.
  Coverage: endpointSend/Receive/Call (inline check), cspaceMint/Copy/Move,
  registerService.
- T6-J (M-IF-1): Added checked dispatch enforcement coverage witness —
  7 policy-gated operations documented and verified complete.
- T6-K (H-3): Defined `RegisterWriteInvariant` predicate for context-switch
  awareness. Stub for WS-U — current TCB model lacks saved registers field.
- T6-L (M-ARCH-4): Added targeted TLB flush operations: `tlbFlushByASID`,
  `tlbFlushByPage`, `tlbFlushByASIDPage` (alias), `tlbFlushAll`. State frame
  proofs for per-ASID and per-page flushes. `tlbFlushAll` marked as
  conservative fallback.
- T6-M (M-ARCH-2): Implemented DTB parsing foundation: `FdtHeader` structure,
  `readBE32` big-endian reader, `parseFdtHeader`, `FdtHeader.isValid`,
  `parseAndValidateFdtHeader`. Proof: empty blob has no valid header.
- Updated `VSpaceMapArgs` delegation theorem to use typed permissions.
- T6 audit fix (T6-I): Documented `syscallEntryChecked` as production entry
  point in API stability table. Added bridging documentation theorem. Updated
  `dispatchSyscall` docstring to clarify unchecked vs checked paths.
- T6 audit fix (T6-J): Replaced trivial `rfl` witness with substantive
  `checkedDispatch_flowDenied_preserves_state` theorem — proves all 3 original
  policy-gated wrappers preserve state on flow denial. Composes existing
  `*_denied_preserves_state` proofs into a single bundle.
- T6 audit fix (T6-M): Added FDT structure block constants, `FdtMemoryRegion`
  type, `readBE64` big-endian 64-bit reader, `extractMemoryRegions` with fuel-
  bounded iteration, `classifyMemoryRegion` (RAM kind for /memory entries),
  `fdtRegionsToMemoryRegions` converter, `DeviceTree.fromDtbWithRegions`
  producing `Option DeviceTree` with populated memory map. Empty-regions
  theorem proves empty input produces empty output.
- Zero sorry, zero axiom. All 13 sub-tasks complete.

## [0.20.4] — WS-T Phase T5: Lifecycle, Service & Cross-Subsystem

- T5-A/B (M-NEW-4): Marked `lifecycleRetypeObject` and `lifecycleRetypeDirect` as
  internal building blocks with safety annotations. External callers must use
  `lifecycleRetypeWithCleanup` for H-05 and S6-C guarantees.
- T5-C (M-NEW-5): Defined `KernelObject.wellFormed` predicate parameterized by the
  object store. TCBs require valid cspaceRoot/vspaceRoot, CNodes require guardBounded.
  Decidable instance enables runtime validation.
- T5-D (M-NEW-5): Added `wellFormed` validation in `lifecycleRetypeWithCleanup`.
  Returns `illegalState` for ill-formed objects (defense-in-depth).
- T5-E (M-LCS-1): Fixed intrusive queue cleanup for mid-queue nodes.
  `spliceOutMidQueueNode` patches predecessor's `queueNext` and successor's
  `queuePrev` to splice out the deleted TCB. Three preservation theorems
  (scheduler, lifecycle, serviceRegistry) proven via field-independence lemma.
- T5-F (L-NEW-1): `cleanupEndpointServiceRegistrations` now calls
  `removeDependenciesOf` for each removed service, preventing orphaned
  dependency edges in the service graph.
- T5-G (L-NEW-2): Proved `cleanupEndpointServiceRegistrations_preserves_registryEndpointValid`
  using `RHTable.filter_get_subset` to show surviving registrations have valid endpoints.
- T5-H (L-NEW-3): Defined `noStaleNotificationWaitReferences` predicate: every
  ThreadId in a notification's `waitingThreads` must reference an existing TCB.
- T5-I (M-CS-1): Extended `noStaleEndpointQueueReferences` to check interior
  queue members via bounded `collectQueueMembers` traversal, not just head/tail.
- T5-J (L-NEW-3): Added `noStaleNotificationWaitReferences` to
  `crossSubsystemInvariant` (now 4-tuple). Updated default state proof,
  predicates list (count 3→4), folded composition, and architecture invariant.
- T5-K (M-LCS-2): Documented `lookupServiceByCap` first-match semantics.
- T5-L (M-MOD-6): Documented `Notification.waitingThreads` LIFO semantics.
- T5-M (M-SCH-3): Defined `threadPriority_membership_consistent` predicate
  formalizing the bidirectional consistency between RunQueue's `threadPriority`
  and `membership` fields. Proved empty-state satisfaction and derivation of
  `runQueueThreadPriorityConsistent` from the new predicate.
- T5-A/B audit fix: Added `@[deprecated]` annotations to `lifecycleRetypeObject` and
  `lifecycleRetypeDirect`, enforcing compile-time deprecation warnings for callers
  that bypass `lifecycleRetypeWithCleanup`.
- T5-E audit fix: Fixed `spliceOutMidQueueNode` to read successor TCB from the
  already-patched `objs` table instead of the original `st.objects`. This prevents
  data corruption in circular queue scenarios (prevTid == nextTid).
- T5-M audit fix: Added `threadPriority_membership_consistent_insert` and
  `threadPriority_membership_consistent_remove` preservation theorems, fully
  closing the M-SCH-3 gap. The consistency predicate is now proven preserved
  across all RunQueue mutation operations.
- Zero sorry, zero axiom. 1,824 proved declarations (+12 from v0.20.3).

## [0.20.3] — WS-T Phase T4: IPC & Capability Proof Closure

- T4-A (M-IPC-1): Proved `endpointCall_preserves_ipcStateQueueConsistent`. The call
  operation's handshake path (PopHead → storeTcbIpcStateAndMessage → ensureRunnable →
  storeTcbIpcState → removeRunnable) and blocking path (Enqueue → storeTcb... →
  removeRunnable) both preserve the ipcState-queue consistency invariant.
- T4-B (M-IPC-1): Proved `endpointReplyRecv_preserves_ipcStateQueueConsistent`. The
  reply phase (storeTcbIpcStateAndMessage → ensureRunnable) and receive phase
  (endpointReceiveDual) compose to preserve the invariant.
- T4-C (M-IPC-1): Proved `notificationSignal_preserves_ipcStateQueueConsistent` and
  `notificationWait_preserves_ipcStateQueueConsistent`. Added helper
  `storeObject_notification_preserves_ipcStateQueueConsistent` for notification store
  operations. Notification operations set ipcState to `.ready` or
  `.blockedOnNotification`, neither of which requires endpoint existence.
- T4-E (M-IPC-3): Proved `endpointSendDualWithCaps_preserves_ipcInvariantFull`,
  `endpointReceiveDualWithCaps_preserves_ipcInvariantFull`, and
  `endpointCallWithCaps_preserves_ipcInvariantFull`. WithCaps wrappers compose
  base ipcInvariant preservation with caller-supplied dualQueue/bounded/badge proofs.
- T4-F (M-IPC-3): All three WithCaps operations covered in T4-E above.
- T4-G (M-CAP-2): Proved `descendantsOf_fuel_sufficiency` and 8 supporting BFS
  lemmas (go_cons, go_nil, go_acc_subset, go_children_found, children_subset,
  go_fuel_mono, go_head_children_found, fuel_bound). Direct children of any CDT
  node are included in the BFS result, providing the foundation for revocation
  completeness.
- T4-H (M-CAP-1): Documented `cspaceMutate` badge override CDT tracking design.
  Badge mutation via Mutate intentionally not tracked in CDT, matching seL4
  CNode_Mutate semantics.
- T4-D (M-IPC-2): Proved `endpointQueueRemoveDual_preserves_dualQueueSystemInvariant`
  — complete sorry-free proof (1023 lines) covering all 4 paths: endpointHead
  queueNext=none (Path A), endpointHead queueNext=some (Path B), tcbNext
  queueNext=none (Path C, tail removal), tcbNext queueNext=some (Path D,
  mid-queue removal). Added `tcbQueueChainAcyclic` invariant to
  `dualQueueSystemInvariant`. Path D handles 3 simultaneously modified TCBs
  (tid cleared, prevTid.next→nextTid, nextTid.prev→prevTid) with full 4-way
  case analysis in both forward and reverse link integrity directions.
- T4-I (M-DS-3): Proved `buildCNodeRadix_lookup_equiv` — bidirectional lookup
  equivalence between RHTable and CNodeRadix after construction. The proof uses
  3 private fold lemmas (foldl_preserves_none, foldl_preserves_some,
  foldl_establishes_some) with list induction over the hash table's slot array.
- T4-J (M-IF-3): Documented NI complex IPC projection hypothesis rationale.
  The externalized projection hypothesis is unavoidable without concrete
  MemoryDomainOwnership; discharged when platform binding provides ownership.
- T4-K (L-P10): Added `ipcInvariantFull_compositional` convenience theorem that
  takes all 4 component proofs and produces the full bundle.
- T4-L (M-SCH-1): Proved `insert_maxPriority_consistency` — after RunQueue insert,
  maxPriority is max(old, prio) by definitional unfolding.
- Version bumped to 0.20.3 across lakefile.toml, Cargo.toml, README badge,
  codebase_map.json.
- Zero sorry/axiom. All test tiers pass.

## [0.20.2] — WS-T Phase T3: Rust ABI Hardening

- T3-A (M-NEW-9): Changed `MessageInfo::encode()` return type from `u64` to
  `Result<u64, KernelError>`. Labels >= 2^55 now return `InvalidMessageInfo`
  instead of silently truncating. Added `MAX_LABEL` constant. Updated
  `MessageInfo::new()` to also reject oversized labels. Propagated Result
  through `encode_syscall()` and `invoke_syscall()`. Closes M-NEW-9.
- T3-B (M-NEW-9): Added MessageInfo label boundary conformance tests: roundtrip
  at 0 and 2^55-1, error at 2^55 and u64::MAX. Added `encode_syscall` rejection
  test for oversized labels.
- T3-C (M-NEW-10): Changed `VSpaceMapArgs.perms` field from raw `u64` to typed
  `PagePerms`. Decode now validates via `PagePerms::try_from()`, rejecting values
  > 0x1F at the ABI boundary. Closes M-NEW-10.
- T3-D (M-NEW-10): Added VSpaceMapArgs perms roundtrip conformance tests for all
  32 valid values (0x00–0x1F) and rejection tests for 0x20, 0xFF, u64::MAX.
- T3-E (M-NEW-11): Changed `ServiceRegisterArgs` `requires_grant` decode from
  permissive `regs[4] != 0` to strict `match regs[4] { 0 => false, 1 => true,
  _ => error }`. Corrupted register contents no longer silently accepted as
  `true`. Closes M-NEW-11.
- T3-F (M-NEW-11): Added ServiceRegisterArgs strict bool conformance tests:
  0 → false, 1 → true, 2 and u64::MAX → rejected.
- T3-G: Verified `#![deny(unsafe_code)]` crate-level attribute already present
  in `sele4n-abi/src/lib.rs` (added in WS-S S1-H). Three targeted
  `#[allow(unsafe_code)]` annotations in `trap.rs`: both `raw_syscall` variants
  (aarch64 and mock) and `invoke_syscall` (calls unsafe `raw_syscall`). No
  additional changes needed.
- T3-H: All Rust tests pass — 119 tests across 4 crates (50 sele4n-abi unit,
  32 conformance, 12 sele4n-sys, 25 sele4n-types). Zero failures.
- Version bumped to 0.20.2 across lakefile.toml, Cargo.toml workspace, README
  badge, codebase_map.json, SELE4N_SPEC.md, gitbook, and i18n READMEs.
- Zero sorry/axiom. Full `test_full.sh` passes. All Rust tests pass.

## [0.20.1] — WS-T Phase T2: Model & CDT Integrity

- T2-A (H-1): Added `AccessRightSet.ofList_valid` theorem proving that `ofList`
  always produces a valid rights set (bits < 2^5). Closes HIGH finding H-1.
- T2-B (H-2): Made `CapDerivationTree` constructor `private` via `private mk ::`
  syntax. External code can no longer construct CDT values with inconsistent
  `edges`/`childMap`/`parentMap` fields. Closes HIGH finding H-2.
- T2-C (H-2): Added `CapDerivationTree.mk_checked` smart constructor requiring
  `cdtMapsConsistent` witness. Added `mk_checked_cdtMapsConsistent` proof.
- T2-D (M-NEW-1): Added `tlb : TlbState` field to `FrozenSystemState` structure.
  TLB state is no longer dropped during freeze.
- T2-E (M-NEW-1): Updated `freeze` function to transfer `TlbState` from
  `IntermediateState` to `FrozenSystemState`. Updated test fixtures.
- T2-F (M-NEW-1): Added `freeze_preserves_tlb` correctness theorem. Closes
  MEDIUM finding M-NEW-1.
- T2-G (M-NEW-2): Added bundled `storeObject_preserves_allTablesInvExt` theorem
  composing 16+ component preservation proofs into a single caller-friendly API.
- T2-H (M-NEW-3): Added `capabilityRefs_filter_preserves_invExt` proof showing
  that `RHTable.filter` on capabilityRefs preserves `invExt`.
- T2-I (M-NEW-3): Added `capabilityRefs_fold_preserves_invExt` proof showing
  that sequential `insert` via `fold` preserves `invExt`. Closes M-NEW-3.
- T2-J (L-NEW-4): Added `CNode.guardBounded` predicate (`guardValue < 2^guardWidth`)
  and integrated into `CNode.wellFormed`. Added `empty_guardBounded` proof.
  Added `resolveSlot_guardMismatch_of_not_guardBounded` theorem proving that
  `resolveSlot` always returns `guardMismatch` when `guardValue ≥ 2^guardWidth`.
  Updated `cspaceDepthConsistent_of_storeObject_sameCNode` to propagate
  guardValue equality. Closes L-NEW-4.
- T2-K (M-BLD-1): Fixed `Builder.createObject` to update `objectIndex` and
  `objectIndexSet` alongside object store insertion. Previously boot objects
  were not registered in the index. Closes M-BLD-1.
- T2-L (M-ST-2): Added comprehensive inline documentation to `attachSlotToCdtNode`
  explaining why the stale-link cleanup ordering is correct. Closes M-ST-2.
- Zero sorry/axiom, full build passes (174 modules), all tests pass.

## [0.19.6] — WS-S Phase S7: Documentation & Polish

- S7-A: Synchronized `README.md` metrics from `docs/codebase_map.json` — version
  0.19.6, 100 production files, 57,506 production LoC, 1,756 proved declarations.
- S7-B: Updated `docs/spec/SELE4N_SPEC.md` with all spec changes from S1–S6:
  trust boundary documentation, alignment requirements, memory scrubbing,
  timeout semantics, capacity enforcement, typed IPC registers.
- S7-C: Updated `docs/DEVELOPMENT.md` with new testing practices (structural
  assertions, golden-output fixture management, Builder-based test states,
  SimRestrictive platform variant).
- S7-D: Updated `docs/CLAIM_EVIDENCE_INDEX.md` with new claims from WS-S:
  CDT maps consistency, RunQueue well-formedness, memory scrubbing, page
  alignment, object capacity enforcement, SecurityLabel lattice properties.
- S7-E: Updated `docs/WORKSTREAM_HISTORY.md` with WS-S completion summary
  (7 phases, 83 sub-tasks, version range v0.19.0–v0.19.6). WS-S marked
  PORTFOLIO COMPLETE.
- S7-F: Regenerated `docs/codebase_map.json` — 110 modules, 3,242 declarations,
  1,756 proved theorem/lemma declarations.
- S7-G: Updated affected GitBook chapters (project overview, specification,
  testing, proof map, codebase reference) to mirror canonical doc changes.
- S7-H: Verified `scripts/website_link_manifest.txt` — all protected paths exist.
- S7-M: Updated `CHANGELOG.md` with WS-S v0.19.0–v0.19.6 release notes.
- S7-N: Produced WS-S closure report (`docs/dev_history/audits/WS_S_CLOSURE_REPORT.md`)
  summarizing all remediated findings, test results, and residual items.
- Version bumped to 0.19.6 in `lakefile.toml`.
- Zero sorry/axiom, all tests pass.

## [0.19.5] — WS-S Phase S6: Hardware Preparation

- S6-A (U-M18): Migrated API dispatch to `WithFlush` VSpace variants
  (`vspaceMapPageCheckedWithFlush`, `vspaceUnmapPageWithFlush`). Trace harness
  updated to use flushing variants on all production paths.
- S6-B (U-M18): Documented unflushed `vspaceMapPage`/`vspaceUnmapPage` as
  internal proof decomposition helpers with clear warnings against direct use.
- S6-C (U-M19): Added memory scrubbing (`zeroMemoryRange`, `scrubObjectMemory`)
  to `lifecycleRetypeWithCleanup`. `Machine.lean` gets `zeroMemoryRange` primitive
  and `memoryZeroed` postcondition predicate.
- S6-D (U-M19): Proved `scrubObjectMemory` preserves lifecycle invariants
  (trivially — only modifies `machine.memory`, not kernel state structures).
- S6-E (U-M19): Proved `scrubObjectMemory` preserves NI (`lowEquivalent`) for
  non-observable targets — scrubbing memory outside an observer's domain does
  not affect their projected state.
- S6-F (U-M20): Created `Platform/DeviceTree.lean` abstraction with `DeviceTree`
  structure. RPi5 `Board.lean` constructs `rpi5DeviceTree`.
- S6-G: Validated all BCM2712 address constants against datasheet. Added
  comprehensive validation table to `Board.lean`.
- Zero sorry/axiom, all tests pass.

## [0.19.4] — WS-S Phase S5: API Cleanup, Platform Hardening & Lifecycle Fidelity

- S5-A (U-M05b): Removed 14 deprecated `api*` wrappers from `API.lean`.
  Production path: `syscallEntry` -> `dispatchSyscall` -> `syscallInvoke` ->
  `dispatchWithCap`.
- S5-B: Audited invariant files — zero references to removed wrappers.
- S5-D (U-M18): Created `SimRestrictive` platform variant with substantive
  contracts (`simRuntimeContractSubstantive`): timer monotonicity, 256 MiB RAM
  memory bound, register writes denied. `SimRestrictivePlatform` binding and
  substantive proof hooks.
- S5-E: Added `SimRestrictive` build check to `test_smoke.sh`.
- S5-F (U-M19): BCM2712 address validation checklist in `Platform/RPi5/Board.lean`;
  pre-hardware-binding gate in `DEVELOPMENT.md`.
- S5-G/S5-H (U-M20/U-M21): Page-alignment check in `retypeFromUntyped` for
  VSpace roots and CNodes — `requiresPageAlignment`, `allocationBasePageAligned`,
  `allocationMisaligned` error variant. All lifecycle invariant preservation
  proofs updated.
- S5-I (U-M22): EDF tie-breaking FIFO semantics documented at `chooseThread`.
- S5-J (U-M23b): Complexity documentation for `TlbState` operations (O(n)),
  `RunQueue.remove` (O(k+n)), `RunQueue.rotateHead` (O(k+n)).
- Zero sorry/axiom, all tests pass.

## [0.19.3] — WS-S Phase S4: Model Fidelity & Type Safety

- S4-A (U-M04): Added `objectIndexBounded` advisory predicate with RPi5 growth
  analysis (512 KB at maxObjects=65536). Added spec section 8 documenting
  object capacity bounds, word-boundedness invariants, alignment model gap,
  and IPC timeout semantics.
- S4-B (U-M12): Added capacity enforcement to `retypeFromUntyped` — returns
  `objectStoreCapacityExceeded` when object count reaches `maxObjects` (65536).
  Added `objectStoreCapacityExceeded` and `invalidCapPtr` to `KernelError`.
- S4-C (U-L02): `CNode.resolveSlot` now masks CPtr to 64 bits (`% machineWordMax`)
  before guard extraction. Added `resolveSlot_mask_idempotent` theorem proving
  the mask is identity for already-bounded values.
- S4-D (U-L04): Changed `IpcMessage.registers` from `Array Nat` to
  `Array RegValue`. Updated `extractMessageRegisters` to return `Array RegValue`
  directly (removed `.map RegValue.val`). Updated all 40+ construction sites
  and 9 display sites across kernel, test, and harness files.
- S4-E (U-M15): Added `wordAligned`/`pageAligned` predicates and
  `alignedRead`/`alignedWrite` advisory predicates to Machine.lean.
  Proved `pageAligned_implies_wordAligned`, `wordAligned_zero`, `pageAligned_zero`.
- S4-F (U-L01): Evaluated `RegisterFile.gpr : RegName → RegValue` Array
  migration — rejected due to ~50 additional proof obligations. Documented
  design rationale in Machine.lean.
- S4-G (U-L06): Evaluated `Notification.waitingThreads` intrusive queue
  migration — rejected (low cardinality, no ordering requirement, O(n) bounded
  by ≤8 waiters). Documented analysis in Types.lean.
- S4-H (U-L07): Documented `UntypedObject.allocate` prepend convention.
- S4-I (U-L08): Simplified `SyscallId.toNat_ofNat` proof with collapsed match
  arms. Documented tactic evaluation for case-enumeration automation.
- S4-J (U-M27): Audited all `objects` iteration sites — confirmed order-
  independence. Documented audit results at `SystemState.objects` field.
- S4-K (U-M17): Changed `decodeCapPtr` to check `isWord64` bounds. Returns
  `invalidCapPtr` for out-of-range values. Updated roundtrip proof with
  `isWord64` precondition. Added `decodeCapPtr_ok_iff` and
  `decodeCapPtr_ok_of_word64` theorems.
- S4-L (U-M23): Documented `cspaceRevoke` O(n) and `cspaceRevokeCdt`
  O(maxObjects) CDT traversal complexity.
- S4-M (U-M24): Documented `endpointCall` timeout absence — matches seL4's
  design where timeout monitoring is scheduler/fault-handler responsibility.
- Zero sorry/axiom, all tests pass.

## [0.19.0] — WS-S Phase S1: Security Boundary & Rust Type Safety

- Begin WS-S workstream (Pre-Benchmark Strengthening), addressing findings from
  two comprehensive v0.18.7 audits (115+ combined findings).
- S1-A (U-H1): Removed deprecated `Badge.ofNat` — zero callers remained after
  WS-R6 migration. All badge construction uses `Badge.ofNatMasked`.
- S1-B (U-H2): Converted `MemoryRegion.wellFormed` from `Bool` to `Prop` with
  `Decidable` instance for decide/native_decide compatibility.
- S1-C (U-H3): Documented `ThreadId.toObjId` identity mapping trust boundary.
- S1-D/E (U-M01): Converted `Cap::restrict()` and `Cap::to_read_only()` from
  panic to `Result<_, CapError>` with new `CapError` error type.
- S1-F (U-M02): Fixed `Restricted::RIGHTS` semantic bug — `restricted_rights`
  field in `Cap` struct now stores actual runtime rights.
- S1-G (U-L05): Added `AccessRightSet.valid` predicate (bits < 2^5), `ofNat`
  masked constructor with validity proof and idempotence theorem.
- S1-H (U-L09): Added `#![deny(unsafe_code)]` to `sele4n-abi` with targeted
  `#[allow(unsafe_code)]` on the single `raw_syscall` function.
- S1-I (U-M30): Migrated 9 `isPowerOfTwo` proofs from `native_decide` to
  `decide`, eliminating TCB dependency on compiled Lean code.
- S1-J (U-M14): Documented `BEq RegisterFile` non-lawfulness, added
  `RegisterFile.ext` extensionality lemma.
- S1-K (U-M16): Added `MonadStateOf` and `MonadExceptOf` instances for `KernelM`.
- S1-M (U-M22): Documented badge-forging implications of Mint right.
- S1-N (U-M13): Documented `machineWordBounded` complete coverage.
- Zero sorry/axiom, all tests pass.

## [0.19.1] — WS-S Phase S2: Test Hardening

- S2-A/B/C (U-H4): Replaced all 101 `reprStr` occurrences across 4 test files
  with `toString` for display. Added blanket `ToString` from `Repr` instance in
  State.lean. **Determinism checks converted to structural `==` via new `BEq Except`
  instance** — eliminates all string-based comparison in test assertions.
- S2-D (U-H5): Documented golden-output fixture management in DEVELOPMENT.md.
- S2-E (U-H5): Enhanced trace fixture diff reporting in test_tier2_trace.sh.
- S2-F (U-L11): Enhanced `BootstrapBuilder.buildValidated` with 8 runtime
  invariant checks. Added `buildChecked` drop-in for `build` that panics on
  violation. Primary test states (`baseState`, `f2UntypedState`, `f2DeviceState`)
  migrated to `buildChecked`.
- S2-G (U-L12): Added 6 capability error-path tests: rights attenuation failure,
  copy/mint to occupied slot, empty revoke report, **copy to full CNode**, and
  **deep CDT chain revocation** (5-deep, exercises multi-level traversal).
- S2-H (U-L12): Added 5 lifecycle error-path tests: allocSize too small, device
  untyped TCB rejection, non-untyped source, **region exhaustion** (watermark at
  capacity), **child ID collision**.
- S2-I (U-L13): Created `SeLe4n/Testing/Helpers.lean` shared module with
  `expectCond`, `expectError`, `expectOk` helpers. Updated InformationFlowSuite
  to use shared helpers. Added `MainTraceHarness` import for library build
  reachability.
- S2-J (U-M05): Migrated all deprecated `api*` wrapper calls in MainTraceHarness
  to direct `syscallInvoke` path. Removed `set_option linter.deprecated false`.
- Zero sorry/axiom, all tests pass.

## [0.19.2] — WS-S Phase S3 (partial): Proof Surface Closure

- S3-A (U-M03): Defined `cdtMapsConsistent` invariant with empty-CDT proof.
- S3-C (U-L03): Defined `removeEdge` for `CapDerivationTree`.
- S3-K (U-M28): Added `RHTable.loadFactorBounded` predicate documenting 75%
  load factor threshold.
- S4-A (U-M04): Added `objectIndexBounded` advisory predicate with growth analysis.
- Documentation updates across spec, gitbook, workstream history.
- Zero sorry/axiom, all tests pass.

## [0.18.7] — WS-R8 Infrastructure & CI Hardening

- Completed Phase 8 (WS-R8) of the Comprehensive Audit Remediation workstream.
- R8-A (I-M01): Elan binary download pinned to versioned URL (`v4.2.1`) with
  SHA-256 hash verification for both x86_64 and aarch64. Replaces
  `/releases/latest/` in the primary download path (`setup_lean_env.sh`).
  SHA mismatch now logs a diagnostic warning instead of being silently swallowed.
- R8-B (I-M02): `codebase_map_sync.yml` converted from auto-push to PR-based
  workflow. Changes proposed via `gh pr create` with review required before merge.
- R8-C (I-M03): Rust test skip now explicit — `::warning::` CI annotation when
  cargo unavailable. Cargo exit codes properly propagated via conditional checks.
- R8-D (I-M04): 4 compiled-but-never-run test suites (`radix_tree_suite`,
  `frozen_state_suite`, `freeze_proof_suite`, `frozen_ops_suite`) now execute
  in Tier 2 negative tests (64 scenarios, 171 individual checks).
- R8-E (L-11): 14 Rust newtype identifier inner fields changed from `pub` to
  `pub(crate)` with `.raw()` accessor methods. `AccessRights` and `PagePerms`
  also encapsulated. All cross-crate consumers updated to use `.raw()`/`::from()`.
  All 99 Rust tests pass (44 abi + 22 types + 8 sys unit + 25 conformance).
- Zero sorry/axiom, all test tiers pass.
- Version bump: v0.18.6 → v0.18.7

## [0.18.6] — WS-R7 Architecture & Hardware Preparation

- Completed Phase 7 (WS-R7) of the Comprehensive Audit Remediation workstream.
- R7-A (M-17): TLB flush enforcement — `TlbState` integrated into `SystemState`,
  `tlbConsistent` added to `proofLayerInvariantBundle` (9th conjunct).
  `vspaceMapPageWithFlush`/`vspaceUnmapPageWithFlush` compose page-table ops with
  full TLB flush. 3 preservation theorems + frame lemma for non-VSpace ops.
- R7-B (L-02): ARM64 register bounds — `RegName.isValid` predicate, `arm64GPRCount`
  constant (32 GPRs), `registerFileGPRCount` tied to `arm64GPRCount`.
- R7-C (L-03): 64-bit value bounds — `isWord64` predicate, `RegValue.valid`,
  `VAddr.valid`, `PAddr.valid`, `machineWordBounded` machine-state invariant with
  default-state proof.
- R7-D (L-06): TCB seL4 fidelity — `faultHandler : Option CPtr` and
  `boundNotification : Option ObjId` fields added with `none` defaults.
- R7-E (L-10): Typed retype arguments — `KernelObjectType.toNat`/`ofNat?` with
  round-trip proof and injectivity theorem. `LifecycleRetypeArgs.newType` typed as
  `KernelObjectType`. `objectOfKernelType` total constructor. Decode boundary
  validates type tags via `ofNat?`. Dispatch uses `objectOfKernelType`.
- Zero sorry/axiom, all test tiers pass.
- Version bump: v0.18.5 → v0.18.6

## [0.18.5] — WS-R6 Model & Frozen State Correctness

- Completed Phase 6 (WS-R6) of the Comprehensive Audit Remediation workstream.
- R6-A: `apiInvariantBundle_frozenDirect` freeze-time equivalence theorem.
- R6-B: Badge deprecation — old `badgeValue` usages cleaned up.
- R6-C: `RegisterFile` structural `BEq` instance for equality comparison.
- R6-D: `schedulerPriorityMatch` preservation proofs for all scheduler ops,
  all sorry eliminated.
- R6-E: Documentation, proof map, and gitbook updated.
- Zero sorry/axiom, all test tiers pass.
- Version bump: v0.18.4 → v0.18.5

## [0.18.4] — WS-R5 Information Flow Completion

- Completed Phase 5 (WS-R5) of the Comprehensive Audit Remediation workstream.
- Internalized IPC non-interference proofs.
- Service NI composition proofs.
- Content-aware memory projection.
- Zero sorry/axiom, all test tiers pass.
- Version bump: v0.18.3 → v0.18.4

## [0.18.3] — WS-R4 Lifecycle & Service Coherence

- Completed Phase 4 (WS-R4) of the Comprehensive Audit Remediation workstream.
- R4-A (M-12): TCB cleanup now removes TCB from endpoint queues and notification
  wait lists via `cleanupTcbReferences`.
- R4-B (M-13): Retyping an endpoint auto-revokes registered services.
- R4-C (M-14): `registerService` requires Write right and endpoint type
  verification (L-09).
- R4-D (M-15): `revokeService` cleans dependency graph via `removeDependenciesOf`.
- R4-E: Cross-subsystem invariant bundle (`crossSubsystemInvariant`) added to
  `proofLayerInvariantBundle`.
- Zero sorry/axiom, all test tiers pass.
- Version bump: v0.18.2 → v0.18.3

## [0.18.2] — WS-R3 IPC Invariant Completion

- Completed Phase 3 (WS-R3) of the Comprehensive Audit Remediation workstream.
- R3-A (M-16): Fixed `notificationSignal` badge delivery — woken thread now
  receives signaled badge via `storeTcbIpcStateAndMessage`.
- R3-B (M-18): Internalized `ipcInvariantFull` preservation hypotheses —
  notification operations and `endpointReply` now have self-contained proofs.
- R3-C (M-19): Completed `notificationWaiterConsistent` preservation chain —
  `notificationSignal`, frame lemma, `endpointReply` preservation theorems.
- Removed `set_option linter.all false` from Structural.lean (L-08).
- Zero sorry/axiom, all test tiers pass.
- Version bump: v0.18.1 → v0.18.2

## [0.18.1] — WS-R2 Capability & CDT Hardening

- Completed Phase 2 (WS-R2) of the Comprehensive Audit Remediation workstream.
- R2-A (M-06): Fixed `processRevokeNode` error swallowing — revocation now
  propagates `cspaceDeleteSlot` errors.
- R2-B (M-05): Fixed `streamingRevokeBFS` fuel exhaustion — returns
  `.error .resourceExhausted` instead of `.ok`. Added `resourceExhausted`
  to `KernelError`.
- R2-C (M-08): Added `isAncestor` decidable predicate for CDT cycle detection.
- Updated all preservation proofs for new `Except` return types.
- Zero sorry/axiom, all test tiers pass.
- Version bump: v0.18.0 → v0.18.1

## [0.18.0] — WS-R1 Pre-Release Blockers

- Completed Phase 1 (WS-R1) of the Comprehensive Audit Remediation workstream:
  eliminated all findings that enable privilege escalation or silent security
  failures in the public API surface.
- R1-A (H-01): Removed `Cap::downgrade()` — replaced with `to_read_only()` and
  `restrict()` with runtime subset assertions. `to_read_only()` validates READ is
  present in current rights (panics on `Restricted` caps). Prevents phantom-typed
  capability escalation in Rust library.
- R1-B (R-M01, R-M02): Added bounds validation to `CSpaceMintArgs::decode()`
  (rejects rights > 0x1F) and `PagePerms::TryFrom<u64>` (replaces silent-truncation
  `From<u64>`). 6 regression tests for boundary values.
- R1-C (R-M03): Refactored `SyscallResponse` to use `x1_raw` field with typed
  accessors `badge()` and `msg_info()`. Eliminates semantic overlap between badge
  and message info interpretations of x1 register.
- R1-D (M-04): Added capability-target validation guards to all 14 `api*`
  convenience wrappers. IPC/CSpace wrappers verify `cap.target` matches the
  supplied target ID. Lifecycle/VSpace/Service wrappers verify `cap.target` is
  an `.object` variant (rejecting reply caps). All wrappers deprecated in favor
  of `syscallEntry`/`dispatchWithCap`.
- R1-E (M-10, M-11): Changed `frozenSaveOutgoingContext` and
  `frozenRestoreIncomingContext` return types from `FrozenSystemState` to
  `Except KernelError FrozenSystemState`. Silent register discard/wrong-context
  paths now return explicit errors. Added preservation theorems for new error paths.
- R1-F: Updated all callers in FrozenOps/Operations.lean, test suites, doc links.
  Fixed 30 broken documentation links to dev_history/ files. Regenerated
  codebase_map.json.
- All test tiers pass (0-3), zero sorry/axiom, clean build with zero warnings

## [0.17.14] — WS-Q9 Integration Testing + Documentation

- Completed Phase 9 (WS-Q9) of the Kernel State Architecture workstream:
  Comprehensive integration testing for the two-phase architecture + full
  documentation sync. **WS-Q portfolio is now COMPLETE** (all 9 phases).
- Q9-A: `TwoPhaseArchSuite.lean` — 14 integration tests (41 checks) covering
  the full builder→freeze→execution pipeline: TPH-001 (builder pipeline),
  TPH-003 (freeze populated + lookup equivalence), TPH-005 (frozen IPC
  send/receive/call), TPH-006 (frozen scheduler tick with preemption),
  TPH-010 (commutativity property), TPH-012 (pre-allocated slot retype),
  TPH-014 (RunQueue frozen operations: schedule/yield/no-eligible)
- Q9-B: Verified Rust conformance XVAL-001..019 (25 tests in conformance.rs)
- Q9-C: Verified service interface SRG-001..010 in MainTraceHarness
- Q9-D: Full documentation sync across 15+ files: WORKSTREAM_HISTORY.md,
  SELE4N_SPEC.md, DEVELOPMENT.md, CLAIM_EVIDENCE_INDEX.md, README.md,
  CLAUDE.md, GitBook chapters (spec, proofs), codebase_map.json
- Test infrastructure: `two_phase_arch_suite` executable in lakefile.toml,
  integrated into test_tier2_negative.sh, scenario registry + fixture updated
- Version bump: v0.17.13 → v0.17.14
- All test tiers pass, zero sorry/axiom

## [0.17.13] — WS-Q8 Rust Syscall Wrappers

- Completed Phase 8 (WS-Q8) of the Kernel State Architecture workstream:
  Rust syscall wrappers (`libsele4n`) — 3 `no_std` crates for ARM64 userspace
- Q8-A: `sele4n-types` crate — 14 newtype identifiers, 34-variant `KernelError`
  enum, `AccessRight`/`AccessRights` bitmask, 14-variant `SyscallId` enum.
  Zero `unsafe`, zero external deps. 22 unit tests.
- Q8-B: `sele4n-abi` crate — `MessageInfo` bitfield encode/decode, register
  ABI encoding (`SyscallRequest`/`SyscallResponse`), inline ARM64 `svc #0`
  trap (single `unsafe` block), 10 per-syscall argument structures,
  `TypeTag` enum (6 variants), `PagePerms` with W^X enforcement,
  `IpcBuffer` for overflow message registers. 38 unit tests.
- Q8-C: `sele4n-sys` crate — safe high-level wrappers for all 14 syscalls:
  IPC (send/receive/call/reply, notification signal/wait), CSpace (mint/copy/
  move/delete), Lifecycle (retype + convenience constructors), VSpace (map with
  W^X pre-check, unmap), Service (register/revoke/query with IPC buffer overflow).
  Phantom-typed `Cap<Obj, Rts>` with sealed traits and rights downgrading.
  4 unit tests.
- Q8-D: 25 conformance tests (RUST-XVAL-001..019 + exhaustive property tests),
  `test_rust.sh` CI script, Lean trace harness XVAL-001..004 cross-validation
  vectors, `test_smoke.sh` integration (Tier 2)
- Files: 21 Rust source files across `rust/` directory, 1 new script
  (`scripts/test_rust.sh`), trace harness + fixture + registry updated
- Lean proof surface: unchanged (zero new sorry/axiom)
- Rust: 89 total tests across 3 crates (64 unit + 25 conformance), all passing
- All test tiers pass

## [0.17.11] — WS-Q5 FrozenSystemState + Freeze

- Completed Phase 5 (WS-Q5) of the Kernel State Architecture workstream:
  FrozenSystemState definition and freeze transformation
- Q5-A: `FrozenMap` and `FrozenSet` types in `SeLe4n/Model/FrozenState.lean`
  — dense `Array ν` value store + `RHTable κ Nat` index mapping, runtime
  bounds-checked `get?` (safe-by-construction), `set` (update existing key),
  `contains`, `fold` operations
- Q5-A: `FrozenSet κ` defined as `FrozenMap κ Unit` with `FrozenSet.mem`
- Q5-B: Per-object frozen types — `FrozenCNode` (uses `CNodeRadix` from Q4
  for O(1) zero-hash slot lookup), `FrozenVSpaceRoot` (uses `FrozenMap` for
  page mappings), `FrozenKernelObject` inductive (6 variants matching
  `KernelObject`), `FrozenSchedulerState`, `FrozenSystemState` (19 fields
  mirroring `SystemState` with all `RHTable` fields replaced by `FrozenMap`)
- Q5-C: Freeze functions — `freezeMap` (RHTable → FrozenMap via fold),
  `freezeCNode`, `freezeVSpaceRoot`, `freezeObject` (per-object freeze with
  CNode→CNodeRadix via Q4 bridge, VSpaceRoot→FrozenMap), `freezeScheduler`,
  `freeze` (IntermediateState → FrozenSystemState, full 19-field conversion)
- Q5-D: Capacity planning — `minObjectSize` constant, `objectCapacity`
  (current objects + potential from untyped memory / minObjectSize)
- 20+ theorems: `freeze_deterministic`, `freeze_preserves_machine`,
  `freeze_preserves_objectIndex`, `freeze_preserves_cdtEdges`,
  `freeze_preserves_objectIndexSet`, `freezeMap_empty` (with `toList_empty`
  helper), `freezeMap_data_size`, `freezeObject_preserves_type`,
  `freezeObject_tcb_passthrough`, `freezeObject_endpoint_passthrough`,
  `freezeObject_notification_passthrough`, `freezeObject_untyped_passthrough`,
  `frozenMap_set_preserves_size`, `objectCapacity_ge_size`, and more
- Q5-T: 15-scenario test suite in `tests/FrozenStateSuite.lean` (49 checks):
  FrozenMap core (FS-001 to FS-007), FrozenKernelObject (FS-008 to FS-010),
  freeze integration (FS-011 to FS-015) including objectIndexSet, scheduler
  freeze, FrozenMap.set size preservation, and data size round-trip
- Files: 1 new (`FrozenState.lean`), 1 new test (`FrozenStateSuite.lean`),
  docs + codebase map updated, `lakefile.toml` version bumped
- All test tiers pass; zero `sorry`/`axiom`
- Bumped `lakefile.toml` version to `0.17.11`

## [0.17.9] — WS-Q3 IntermediateState Formalization

- Completed Phase 3 (WS-Q3) of the Kernel State Architecture workstream:
  IntermediateState formalization with builder-phase invariant witnesses
- Q3-A: `IntermediateState` type definition in `SeLe4n/Model/IntermediateState.lean`
  — wraps `SystemState` with four machine-checked invariant witnesses:
  `allTablesInvExt` (14 RHTable maps + 2 RHSet fields), `perObjectSlotsInvariant`
  (CNode `slotsUnique`), `perObjectMappingsInvariant` (VSpaceRoot
  `mappings.invExt`), `lifecycleMetadataConsistent`
- Q3-A: `mkEmptyIntermediateState` with `mkEmptyIntermediateState_valid` proof
- Q3-A: Named predicates `perObjectSlotsInvariant`, `perObjectMappingsInvariant`
  with default-state proofs
- Q3-B: 7 builder operations in `SeLe4n/Model/Builder.lean`, each carrying
  forward all four invariant witnesses:
  - `registerIrq` — IRQ handler insertion
  - `registerService` — service registry insertion
  - `addServiceGraph` — service graph entry insertion
  - `createObject` — simplified boot-time object creation with per-object proofs
  - `deleteObject` — object erasure with erase preservation
  - `insertCap` — CNode slot capability insertion (delegates to `createObject`)
  - `mapPage` — VSpaceRoot page mapping insertion (delegates to `createObject`)
- Q3-B: Helper theorem `insert_capacity_ge4` for capacity preservation
- Q3-C: Boot sequence in `SeLe4n/Platform/Boot.lean`:
  - `PlatformConfig`, `IrqEntry`, `ObjectEntry` types
  - `foldIrqs`, `foldObjects` fold helpers
  - `bootFromPlatform` — deterministic boot from platform configuration
  - `bootFromPlatform_valid` — master validity theorem (all four witnesses)
  - `bootFromPlatform_deterministic`, `bootFromPlatform_empty` properties
- Files: 3 new (`IntermediateState.lean`, `Builder.lean`, `Boot.lean`), 3+
  modified (docs, codebase map, lakefile)
- All test tiers pass; zero `sorry`/`axiom`
- Bumped `lakefile.toml` version to `0.17.9`

## [0.17.5] — WS-N5 Test Coverage + Documentation

- Completed Phase 5 (WS-N5) of the Robin Hood hashing workstream: test coverage
  and documentation sync. WS-N portfolio **COMPLETE** (v0.17.0–v0.17.5)
- N5-A: 12 standalone Robin Hood test scenarios in `tests/RobinHoodSuite.lean`:
  RH-001 (empty table), RH-002 (insert/get roundtrip), RH-003 (insert/erase),
  RH-004 (overwrite), RH-005 (10 distinct keys), RH-006 (collision handling),
  RH-007 (Robin Hood swap), RH-008 (backward-shift after erase), RH-009
  (resize trigger at 75% load), RH-010 (post-resize correctness), RH-011
  (large-scale 200 inserts + 100 erases), RH-012 (fold/toList)
- N5-B: 6 CNode integration regression tests: RH-INT-001 (lookup/insert/remove),
  RH-INT-002 (revokeTargetLocal with filter), RH-INT-003 (findFirstEmptySlot),
  RH-INT-004 (slotCountBounded), RH-INT-005 (CSpace resolution), RH-INT-006
  (BEq comparison)
- N5-C: Test infrastructure — `robin_hood_suite` executable in `lakefile.toml`,
  added to Tier 2 test script (`test_tier2_negative.sh`), 18 scenario IDs
  registered in `tests/fixtures/scenario_registry.yaml`
- N5-D: Full documentation sync across 8 canonical files (README.md,
  DEVELOPMENT.md, SELE4N_SPEC.md, CLAIM_EVIDENCE_INDEX.md, WORKSTREAM_HISTORY.md,
  CLAUDE.md, CHANGELOG.md, website_link_manifest.txt) + 4 GitBook chapters
  (03-architecture, 04-design-deep-dive, 05-specification, 12-proof-invariant-map)
- Files: 1 new (`tests/RobinHoodSuite.lean`), 15+ modified
- All test tiers pass; zero `sorry`/`axiom`
- Bumped `lakefile.toml` version to `0.17.5`

## [0.17.4] — WS-N4 Kernel Integration (CNode.slots)

- Completed Phase 4 (WS-N4): replaced `CNode.slots : Std.HashMap Slot Capability`
  with `RHTable Slot Capability` across the kernel
- Updated CNode operations, ~25 CNode/capability theorems, ~15 invariant proofs
  across Capability/InformationFlow subsystems
- `slotsUnique` repurposed from `True` to substantive `invExt ∧ size < capacity
  ∧ 4 ≤ capacity` invariant
- 3 new bridge lemmas: `filter_fold_absent_by_pred`, `filter_get_pred`,
  `filter_filter_getElem?`
- 20+ files modified; test fixtures updated; zero `sorry`/`axiom`
- Bumped `lakefile.toml` version to `0.17.4`

## [0.17.3] — WS-N3 Kernel API Bridge

- Completed Phase 3 (WS-N3): kernel API bridge in
  `SeLe4n/Kernel/RobinHood/Bridge.lean` (~307 lines)
- N3-A: `Inhabited`/`BEq` typeclass instances for `RHTable`
- N3-B: 12 bridge lemmas matching `Std.HashMap` patterns (`getElem?_insert_self`,
  `getElem?_insert_ne`, `getElem?_erase_self`, `getElem?_erase_ne`,
  `getElem?_empty`, `size_erase_le`, `size_insert_le`,
  `mem_iff_isSome_getElem?`, `getElem?_eq_some_getElem`, `fold_eq_slots_foldl`)
- N3-C: `RHTable.filter` with `size_filter_le_size` preservation
- `RHTable.ofList` constructor, `get_after_erase_ne` proof (+247 lines in
  `Lookup.lean`)
- Zero `sorry`/`axiom`; all test tiers pass
- Bumped `lakefile.toml` version to `0.17.3`

## [0.17.2] — WS-N2 Robin Hood Invariant Proofs

- Completed Phase 2 (WS-N2) of the Robin Hood hashing workstream: invariant
  definitions, WF/distCorrect preservation, modular arithmetic helpers, loop
  count/correctness proofs, bundle preservation theorems, and lookup correctness
  signatures
- N2-A: Invariant definitions in `SeLe4n/Kernel/RobinHood/Invariant/Defs.lean`:
  `distCorrect` (probe distance accuracy), `noDupKeys` (key uniqueness),
  `robinHoodOrdered` (non-decreasing cluster distances), `RHTable.invariant`
  4-conjunct bundle; `empty_distCorrect`, `empty_noDupKeys`,
  `empty_robinHoodOrdered`, `empty_invariant` proofs
- N2-B: WF preservation in `SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean`:
  `insertNoResize_preserves_wf`, `insert_preserves_wf`, `resize_preserves_wf`,
  `erase_preserves_wf`; modular arithmetic helpers `mod_succ_eq`,
  `dist_step_mod`; `countOccupied_le_size` bound proof
- N2-C: distCorrect preservation: `insertLoop_preserves_distCorrect` (full
  induction proof with modular arithmetic),
  `insertNoResize_preserves_distCorrect`, `insert_preserves_distCorrect`,
  `resize_preserves_distCorrect` (via fold induction)
- N2-D: Loop count and correctness: `insertLoop_countOccupied`,
  `backshiftLoop_countOccupied`, `findLoop_lt`, `findLoop_correct`
- N2-E: Bundle preservation: `insert_preserves_invariant`,
  `erase_preserves_invariant`, `resize_preserves_invariant`
- N2-F: Lookup correctness signatures in
  `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean`: `get_after_insert_eq`,
  `get_after_insert_ne`, `get_after_erase_eq`
- N2-G: Re-export hub `SeLe4n/Kernel/RobinHood/Invariant.lean`; updated
  `SeLe4n/Kernel/RobinHood.lean` to import Invariant; changed `private` to
  `protected` for `insertNoResize`, `insertNoResize_capacity`,
  `resize_fold_capacity` in `Core.lean`
- **Major finding:** `robinHoodOrdered` (non-decreasing dist within clusters)
  is NOT preserved by backshift-on-erase. `invExt` bundle restructured to use
  `probeChainDominant` instead, which IS preserved by all operations
- Additional helper lemmas proved: `noDupKeys_after_clear`,
  `backshiftLoop_preserves_noDupKeys`, `erase_preserves_noDupKeys`,
  `displacement_backward`, `backshiftLoop_preserves_distCorrect`,
  `erase_preserves_distCorrect`
- Preservation theorems complete: WF (all ops), distCorrect (all ops),
  noDupKeys (all ops), probeChainDominant (all ops)
- TPI-D1 completed: `insertLoop_preserves_noDupKeys` — full fuel induction
  proving noDupKeys for insertLoop result (zero sorry)
- TPI-D2 completed: `insertLoop_preserves_pcd` — full fuel induction proving
  probeChainDominant for insertLoop result (zero sorry)
- TPI-D3 completed: `erase_preserves_probeChainDominant` — relaxedPCD
  framework proving PCD preservation through backshift-on-erase via
  `pcd_to_relaxedPCD_after_clear`, `backshiftStep_relaxedPCD`,
  `relaxedPCD_to_pcd_at_termination` (zero sorry)
- TPI-D4 completed: `get_after_insert_eq` — insert lookup correctness via
  `getLoop_finds_present` + `insertLoop_places_key` (zero sorry)
- TPI-D5 completed: `get_after_insert_ne` — insert non-interference via
  `insertLoop_absent_ne_key` (none case) + `insertLoop_output_source` +
  `resize_preserves_key_absence` (some case) (zero sorry)
- TPI-D6 completed: `get_after_erase_eq` — erase lookup correctness via
  `erase_removes_key` + `getLoop_none_of_absent` (zero sorry)
- Helper infrastructure: `offset_injective` (modular offset injectivity),
  `getElem_idx_eq` (array access proof irrelevance), `carried_key_absent`
  (key absent if probe reached empty/swap position), `getLoop_none_of_absent`,
  `findLoop_none_implies_absent`, `backshiftLoop_preserves_key_absence`,
  `getLoop_finds_present`, `insertLoop_places_key`, `displacement_backward`,
  `relaxedPCD` (gap-excused PCD invariant)
- Files: 4 new (`Invariant/Defs.lean`, `Invariant/Preservation.lean`,
  `Invariant/Lookup.lean`, `Invariant.lean`), 2 modified (`Core.lean`,
  `RobinHood.lean`); ~4,655 LoC total
- All 6 TPI-D items completed (D1–D6); WS-N2 COMPLETE
- Zero `sorry`/`axiom`; zero warnings; all test tiers pass
- Bumped `lakefile.toml` version to `0.17.2`

## [0.17.1] — WS-N1 Core Robin Hood Types + Operations

- Completed Phase 1 (WS-N1) of the Robin Hood hashing workstream: core data
  types, fuel-bounded operations, and array-size preservation proofs
- N1-A: `RHEntry` (key, value, probe distance) and `RHTable` (single-
  representation `Array (Option (RHEntry α β))` with `hCapPos`/`hSlotsLen`
  invariants); `idealIndex`/`nextIndex` with `@[inline]`; `idealIndex_lt`/
  `nextIndex_lt` bound proofs via `Nat.mod_lt`
- N1-B: `RHTable.empty` constructor from `List.replicate`; `countOccupied`
  helper; 4-conjunct `RHTable.WF` predicate (slotsLen, capPos, sizeCount,
  sizeBound); `empty_wf` proof (zero sorry)
- N1-C: Fuel-bounded `insertLoop` with 5 branches (empty slot, key match,
  Robin Hood swap, continue probing, fuel exhausted); structural recursion on
  `fuel : Nat`; `insertLoop_preserves_len` by induction
- N1-D: `RHTable.insert` with 75% load-factor resize trigger; private
  `insertNoResize` helper to avoid resize/insert circularity;
  `insertNoResize_size_le` proof
- N1-E: Fuel-bounded `getLoop` with Robin Hood early termination (empty slot,
  dist < search dist); `RHTable.get?`; `RHTable.contains`
- N1-F: `findLoop` (locate target slot) + `backshiftLoop` (fill gap after
  removal, decrement dist); `backshiftLoop_preserves_len` proof;
  `RHTable.erase` composing both phases
- N1-G: `RHTable.fold`, `RHTable.toList`, `RHTable.resize` (double capacity,
  re-insert all via `insertNoResize`); `resize_preserves_len` proof
  (`slots.size = capacity * 2` via `Array.foldl_induction`);
  `resize_fold_capacity` proof; `Membership` instance;
  `GetElem`/`GetElem?` instances enabling `t[k]?` bracket notation
- N1-H: Re-export hub `SeLe4n/Kernel/RobinHood.lean`
- Files: `SeLe4n/Kernel/RobinHood/Core.lean` (379 lines),
  `SeLe4n/Kernel/RobinHood.lean` (15 lines)
- Zero `sorry`/`axiom`; zero warnings; all test tiers pass
- Bumped `lakefile.toml` version to `0.17.1`

## [0.16.18] — WS-M4 Test Coverage Expansion

- Completed Phase 4 (WS-M4) of the capability subsystem workstream: test
  coverage expansion for `resolveCapAddress` edge cases and `cspaceRevokeCdtStrict`
  stress scenarios
- M4-A: 6 `resolveCapAddress` edge case tests in `NegativeStateSuite.lean`:
  - M4-A1: Guard-only CNode (zero radixWidth, non-zero guardWidth) resolves
    to slot 0; wrong guard correctly rejected (SCN-RESOLVE-GUARD-ONLY)
  - M4-A2: 64-bit resolution across 8 CNodes (8 bits per hop) succeeds
    end-to-end; 65-bit overflow returns `.invalidCapability` due to bit-shift
    misalignment (SCN-RESOLVE-MAX-DEPTH)
  - M4-A3: Guard mismatch at intermediate level in 3-level CNode chain
    returns `.invalidCapability` (SCN-RESOLVE-GUARD-MISMATCH-MID)
  - M4-A4: Partial bit consumption (bitsRemaining < guardWidth + radixWidth)
    and zero bitsRemaining both return `.illegalState` (SCN-RESOLVE-PARTIAL-BITS)
  - M4-A5: Single-level leaf resolution with exact bit consumption
    (SCN-RESOLVE-SINGLE-LEVEL)
- M4-B: 3 `cspaceRevokeCdtStrict` stress tests in `OperationChainSuite.lean`:
  - M4-B1: 15-level deep chain strict revocation — all 15 descendants deleted,
    `deletedSlots.length = 15`, root slot preserved, CDT nodes detached
    (SCN-REVOKE-STRICT-DEEP)
  - M4-B2: Partial failure mid-traversal — corrupted CNode triggers
    `.objectNotFound`, `firstFailure` populated with correct context,
    `deletedSlots.length = 2` (exactly the nodes before the failure point),
    traversal halts at failure point (SCN-REVOKE-STRICT-PARTIAL-FAIL)
  - M4-B3: Branching tree (root→A→A1, root→B→B1→B2) — all 5 descendants
    deleted, set-membership verified, parent-before-child ordering verified
    for each sub-chain (SCN-REVOKE-STRICT-ORDER)
- Refined WS-M4 workstream plan with detailed subtask specifications,
  dependency graph, and execution order
- 9 new test scenarios; zero sorry/axiom; zero warnings
- All test tiers pass (test_full.sh Tier 0-3)
- Bumped `lakefile.toml` version to 0.16.18

## [0.16.17] — WS-M3 IPC Capability Transfer Implementation

- Completed Phase 3 (WS-M3) of the capability subsystem workstream: IPC
  capability transfer with seL4-aligned receive-side cap unwrapping
- M3-A: Added `CapTransferResult` inductive (`installed`/`noSlot`/`grantDenied`),
  `CapTransferSummary` structure, `DerivationOp.ipcTransfer` CDT variant
- M3-B: Implemented `CNode.findFirstEmptySlot` with structural recursion on
  `limit` parameter; `findFirstEmptySlot_spec` and `findFirstEmptySlot_zero`
  correctness theorems
- M3-C: Implemented `ipcTransferSingleCap` — single-cap transfer with CDT edge
  tracking via `.ipcTransfer` derivation op; `ipcTransferSingleCap_preserves_scheduler`
  and `ipcTransferSingleCap_preserves_capabilityInvariantBundle` preservation proofs
- M3-D: Implemented `ipcUnwrapCaps` batch cap unwrap with `ipcUnwrapCapsLoop`
  recursive helper (fuel-based structural recursion); Grant-right gate drops
  all caps when endpoint lacks Grant right; `ipcUnwrapCaps_preserves_scheduler`
  preservation proof by induction on fuel;
  `ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant` proves bundle
  preservation when Grant right is absent (state unchanged)
- M3-E: Added `endpointSendDualWithCaps`, `endpointReceiveDualWithCaps`,
  `endpointCallWithCaps` wrapper operations composing existing IPC ops with
  cap transfer during rendezvous; `lookupCspaceRoot` helper reads receiver's
  CSpace root from TCB; `ipcUnwrapCaps_preserves_ipcInvariant`,
  `endpointSendDualWithCaps_preserves_ipcInvariant`,
  `endpointReceiveDualWithCaps_preserves_ipcInvariant`,
  `endpointCallWithCaps_preserves_ipcInvariant` preservation theorems
- M3-F: Added `decodeExtraCapAddrs` with determinism theorem; `resolveExtraCaps`
  pure fold over CPtr array; updated `dispatchWithCap` to use WithCaps wrappers
  for send/call paths; renamed theorems (`dispatchWithCap_send_uses_withCaps`,
  `dispatchWithCap_call_uses_withCaps`)
- M3-G: Added 4 test scenarios: SCN-IPC-CAP-TRANSFER-BASIC,
  SCN-IPC-CAP-TRANSFER-NO-GRANT, SCN-IPC-CAP-TRANSFER-FULL-CNODE,
  SCN-IPC-CAP-BADGE-COMBINED; `chain12`–`chain14` in OperationChainSuite +
  `runWSM3CapTransferNegativeChecks` in NegativeStateSuite
- New files: `SeLe4n/Kernel/IPC/Operations/CapTransfer.lean`,
  `SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean`
- Resolves L-T03 (capability transfer during IPC — last WS-L deferred item)
- 12+ new proved declarations; zero sorry/axiom; zero warnings
- All test tiers pass (test_full.sh Tier 0-3)
- Bumped `lakefile.toml` version to 0.16.17

## [0.16.16] — WS-M3 IPC Capability Transfer Plan Refinement

- Refined and expanded Phase 3 (WS-M3) workstream plan for IPC capability
  transfer from 4 coarse tasks to 7 tasks with 20 atomic subtasks
- Corrected architectural alignment: cap unwrapping happens on the receive side
  (seL4 semantics), not the send side as originally planned
- Added `CapTransferResult`/`CapTransferSummary` type specifications with
  seL4-accurate `grantDenied` variant (replacing incorrect `attenuationFailed`)
- Added `DerivationOp.ipcTransfer` CDT variant for tracking IPC-transferred caps
- Designed `CNode.findFirstEmptySlot` with bounded iteration (structural
  recursion on `limit`) and correctness theorem specifications
- Specified `ipcTransferSingleCap` operation with CDT edge tracking and
  `ipcUnwrapCaps` batch operation with Grant-right gate
- Designed wrapper pattern (`endpointSendDualWithCaps`,
  `endpointReceiveDualWithCaps`, `endpointCallWithCaps`) preserving all existing
  IPC operation signatures and proofs
- Added `decodeExtraCapAddrs` and `resolveExtraCaps` specifications for wiring
  extra cap addresses from `SyscallDecodeResult.msgInfo.extraCaps` through
  `dispatchWithCap`
- Specified 4 test scenarios: positive transfer, grant-right gate, no-slot
  negative, badge+cap combined (SCN-IPC-CAP-TRANSFER-*)
- Full dependency graph with 9 sequential steps and parallelism opportunities
- Corrected Phase 4/5 target versions (0.16.17/0.16.18, consistent with patch
  version scheme)
- All tests pass (test_full.sh Tier 0-3); zero sorry/axiom; zero warnings
- Bumped `lakefile.toml` version to 0.16.16

## [0.16.15] — Capability Performance Optimization (WS-M2)

- Completed Phase 2 (WS-M2) of the capability subsystem workstream: performance
  optimization across CSpace revoke, CDT parent lookup, and proof infrastructure
- M2-A: Fused `revokeAndClearRefsState` single-pass revoke — eliminates
  intermediate `revokedRefs` list allocation and second O(m) traversal through
  `clearCapabilityRefsState`, cutting revoke hot path from two O(m) passes to one
- M2-A2: Added comprehensive field preservation lemmas for
  `revokeAndClearRefsState` — objects, scheduler, machine, services, irqHandlers,
  objectIndex, objectIndexSet, CDT fields — using `Std.HashMap.fold_eq_foldl_toList`
  bridge with list induction
- M2-B1: Added `parentMap : Std.HashMap CdtNodeId CdtNodeId` field to
  `CapDerivationTree` — child-indexed parent map symmetric to existing `childMap`
- M2-B2/B3: Rewrote `parentOf` to use `parentMap[node]?` (O(E) → O(1)),
  updated `addEdge` to maintain `parentMap` alongside `childMap` and `edges`
- M2-B4/B5: Updated `removeAsChild`, `removeAsParent`, `removeNode` for
  targeted `parentMap` erasure — `removeNode` childMap update goes from O(E)
  full rebuild to O(children.length) targeted splice
- M2-B6/B7: Defined `parentMapConsistent` invariant with proofs for `empty`,
  `addEdge`, and `removeNode` (requires `childMapConsistent` co-hypothesis)
- M2-C: Extracted `capabilityInvariantBundle_of_storeTcbAndEnsureRunnable`
  private theorem — shared reply-preservation proof body eliminating duplication
  across authorized and unrestricted dispatch branches
- Updated non-interference proofs (Helpers.lean, Operations.lean) to use
  `revokeAndClearRefsState_preserves_*` and `revokeAndClearRefsState_preserves_projectState`
- Added `cdtParentMapConsistentCheck` runtime invariant check in test harness
- Removed dead code: `clearCapabilityRefsState`, `clearCapabilityRefs`, and 11
  associated preservation theorems — fully superseded by `revokeAndClearRefsState`
- Net +1 proved declarations (12 added, 11 dead removed); zero sorry/axiom
- All test tiers pass (test_full.sh); 150/150 trace fixtures matched
- Bumped `lakefile.toml` version to 0.16.15

## [0.16.14] — Capability Proof Strengthening (WS-M1)

- Completed Phase 1 (WS-M1) of the capability subsystem workstream: proof
  strengthening and correctness improvements across CSpace resolution, CDT
  acyclicity, mint completeness, and revoke error consistency
- M1-A: Added `resolveCapAddress_guard_match` theorem — forward-direction
  companion proving that successful resolution implies guard bits match the
  CNode's stored guardValue (complements existing `resolveCapAddress_guard_reject`)
- M1-B1: Introduced `cdtMintCompleteness` predicate — every CDT node with a
  slot mapping either has a parent edge (derived node) or is completely isolated
  (root node with no edges at all)
- M1-B2: Added `cdtMintCompleteness_of_cdt_edges_nodeSlot_eq` transfer theorem
  for state transitions that preserve CDT edges and nodeSlot mappings
- M1-B3: Defined `capabilityInvariantBundleWithMintCompleteness` extended
  invariant bundle with extraction theorems
- M1-C1: Proved `addEdge_preserves_edgeWellFounded_fresh` — CDT edge addition
  preserves acyclicity when the child node is fresh (not in any existing edge),
  covering the common `ensureCdtNodeForSlot` kernel pattern
- M1-C2: Added `addEdgeWouldBeSafe` runtime acyclicity check (parent ≠ child ∧
  parent ∉ descendantsOf child)
- M1-D1: Added `cspaceRevokeCdt_swallowed_error_consistent` theorem — proves
  invariant preservation, object stability, and edge-set monotonicity through
  the error-swallowing path of `revokeCdtFoldBody`
- M1-D2/E: Updated `cspaceRevokeCdt` and `cspaceRevoke` docstrings with
  accurate cross-references and error-handling design rationale
- Refined Phase 1 workstream plan: split 5 high-level tasks into 10 atomic
  subtasks (M1-E, M1-A1/A2, M1-B1/B2/B3, M1-C1/C2, M1-D1/D2)
- 7 new proved declarations; zero sorry/axiom; all proofs machine-checked
- All test tiers pass (test_full.sh); production LoC: 38,556 across 69 files
- Bumped `lakefile.toml` version to 0.16.14

## [0.16.12] — IPC Test Coverage Expansion (WS-L4)

- Completed WS-L4 phase: filled all 4 IPC test coverage gaps (L-T01, L-T02,
  L-T04, L-T05) with 9 new scenario IDs (16 total across L4 test functions)
- L4-A2: Extended `runReplyRecvRoundtripTrace` with second-sender rendezvous
  path — verifies `endpointReplyRecv` replies to caller A AND immediately
  receives caller B's message in a single atomic operation (RRC-002, RRC-006);
  refined RRC-005 to verify server is `.ready` after rendezvous (not just
  not-blocked)
- L4-B: New `runEndpointLifecycleTrace` — endpoint retype while senders are
  blocked on sendQ, validates graceful-failure-by-guard model: senders retain
  stale `blockedOnSend` state, stale IPC operations rejected with
  `.invalidCapability` (ELC-001 through ELC-004)
- L4-D2/D3: Extended `runMultiEndpointInterleavingTrace` from 2 to 3 endpoints
  with out-of-order receive (EP3 before EP1) and FIFO verification on EP1
  second message round (MEI-004, MEI-005, MEI-006)
- L4-C: Extended blocked-thread IPC rejection tests with 2 cross-state
  scenarios (blocked-on-receive rejects send to different endpoint;
  blocked-on-send rejects receive from different endpoint) — 5 total rejection
  cases
- Refined WS-L4 workstream plan with detailed gap analysis, sub-step breakdown,
  and implementation status tracking
- Updated fixture files and scenario registry for all new scenario IDs
- Inter-transition invariant check count: 22 (up from 21)
- Bumped `lakefile.toml` version to 0.16.12
- Zero sorry/axiom; all proofs machine-checked; test_full.sh passes

## [0.16.11] — IPC Proof Strengthening (WS-L3)

- Added 22 new theorems and 1 new invariant definition strengthening formal
  assurance of the IPC dual-queue subsystem
- L3-A: Enqueue-dequeue round-trip theorem — proves that a thread enqueued
  into an empty queue can be successfully dequeued via popHead
  (`endpointQueueEnqueue_then_popHead_succeeds` + 2 postcondition lemmas)
- L3-B: Standalone `tcbQueueLinkIntegrity` preservation for popHead and
  enqueue, extracted from bundled `dualQueueSystemInvariant` preservation
- L3-C: New `ipcStateQueueConsistent` invariant (blocked → endpoint exists)
  with queue-operation preservation theorems; 3 forward endpoint preservation
  helpers (`storeTcbQueueLinks_endpoint_forward`, `endpointQueuePopHead_endpoint_forward`,
  `endpointQueueEnqueue_endpoint_forward`)
- L3-D: Tail consistency for `endpointQueueRemoveDual` — non-tail removal
  preserves tail, tail removal characterization
- L3-E: Identified as already resolved (pre-existing in `CallReplyRecv.lean:797`)
- Refined WS-L3 workstream plan with granular subtask breakdown
- L3-C3: high-level `ipcStateQueueConsistent` preservation theorems for
  `endpointSendDual`, `endpointReceiveDual`, `endpointReply` — plus 5
  sub-operation helpers (`ensureRunnable`, `removeRunnable`,
  `storeTcbIpcStateAndMessage`, `storeTcbIpcState`, `storeTcbPendingMessage`)
- Regenerated `docs/codebase_map.json` — 38,186 production LoC, 1,224 proved
  declarations
- Bumped `lakefile.toml` version to 0.16.11
- Zero sorry/axiom; all proofs machine-checked; test_full.sh passes

## [0.16.10] — Code Quality & HashMap.fold Migration (WS-L2)

- Eliminated all 4 `Std.HashMap.toList.foldl/foldr` anti-patterns across codebase,
  replacing with direct `HashMap.fold` calls that avoid intermediate list allocation
- L2-A: Migrated 3 fold patterns in `Testing/InvariantChecks.lean`
  (`cspaceSlotCoherencyChecks`, `capabilityRightsStructuralChecks`,
  `cdtChildMapConsistentCheck`) from `.toList.foldr` to `HashMap.fold`
- L2-B: Migrated `detachCNodeSlots` in `Kernel/Lifecycle/Operations.lean` from
  `.toList.foldl` to `HashMap.fold`; updated 3 preservation proofs
  (`_objects_eq`, `_lifecycle_eq`, `_scheduler_eq`) using
  `Std.HashMap.fold_eq_foldl_toList` bridge lemma
- Refined WS-L2 workstream plan: expanded scope from 1 site to 4, added
  sub-task breakdown with proof update strategy and risk assessment
- Regenerated `docs/codebase_map.json`
- Bumped `lakefile.toml` version to 0.16.10
- Zero sorry/axiom; all proofs machine-checked; test_full.sh passes

## [0.16.9] — IPC Performance Optimization (WS-L1)

- Eliminated 4 redundant TCB lookups on IPC hot paths (L-P01, L-P02, L-P03)
- Changed `endpointQueuePopHead` return type to `(ThreadId × TCB × SystemState)`,
  providing pre-dequeue TCB to callers (L1-A)
- Added `storeTcbIpcStateAndMessage_fromTcb` and `storeTcbIpcState_fromTcb`
  variants with equivalence theorems — zero new preservation lemmas needed (L1-B, L1-C)
- Added `lookupTcb_preserved_by_storeObject_notification` helper for cross-store
  TCB stability
- Updated all transport lemmas and preservation theorems for new PopHead return type
  (~18 mechanical pattern-match updates across 6 invariant files)
- Refined WS-L1 workstream plan with smaller task units and optimal implementation
  strategy (equivalence-theorem approach vs. duplicated lemmas)
- Regenerated `docs/codebase_map.json`
- Bumped `lakefile.toml` version to 0.16.9
- Zero sorry/axiom; all proofs machine-checked; test_full.sh passes

## [0.16.8] — Documentation Sync and Workstream Closeout (WS-K-H)

- Synchronized all project documentation with completed WS-K implementation
  (K-A through K-G): canonical root docs, GitBook mirrors, metrics, version
- Updated `docs/WORKSTREAM_HISTORY.md` with WS-K portfolio completion
  (v0.16.0–v0.16.8, all 8 phases)
- Updated `docs/spec/SELE4N_SPEC.md` with v0.16.8 current state snapshot,
  WS-K PORTFOLIO COMPLETE status, and updated metrics
- Updated `docs/DEVELOPMENT.md` with WS-K completion and RPi5 next priority
- Updated `docs/CLAIM_EVIDENCE_INDEX.md` with comprehensive WS-K claim row
  covering all deliverables and evidence commands
- Updated GitBook chapters: architecture module map (03), design deep dive (04),
  specification and roadmap (05), proof and invariant map (12)
- Added `SyscallArgDecode.lean` entry to architecture module map with WS-K-B/K-F
  annotations
- Added two-layer syscall argument decode section to design deep dive
- Documented WS-K proof surface (44+ theorems) in proof and invariant map
- Regenerated `docs/codebase_map.json` with current Lean source metrics
- Synced `README.md` metrics from regenerated codebase map
- Bumped `lakefile.toml` version to 0.16.8
- Zero code changes to Lean source — documentation-only workstream

## [0.16.7] — Comprehensive Testing for Syscall Dispatch Completion (WS-K-G)

- Refined WS-K-G workstream plan into 7 granular sub-phases (K-G1 through K-G7)
  with detailed test specifications, design rationale, and acceptance criteria
- Added 21 negative-state tests in `NegativeStateSuite.lean` (`runWSKGChecks`):
  K-G1 (6 tests) CSpace decode/dispatch error coverage, K-G2 (7 tests)
  lifecycle/VSpace error coverage, K-G3 (5 tests) service policy and boundary
  coverage, K-G4 (3 tests) determinism verification for decode pipeline
- Added 8 trace scenarios in `MainTraceHarness.lean` (`runSyscallDispatchTrace`):
  KSD-001 through KSD-008 covering CSpace mint/copy/delete, lifecycle retype,
  VSpace map, service start, IPC message population, and layer 1+2 round-trip;
  all scenarios exercise the full Layer-2 decode pipeline (SyscallDecodeResult →
  typed args → kernel operation)
- Added 34 Tier 3 invariant surface anchors (11 `rg` pattern checks + 23
  `#check` type-level validations) for K-F and K-G proof surface in
  `scripts/test_tier3_invariant_surface.sh`
- Updated scenario registry with KSD-001 through KSD-008 entries
- Updated fixture file with new trace output (134 lines, ITR-001 count 18→19)
- All tiers (0-3) pass; zero `sorry`, zero `axiom`

## [0.16.6] — Lifecycle NI Proof Completion and Deferred Proof Resolution (WS-K-G)

- Added `cspaceRevoke_preserves_projection` standalone theorem in
  `InformationFlow/Invariant/Operations.lean` — extracted from inline proof in
  Composition.lean for compositional reuse in lifecycle NI proofs
- Added `lifecycleRevokeDeleteRetype_preserves_projection` theorem — chains
  projection preservation across `cspaceRevoke`, `cspaceDeleteSlot`, and
  `lifecycleRetypeObject` sub-operations via their respective projection theorems
- Added `lifecycleRevokeDeleteRetype_preserves_lowEquivalent` two-run NI theorem
  — completes the previously deferred `lifecycleRevokeDeleteRetype` NI proof
  using compositional projection-preservation reasoning
- Extended `NonInterferenceStep` inductive with `lifecycleRevokeDeleteRetype`
  constructor (34 constructors total, up from 33) covering the composed
  revoke-delete-retype lifecycle operation
- Updated `step_preserves_projection` with the new constructor case using
  the standalone `lifecycleRevokeDeleteRetype_preserves_projection` theorem
- Updated `syscallNI_coverage_witness` documentation to reflect 34-constructor
  exhaustive match (verified by Lean exhaustiveness checker)
- Zero `sorry`, zero `axiom` — all proofs machine-checked

## [0.16.5] — Proofs: Round-Trip, Preservation, and NI Integration (WS-K-F)

- Added 7 encode functions in `SyscallArgDecode.lean` (`encodeCSpaceMintArgs`,
  `encodeCSpaceCopyArgs`, `encodeCSpaceMoveArgs`, `encodeCSpaceDeleteArgs`,
  `encodeLifecycleRetypeArgs`, `encodeVSpaceMapArgs`, `encodeVSpaceUnmapArgs`)
  completing the encode/decode symmetry for all layer-2 typed argument structures
- Proved 7 layer-2 round-trip theorems via structure eta reduction (`rcases + rfl`)
  with `decode_layer2_roundtrip_all` composed conjunction
- Added `extractMessageRegisters_roundtrip` in `RegisterDecode.lean` — proves
  encoding `Nat` values as `RegValue` then extracting recovers the originals
  (closes the layer-1 extraction round-trip gap)
- Added `dispatchWithCap_layer2_decode_pure` in `API.lean` — proves all 7
  layer-2 decode functions depend only on `msgRegs` (two `SyscallDecodeResult`
  values with identical `msgRegs` produce identical decode results)
- Added `dispatchWithCap_preservation_composition_witness` structural
  preservation theorem in `API.lean` — witnesses compositional invariant
  preservation through the syscall entry → decode → dispatch → subsystem pipeline
- Added `retypeFromUntyped_preserves_lowEquivalent` NI theorem in
  `InformationFlow/Invariant/Operations.lean` — completes the last deferred
  NI proof using two-stage `storeObject_at_unobservable_preserves_lowEquivalent`
  composition through intermediate untyped update state
- Added `syscallNI_coverage_witness` in `InformationFlow/Invariant/Composition.lean`
  — witnesses that (1) decode-error path produces a valid NI step, (2) every NI
  step composes into a trace, and (3) `step_preserves_projection` is total over
  all 33 `NonInterferenceStep` constructors
- Refined WS-K-F workstream plan into 6 granular sub-phases (K-F1 through K-F6)
  with detailed task breakdowns, proof patterns, and exit criteria
- Zero `sorry`, zero `axiom` — all proofs machine-checked

## [0.16.4] — Service Policy and IPC Message Population (WS-K-E)

- Replaced `(fun _ => true)` service policy stubs in `dispatchWithCap` with
  configuration-sourced predicates: `.serviceStart` reads
  `st.serviceConfig.allowStart`, `.serviceStop` reads `st.serviceConfig.allowStop`
- Added `ServiceConfig` structure in `Model/State.lean` with `Inhabited` default
  (permissive `fun _ => true`), preserving backward compatibility
- Extended `SystemState` with `serviceConfig : ServiceConfig := default` field
- Added `extractMessageRegisters` in `RegisterDecode.lean` — converts
  `Array RegValue` → `Array Nat` (matching `IpcMessage.registers : Array Nat`)
  with triple bound (`info.length`, `maxMessageRegisters`, `msgRegs.size`)
- Updated `.send`, `.call`, `.reply` IPC dispatch arms to populate message bodies
  from decoded registers instead of empty arrays (`registers := #[]`)
- Proved `extractMessageRegisters_length` (result size ≤ `maxMessageRegisters`),
  `extractMessageRegisters_ipc_bounded` (constructed `IpcMessage` satisfies
  `bounded`), `extractMessageRegisters_deterministic`
- 5 delegation theorems proved (`dispatchWithCap_serviceStart_uses_config`,
  `dispatchWithCap_serviceStop_uses_config`, `dispatchWithCap_send_populates_msg`,
  `dispatchWithCap_call_populates_msg`, `dispatchWithCap_reply_populates_msg`)
- All existing soundness theorems compile unchanged
- `BootstrapBuilder` extended with `serviceConfig` field and `withServiceConfig`
  combinator for test scenario configuration
- 11 Tier 3 invariant surface anchors (rg + #check) for all new definitions
- Refined WS-K-E workstream plan with 17 detailed subtasks (K-E.1–K-E.17)
- Zero `(fun _ => true)` policy stubs remain in `dispatchWithCap`
- Zero `registers := #[]` in IPC dispatch arms
- Zero `sorry`, zero `axiom` — all proofs machine-checked

## [0.16.3] — Lifecycle and VSpace Syscall Dispatch (WS-K-D)

- Wired all 3 remaining syscall stubs (`lifecycleRetype`, `vspaceMap`,
  `vspaceUnmap`) through `dispatchWithCap` using decoded message register
  arguments — zero `.illegalState` stubs remain; all 13 syscalls fully dispatch
- Added `objectOfTypeTag` helper mapping raw type tags (0–5) to default
  `KernelObject` constructors with dedicated `invalidTypeTag` error variant for
  unrecognized tags; includes type, error-exclusivity, and determinism theorems
- Added `lifecycleRetypeDirect` — companion to `lifecycleRetypeObject` for
  register-sourced dispatch where the authority cap is already resolved by
  `syscallInvoke`; avoids double capability lookup; includes equivalence theorem
  linking it to `lifecycleRetypeObject`
- Added `PagePermissions.ofNat`/`toNat` bitfield codec (bit 0=read, 1=write,
  2=execute, 3=user, 4=cacheable) with round-trip theorem
- `vspaceMap` dispatch uses `vspaceMapPageChecked` (bounds-checked variant,
  rejects `paddr ≥ 2^52`) for user-space entry safety
- 3 delegation theorems proved (`dispatchWithCap_lifecycleRetype_delegates`,
  `dispatchWithCap_vspaceMap_delegates`, `dispatchWithCap_vspaceUnmap_delegates`)
- All existing soundness theorems compile unchanged after dispatch changes
- Tier 3 invariant surface anchors added for all new definitions and theorems
- Refined WS-K-D workstream plan with 10 detailed subtasks (K-D.1–K-D.10)
- Zero `sorry`, zero `axiom` — all proofs machine-checked

## [0.16.2] — CSpace Syscall Dispatch (WS-K-C)

- Wired all 4 CSpace syscalls (`cspaceMint`, `cspaceCopy`, `cspaceMove`,
  `cspaceDelete`) through `dispatchWithCap` using decoded message register
  arguments from `SyscallArgDecode`
- Changed `dispatchWithCap` signature from `SyscallId` to `SyscallDecodeResult`
  so CSpace dispatch arms can extract per-syscall typed arguments from
  `decoded.msgRegs`
- `cspaceMint` dispatch: decodes srcSlot, dstSlot, rights bitmask, and badge
  from 4 message registers; badge=0 maps to `none` (seL4 convention)
- `cspaceCopy`/`cspaceMove` dispatch: decodes srcSlot and dstSlot from 2
  message registers; delegates to kernel-level copy/move with CDT integration
- `cspaceDelete` dispatch: decodes targetSlot from 1 message register
- 4 delegation theorems proved (`dispatchWithCap_cspaceMint_delegates`, etc.)
- All 3 existing soundness theorems (`dispatchSyscall_requires_right`,
  `syscallEntry_implies_capability_held`, `syscallEntry_requires_valid_decode`)
  compile unchanged after signature refactoring
- Refined WS-K-C workstream plan with 8 detailed subtasks (K-C.1–K-C.8)
- Zero `sorry`, zero `axiom` — all proofs machine-checked

## [0.16.1] — Per-Syscall Argument Decode Layer (WS-K-B)

- Added `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` — layer 2 of the
  two-layer syscall decode architecture
- 7 per-syscall typed argument structures: `CSpaceMintArgs`, `CSpaceCopyArgs`,
  `CSpaceMoveArgs`, `CSpaceDeleteArgs`, `LifecycleRetypeArgs`, `VSpaceMapArgs`,
  `VSpaceUnmapArgs`
- 7 total decode functions with explicit `Except KernelError` error handling
- 7 determinism theorems (trivial `rfl`)
- 7 error-exclusivity theorems (`decode fails ↔ msgRegs.size < N`)
- Zero `sorry`, zero `axiom` — all proofs machine-checked
- Integrated into `API.lean` import graph

## [0.16.0] - 2026-03-14

### WS-K-A: Message Register Extraction into SyscallDecodeResult

- **SyscallDecodeResult extension**: Added `msgRegs : Array RegValue := #[]`
  field to `SyscallDecodeResult` in `Model/Object/Types.lean`. Default value
  ensures backward compatibility with all existing construction sites.
- **Decode function update**: Updated `decodeSyscallArgs` in
  `RegisterDecode.lean` to validate and read message registers (x2–x5 on
  ARM64) in a single pass via `Array.mapM`, replacing the previous
  bounds-only validation loop.
- **Encoding helper**: Added `encodeMsgRegs` identity encoder for round-trip
  proof surface completeness.
- **Length invariant**: Proved `decodeMsgRegs_length` — when decode succeeds,
  `decoded.msgRegs.size = layout.msgRegs.size`. Proved via novel
  `list_mapM_except_length` / `array_mapM_except_size` helper lemmas.
- **Round-trip lemma**: Proved `decodeMsgRegs_roundtrip` — encoding then
  decoding message register values is identity.
- **Extended composition**: Updated `decode_components_roundtrip` to include
  the `msgRegs` component (4-conjunct from 3-conjunct).
- **Test updates**: NegativeStateSuite J1-NEG-17 now verifies `msgRegs.size = 4`
  for ARM64 layout. MainTraceHarness RDT-002 trace output includes `msgRegs`
  count. Trace fixture updated. 4 new Tier 3 surface anchors added.
- **Workstream plan refinement**: WS-K-A section decomposed into 8 detailed
  subtasks (K-A.1 through K-A.8) with per-subtask acceptance criteria.
- **Build jobs:** 140. Zero sorry/axiom. Zero warnings.
- **Closes:** WS-K Phase A.

## [0.15.10] - 2026-03-14

### WS-J1-F: CdtNodeId Cleanup and Documentation Sync

- **Typed wrapper replacement**: Replaced `abbrev CdtNodeId := Nat` with
  `structure CdtNodeId where val : Nat` in `Model/Object/Structures.lean`,
  matching the typed wrapper pattern used by all 15 other kernel identifiers.
- **Instance suite**: Added `DecidableEq`, `Hashable`, `LawfulHashable`,
  `EquivBEq`, `LawfulBEq`, `Repr`, `ToString`, `Inhabited`, `ofNat`/`toNat`
  conversion functions — all co-located with the type definition in
  `Structures.lean`.
- **Downstream compilation fixes**: Updated `SystemState` field defaults
  (`cdtNextNode := ⟨0⟩`), monotone allocator (`⟨node.val + 1⟩`), and test
  literals in `NegativeStateSuite.lean` to use explicit constructor syntax.
- **Documentation synchronization**: Updated all canonical sources (README,
  SELE4N_SPEC, DEVELOPMENT, WORKSTREAM_HISTORY, CLAIM_EVIDENCE_INDEX) and
  GitBook chapters (03, 04, 05, 12) to reflect WS-J1-F completion.
- **Codebase map regeneration**: `docs/codebase_map.json` regenerated with
  updated declaration counts and version.
- **Build jobs:** 140. Zero sorry/axiom. Zero warnings.
- **Closes:** WS-J1 Phase F. **WS-J1 portfolio fully completed.**

## [0.15.7] - 2026-03-14

### WS-J1-C: Audit Refinements

- **CSpace/lifecycle/VSpace dispatch**: `dispatchWithCap` now returns
  `illegalState` for operations requiring message-register data (CSpace
  mint/copy/move/delete, lifecycle retype, VSpace map/unmap). Full MR-based
  argument extraction deferred to WS-J1-E.
- **Register count parameter**: `syscallEntry` accepts `regCount : Nat`
  (default 32 for ARM64) forwarded to `decodeSyscallArgs` for architectural
  register bounds validation.
- **Strengthened capability-held theorem**: `syscallEntry_implies_capability_held`
  now proves the full chain from entry success through TCB/CSpace lookup to
  capability resolution with the required access right, composing with
  `dispatchSyscall_requires_right`.
- **Stability table**: added `syscallEntry`, `lookupThreadRegisterContext`,
  `dispatchSyscall` entries.
- **Build jobs:** 140. Zero sorry/axiom. Zero warnings.

## [0.15.6] - 2026-03-14

### WS-J1-C: Syscall Entry Point and Dispatch

- **Syscall entry point**: `syscallEntry : SyscallRegisterLayout → Nat → Kernel Unit`
  — top-level user-space entry point that reads the current thread's register
  file, decodes raw register values via `decodeSyscallArgs` (with configurable
  `regCount`, default 32), and dispatches to the appropriate capability-gated
  kernel operation.
- **Register context lookup**: `lookupThreadRegisterContext : ThreadId → Kernel
  RegisterFile` — extracts the saved register context from the current thread's
  TCB, with `objectNotFound`/`illegalState` error paths.
- **Syscall dispatch**: `dispatchSyscall : SyscallDecodeResult → ThreadId →
  Kernel Unit` — constructs a `SyscallGate` from the caller's TCB and CSpace
  root CNode, then routes through `syscallInvoke` to the appropriate internal
  kernel operation based on the decoded `SyscallId`.
- **Per-syscall routing**: `dispatchWithCap` handles all 13 modeled syscalls.
  IPC ops (send/receive/call/reply) and service ops extract the target from the
  resolved capability's `CapTarget`. CSpace ops (mint/copy/move/delete),
  lifecycle retype, and VSpace ops (map/unmap) return `illegalState` as they
  require message-register data not yet available in the decode path.
- **Right mapping**: `syscallRequiredRight : SyscallId → AccessRight` — total
  function mapping each syscall to its required access right, matching the
  authority requirements of the existing `api*` wrappers.
- **MachineConfig field**: `registerCount` promoted from computed def to
  configurable structure field with default 32 (ARM64).
- **Soundness theorems**:
  - `syscallEntry_requires_valid_decode` — successful entry implies register
    decode succeeded.
  - `syscallEntry_implies_capability_held` — successful entry implies dispatch
    succeeded (capability was resolved and authorized).
  - `dispatchSyscall_requires_right` — dispatch success implies the caller held
    a capability with the required access right for the invoked syscall.
  - `lookupThreadRegisterContext_state_unchanged` — register context lookup is
    read-only.
  - `syscallRequiredRight_total` — every syscall maps to exactly one right.
- **Build jobs:** 140. Zero sorry/axiom. Zero warnings.
- **Closes:** WS-J1 Phase C.

## [0.15.5] - 2026-03-14

### WS-J1-B: Register Decode Layer

- **Syscall decode types**: `SyscallId` inductive (13 modeled syscalls with
  injective `toNat`/total `ofNat?` encoding, round-trip and injectivity
  theorems), `MessageInfo` structure (seL4 message-info word layout with
  bit-field encode/decode), `SyscallDecodeResult` (typed decode output
  consumed by syscall dispatch).
- **Register decode functions**: `decodeCapPtr` (total, unbounded CPtr address
  space), `decodeMsgInfo` (partial, validates length/extraCaps bounds),
  `decodeSyscallId` (partial, validates against modeled syscall set),
  `validateRegBound` (per-architecture register index bounds check),
  `decodeSyscallArgs` (entry point combining all register reads and decodes).
- **Platform configuration**: `SyscallRegisterLayout` structure mapping
  hardware registers to syscall arguments, `arm64DefaultLayout` constant
  (x0=capPtr, x1=msgInfo, x2–x5=msgRegs, x7=syscallNum),
  `MachineConfig.registerCount` field.
- **KernelError variants**: `invalidRegister`, `invalidSyscallNumber`,
  `invalidMessageInfo` for explicit decode failure reporting.
- **Correctness theorems**: `decodeCapPtr_roundtrip`, `decodeSyscallId_roundtrip`
  (encode-then-decode recovery), `decodeSyscallArgs_deterministic` (pure
  determinism), `decodeSyscallId_error_iff`, `decodeMsgInfo_error_iff` (error
  exclusivity), `validateRegBound_ok_iff`/`error_iff` (bounds iff-theorems),
  `decodeCapPtr_always_ok` (universal CPtr success), `SyscallId.toNat_injective`
  (encoding injectivity).
- **New file**: `SeLe4n/Kernel/Architecture/RegisterDecode.lean` — self-contained
  module importing only `Model.State`, no kernel subsystem dependencies.
- **Build jobs:** 140. Zero sorry/axiom. Zero warnings.
- **Closes:** WS-J1 Phase B.

## [0.14.10] - 2026-03-13

### WS-I1: Critical Testing Infrastructure

- **Part A (R-01): Inter-transition invariant assertions.** Added 17
  `checkInvariants` calls across all 13 trace functions in
  `MainTraceHarness.lean`, validating scheduler, CSpace, IPC, lifecycle,
  service, VSpace, and CDT invariants after each major transition group.
  Counter-based tracking via `IO.Ref Nat` prints summary count at trace end.
  Catches state corruption (CDT orphans, ASID mismatches, queue pointer
  corruption) that would previously pass silently.
- **Part B (R-02): Mandatory determinism validation.** Created
  `scripts/test_tier2_determinism.sh` executing `lake exe sele4n` twice and
  diffing output. Integrated into `test_smoke.sh` between trace fixture and
  negative state checks. Non-determinism bugs (HashMap iteration order, random
  scheduling) now caught immediately rather than at nightly Tier 4.
- **Part C (R-03): Scenario ID traceability.** Added `[PREFIX-NNN]` tags to all
  121 trace output lines across 15 prefixes (ENT, CAT, SST, LEP, CIC, IMT,
  IMB, DDT, ICS, BME, STD, UMT, SGT, RCF, ITR, PTY). Updated fixture file to
  pipe-delimited format (`SCENARIO_ID | SUBSYSTEM | fragment`). Created
  `tests/fixtures/scenario_registry.yaml` mapping each ID to source function
  and subsystem. Added `validate-registry` subcommand to `scenario_catalog.py`
  with Tier 0 hygiene integration. Developers can now answer coverage questions
  by grepping the registry.
- **Build jobs:** 138. Zero sorry/axiom. Zero warnings.
- **Recommendations closed:** R-01, R-02, R-03.

### WS-I2: Test Coverage and Memory domain ownership

- proof/validation depth completed: Tier 0 now runs semantic L-08 theorem-body
  analysis (`scripts/check_proof_depth.py` with regex fallback), Tier 3 now runs
  Lean `#check` correctness anchors across
  scheduler/capability/IPC/lifecycle/service/VSpace/IF preservation theorems,
  and IF projection now supports optional memory-domain ownership
  (`memoryOwnership`) with backward-compatible default (`none`).

### WS-I3: Test coverage expansion —

- new tests/OperationChainSuite.lean adds 6 multi-operation chain tests
  (retype→mint→revoke, send/send/receive FIFO, map/lookup/unmap/lookup,
  service start/stop dependency sequencing, copy/move/delete,   notification
  badge accumulation), scheduler stress coverage (16-thread repeated scheduling,
  same-priority determinism, multi-domain isolation), and Tier 2 integration via
  scripts/test_tier2_negative.sh; tests/InformationFlowSuite.lean now includes
  declassification runtime checks for authorized downgrade, normal-flow rejection,
  policy-denied rejection, and 3-domain lattice behavior. Closes R-06/R-07/R-08
  Declassification policy denial now reports a distinct declassificationDenied
   error in declassifyStore and suite expectations.
   
## [0.14.9] - 2026-03-11

### WS-F5: Model Fidelity

- **F5-D1 (CRIT-06): Word-bounded badge.** `Badge.val` is now logically bounded
  to 64-bit machine word size via `machineWordBits`/`machineWordMax` constants.
  New constructors: `Badge.ofNatMasked` (truncating), `Badge.bor` (word-bounded
  OR combiner). Theorems: `ofNatMasked_valid`, `bor_valid`, `bor_comm`,
  `bor_idempotent`, `ofNat_lt_valid`. `notificationSignal` uses `Badge.bor`
  for accumulation. Updated: `badge_merge_idempotent`,
  `notificationSignal_badge_stored_fresh`, `badge_notification_routing_consistent`.
- **F5-D2 (HIGH-04): Order-independent access rights.** `Capability.rights` is
  now `AccessRightSet` (bitmask) instead of `List AccessRight`. `AccessRightSet`
  provides O(1) membership, subset, union, intersection. `ofList` converts from
  list literals; `ofList_comm` proves order-independence. `rightsSubset_sound`
  re-proved via finite enumeration. All capability operations, invariant proofs,
  information-flow wrappers, and test fixtures migrated.
- **F5-D3 (MED-03): Deferred operations documented.** `setPriority`,
  `setMCPriority`, `suspend`, `resume`, `setIPCBuffer` explicitly documented in
  API.lean deferred operations table with rationale and prerequisites. Spec
  section 5.13 added. Claim evidence index updated.
- **Prior work acknowledged:** Per-thread register context (WS-H12c, v0.14.0)
  and multi-level CSpace resolution (WS-H13, v0.14.4) were already delivered
  and are marked as completed in the refined WS-F5 plan.
- **Workstream plan refined:** Original 5-deliverable plan replaced with
  detailed 3-deliverable plan (13 sub-tasks) reflecting actual remaining scope.
- **Build jobs:** 138. Zero sorry/axiom. Zero warnings.
- **Findings closed:** CRIT-06, HIGH-04, MED-03. Prior: HIGH-01 (WS-H13),
  HIGH-02 (WS-H12c).

## [0.14.8] - 2026-03-10

### WS-H16: Testing, Documentation & Cleanup

- **Part A (M-18):** Lifecycle negative tests — 10 new `expectError` tests in
  `NegativeStateSuite.lean` exercising error branches in `lifecycleRetypeObject`
  (non-existent target, metadata mismatch, insufficient authority, bad authority
  CNode), `lifecycleRevokeDeleteRetype` (authority = cleanup, bad cleanup CNode,
  non-existent retype target), and `retypeFromUntyped` (exhausted untyped,
  non-untyped source type mismatch, device untyped restriction).
- **Part B (A-43):** Semantic Tier 3 assertions — 13 new proof-surface anchors
  in `test_tier3_invariant_surface.sh` checking structural properties:
  `capabilityInvariantBundle` conjunct count, `schedulerInvariantBundleFull`
  component inclusion, `NonInterferenceStep` constructor count,
  `objectIndexLive` and `runQueueThreadPriorityConsistent` definitions and
  theorems, `runWSH16LifecycleChecks` test function, `schedule` O(1) RunQueue
  membership.
- **Part D (A-13):** `objectIndexLive` liveness invariant — new predicate in
  `Model/State.lean` with `objectIndexLive_default` theorem and
  `storeObject_preserves_objectIndexLive` preservation proof. Ensures every
  `objectIndex` entry resolves to a live object in the store.
- **Part D (A-19):** `runQueueThreadPriorityConsistent` predicate — new
  bi-directional consistency predicate in `Scheduler/Invariant.lean` with
  `runQueueThreadPriorityConsistent_default` theorem. Formalizes the invariant
  that every RunQueue member has a `threadPriority` entry and vice versa.
- **Part D (A-18):** O(n) membership check audit — confirmed `schedule` already
  uses O(1) `HashSet`-backed `RunQueue.contains` (not the O(n) `runnable` flat
  list alias). No code change required.
- **Documentation sync (M-21/A-45):** Updated `CLAUDE.md` file-size table,
  `README.md` metrics, `WORKSTREAM_HISTORY.md`, `CHANGELOG.md`, GitBook
  proof-and-invariant map.
- **Build jobs:** 138. Zero sorry/axiom.
- **Findings closed:** M-18, A-43, A-13, A-18, A-19, M-21/A-45.

## [0.14.7] - 2026-03-10

### WS-H15a–d: Platform & API Hardening

- **WS-H15a:** Added `Decidable` instance fields (`irqLineSupportedDecidable`,
  `irqHandlerMappedDecidable`) to `InterruptBoundaryContract`, enabling
  adapter code to branch on interrupt predicates using `if` without manual
  instance threading. Updated `simInterruptContract` and `rpi5InterruptContract`.
- **WS-H15b:** RPi5 platform contract hardening:
  - Added MMIO region definitions (`mmioRegions`) with disjointness proof
    (`mmioRegionDisjoint_holds`) via `native_decide`.
  - Proved `rpi5MachineConfig_wellFormed` (region sizes, overlaps, PA bounds).
  - Replaced `True` placeholder boot predicates with substantive checks
    (empty object store, empty capability refs at boot).
  - Strengthened `rpi5InterruptContract.irqHandlerMapped` from `True` to
    handler-map lookup validation.
  - Strengthened `rpi5RuntimeContract.registerContextStable` from `True` to
    SP-preservation-or-context-switch predicate.
- **WS-H15c:** Syscall capability-checking wrappers:
  - Added `SyscallGate` structure and `syscallLookupCap`/`syscallInvoke`
    combinators implementing the seL4 CSpace-lookup + rights-check pattern.
  - 3 soundness theorems: `syscallLookupCap_implies_capability_held`,
    `syscallLookupCap_state_unchanged`, `syscallInvoke_requires_right`.
  - 13 capability-gated `api*` wrappers: `apiEndpointSend`, `apiEndpointReceive`,
    `apiEndpointCall`, `apiEndpointReply`, `apiCspaceMint`, `apiCspaceCopy`,
    `apiCspaceMove`, `apiCspaceDelete`, `apiLifecycleRetype`, `apiVspaceMap`,
    `apiVspaceUnmap`, `apiServiceStart`, `apiServiceStop`.
  - Added `retype` variant to `AccessRight` enum.
- **WS-H15a (addendum):** Decidability consistency theorems:
  `irqLineSupported_decidable_consistent` and
  `irqHandlerMapped_decidable_consistent` proving `decide` agrees with the
  underlying predicate.
- **WS-H15d:** AdapterProofHooks concrete instantiation:
  - Generic `advanceTimerState_preserves_proofLayerInvariantBundle` theorem
    proving timer advancement preserves the full 7-conjunct invariant bundle.
  - `simRestrictiveAdapterProofHooks` concrete instance for the simulation
    restrictive runtime contract with 3 end-to-end theorems
    (`simRestrictive_adapterAdvanceTimer_preserves`,
    `simRestrictive_adapterWriteRegister_preserves`,
    `simRestrictive_adapterReadMemory_preserves`).
  - `rpi5RestrictiveAdapterProofHooks` concrete instance for the RPi5
    restrictive runtime contract (`rpi5RuntimeContractRestrictive`) with 3
    end-to-end theorems. Timer advancement uses the generic preservation
    lemma substantively; register write and memory read paths are vacuous
    (restrictive contract rejects all register writes).
  - Design note: production RPi5 contract (`rpi5RuntimeContract`) admits
    all register writes (because `writeReg` never modifies `sp`), making
    `contextMatchesCurrent` preservation unprovable for arbitrary writes.
    A future context-switch-aware adapter (WS-H3) will resolve this by
    combining register-file load with `scheduler.current` update atomically.
- **WS-H15e:** Testing and documentation:
  - 31 Tier 3 invariant surface anchors covering all WS-H15 additions.
  - Syscall capability-gating trace in `MainTraceHarness.lean` (5 scenarios:
    correct gate, bad root, insufficient rights, missing cap, retype gate).
  - 6 negative tests in `NegativeStateSuite.lean` exercising syscall
    capability-checking error paths.
  - 7 platform contract tests validating `rpi5MachineConfig.wellFormed`,
    `mmioRegionDisjointCheck`, GIC-400 IRQ boundary values (INTID 0, 223, 224),
    and boot contract predicates.
  - Stability table in `API.lean` updated with all 13 `api*` syscall wrappers.
  - Regenerated `docs/codebase_map.json`.
- **Build jobs:** 138 (up from 134). Zero sorry/axiom.

## [0.14.5] - 2026-03-10

### Codebase Module Restructuring

- **Module decomposition:** Decomposed 9 large monolithic files (1,000–5,800
  lines each) into 24 focused submodule files using the re-export hub pattern.
  Original files preserved as thin import hubs for full backward compatibility.
- **Model/Object.lean** → `Object/Types.lean` (core data types) +
  `Object/Structures.lean` (VSpaceRoot, CNode, KernelObject, CDT helpers).
- **Scheduler/Operations.lean** → `Operations/Selection.lean` (EDF predicates) +
  `Operations/Core.lean` (core transitions) +
  `Operations/Preservation.lean` (preservation theorems).
- **IPC/DualQueue.lean** → `DualQueue/Core.lean` (dual-queue operations) +
  `DualQueue/Transport.lean` (transport lemmas).
- **IPC/Operations.lean** → `Operations/Endpoint.lean` (core endpoint ops) +
  `Operations/SchedulerLemmas.lean` (scheduler preservation lemmas).
- **IPC/Invariant.lean** → `Invariant/Defs.lean` + `Invariant/EndpointPreservation.lean` +
  `Invariant/CallReplyRecv.lean` + `Invariant/NotificationPreservation.lean` +
  `Invariant/Structural.lean`.
- **Capability/Invariant.lean** → `Invariant/Defs.lean` + `Invariant/Authority.lean` +
  `Invariant/Preservation.lean`.
- **InformationFlow/Invariant.lean** → `Invariant/Helpers.lean` +
  `Invariant/Operations.lean` + `Invariant/Composition.lean`.
- **InformationFlow/Enforcement.lean** → `Enforcement/Wrappers.lean` +
  `Enforcement/Soundness.lean`.
- **Service/Invariant.lean** → `Invariant/Policy.lean` + `Invariant/Acyclicity.lean`.
- **Private definition visibility:** ~53 cross-module `private` definitions
  made non-private to support submodule access across file boundaries.
  Post-decomposition audit re-privatized 15 definitions that were only used
  within their own submodule file (11 CNode helper theorems, 4 projection
  preservation lemmas), tightening the API surface.
- **Tier 3 invariant surface tests:** Updated 209 anchor checks to reference
  new submodule file paths.
- **Build jobs:** Increased from 86 to 134 (finer-grained parallelism).
- **Zero sorry/axiom:** No regressions — all proof surface remains complete.

## [0.14.4] - 2026-03-10

### WS-H13: CSpace, Lifecycle & Service Model Enrichment

- **CSpace depth-consistency invariant (`cspaceDepthConsistent`):** Added to
  `capabilityInvariantBundle` as the 8th conjunct, ensuring every CNode has
  `depth ≤ maxCSpaceDepth` and well-formedness when `bitsConsumed > 0`. All
  preservation proofs updated for the expanded 8-tuple.
- **Multi-level `resolveCapAddress` theorems (Part A):**
  - `resolveCapAddress_deterministic` — pure function determinism.
  - `resolveCapAddress_zero_bits` — zero-bits returns `.error .illegalState`.
  - `resolveCapAddress_result_valid_cnode` — success implies the returned slot
    reference points to a valid CNode in the object store (proved by
    well-founded induction on `bitsRemaining`).
  - `resolveCapAddress_guard_reject` — guard mismatch at any CNode level
    returns `.error .invalidCapability` (attack surface coverage).
- **Service backing-object verification (Part C / A-29):**
  - `serviceStop` now verifies `st.objects[svc.identity.backingObject]? ≠ none`
    before allowing the transition. Returns `.backingObjectMissing` if absent.
  - Added `serviceStop_error_backingObjectMissing` theorem.
  - Updated `serviceStop_error_policyDenied` to require backing-object
    existence hypothesis.
  - All `serviceStop_preserves_*` theorems updated for the new branch.
  - `serviceStart` backing check already present from prior work.
- **`serviceGraphInvariant` preservation proofs (Part E / M-17):**
  - `serviceGraphInvariant` bundle (`serviceDependencyAcyclic ∧
    serviceCountBounded`) with preservation for `serviceRegisterDependency`,
    `serviceStart`, and `serviceStop`.
  - Added transfer lemmas: `serviceEdge_of_storeServiceState_sameDeps`,
    `serviceNontrivialPath_of_storeServiceState_sameDeps`,
    `serviceDependencyAcyclic_of_storeServiceState_sameDeps`,
    `bfsUniverse_of_storeServiceState_sameDeps`,
    `serviceCountBounded_of_storeServiceState_sameDeps`,
    `serviceGraphInvariant_of_storeServiceState_sameDeps`.
- **Capability move atomicity (Part B / A-21):**
  - `cspaceMove_error_no_state` — error-path exclusion: on error, no success
    state is reachable.
  - `cspaceMove_ok_implies_source_exists` — success-path: if move succeeds,
    the source slot had a valid capability.
  - Documented that the sequential kernel's `Except` monad provides implicit
    both-or-neither semantics: on error, no intermediate state is returned.
- **CNode field migration:** Updated `NegativeStateSuite.lean` CNode
  constructions from old `guard`/`radix` fields to new `depth`/`guardWidth`/
  `guardValue`/`radixWidth` fields.
- **Default-state proof updated:** `default_capabilityInvariantBundle` in
  `Architecture/Invariant.lean` extended to 8-tuple with
  `cspaceDepthConsistent` component.
- **`docs/codebase_map.json` regenerated.**
- **New negative tests (WS-H13):**
  - `MainTraceHarness`: service start with missing backing object
    (`backingObjectMissing` error).
  - `NegativeStateSuite`: `runWSH13Checks` — backing-object missing and
    restart start-stage failure (dependency violation).
- **Expected fixture updated:** `tests/fixtures/main_trace_smoke.expected`
  updated with 1 new output line (110 total).
- **Zero sorry/axiom, zero warnings.** Build: 86 jobs, zero errors.
- **All tests pass:** `test_full.sh` (Tier 0-3) clean.
- **Findings addressed:** H-01 (multi-level CSpace resolution), A-29 (service
  backing-object verification), A-21 (capability move atomicity), A-30
  (service restart implicit rollback via error monad), M-17/A-31
  (`serviceCountBounded` invariant).

## [0.14.3] - 2026-03-09

### WS-H12f: Test Harness Update & Documentation Sync

- **Dequeue-on-dispatch trace scenario:** Added `runDequeueOnDispatchTrace` to
  `MainTraceHarness.lean` exercising the full dequeue-on-dispatch lifecycle:
  schedule selects highest-priority thread and dequeues it from `runQueue`,
  non-dispatched thread remains in queue, and after preemption (timer tick
  expiry) the preempted thread is re-enqueued while a higher-priority thread
  takes over.
- **Inline context switch trace scenario:** Added `runInlineContextSwitchTrace`
  demonstrating that `handleYield` → `schedule` saves the outgoing thread's
  `machine.regs` into its TCB `registerContext` and restores the incoming
  thread's `registerContext` into `machine.regs`, establishing
  `contextMatchesCurrent` atomically.
- **Bounded message extended trace scenario:** Added
  `runBoundedMessageExtendedTrace` verifying boundary behavior: zero-length
  messages accepted, sub-boundary messages (119 registers) accepted, and
  max-cap messages (3 caps) accepted — complementing the existing WS-H12d
  rejection tests.
- **Legacy `endpointInvariant` comment cleanup:** Removed stale comments in
  `IPC/Invariant.lean` referencing the deleted legacy endpoint fields (`state`,
  `queue`, `waitingReceiver`) and `endpointQueueWellFormed`. Updated
  preservation theorem docstrings to reference `ipcInvariant` (notification
  well-formedness) instead of the removed `endpointInvariant`.
- **Expected fixture updated:** `tests/fixtures/main_trace_smoke.expected`
  updated to include all 11 new trace output lines (108 total, up from 98).
- **Tier 3 invariant surface anchors:** Added 9 new anchors to
  `test_tier3_invariant_surface.sh` for WS-H12f trace functions and fixture
  output lines.
- **Documentation synchronized:** CHANGELOG, SELE4N_SPEC, DEVELOPMENT,
  CLAIM_EVIDENCE_INDEX, codebase_map.json, README, and GitBook chapters
  updated to reflect WS-H12f completion and WS-H12 composite closure.
- **`docs/codebase_map.json` regenerated.**
- **Zero sorry/axiom, zero warnings.** Build: 86 jobs, zero errors.
- **Findings addressed:** Documentation component of all WS-H12 findings
  (A-08/M-01/A-25, H-04, H-03, A-09). Completes WS-H12 composite workstream.

## [0.14.2] - 2026-03-09

### WS-H12e: Cross-Subsystem Invariant Reconciliation

- **`schedulerInvariantBundleFull` expanded:** Added `contextMatchesCurrent`
  (from WS-H12c) as the 5th conjunct to the full scheduler invariant bundle.
  Previously the register-context coherence invariant was defined and preserved
  but orphaned from all composition bundles.
- **`coreIpcInvariantBundle` strengthened:** Updated from `ipcInvariant` to
  `ipcInvariantFull` (which composes `ipcInvariant ∧ dualQueueSystemInvariant ∧
  allPendingMessagesBounded`). The M3 seed bundle now includes dual-queue
  structural well-formedness and message payload bounds in the cross-subsystem
  proof surface.
- **`ipcSchedulerCouplingInvariantBundle` extended:** Added
  `contextMatchesCurrent` and `currentThreadDequeueCoherent` to the M3.5
  coupling bundle, ensuring register-context coherence and dequeue-on-dispatch
  predicates are composed into the cross-subsystem invariant.
- **`proofLayerInvariantBundle` upgraded:** Uses `schedulerInvariantBundleFull`
  (5-conjunct, with `contextMatchesCurrent`) instead of the bare
  `schedulerInvariantBundle` (3-conjunct). The top-level architecture proof
  surface now includes all WS-H12a–d invariant additions.
- **Extraction theorems:** Added `coreIpcInvariantBundle_to_ipcInvariant`,
  `coreIpcInvariantBundle_to_dualQueueSystemInvariant`,
  `coreIpcInvariantBundle_to_allPendingMessagesBounded`, and
  `schedulerInvariantBundleFull_to_contextMatchesCurrent` for backward-compatible
  proof composition.
- **`switchDomain_preserves_contextMatchesCurrent`:** New preservation theorem
  for `contextMatchesCurrent` through domain switches (vacuous when
  `current = none` after switch, unchanged in single-domain no-op).
- **Default state proof updated:** `default_system_state_proofLayerInvariantBundle`
  extended with proofs for `dualQueueSystemInvariant`, `allPendingMessagesBounded`,
  `contextMatchesCurrent`, `currentThreadDequeueCoherent`, and
  `schedulerInvariantBundleFull` on the default (empty) system state.
- **`contextMatchesCurrent` relocated:** Moved definition before
  `schedulerInvariantBundleFull` in `Scheduler/Invariant.lean` to resolve
  forward-reference issue in bundle composition.
- **Preservation theorem updates:** Updated all 4 `*_preserves_schedulerInvariantBundleFull`
  theorems (`schedule`, `handleYield`, `timerTick`, `switchDomain`) to include
  `contextMatchesCurrent` in destructuring and construction.
  Updated `lifecycleRetypeObject_preserves_coreIpcInvariantBundle` and
  `lifecycleRetypeObject_preserves_lifecycleCompositionInvariantBundle` for
  the enriched bundle signatures.
- **`allPendingMessagesBounded` frame lemmas:** Added 8 primitive-operation
  frame lemmas (`ensureRunnable`, `removeRunnable`, `storeTcbIpcState`,
  `storeTcbIpcStateAndMessage`, `storeTcbPendingMessage`, `storeObject_endpoint`,
  `storeTcbQueueLinks`, `storeObject_notification`) proving each operation
  preserves the `allPendingMessagesBounded` system invariant.
- **Compound `allPendingMessagesBounded` preservation:** Added
  `notificationSignal_preserves_allPendingMessagesBounded`,
  `notificationWait_preserves_allPendingMessagesBounded`, and
  `endpointReply_preserves_allPendingMessagesBounded` — full proofs composing
  frame lemmas for multi-step IPC operations.
- **Composed `ipcInvariantFull` preservation theorems:** Added 7 theorems
  (`notificationSignal`, `notificationWait`, `endpointReply`,
  `endpointSendDual`, `endpointReceiveDual`, `endpointCall`,
  `endpointReplyRecv`) each proving preservation of the full 3-conjunct
  `ipcInvariantFull` bundle.
- **Tier 3 invariant surface anchors:** Updated `coreIpcInvariantBundle` body
  anchor from `ipcInvariant` to `ipcInvariantFull`. Added 30 new anchors for
  WS-H12e invariant definitions, extraction theorems, frame lemmas, compound
  preservation theorems, and composed `ipcInvariantFull` preservation proofs.
- **`docs/codebase_map.json` regenerated.**
- **Zero sorry/axiom, zero warnings:** Full production proof surface verified
  clean. Build produces 86 jobs, zero errors and zero warnings.
- **Findings addressed:** Systemic invariant composition gaps from WS-H12a–d.
  Completed deferred `allPendingMessagesBounded` preservation from WS-H12d.

## [0.14.1] - 2026-03-09

### WS-H12d: IPC Message Payload Bounds

- **Bounded IPC message type:** Replaced unbounded `List Nat` / `List Capability`
  in `IpcMessage` with bounded `Array Nat` / `Array Capability`, matching seL4's
  `seL4_MsgMaxLength` (120) and `seL4_MsgMaxExtraCaps` (3) limits.
- **Message size constants:** Added `maxMessageRegisters` (120) and `maxExtraCaps`
  (3) to `Model/Object.lean`, matching seL4's standard configuration.
- **Bounds enforcement at send boundaries:** All four IPC send operations
  (`endpointSendDual`, `endpointCall`, `endpointReply`, `endpointReplyRecv`)
  and the policy-checked `endpointSendDualChecked` now validate payload size
  before proceeding. Oversized payloads return `ipcMessageTooLarge` or
  `ipcMessageTooManyCaps` errors.
- **New error variants:** Added `KernelError.ipcMessageTooLarge` and
  `KernelError.ipcMessageTooManyCaps` for bounds violation reporting.
- **`IpcMessage.bounded` predicate:** Formal proposition asserting registers
  and caps satisfy seL4 bounds. `IpcMessage.checkBounds` provides decidable
  runtime checking. `checkBounds_iff_bounded` bridges the two.
- **Send-produces-bounded-message theorems:** Proved `endpointSendDual_message_bounded`,
  `endpointCall_message_bounded`, `endpointReply_message_bounded`, and
  `endpointReplyRecv_message_bounded` — if the operation succeeds, the message
  satisfies `IpcMessage.bounded`.
- **`allPendingMessagesBounded` system invariant:** Added to `IPC/Invariant.lean`,
  asserting all pending messages in TCBs satisfy payload bounds. Integrated into
  `ipcInvariantFull` 3-conjunct bundle (ipcInvariant ∧ dualQueueSystemInvariant ∧
  allPendingMessagesBounded) — preservation theorems implemented in WS-H12e.
- **Enforcement theorem updates:** Updated `endpointSendDualChecked_flowDenied`
  to require `msg.checkBounds = true` (bounds checks precede flow checks).
  Updated `enforcement_sufficiency_endpointSendDual` to include bounds-error
  cases in the complete disjunction. Updated `enforcementSoundness_endpointSendDualChecked`
  with bounds-check elimination.
- **~40 invariant preservation proofs updated:** All IPC/capability/info-flow
  preservation theorems that unfold send operations now handle the new
  bounds-check if-branches via contradiction (error ≠ ok).
- **Trace verification:** Added 5 H12d trace scenarios verifying oversized
  registers/caps rejection, boundary acceptance, and cross-operation coverage.
- **Negative tests:** Added 10 negative tests in `NegativeStateSuite` for all
  four IPC send operations with oversized registers and oversized caps, plus
  boundary-exact message acceptance.
- **Zero sorry/axiom, zero warnings:** Full production proof surface verified
  clean. Build produces zero errors and zero warnings.
- **Finding closed:** A-09 (HIGH, IpcMessage unbounded payload).

## [0.14.0] - 2026-03-09

### WS-H12c: Per-TCB Register Context with Inline Context Switch

- **Per-TCB register save area:** Added `registerContext : RegisterFile`
  field to TCB structure (`Model/Object.lean`), with `default` initialization.
  Each thread now carries its own register file, matching seL4's per-TCB
  `tcbContext` (ARM `user_context_t`).
- **Inline context save/restore in `schedule`:** `schedule` now performs
  `saveOutgoingContext` (saves `machine.regs` into the outgoing TCB's
  `registerContext`) and `restoreIncomingContext` (loads the incoming TCB's
  `registerContext` into `machine.regs`) directly inline, matching seL4's
  `switchToThread` → `Arch_switchToThread` → `vcpu_switch`/`setVMRoot`
  context-switch path.
- **`saveOutgoingContext`/`restoreIncomingContext` functions:** Public
  definitions with `@[simp]` frame lemmas proving scheduler/objects
  preservation, enabling downstream proof automation.
- **`contextMatchesCurrent` invariant:** Added to `Scheduler/Invariant.lean`
  — states that `st.machine.regs = tcb.registerContext` when a thread is
  current, formalizing the register-context coherence property.
- **`endpointInvariant` removal:** Completely removed the deprecated
  `endpointInvariant` predicate and all references from `IPC/Invariant.lean`,
  `Capability/Invariant.lean`, and `Architecture/Invariant.lean`. Simplifies
  `ipcInvariant` to its essential predicates.
- **Information-flow projection update:** Modified `projectKernelObject` in
  `Projection.lean` to strip `registerContext` from TCBs (replacing with
  `default`), ensuring register contents don't leak through the information-flow
  projection.
- **Projection preservation proofs:** Added `saveOutgoingContext_preserves_projection`,
  `restoreIncomingContext_preserves_projection`, and
  `saveOutgoingContext_with_sched_preserves_projection` theorems in
  `InformationFlow/Invariant.lean`, proving context switch preserves
  low-equivalence.
- **Frame lemma suite:** Added `saveOutgoingContext_preserves_tcb`,
  `saveOutgoingContext_tcb_fields`, `saveOutgoingContext_preserves_non_tcb_lookup`,
  `saveOutgoingContext_preserves_timeSlicePositive`, and
  `restoreIncomingContext_preserves_timeSlicePositive`.
- **Scheduler preservation proofs:** Added `schedule_preserves_contextMatchesCurrent`,
  `handleYield_preserves_contextMatchesCurrent`, `timerTick_preserves_contextMatchesCurrent`,
  and `contextMatchesCurrent_frame` general frame theorem to `Scheduler/Operations.lean`.
- **IPC preservation proofs:** Added `storeObject_preserves_contextMatchesCurrent`,
  `storeTcbIpcState_preserves_contextMatchesCurrent`,
  `storeTcbIpcStateAndMessage_preserves_contextMatchesCurrent`,
  `storeTcbPendingMessage_preserves_contextMatchesCurrent`,
  `storeTcbQueueLinks_preserves_contextMatchesCurrent`,
  `ensureRunnable_preserves_contextMatchesCurrent`, and
  `removeRunnable_preserves_contextMatchesCurrent` to `IPC/Invariant.lean`.
- **Trace verification:** Added context switch trace scenario to `MainTraceHarness`
  verifying `machine.regs` matches the incoming thread's `registerContext` after
  `schedule`.
- **Zero sorry/axiom, zero warnings:** Full production proof surface verified
  clean. Build produces zero errors and zero warnings.
- **Finding closed:** H-03 (HIGH, no per-TCB register context).

## [0.13.9] - 2026-03-09

### WS-H12b: Dequeue-on-Dispatch Scheduler Semantics

- **Scheduler invariant inversion:** Changed `queueCurrentConsistent` from
  `current = some tid → tid ∈ runnable` to `current = some tid → tid ∉ runnable`,
  matching seL4's `switchToThread`/`tcbSchedDequeue` dequeue-on-dispatch
  semantics where the running thread is removed from the ready queue at
  dispatch time.
- **`schedule` dequeue-on-dispatch:** `schedule` now dequeues the chosen
  thread from the run queue before dispatching via `setCurrentThread`,
  mirroring seL4's `switchToThread` → `tcbSchedDequeue` path.
- **`handleYield` re-enqueue:** Since the current thread is not in the run
  queue, `handleYield` now inserts the current thread and rotates to back
  before calling `schedule`, matching seL4's `handleYield` →
  `tcbSchedDequeue` + `tcbSchedAppend` path.
- **`timerTick` re-enqueue on preemption:** On time-slice expiry,
  `timerTick` inserts the current thread back into the run queue before
  scheduling, mirroring seL4's `timerInterrupt` → `rescheduleRequired` →
  `tcbSchedEnqueue` → `schedule` path.
- **`switchDomain` re-enqueue:** `switchDomain` re-enqueues the current
  thread before the domain switch so the outgoing thread returns to the
  runnable pool for its next domain slot.
- **`currentTimeSlicePositive` predicate:** Added predicate to ensure the
  current thread's time slice is positive (not covered by `timeSlicePositive`
  since the current thread is no longer in the run queue).
  `schedulerInvariantBundleFull` extended to include `currentTimeSlicePositive`.
- **`schedulerPriorityMatch` predicate:** Added predicate and supporting
  theorems `RunQueue.insert_preserves_wellFormed` and
  `insert_threadPriority` for priority consistency.
- **IPC invariant updates:** Added `currentThreadIpcReady`,
  `currentNotEndpointQueueHead`, `currentNotOnNotificationWaitList`, and
  `currentThreadDequeueCoherent` predicates to `IPC/Invariant.lean`.
  Updated 23 cross-subsystem proof sites.
- **Information-flow invariant updates:** Updated 5 error sites in
  `InformationFlow/Invariant.lean` with new helper theorems for the
  inverted scheduler semantics.
- **Helper lemmas:** Added `ensureRunnable_not_mem_of_not_mem` and
  `removeRunnable_not_mem_of_not_mem` to `Scheduler/Operations.lean`;
  added `ThreadId.ext` theorem to `Prelude.lean`.
- **Test invariant checker:** Updated `Testing/InvariantChecks.lean` to
  verify dequeue-on-dispatch semantics at runtime.
- **~1800 lines of preservation proofs** re-proved across
  `Scheduler/Operations.lean`, `IPC/Invariant.lean`, and
  `InformationFlow/Invariant.lean`.
- **Finding closed:** H-04 (HIGH, running thread stays in ready queue).

## [0.13.8] - 2026-03-09

### WS-H12a: Legacy Endpoint Field & Operation Removal

- **Legacy endpoint fields removed:** Deleted `EndpointState` inductive type
  and three legacy fields (`state`, `queue`, `waitingReceiver`) from the
  `Endpoint` structure. Endpoint now contains only `sendQ`/`receiveQ`
  intrusive queues.
- **Legacy IPC operations deleted:** Removed `endpointSend`,
  `endpointAwaitReceive`, `endpointReceive` from `IPC/Operations.lean` and
  `endpointSendChecked` from `InformationFlow/Enforcement.lean`. All IPC now
  uses exclusively the O(1) dual-queue path (`endpointSendDual`/
  `endpointReceiveDual`).
- **Legacy KernelOperation entries removed:** Deleted `endpointSend`,
  `endpointAwaitReceive`, `endpointReceive` from `KernelOperation` inductive
  and `TransitionSurface` in `Architecture/Assumptions.lean`.
- **Legacy theorem cleanup:** Deleted ~60 legacy preservation theorems from
  `IPC/Invariant.lean`, `Capability/Invariant.lean`,
  `InformationFlow/Invariant.lean`, and `InformationFlow/Enforcement.lean`
  that proved preservation for deleted operations.
- **endpointInvariant rewrite:** Redefined `endpointInvariant` as vacuous
  (`True`) for structural compatibility. Actual dual-queue well-formedness
  is enforced system-wide via `dualQueueSystemInvariant` (per-endpoint
  `dualQueueEndpointWellFormed` + `tcbQueueLinkIntegrity`).
- **endpointReplyRecv fix:** Migrated `endpointReplyRecv` from legacy
  `endpointAwaitReceive` to `endpointReceiveDual`, completing the dual-queue
  transition for all compound IPC operations.
- **Test migration:** `NegativeStateSuite`, `InformationFlowSuite`, and
  `TraceSequenceProbe` updated to use dual-queue operations exclusively.
  All endpoint fixtures use only `sendQ`/`receiveQ` fields.
- **Tier-3 anchor updates:** Removed stale legacy anchors from
  `test_tier3_invariant_surface.sh`; updated counts and added new
  dual-queue-only anchors.
- **Findings closed:** A-08 (HIGH, redundant legacy endpoint fields), M-01
  (MEDIUM, redundant legacy endpoint fields), A-25 (MEDIUM, legacy O(n) IPC
  retained without deprecation path).

## [0.13.7] - 2026-03-08

### WS-H11: VSpace & Architecture Enrichment

- **Part A — PagePermissions & W^X enforcement:** `PagePermissions` struct with
  `wxCompliant` predicate; W^X enforced at insertion time in `vspaceMapPage`;
  enriched mappings `HashMap VAddr (PAddr × PagePermissions)` with
  `vspaceLookupFull` returning permissions alongside physical address.
- **Part B — Address bounds check:** `vspaceMapPageChecked` rejects physical
  addresses ≥ 2^52 (ARM64 52-bit PA bound); `physicalAddressBound` constant;
  `addressOutOfBounds` error variant; preservation theorem
  `vspaceMapPageChecked_success_preserves_vspaceInvariantBundle`.
- **Part C — ASID uniqueness & consistency:** `asidTableConsistent` and
  `vspaceAsidRootsUnique` in the 5-conjunct `vspaceInvariantBundle`;
  `resolveAsidRoot` extraction and characterization lemmas.
- **Part D — TLB/cache maintenance model:** `TlbEntry`, `TlbState`,
  `adapterFlushTlb`, `adapterFlushTlbByAsid`, `tlbConsistent`; abstract TLB
  model with full and per-ASID flush operations proven correct.
- **VSpaceBackend typeclass:** Platform-agnostic VSpace operations abstraction
  with `hashMapVSpaceBackend` instance; prepares for ARM page table backend.
- **ASID table composition:** Explicit `resolveAsidRoot` agreement theorems
  for `vspaceMapPage` and `vspaceUnmapPage`, proving ASID table consistency
  is preserved through page table modifications.
- **TLB selectivity:** `adapterFlushTlbByAsid_removes_matching` and
  `adapterFlushTlbByAsid_preserves_other` theorems proving per-ASID flush
  removes exactly matching entries and preserves all others.
- **Per-VAddr TLB flush:** `adapterFlushTlbByVAddr` operation (ARM64 `TLBI VAE1`)
  with preservation, selectivity, and composition theorems; targeted flush for
  single page table entry modifications.
- **Cross-ASID TLB isolation:** `cross_asid_tlb_isolation` theorem proving
  per-ASID flush on one ASID does not affect TLB entries belonging to a
  different ASID — key security property for multi-address-space systems.
- **Proof deduplication:** Extracted `VSpaceRoot.mapPage_mappings_insert`,
  `VSpaceRoot.unmapPage_mappings_erase`, and `HashMap_lookup_of_erase_lookup`
  helper lemmas, reducing duplicated proof code in VSpaceInvariant.lean.
- **Testing:** 19+ new negative-state tests covering W^X, address bounds, ASID
  errors, TLB flush (full, per-ASID, per-VAddr), permission round-trip,
  cross-ASID isolation, multiple concurrent mappings, and map-unmap-remap
  cycles; 3 new MainTraceHarness traces (VSPACE-05..07).

## [0.13.6] - 2026-03-08

### End-to-End Codebase Audit

- **Comprehensive audit:** Full end-to-end audit of all 40 production Lean
  files (29,351 LoC), 866 theorem/lemma declarations, 3 test suites (2,063
  LoC), build scripts, platform bindings, and documentation. Zero critical
  issues found. Zero sorry/axiom confirmed across the entire codebase.
- **A-v13.6-01 (MEDIUM): Stale theorem count in spec.** Fixed
  `docs/spec/SELE4N_SPEC.md` theorem count from 833 to 866.
- **A-v13.6-02 (MEDIUM): Stale metrics in gitbook.** Fixed
  `docs/gitbook/17-project-usage-value.md` LoC from 26,194 to 29,351 and
  theorem count from 753 to 866.
- **A-v13.6-06 (LOW): Stale milestone reference.** Fixed milestone
  progression reference from "WS-B..F" to "WS-B..H" in gitbook.
- **Documentation sync:** Updated README.md, SELE4N_SPEC.md, DEVELOPMENT.md,
  CLAIM_EVIDENCE_INDEX.md, and 5 GitBook chapters with audit workstream
  entry, latest audit reference, and corrected metrics.
- **Audit report:** Created `docs/audits/AUDIT_CODEBASE_v0.13.6.md` with
  detailed findings across all subsystems, security property verification,
  performance characteristic confirmation, and test coverage assessment.

### WS-H10: Security Model Foundations

- **C-05/A-38 (CRITICAL): MachineState projection in IF model.** Extended
  `ObservableState` with `machineRegs : Option RegisterFile` — the machine
  register file is projected through current-thread observability gating
  (visible only when the executing thread is observable). Machine timer is
  deliberately excluded to prevent covert timing channels. Machine memory
  projection deferred to WS-H11 (VSpace domain ownership model required).
  All 863 proved declarations updated — zero sorry/axiom.
- **A-34 (CRITICAL): Security lattice resolution.** Added formal threat model
  justification documenting the legacy integrity model as a valid "write-up"
  policy. Introduced `bibaIntegrityFlowsTo`, `bibaSecurityFlowsTo`, and
  `bibaPolicy` as standard BIBA alternatives with reflexivity/transitivity
  proofs. Added `securityLattice_reflexive` and `securityLattice_transitive`
  alias theorems confirming the legacy lattice forms a valid pre-order.
- **A-39 (MEDIUM): Declassification model.** Added `DeclassificationPolicy`
  structure with `canDeclassify` predicate, `DeclassificationPolicy.none`
  (strictest policy), and `isDeclassificationAuthorized` (base policy denial +
  declass authorization). Added `declassifyStore` operation in Enforcement.lean
  with 5 theorems: authorization equivalence, normal-flow rejection,
  declass-denied rejection, state preservation on denial, and enforcement
  soundness.
- **M-16 (MEDIUM): Endpoint flow policy well-formedness.** Added
  `endpointFlowPolicyWellFormed` predicate requiring both global and per-
  endpoint override policies to satisfy reflexivity + transitivity. Added
  `endpointFlowPolicyWellFormed_no_overrides`, `endpointFlowCheck_reflexive`,
  and `endpointFlowCheck_transitive` theorems.
- **Declassification NI theorem (C.10).** Added `declassifyStore_NI` — proves
  that declassification at a non-observable target preserves low-equivalence
  for non-target observers (the key NI property for controlled downgrade).
- **IF configuration invariant bundle.** Added `InformationFlowConfigInvariant`
  structure collecting global policy well-formedness, per-endpoint override
  well-formedness, and declassification consistency. Added
  `defaultConfigInvariant` existence proof. Kernel transitions trivially
  preserve the bundle since policies are external to `SystemState`.
- **Strengthened `declassifyStore_denied_no_state_change`.** Replaced
  the previously trivial (`True`) state preservation theorem with a proper
  proof that no successful result exists when the operation returns an error.
- **Version bump:** `lakefile.toml` version updated to 0.13.6.
- **Documentation sync:** Updated README.md, SELE4N_SPEC.md, DEVELOPMENT.md,
  CLAIM_EVIDENCE_INDEX.md, and GitBook chapters with current metrics and
  WS-H10 completion.
- **866 proved declarations. Zero sorry/axiom. Zero warnings. `test_full.sh` passes.**

## [0.13.5] - 2026-03-08

### Comprehensive Audit Remediation & WS-H Completion

- **WS-H8 gap closure:** Added `endpointReceiveDualChecked_NI` bridge theorem
  connecting the enforcement-checked receive wrapper to non-interference
  guarantees. All 5 enforced operations now have complete NI bridge theorems.
- **WS-H9 IPC NI completion:** Added `endpointReceiveDual_preserves_lowEquivalent`,
  `endpointCall_preserves_lowEquivalent`, and
  `endpointReplyRecv_preserves_lowEquivalent` theorems using the hypothesis-based
  bridge pattern. These close the remaining ~6% gap in NI coverage.
- **NonInterferenceStep extended to 31 constructors:** Added
  `endpointReceiveDualHigh`, `endpointCallHigh`, and `endpointReplyRecvHigh`
  constructors with projection preservation hypotheses. Up from 28 constructors.
- **WS-H7 BEq soundness lemmas:** Added `VSpaceRoot.beq_sound` and
  `CNode.beq_sound` theorems proving the fold-based HashMap comparison extracts
  correct structural fields (ASID, size, guard, radix).
- **Version bump:** `lakefile.toml` version updated to 0.13.5.
- **Documentation sync:** Updated README.md (28,713 LoC, 840 theorems), CLAUDE.md
  (large file sizes), SELE4N_SPEC.md, DEVELOPMENT.md, CLAIM_EVIDENCE_INDEX.md,
  and 5 GitBook chapters (overview, spec/roadmap, audit/quality, proof map,
  threat model) with current metrics, WS-H9 completion, and corrected next
  workstream references (WS-H10..H16).
- **Codebase map regenerated** to reflect new declarations.
- **840 proved declarations. Zero sorry/axiom. Zero warnings. `test_full.sh` passes.**

## [0.13.4] - 2026-03-07

### WS-H9: Non-Interference Coverage Extension

- **NI coverage extended from ~25% to >80% (C-02/A-40 CRITICAL):** Added 27
  new non-interference preservation theorems covering scheduler, IPC, CSpace,
  VSpace, and observable-state operations. Total NI theorems in
  `Invariant.lean`: 69 (up from ~19). Proof surface covers all kernel
  transitions that modify security-relevant state.
- **NonInterferenceStep inductive extended to 28 constructors (M-15 MEDIUM):**
  Up from 11 constructors. Covers: `chooseThread`, `endpointSend`,
  `cspaceMint`, `cspaceRevoke`, `lifecycleRetype`, `notificationSignal`,
  `notificationWait`, `cspaceInsertSlot`, `serviceStart`, `serviceStop`,
  `serviceRestart`, `schedule`, `vspaceMapPage`, `vspaceUnmapPage`,
  `vspaceLookup`, `cspaceCopy`, `cspaceMove`, `cspaceDeleteSlot`,
  `endpointReply`, `storeObjectHigh`, `setCurrentThread`,
  `ensureRunnableHigh`, `removeRunnableHigh`,
  `storeTcbIpcStateAndMessageHigh`, `storeTcbQueueLinksHigh`,
  `cspaceMutateHigh`, `handleYield`, `timerTick`.
- **Scheduler NI proofs (Part A):** `schedule_preserves_projection` (with
  high-current and all-runnable-high side conditions),
  `setCurrentThread_preserves_projection`,
  `ensureRunnable_preserves_projection`,
  `removeRunnable_preserves_projection`,
  `rotateToBack_preserves_projection`,
  `handleYield_preserves_projection` / `_lowEquivalent`,
  `insert_tick_preserves_projection`,
  `timerTick_preserves_projection` / `_lowEquivalent`.
- **IPC NI proofs (Part B):** `endpointReply_preserves_projection` /
  `_lowEquivalent`, `storeTcbIpcStateAndMessage_preserves_projection`,
  `storeTcbQueueLinks_preserves_projection`,
  `storeTcbPendingMessage_preserves_projection`.
- **CSpace NI proofs (Part C):** `cspaceCopy_preserves_projection` /
  `_lowEquivalent`, `cspaceMove_preserves_projection` / `_lowEquivalent`,
  `cspaceDeleteSlot_preserves_projection` / `_lowEquivalent`,
  `cspaceMutate` handled via `cspaceMutateHigh` constructor.
- **VSpace NI proofs (Part D):** `vspaceMapPage_preserves_projection` /
  `_lowEquivalent`, `vspaceUnmapPage_preserves_projection` /
  `_lowEquivalent`, `vspaceLookup_preserves_state` / `_lowEquivalent`.
- **Observable-state NI (Part E):** `storeObject_preserves_projection`,
  `storeCapabilityRef_preserves_projection`, CDT-only helpers
  (`cdt_only_preserves_projection`, `ensureCdtNodeForSlot_preserves_projection`,
  `attachSlotToCdtNode_preserves_projection`).
- **switchDomain two-sided NI (Part A supplement):**
  `switchDomain_preserves_lowEquivalent` — domain switching modifies scheduler
  globals so one-sided projection is NOT preserved, but two-sided
  low-equivalence IS preserved since both states see the same domain change.
- **RunQueue filter_erase_of_false fix:** Corrected Bool/Prop coercion in
  `SeLe4n/Kernel/Scheduler/RunQueue.lean`.
- **827 proved declarations. Zero sorry/axiom. `test_full.sh` passes.**

## [0.13.3] - 2026-03-07

### WS-H6: EDF Scheduler Proof Completion

- **EDF bridge theorem completed (A-14/H-06 CRITICAL):** `chooseBestInBucket_edf_bridge` —
  proves that `chooseBestInBucket` result is EDF-optimal among all domain-eligible
  runnable threads at the same priority level. Handles both bucket-success and
  full-scan-fallback paths using RunQueue well-formedness and priority-match
  external predicates.
- **RunQueue well-formedness predicate (H-06):** `RunQueue.wellFormed` — external
  predicate capturing the implicit invariant maintained by insert/remove/rotate
  API: forward (bucket→membership+threadPriority) and reverse
  (membership→bucket) consistency.
- **RunQueue well-formedness lemmas (H-06):** `maxPriorityBucket_subset`,
  `maxPriorityBucket_threadPriority`, `mem_maxPriorityBucket_of_threadPriority`
  — bridge lemmas connecting well-formedness to bucket-first EDF scheduling.
- **Rotation preserves well-formedness (H-06):** `rotateToBack_preserves_wellFormed`
  and 6 field-preservation lemmas (`rotateToBack_membership`,
  `rotateToBack_threadPriority`, `rotateToBack_maxPriority`,
  `rotateToBack_contains`, `rotateToBack_mem_iff`,
  `rotateToBack_flat_subset`, `rotateToBack_flat_superset`) — proves that
  `rotateToBack` preserves `wellFormed` and all RunQueue structural fields.
- **External priority-match predicate (H-06):** `schedulerPriorityMatch` —
  bridges RunQueue's internal `threadPriority` to authoritative TCB priority
  in the object store.
- **Full EDF preservation chain (H-06):**
  `schedule_preserves_edfCurrentHasEarliestDeadline`,
  `handleYield_preserves_edfCurrentHasEarliestDeadline`,
  `timerTick_preserves_edfCurrentHasEarliestDeadline` — all sorry-free.
- **Full bundle composition (H-06):**
  `schedule_preserves_schedulerInvariantBundleFull`,
  `handleYield_preserves_schedulerInvariantBundleFull`,
  `timerTick_preserves_schedulerInvariantBundleFull`.
- **Fold result membership lemma (H-06):**
  `chooseBestRunnableBy_result_mem_aux` and `chooseBestRunnableBy_result_mem` —
  proves that `chooseBestRunnableBy` result is drawn from the scanned list.
- **Zero sorry/axiom.** `test_full.sh` passes (Tier 0-3).

## [0.13.2] - 2026-03-07

### WS-H8: Enforcement-NI Bridge & Missing Wrappers

- **Enforcement-NI bridge connected (A-35/H-07 CRITICAL):** Added enforcement
  soundness meta-theorems (`enforcementSoundness_endpointSendDualChecked`,
  `enforcementSoundness_notificationSignalChecked`,
  `enforcementSoundness_cspaceCopyChecked`,
  `enforcementSoundness_cspaceMoveChecked`,
  `enforcementSoundness_endpointReceiveDualChecked`) proving that checked
  operation success implies the `securityFlowsTo` check passed. These form the
  foundational bridge connecting the enforcement layer to non-interference
  hypotheses.
- **4 new enforcement wrappers (H-07 HIGH):** `notificationSignalChecked`,
  `cspaceCopyChecked`, `cspaceMoveChecked`, `endpointReceiveDualChecked` —
  each gates on `securityFlowsTo` before delegating to the unchecked operation.
  Enforcement boundary extended from 3 to 8 policy-gated operations.
- **NI bridge theorems:** `endpointSendDualChecked_NI`,
  `notificationSignalChecked_NI`, `cspaceCopyChecked_NI`,
  `cspaceMoveChecked_NI` — each proves that if the checked wrapper succeeds,
  low-equivalence is preserved (cspaceCopy/Move take underlying NI as
  hypothesis pending WS-H9 decomposition lemmas).
- **Projection hardening (A-36/A-37/H-11 HIGH):** Extended `ObservableState`
  with `domainTimeRemaining`, `domainSchedule`, `domainScheduleIndex` fields.
  Added projection helpers and updated all 19 NI theorems in Invariant.lean.
  `activeDomain` kept always-visible as deliberate scheduling transparency.
- **Correctness theorems:** `*_eq_*_when_allowed` (4), `*_flowDenied` (4),
  `*_denied_preserves_state` (4), `enforcement_sufficiency_*` (4) for all
  new wrappers.
- **Extended enforcement boundary:** `enforcementBoundaryExtended` — 8
  policy-gated operations (up from 3 in `enforcementBoundary`).
- **Test coverage:** 12 new executable tests in `InformationFlowSuite.lean`
  covering same-domain match, cross-domain denial, boundary classification,
  and domain timing metadata projection.
- **26 new theorems.** Zero sorry/axiom. `test_full.sh` passes (Tier 0-3).
  779 proved theorems total.

## [0.13.1] - 2026-03-07

### WS-H6: Scheduler Proof Completion (partial)

- **Time-slice positivity fully proven (A-15/H-08 CRITICAL):** Added preservation
  theorems for `timeSlicePositive` across all scheduler operations:
  `setCurrentThread_preserves_timeSlicePositive`,
  `chooseThread_preserves_timeSlicePositive`,
  `schedule_preserves_timeSlicePositive`,
  `handleYield_preserves_timeSlicePositive`,
  `switchDomain_preserves_timeSlicePositive`,
  `timerTick_preserves_timeSlicePositive`. Previously defined but with zero proofs.
- **Candidate selection optimality proven (A-17/M-05/M-06 HIGH):**
  `isBetterCandidate_transitive` (strict partial order completion),
  `isBetterCandidate_not_better_trans` (negation transitivity),
  `chooseBestRunnableBy_optimal_combined` and `chooseBestRunnableBy_optimal`
  (fold-based selection produces no strictly better alternative).
- **EDF invariant definition fixed (A-14 design gap):**
  `edfCurrentHasEarliestDeadline` previously quantified over all runnable threads
  regardless of scheduling domain, which was unprovable for the domain-aware
  scheduler. Added `tcb.domain = curTcb.domain` constraint to align the invariant
  with `chooseBestRunnableInDomain` semantics.
- **EDF bridge lemma:** `noBetter_implies_edf` — converts `isBetterCandidate = false`
  at equal priority to the deadline-comparison form used by the EDF invariant.
- **EDF trivial preservation:** `setCurrentThread_none_preserves_edfCurrentHasEarliestDeadline`,
  `switchDomain_preserves_edfCurrentHasEarliestDeadline`.
- **Full scheduler bundle:** `schedulerInvariantBundleFull` (5-tuple extending the
  structural triad with `timeSlicePositive` and `edfCurrentHasEarliestDeadline`),
  `schedulerInvariantBundleFull_to_base` (projection),
  `switchDomain_preserves_schedulerInvariantBundleFull` (composition).
- **Refactoring:** Extracted `threadId_ne_objId_beq_false` helper to deduplicate
  recurring ObjId inequality proofs in `timerTick_preserves_timeSlicePositive`.
  Made `noBetter_implies_edf` private (internal bridge lemma).
- **Linker hardening:** Added CRT startup file verification (`crti.o`, `crt1.o`,
  `Scrt1.o`) to `setup_lean_env.sh` with automatic toolchain re-download on
  incomplete extraction. Prevents `ld: cannot find crti.o` linker errors.
- **14 new theorems.** Zero sorry/axiom. `test_full.sh` passes (Tier 0-3).
  753 proved theorems total.

## [0.13.0] - 2026-03-03

### WS-H5 audit: documentation sync and Tier 3 surface anchors

- **Documentation sync:** Fixed stale version and metric references across 7 documentation files — SELE4N_SPEC.md theorem count (575 -> 627), GitBook README/navigation_manifest version (0.12.15 -> 0.12.19), development workflow WS-H reference (H1..H3 -> H1..H5), kernel performance chapter theorem count (400+ -> 627), project usage value LoC/module/theorem counts (16,485/34/400+ -> 21,340/40/627).
- **Tier 3 invariant surface anchors:** Added 18 WS-H5 anchor checks to `test_tier3_invariant_surface.sh` covering all 5 predicate definitions (`intrusiveQueueWellFormed`, `tcbQueueLinkIntegrity`, `dualQueueEndpointWellFormed`, `dualQueueSystemInvariant`, `ipcInvariantFull`), 5 safety/closure theorems (A-23/A-24), and 8 preservation theorems for all dual-queue operations.
- **Testing milestone:** Added WS-H5 bullet to `07-testing-and-ci.md` milestone testing trajectory.
- **Zero sorry/axiom.** `test_full.sh` passes (Tier 0-3). 627 proved theorems total.

## [0.12.19] - 2026-03-03

### WS-H5: IPC Dual-Queue Structural Invariant (completed)

- **C-04 / A-22 (CRITICAL): Formal well-formedness predicate for intrusive dual-queue IPC.** The dual-queue structure (`sendQ`/`receiveQ`, TCB `queueNext`/`queuePrev`/`queuePPrev` linkage) previously had zero formal well-formedness guarantees. Defined `intrusiveQueueWellFormed` (head/tail emptiness iff, head has prev=none, tail has next=none, TCB existence) and `dualQueueEndpointWellFormed` composing both queues. Integrated as `dualQueueSystemInvariant` covering all endpoints and `tcbQueueLinkIntegrity` (doubly-linked forward/reverse consistency).
- **A-23 (HIGH): Link dereference safety in `endpointQueuePopHead`.** Under `dualQueueSystemInvariant`, `headTcb.queueNext` is guaranteed to be either `none` (tail) or a valid TCB. Proved via `endpointQueuePopHead_preserves_dualQueueSystemInvariant`.
- **A-24 (HIGH): Message lookup after dequeue.** Under `dualQueueSystemInvariant`, the TCB existence guarantee ensures `lookupTcb` after `popHead` succeeds. Proved via `endpointReceiveDual_preserves_dualQueueSystemInvariant`.
- **Predicate definitions in `IPC/Invariant.lean`:** `intrusiveQueueWellFormed`, `dualQueueEndpointWellFormed`, `tcbQueueLinkIntegrity`, `dualQueueSystemInvariant`.
- **13 preservation theorems:** `ensureRunnable_preserves_dualQueueSystemInvariant`, `removeRunnable_preserves_dualQueueSystemInvariant`, `storeTcbIpcState_preserves_dualQueueSystemInvariant`, `storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant`, `storeTcbPendingMessage_preserves_dualQueueSystemInvariant`, `endpointReply_preserves_dualQueueSystemInvariant`, `endpointAwaitReceive_preserves_dualQueueSystemInvariant`, `endpointReplyRecv_preserves_dualQueueSystemInvariant`, `endpointQueuePopHead_preserves_dualQueueSystemInvariant`, `endpointQueueEnqueue_preserves_dualQueueSystemInvariant`, `endpointSendDual_preserves_dualQueueSystemInvariant`, `endpointReceiveDual_preserves_dualQueueSystemInvariant`, `endpointCall_preserves_dualQueueSystemInvariant`.
- **Helper infrastructure:** `storeTcbQueueLinks_result_tcb`, `storeTcbQueueLinks_preserves_iqwf`, `storeTcbQueueLinks_clearing_preserves_linkInteg`, `storeTcbQueueLinks_none_prevnext_preserves_linkInteg` — transport lemmas for queue link mutations.
- **Zero sorry/axiom.** `test_full.sh` passes (Tier 0-3). 627 proved theorems total.

## [0.12.18] - 2026-03-02

### WS-H4: Capability Invariant Redesign (completed)

- **capabilityInvariantBundle extended from 4-tuple to 7-tuple (C-03 CRITICAL):** The `capabilityInvariantBundle` previously contained only `cspaceSlotUnique ∧ cspaceLookupSound ∧ cspaceAttenuationRule ∧ lifecycleAuthorityMonotonicity` — all trivially true or structural. Replaced with a meaningful 7-conjunct bundle adding: `cspaceSlotCountBounded` (every CNode has bounded slot count), `cdtCompleteness` (every CDT node-slot mapping references an existing object), and `cdtAcyclicity` (CDT derivation forest is well-founded via path-based acyclicity).
- **New predicates in Model/Object.lean:** `CNode.slotCountBounded` (slot count ≤ maxCNodeSlots), `CapDerivationTree.edgeWellFounded` (no non-empty path from a node to itself), `edgeWellFounded_sub` (edge-subset preserves well-foundedness), `removeNode_edges_sub` (removeNode produces edge subset), `CNode.remove_slotCountBounded` and `CNode.revokeTargetLocal_slotCountBounded` (CNode operations preserve bounds).
- **New predicates in Capability/Invariant.lean:** `cspaceSlotCountBounded st`, `cdtCompleteness st`, `cdtAcyclicity st` — formalized as quantified propositions over system state.
- **Transfer theorem infrastructure:** Added ~20 helper theorems for propagating the 3 new predicates through state transitions: `cspaceSlotCountBounded_of_objects_eq`, `cdtCompleteness_of_storeObject`, `cdtAcyclicity_of_cdt_eq`, `cdtPredicates_through_blocking_path`, `cdtPredicates_through_handshake_path`, `cdtPredicates_through_reply_path`, `cdtPredicates_of_detachSlotFromCdt`, `boundedCompleteness_of_cdt_only_update`, `capabilityInvariantBundle_of_cdt_update`, and more.
- **All preservation theorems re-proved:** Every `_preserves_capabilityInvariantBundle` theorem (cspaceInsertSlot, cspaceMint, cspaceCopy, cspaceMove, cspaceMintWithCdt, cspaceMutate, cspaceDeleteSlot, cspaceRevoke, revokeCdtFoldBody, revokeCdtFold, endpointReply, endpointSend, endpointReceive, endpointAwaitReceive, lifecycleRetypeObject, storeServiceState) re-proved against the non-trivial 7-conjunct bundle.
- **CDT-modifying operations:** For `cspaceCopy`, `cspaceMove`, `cspaceMintWithCdt` (which add CDT edges that could break acyclicity), cdtCompleteness and cdtAcyclicity of the post-state are taken as hypotheses. For CDT-shrinking operations (removeNode in revoke), acyclicity is proven via `edgeWellFounded_sub` and `removeNode_edges_sub`.
- **CNode insertion operations:** A `hSlotCapacity` / `hDstCapacity` hypothesis added to `cspaceInsertSlot`, `cspaceMint`, `cspaceCopy`, `cspaceMove`, `cspaceMintWithCdt`, `cspaceMutate` since no HashMap size_insert lemma is available.
- **Downstream callers updated:** Architecture/Invariant.lean default-state proofs, Service/Invariant.lean `storeServiceState_preserves`, and lifecycle composition theorems all updated for the 7-tuple.
- **Zero sorry/axiom.** `test_full.sh` passes (Tier 0-3).

### WS-H4 refinement: audit, optimization, and documentation sync

- **Architecture/Invariant.lean proof deduplication:** Extracted `default_capabilityInvariantBundle` helper theorem, eliminating 4x duplication of the 7-tuple default-state construction in `default_system_state_proofLayerInvariantBundle`.
- **API.lean M-08/A-20 annotation:** Added untracked-capability warning to `cspaceMint` API table entry — capabilities created via the non-CDT mint path are not tracked by CDT-based revocation; `cspaceMintWithCdt` should be preferred for tracked derivation.
- **Docstring refinements:** Updated `cdtCompleteness` docstring to clarify node-slot reachability scope vs. spec-intended mint-based completeness. Updated `capabilityInvariantBundle` docstring with WS-H4 design decision rationale (hCdtPost hypothesis pattern, edgeWellFounded_sub strategy, slotsUnique retention).
- **GitBook sync:** Updated 6 GitBook chapters (01-project-overview, 05-specification-and-roadmap, 07-testing-and-ci, 12-proof-and-invariant-map, 19-end-to-end-audit, 22-next-slice-development-path) with WS-H4 completion references, bundle redefinition details, and transfer theorem documentation.
- **Spec/CLAUDE.md sync:** Updated `SELE4N_SPEC.md` portfolio table, `CLAUDE.md` workstream context, and `docs/DEVELOPMENT.md` with WS-H4 (v0.12.18) completion status.

## [0.12.17] - 2026-03-02

### WS-H3: Build/CI Infrastructure Fixes (completed)

- **run_check return value fix (H-12 HIGH):** `run_check` in `scripts/test_lib.sh` previously fell through to an implicit `return 0` after recording a failure when `CONTINUE_MODE=1`, causing callers to receive success even on failure. Fixed by adding explicit `return 1` in the failure path. In continue mode, `set -e` is now disabled after `parse_common_args` so that `run_check` can return non-zero without aborting the script; failure tracking is managed by `record_failure`/`finalize_report`.
- **Documentation sync CI integration (M-19 MEDIUM):** `test_docs_sync.sh` was previously available only as a standalone local tool. Now integrated into both the `test_smoke.sh` entrypoint (local runs) and the `lean_action_ci.yml` smoke CI job (automated PR checks). Documentation navigation/link drift is now caught automatically on every PR.
- **Tier 3 rg availability guard (M-20 MEDIUM):** `test_tier3_invariant_surface.sh` has ~440 `rg` invocations. Previously, a missing `rg` produced hundreds of command-not-found errors. Added a guard at script entry that checks for `rg` availability. If absent, a `grep -P` fallback shim is created on PATH (handling both direct calls and `bash -lc` subshell invocations). If neither `rg` nor `grep -P` is available, the script fails with a single clear diagnostic message.
- **Full integration:** `test_full.sh` passes (Tier 0-3). Zero sorry/axiom.

### WS-H2/B-5: Lifecycle hFresh Auto-Derivation (audit gap closure)

- **retypeFromUntyped_ok_childId_ne:** New theorem proving `childId ≠ untypedId` is automatically derivable from successful `retypeFromUntyped` execution (H-06 self-overwrite guard).
- **retypeFromUntyped_ok_childId_fresh:** New theorem proving childId freshness among existing untyped children is automatically derivable from successful `retypeFromUntyped` execution (A-27 collision guard).
- **retypeFromUntyped_preserves_untypedMemoryInvariant_auto:** New auto-derivation wrapper that eliminates the manual `hNe` and `hFresh` proof obligations from `retypeFromUntyped_preserves_untypedMemoryInvariant`. Callers need only supply the invariant precondition, new-object well-formedness, and success hypothesis — both safety conditions are derived from the operation semantics.
- **Documentation updates:** GitBook chapters updated to v0.12.17 (19-end-to-end-audit, 22-next-slice-development-path, 07-testing-and-ci, README). Audit lineage table extended with WS-H portfolio entry. Theorem count updated to 575+.

## [0.12.16] - 2026-03-02

### WS-H1: IPC Call-Path Semantic Fix (completed)

- **blockedOnCall IPC state (C-01 CRITICAL):** Added `blockedOnCall` variant to `ThreadIpcState` enum in `Model/Object.lean`. A Call sender blocked on the send queue now carries `blockedOnCall endpointId` (distinct from `blockedOnSend endpointId`), signaling that upon dequeue by `endpointReceiveDual`, the sender transitions to `blockedOnReply` (not `.ready`). This fixes the semantic bug where a blocked Call sender was erroneously unblocked as if it were a plain Send, violating the Call contract.
- **Receiver-side call/send dispatch (C-01):** `endpointReceiveDual` now inspects the dequeued sender's `ipcState` to determine post-dequeue transition: `blockedOnCall` senders transition to `blockedOnReply` (caller stays blocked awaiting reply), while plain `blockedOnSend` senders transition to `.ready` (sender unblocked). The `let senderWasCall` conditional dispatches between the two paths.
- **Reply-target scoping (M-02 MEDIUM):** Added optional `replyTarget : Option ThreadId` field to the `blockedOnReply` state, recording which server thread is authorized to reply. `endpointReply` and `endpointReplyRecv` now validate that the replier matches `replyTarget` (when set), preventing confused-deputy attacks where any thread could reply to any blocked caller.
- **endpointCall updates:** Blocking path uses `blockedOnCall endpointId` instead of `blockedOnSend`; handshake path populates `blockedOnReply endpointId (some receiver)` with the receiver's ThreadId.
- **ipcSchedulerContractPredicates expanded:** Predicate bundle extended from 3 to 5 conjuncts with `blockedOnCallNotRunnable` and `blockedOnReplyNotRunnable`, ensuring threads in call/reply blocking states are not in the runnable queue.
- **Invariant proof maintenance:** All IPC invariant preservation theorems re-proved for the updated state transitions, including `endpointReceiveDual` dual-path proofs (call path and send path), `endpointCall` blocking/handshake proofs, and all `endpointReplyRecv` chain proofs.
- **Trace and test coverage:** Updated trace harness with WS-H1 blocking-path scenarios (H1-01 through H1-05) verifying call/reply lifecycle. Updated `NegativeStateSuite` pattern matches for the new `blockedOnReply` signature.
- **Code quality refinement:** Refactored `endpointReply` to use `let authorized := ...` pattern matching `endpointReplyRecv`, eliminating duplicated reply-delivery logic. Consolidated dual `lookupTcb` calls in `endpointReceiveDual` into a single lookup returning `(senderMsg, senderWasCall)`. Proof duplication in `endpointReply_preserves_ipcSchedulerContractPredicates` and `endpointReply_preserves_capabilityInvariantBundle` eliminated via `suffices` abstraction.
- **Full proof migration:** zero sorry/axiom across all modified files. `test_full.sh` passes (Tier 0-3).

### WS-H2: Lifecycle Safety Guards (completed)

- **childId self-overwrite guard (H-06 CRITICAL):** `retypeFromUntyped` now rejects calls where `childId = untypedId`, preventing the untyped object from being overwritten by its own child. Returns new `KernelError.childIdSelfOverwrite` error.
- **childId collision guards (A-26/A-27 HIGH):** `retypeFromUntyped` rejects calls where `childId` collides with an existing object in `st.objects` or with an existing child in the untyped's `children` list. Returns new `KernelError.childIdCollision` error.
- **TCB retype scheduler cleanup (H-05 CRITICAL):** New `cleanupTcbReferences` helper removes a TCB's ThreadId from the scheduler run queue before retype. New `detachCNodeSlots` helper clears CDT slot mappings when a CNode is replaced by a non-CNode object. Both composed in `lifecyclePreRetypeCleanup`.
- **Safe retype wrapper (H-05):** `lifecycleRetypeWithCleanup` wraps `lifecyclePreRetypeCleanup` + `lifecycleRetypeObject`, providing the recommended entry point with safety guarantees. Original `lifecycleRetypeObject` is unchanged to preserve all downstream invariant proofs.
- **Theorem: no dangling runnable after TCB retype:** `lifecycleRetypeWithCleanup_ok_runnable_no_dangling` proves that after a successful TCB retype via the safe wrapper, the old ThreadId is not in the run queue.
- **Atomic retype (A-28):** `retypeFromUntyped` computes both the updated untyped and the new child object before any state mutation, preventing partial-update inconsistencies.
- **Preservation proofs:** Field-orthogonality theorems for all cleanup operations (`*_objects_eq`, `*_lifecycle_eq`, `*_scheduler_eq`). Fold induction proofs for `detachCNodeSlots` CDT traversal.
- **Trace coverage:** F2-09/F2-10 trace scenarios for childId guards, LIFE-10 scenario for `lifecycleRetypeWithCleanup` with TCB cleanup verification. 3 new scenario catalog entries.
- **Negative test coverage:** H2-NEG-01 through H2-NEG-03 in `NegativeStateSuite.lean` testing childIdSelfOverwrite, childIdCollision (existing object), and childIdCollision (untyped child).
- **Full proof migration:** zero sorry/axiom. `test_smoke.sh` passes (86/86 trace, all negative checks).

## [0.12.15] - 2026-03-02

### WS-G Refinement: Scheduler optimization, validation hardening, and audit coverage expansion

- **RunQueue.remove bucket precomputation (WS-G4 refinement):** `RunQueue.remove` previously computed the filtered bucket twice — once for `byPriority` update and once for `maxPriority` update. Refactored to compute the filtered bucket once and reuse for both, eliminating redundant `List.filter` evaluation on every thread removal. Structural invariant documentation added explaining the implicit `membership` ↔ `threadPriority` consistency maintained by the insert/remove API.
- **MachineConfig.wellFormed page-size validation hardened:** Added `isPowerOfTwo` helper using bitwise characterization (`n > 0 ∧ n &&& (n - 1) == 0`). `MachineConfig.wellFormed` now validates `pageSize` as a positive power of two instead of merely positive, catching misconfigured platforms with non-standard page sizes (e.g., `pageSize = 3`).
- **Dead code removal:** Removed unused `filterByDomain` function from `Scheduler/Operations.lean` — dead code since WS-G4 replaced domain filtering with bucket-first scheduling via `chooseBestInBucket`. Added performance documentation note to `schedule` explaining the O(n) `List.Mem` membership check vs deferred O(1) HashSet alternative.
- **Phantom object cleanup:** Removed phantom object ID 200 from `bootstrapInvariantObjectIds` in `MainTraceHarness.lean` — this ID had no corresponding object in the bootstrap state and added false positive invariant check passes.
- **Runtime invariant checks expanded:** Added `runQueueThreadPriorityConsistentB` verifying that every thread in the RunQueue flat list has a corresponding `threadPriority` entry (structural API safety net). Added `cdtChildMapConsistentCheck` verifying bidirectional consistency between `CapDerivationTree.childMap` HashMap and `edges` list (both forward and backward directions).
- **StateBuilder TCB priority integration (WS-G4 fix):** `BootstrapBuilder.build` now uses actual TCB priorities from the builder's object list for RunQueue bucketing via `lookupThreadPriority`, instead of defaulting all threads to priority 0. This ensures test states have correctly bucketed run queues matching their thread priority configuration.
- **Audit test coverage expansion:** Added `runAuditCoverageChecks` to `NegativeStateSuite.lean` with comprehensive `endpointReplyRecv` coverage (2 negative checks: non-existent target, target not in blockedOnReply state; 1 positive flow via endpointCall→endpointReplyRecv chain verifying caller unblock) and `cspaceMutate` coverage (2 negative checks: non-existent CNode, rights escalation; 2 positive checks: rights attenuation, badge override).
- **Full proof migration:** zero sorry/axiom across all 7 modified files. `test_full.sh` passes (Tier 0-3).

## [0.12.14] - 2026-03-01

### WS-G9: Information-Flow Projection Optimization (completed)

- **Precomputed observable set (F-P09):** `projectState` previously evaluated `objectObservable` redundantly across `projectObjects`, `projectIrqHandlers`, and `projectObjectIndex` — repeated `securityFlowsTo` label comparisons for every object at each sub-projection call site. New `computeObservableSet` builds a `Std.HashSet ObjId` via single `foldl` pass over `st.objectIndex`; `projectObjectsFast`, `projectIrqHandlersFast`, `projectObjectIndexFast` now use O(1) `contains` lookups instead of re-evaluating `objectObservable`.
- **`@[csimp]`-ready design:** Original `projectState` definition kept unchanged to preserve all existing non-interference proofs in `Invariant.lean` (1448 lines, untouched). New `projectStateFast` is an optimized alternative with `projectObjectsFast`, `projectIrqHandlersFast`, `projectObjectIndexFast` — all using the precomputed HashSet. Top-level equivalence theorem `projectStateFast_eq` proves `projectStateFast = projectState` under standard state synchronization invariants, ready for `@[csimp]` compiler substitution.
- **HashSet bridge lemmas:** 3 new `List.foldl` monotonicity/preservation lemmas in `Prelude.lean`: `foldl_preserves_contains`, `foldl_not_contains_when_absent`, `foldl_preserves_when_pred_false`. Core induction lemma `foldl_observable_set_mem` in `Projection.lean` proves membership equivalence for the observable set.
- **Zero downstream proof breakage:** All non-interference theorems, enforcement wrappers, and invariant proofs remain unchanged. `projectState` definition is untouched; `projectStateFast` provides the performance path.
- **Full proof migration:** zero sorry/axiom across all 2 modified files. `test_full.sh` passes (Tier 0-3).
- Closes finding F-P09 (information-flow projection redundant observability evaluation).

## [0.12.13] - 2026-03-01

### WS-G8: Graph Traversal Optimization (completed)

- **Service dependency DFS with HashSet (Phase A / F-P08):** `serviceHasPathTo` rewritten from O(n²) BFS with `List ServiceId` visited set to O(n+e) DFS with `Std.HashSet ServiceId`. Visited-set membership checks now O(1) amortized. Frontier ordering changed from BFS (`rest ++ newDeps`) to DFS (`newDeps ++ rest`) for stack-friendly traversal. Three HashSet bridge lemmas added to `Prelude.lean`: `HashSet_contains_insert_iff`, `HashSet_not_contains_insert`, `HashSet_contains_insert_self`.
- **CDT childMap index (Phase B / F-P14):** `CapDerivationTree` extended with `childMap : Std.HashMap CdtNodeId (List CdtNodeId)` parent-indexed edge index. `childrenOf` rewritten from O(E) edge-list scan to O(1) HashMap lookup. `descendantsOf` BFS complexity reduced from O(N×E) to O(N+E). `addEdge`, `removeAsChild`, `removeAsParent`, `removeNode` all maintain `childMap` alongside `edges`.
- **Consistency invariant:** `childMapConsistent` defines bidirectional correspondence between `childMap` and `edges`. `empty_childMapConsistent` and `addEdge_childMapConsistent` proved; `edges` remains the proof anchor.
- **Invariant proofs re-proved:** `bfsClosed`, `bfsClosed_init`, `bfsClosed_skip`, `bfsClosed_expand`, `bfs_boundary_lemma`, `filter_vis_decrease`, `go_tgt_eq`, `go_skip_eq`, `go_expand_eq`, `go_complete`, `bfs_complete_for_nontrivialPath` all migrated to HashSet-based visited set in `Service/Invariant.lean`.
- **Test infrastructure updated:** `NegativeStateSuite.lean` CDT construction migrated from raw struct literals to `addEdge` API calls, ensuring `childMap` consistency.
- **Full proof migration:** zero sorry/axiom across all 5 modified files. `test_full.sh` passes (Tier 0-3).
- Closes findings F-P08 (service dependency BFS O(n²)) and F-P14 (CDT descendantsOf BFS O(N×E)).

## [0.12.12] - 2026-03-01

### WS-G7: IPC Queue Completion & Notification (completed)

- **Legacy endpoint deprecation (Phase A / F-P04):** Trace harness and sequence probe migrated from legacy `endpointSend`/`endpointReceive`/`endpointAwaitReceive` to O(1) dual-queue `endpointSendDual`/`endpointReceiveDual`. Legacy operations marked deprecated with docstring annotations. New `endpointSendDualChecked` enforcement wrapper provides information-flow gating for the dual-queue send path, matching the legacy `endpointSendChecked` pattern.
- **Notification wait optimization (Phase B / F-P11):** `notificationWait` O(n) duplicate check `waiter ∈ ntfn.waitingThreads` replaced with O(1) TCB `ipcState` check via `lookupTcb`. O(n) append `ntfn.waitingThreads ++ [waiter]` replaced with O(1) prepend `waiter :: ntfn.waitingThreads`.
- **New `notificationWaiterConsistent` invariant:** Bridges TCB `ipcState` to notification queue membership, ensuring the O(1) TCB-based duplicate check is sound. Bridge lemma `not_mem_waitingThreads_of_ipcState_ne` enables `uniqueWaiters` preservation under prepend. Base case `default_notificationWaiterConsistent` proved. Runtime `notificationWaiterConsistentChecks` added to invariant check surface with Tier-3 anchor.
- **Invariant proofs re-proved:** `notificationWait_preserves_uniqueWaiters`, `notificationWait_preserves_ipcInvariant`, `notificationWait_preserves_schedulerInvariantBundle`, `notificationWait_preserves_ipcSchedulerContractPredicates` all re-proved against new O(1) logic. `notificationWait_recovers_pending_badge` (Capability) and `notificationWait_projection_preserved` (InformationFlow) updated for `lookupTcb` match structure.
- **`endpointSendDualChecked` enforcement:** New checked dual-queue send in `Enforcement.lean` with correctness theorems `endpointSendDualChecked_eq_endpointSendDual_when_allowed` and `endpointSendDualChecked_flowDenied`.
- **API stability table updated:** Legacy `endpointSend`/`endpointReceive`/`endpointAwaitReceive` and `endpointSendChecked` marked `Deprecated (WS-G7)`. `endpointSendDualChecked` added as stable entry point.
- **Structured fixture updated:** Trace fixture migrated to dual-queue output (IPC-03 updated, legacy-only IPC-05/IPC-06 removed). Tier-3 surface anchors updated for `endpointReceiveDual`.
- **Full proof migration:** zero sorry/axiom across all 9 modified files. `test_full.sh` passes (Tier 0-3).
- Closes findings F-P04 (legacy endpoint queue O(n) append) and F-P11 (notification duplicate wait O(n) check).

## [0.12.11] - 2026-03-01

### WS-G6: VSpace Mapping HashMap (completed)

- **VSpace mapping HashMap migration:** `VSpaceRoot.mappings` changed from `List (VAddr × PAddr)` to `Std.HashMap VAddr PAddr`. All page lookups (`VSpaceRoot.lookup`), inserts (`VSpaceRoot.mapPage`), and erasures (`VSpaceRoot.unmapPage`) now O(1) amortized instead of O(m) linear scan.
- **`noVirtualOverlap` trivially true:** HashMap enforces key uniqueness by construction. `noVirtualOverlap` reformulated from list membership to `lookup`-based semantics. Universal `noVirtualOverlap_trivial` theorem proves the property for *all* VSpaceRoots; `noVirtualOverlap_empty`, `mapPage_noVirtualOverlap`, and `unmapPage_noVirtualOverlap` delegate to it.
- **Round-trip theorems re-proved:** `lookup_mapPage_eq`, `lookup_unmapPage_eq_none`, `lookup_mapPage_ne`, `lookup_unmapPage_ne` all re-proved using `HashMap_getElem?_insert`/`HashMap_getElem?_erase` bridge lemmas. `lookup_eq_none_iff` replaces `lookup_eq_none_not_mem` with bidirectional HashMap membership characterization.
- **BEq instance:** Manual `BEq VSpaceRoot` (entry-wise HashMap comparison) replaces lost `DecidableEq VSpaceRoot` derivation, matching the `BEq CNode` pattern from WS-G5.
- **VSpaceBackend updated:** `listVSpaceBackend` renamed to `hashMapVSpaceBackend`; docstring updated to reflect HashMap backing.
- **`boundedAddressTranslation` reformulated:** From list membership `(v, p) ∈ root.mappings` to HashMap lookup `root.mappings[v]? = some p`.
- **Test infrastructure updated:** `MainTraceHarness.lean`, `NegativeStateSuite.lean` use `mappings := {}` for VSpaceRoot construction. All test suites pass (Tier 0-3).
- **Full proof migration:** zero sorry/axiom across all 7 modified files. `test_full.sh` passes (Tier 0-3).
- Closes finding F-P05 (VSpace mapping linear scan).

## [0.12.10] - 2026-03-01

### WS-G5: CNode Slot HashMap (completed)

- **CNode slot HashMap migration:** `CNode.slots` changed from `List (Slot × Capability)` to `Std.HashMap Slot Capability`. All capability lookups (`CNode.lookup`), inserts (`CNode.insert`), and deletes (`CNode.remove`) now O(1) amortized instead of O(m) linear scan.
- **`slotsUnique` invariant trivially true:** HashMap enforces key uniqueness by construction. `CNode.slotsUnique` redefined as `True`, and all three preservation theorems (`insert_slotsUnique`, `remove_slotsUnique`, `revokeTargetLocal_slotsUnique`) now prove `trivial`.
- **Bridge lemmas:** `HashMap_filter_preserves_key` (single-filter key preservation for `revokeTargetLocal`) and `HashMap_filter_filter_getElem?` (double-filter idempotency for projection) in `Prelude.lean`. Both avoid `Std.HashMap`'s `Option.pfilter` dependent types by working at the membership level.
- **Projection idempotency reformulated:** `projectKernelObject_idempotent` in `Projection.lean` reformulated from structural equality to slot-level lookup equality, because `Std.HashMap.filter` reverses internal `AssocList` bucket ordering making `(m.filter f).filter f ≠ m.filter f` structurally.
- **BEq instances for runtime tests:** Manual `BEq CNode` (entry-wise HashMap comparison) and `BEq KernelObject` instances replace the lost `DecidableEq KernelObject` derivation.
- **CSpace invariant proofs migrated:** `cspaceRevoke_local_target_reduction` rewritten with HashMap-level reasoning (`mem_filter`, `getKey_beq`, `getElem_filter`). `cspaceLookupSound_of_cspaceSlotUnique` simplified (HashMap lookup is direct). `revokedRefs` computed via `HashMap.fold` in a single O(m) pass (no intermediate `.toList` allocation).
- **Test infrastructure updated:** `InvariantChecks.lean` uses `cn.slots.toList.foldr`. `MainTraceHarness.lean` and all test suites use `Std.HashMap.ofList` for CNode construction. `InformationFlowSuite.lean` uses `cn.slots.contains` for O(1) key-existence checks and `cn.slots.size` for slot counts.
- **Full proof migration:** zero sorry/axiom across all 10 modified files. `test_full.sh` passes (Tier 0-3).
- Closes finding F-P03 (CNode slot linear scan).

## [0.12.9] - 2026-03-01

### WS-G4: Run Queue Restructure (completed)

- **Priority-bucketed RunQueue:** New `RunQueue` structure in `Scheduler/RunQueue.lean` replaces flat `List ThreadId` runnable queue. Backed by `Std.HashMap Priority (List ThreadId)` for priority bucketing, `Std.HashSet ThreadId` for O(1) membership, and `Std.HashMap ThreadId Priority` for O(1) priority lookup. `flat : List ThreadId` maintained for proof/projection compatibility.
- **O(1) scheduler hot-path operations:** `insert`, `remove`, `contains`, `rotateHead`, `rotateToBack` all O(1) amortized. `maxPriority` cached and maintained incrementally (recomputed only on bucket exhaustion).
- **Bucket-first scheduling (F-P07):** `chooseBestInBucket` scans only the max-priority bucket for domain-eligible threads, reducing best-candidate selection from O(t) to O(k) where k is the bucket size (typically 1-3). Falls back to full-list scan when max-priority bucket has no eligible thread in the active domain.
- **Structural invariant `flat_wf`:** `∀ tid, tid ∈ flat → membership.contains tid = true` — Prop field that formally bridges HashSet and flat list membership. Maintained by inline proofs in every RunQueue mutation.
- **SchedulerState restructured:** `runQueue : RunQueue` replaces `runnable : List ThreadId`. Eliminated `runnableHead`, `runnableTail` cache fields. Eliminated `withRunnableQueue` helper (subsumed by RunQueue structure). Dead `rotateCurrentToBack` private function removed.
- **IPC operations rewritten:** `removeRunnable` uses `RunQueue.remove`; `ensureRunnable` uses `RunQueue.contains` + `RunQueue.insert`. `handleYield`/`timerTick` use `RunQueue.rotateToBack` directly.
- **13 RunQueue bridge lemmas:** `mem_insert`, `mem_remove`, `mem_rotateHead`, `mem_rotateToBack`, `not_mem_empty`, `toList_insert_not_mem`, `toList_filter_insert_neg`, `toList_filter_remove_neg`, `not_mem_toList_of_not_mem`, `not_mem_remove_toList`, `mem_toList_rotateToBack_self`, `toList_rotateToBack_nodup`, `mem_toList_rotateToBack_ne`.
- **IPC invariant migration:** 30+ proofs in `IPC/Invariant.lean` migrated to flat-list variants (`removeRunnable_runnable_mem`, `ensureRunnable_runnable_mem_old`). `ensureRunnable_nodup` simplified (no longer needs `hWF` parameter).
- **Information-flow preservation:** `ensureRunnable_preserves_projection` re-proved via `congr 1` + `RunQueue.toList_filter_insert_neg`.
- **Full proof migration:** zero sorry/axiom across all 7 modified files. `test_full.sh` passes (Tier 0-3).
- Closes findings F-P02 (runnable queue O(n) ops), F-P07 (scheduler best-candidate O(t) scan), F-P12 (`withRunnableQueue` tail recomputation).

## [0.12.8] - 2026-03-01

### WS-G3: ASID Resolution Table (completed)

- **ASID resolution O(1) via HashMap:** `resolveAsidRoot` rewritten from O(n) `objectIndex.findSome?` linear scan to O(1) `Std.HashMap ASID ObjId` lookup with object-store validation. New `asidTable` field in `SystemState`.
- **asidTable maintenance in storeObject:** erase-before-insert pattern ensures old ASID entries are cleaned up when overwriting a VSpaceRoot. Three bridge lemmas: `storeObject_asidTable_vspaceRoot`, `storeObject_asidTable_vspaceRoot_ne`, `storeObject_asidTable_non_vspaceRoot`.
- **asidTableConsistent invariant:** bidirectional soundness + completeness agreement between `asidTable` and VSpaceRoot objects. `vspaceInvariantBundle` extended from 2-conjunct to 3-conjunct (+ `asidTableConsistent`).
- **Preservation proofs updated:** both map/unmap success-path theorems prove `asidTableConsistent` preservation via shared `asidTableConsistent_of_storeObject_vspaceRoot` helper (deduplicates ~50 lines). All 4 round-trip theorems simplified (no longer need `objectIndexSetSync` hypothesis).
- **StateBuilder + InvariantChecks:** test state builder auto-populates `asidTable` from VSpaceRoot objects. Runtime `asidTableConsistencyChecks` added to invariant check surface with Tier-3 anchor.
- **Tier-3 test anchors:** `objectIndex.findSome?` exit criterion (expect NOT found in VSpace.lean), `st.asidTable` positive anchor, `asidTableConsistencyChecks` runtime check anchor, updated theorem name anchors.
- **Full proof migration:** zero sorry/axiom. `test_full.sh` passes (Tier 0-3).
- Closes finding F-P06 (ASID resolution linear scan).

## [0.12.7] - 2026-03-01

### WS-G2: Object Store & ObjectIndex HashMap (completed)

- **Object store HashMap migration:** `SystemState.objects` changed from closure-chain `ObjId → Option KernelObject` to `Std.HashMap ObjId KernelObject`. All object lookups now O(1) amortized instead of O(k) chain-walking. `storeObject` uses `HashMap.insert` directly.
- **ObjectIndex shadow HashSet:** new `objectIndexSet : Std.HashSet ObjId` field enables O(1) membership checks for `storeObject`'s index-deduplication guard. New `objectIndexSetSync` invariant ensures consistency between `objectIndex` and `objectIndexSet`.
- **Lifecycle metadata HashMap:** `LifecycleMetadata.objectTypes` migrated to `Std.HashMap ObjId KernelObjectType` for O(1) type metadata lookups.
- **Bridge lemmas:** `HashMap_getElem?_insert`, `HashMap_getElem?_empty`, `HashMap_getElem?_eq_get?`, `HashMap_get?_eq_getElem?` in `Prelude.lean`. `LawfulHashable` and `EquivBEq` instances for all key types.
- **Full proof migration:** all 400+ theorems re-verified. Zero sorry/axiom. `test_full.sh` passes (Tier 0-3).
- **Closure elimination:** all `fun oid => if oid = X then ... else st.objects[oid]?` patterns replaced with `st.objects.insert`.
- Closes findings F-P01 (object store closure chain), F-P10 (objectIndex linear scan), F-P13 (lifecycle metadata linear scan).

## [0.12.6] - 2026-03-01

### WS-G1: Hashable/BEq Infrastructure (completed)

- **Hashable instances for all 13 typed identifiers:** `ObjId`, `ThreadId`, `DomainId`, `Priority`, `Deadline`, `Irq`, `ServiceId`, `CPtr`, `Slot`, `Badge`, `ASID`, `VAddr`, `PAddr` — all marked `@[inline]` for zero runtime overhead, delegating to `Nat` hash. BEq is provided by the existing `DecidableEq` derivations via `instBEqOfDecidableEq`.
- **Hashable instance for composite key `SlotRef`:** uses `mixHash` to combine `cnode` and `slot` hashes for uniform distribution in HashMap/HashSet.
- **Std imports:** `Std.Data.HashMap` and `Std.Data.HashSet` imported in `Prelude.lean`, making O(1) hash-based data structures available to all kernel modules.
- **Zero behavioral change:** all existing tests pass identically (Tier 0-3). Zero sorry/axiom.
- **Foundation for WS-G2..G9:** every subsequent performance workstream depends on these instances for HashMap/HashSet usage.

## [0.12.5] - 2026-03-01

### WS-F4: Proof Gap Closure (completed)

- **timerTick preservation (F-03):** `timerTick_preserves_schedulerInvariantBundle` and `timerTick_preserves_kernelInvariant` — covers `queueCurrentConsistent`, `runQueueUnique`, `currentThreadValid`, `currentThreadInActiveDomain`. Expired-timeslice path delegates to `schedule_preserves_*`; non-expired path proves scheduler unchanged directly.
- **cspaceMutate preservation (F-06):** `cspaceMutate_preserves_capabilityInvariantBundle` — uses `revert/unfold` decomposition through capability lookup, rights check, and storeObject.
- **cspaceRevokeCdt/cspaceRevokeCdtStrict preservation (F-06):** Fold induction via extracted `revokeCdtFoldBody` with error propagation lemmas (`revokeCdtFoldBody_foldl_error`). CDT-only state updates handled by `capabilityInvariantBundle_of_cdt_update`.
- **Notification preservation (F-12):** `notificationSignal_preserves_ipcInvariant`, `notificationSignal_preserves_schedulerInvariantBundle`, `notificationWait_preserves_ipcInvariant`, `notificationWait_preserves_schedulerInvariantBundle`. Compositional through new `storeObject_notification_preserves_ipcInvariant` helper. Wake/merge/badge-consume/wait paths fully covered with existing well-formedness lemmas.
- **Notification contract predicate preservation:** `notificationSignal_preserves_ipcSchedulerContractPredicates` and `notificationWait_preserves_ipcSchedulerContractPredicates` — closes the gap where notification operations lacked proof of scheduler-IPC coherence (M3.5). Wake/badge-consume paths use backward TCB transport through storeObject + storeTcbIpcState with ensureRunnable. Merge path uses `contracts_of_same_scheduler_ipcState`. Wait path handles `.blockedOnNotification` (not covered by `blockedOnSend`/`blockedOnReceive` predicates) with removeRunnable.
- **Testing:** 11 Tier-3 surface anchors. `test_full.sh` passes (Tier 0-3). Zero sorry/axiom.
- **Fix:** Capability invariant proof comments corrected from F-03 to F-06 (F-03 is timerTick; F-06 is cspaceMutate/revoke).
- Closes F-03 (timerTick no proofs), F-06 (cspaceMutate etc.), F-12 (notification preservation).

## [0.12.4] - 2026-03-01

### Audit hardening: F1-A silent data loss fix and O-3 allocSize validation

- **F1-A fix (IPC):** `endpointReceiveDual` now propagates `storeTcbPendingMessage` errors instead of silently succeeding when the receiver TCB doesn't exist, preventing a data loss path where the sender's message is cleared but never delivered.
- **O-3 fix (Untyped memory):** `retypeFromUntyped` validates `allocSize >= objectTypeAllocSize` for the target object type before attempting allocation. New error variant `untypedAllocSizeTooSmall`, error theorem `retypeFromUntyped_error_allocSizeTooSmall`, negative test F2-NEG-06, trace anchor F2-08.
- **Proof updates:** 3 IPC invariant proofs simplified (error branch now contradiction). Decomposition theorem `retypeFromUntyped_ok_decompose` extended with allocSize bound conjunct. Downstream invariant proofs updated.
- **Testing:** 80 trace expectations (was 68), 6 WS-F2 negative tests (was 5), 4 new Tier-3 surface anchors.

## [0.12.3] - 2026-02-28

### WS-F2: Untyped Memory Model (completed)

- **UntypedObject data model:** `UntypedObject` structure with `regionBase`, `regionSize`, `watermark`, `children`, and `isDevice` fields. `UntypedChild` tracks carved child objects with `objId`, `offset`, and `size`. Added `.untyped` variant to `KernelObject` and `KernelObjectType`.
- **retypeFromUntyped operation:** carves a typed kernel object from an untyped memory region, advancing the watermark. Enforces authority via `cspaceLookupSlot`, region bounds via `canAllocate`, and device restrictions (device untypeds can only produce more untypeds).
- **Error variants:** `untypedRegionExhausted`, `untypedTypeMismatch`, `untypedDeviceRestriction`, `untypedAllocSizeTooSmall` added to `KernelError`.
- **Proof surface:** `allocate_some_iff` decomposition lemma, `allocate_watermark_advance/monotone`, `allocate_preserves_watermarkValid/region`, `reset_wellFormed`, `empty_wellFormed`, `canAllocate_implies_fits`. Decomposition theorem `retypeFromUntyped_ok_decompose` and error characterization theorems.
- **Invariants:** `untypedWatermarkInvariant`, `untypedChildrenBoundsInvariant`, `untypedChildrenNonOverlapInvariant`, `untypedChildrenUniqueIdsInvariant`, `untypedMemoryInvariant`. Default-state theorem. Preservation through `retypeFromUntyped` for both `lifecycleMetadataConsistent` and `lifecycleInvariantBundle`.
- **Testing:** 8 trace scenarios (F2-01..F2-08), 6 negative-state tests, runtime watermark invariant checks, 27 Tier-3 surface anchors.
- Closes CRIT-04 (No Untyped memory).

### WS-F3: Information-Flow Completeness (completed)

- **ObservableState extension (CRIT-02):** 3 new security-relevant fields — `activeDomain` (scheduling transparency, always visible), `irqHandlers` (filtered by target object observability), `objectIndex` (filtered by object observability). All NI theorems extended to preserve the 7-field projection.
- **CNode slot filtering (F-22):** `projectKernelObject` redacts CNode capability slots whose targets reference high-domain objects. `capTargetObservable` gate covers `.object`, `.cnodeSlot`, and `.replyCap` target variants. Safety theorems: `projectKernelObject_idempotent` and `projectKernelObject_objectType`.
- **NI theorem coverage (CRIT-03):** 12 standalone `_preserves_lowEquivalent` theorems (endpointSend, chooseThread, cspaceMint, cspaceRevoke, lifecycleRetypeObject, notificationSignal, notificationWait, cspaceInsertSlot, serviceStart, serviceStop, serviceRestart, storeObject). 3 enforcement-NI bridge theorems (endpointSendChecked_NI, cspaceMintChecked_NI, serviceRestartChecked_NI).
- **Enforcement-NI bridge (F-20):** Bool case-splitting pattern connects checked operations to NI domain-separation hypotheses. Each bridge theorem extracts the flow-allowed proof, rewrites to the unchecked operation, and delegates to the standalone NI theorem.
- **Composed NI framework (H-05):** `NonInterferenceStep` inductive with 11 constructors (storeObject is standalone infrastructure, not an API constructor), `step_preserves_projection` one-sided theorem, `composedNonInterference_step/trace` two-sided bundle theorems, `preservesLowEquivalence` abstract predicate with sequential composition and error-action helpers.
- **Testing:** 39 WS-F3 tests in InformationFlowSuite covering activeDomain projection, IRQ handler filtering, object index filtering, CNode slot filtering (all 3 CapTarget variants), 7-field low-equivalence, serviceRestartChecked enforcement. 22 Tier-3 surface anchors.
- Closes CRIT-02 (incomplete projection), CRIT-03 (NI 5→12 operations), F-20 (enforcement-NI gap), F-21 (notificationSignal NI), F-22 (CNode projection leak).

### WS-F1: IPC message transfer and dual-queue verification (completed)

- **IPC message transfer:** `endpointSendDual`, `endpointReceiveDual`, `endpointCall`, `endpointReply`, and `endpointReplyRecv` now carry `IpcMessage` payloads (registers, caps, badge) through send/receive rendezvous. Messages are staged in sender's `TCB.pendingMessage` while blocked and transferred to the receiver's TCB on handshake/dequeue. `endpointReceiveDual` propagates message delivery errors (receiver TCB not found) instead of silently swallowing them, preventing silent data loss.
- **TCB.pendingMessage field:** new `Option IpcMessage` field on TCB for staging message content during IPC transfers.
- **Combined state+message helpers:** `storeTcbIpcStateAndMessage` and `storeTcbPendingMessage` update IPC state and pending message in a single `storeObject` call, simplifying both implementation and proof tracking.
- **Invariant preservation theorems:** 14 new theorems for dual-queue and compound operations (`endpointSendDual`, `endpointReceiveDual`, `endpointQueueRemoveDual`, `endpointCall`, `endpointReplyRecv`, `endpointReply`) preserving `ipcInvariant`, `schedulerInvariantBundle`, and `ipcSchedulerContractPredicates`. Tracked as TPI-D08/TPI-D09 for mechanical unfolding through private multi-step `storeObject` chains.
- **Supporting proof lemmas:** backward endpoint/notification preservation, scheduler equality, IPC state readback, and TCB existence lemmas for `storeTcbIpcStateAndMessage`, `storeTcbPendingMessage`, and `storeTcbQueueLinks`.
- **Trace harness scenarios:** 7 new fixture anchors (F1-01a..F1-03b) demonstrating actual data transfer: send-then-receive with registers/badge, rendezvous delivery, and call/reply roundtrip.
- Closes CRIT-01 (no message transfer), CRIT-05 (dual-queue unverified), F-10, F-11.

## [0.12.2] - 2026-02-27

### Optimization work continues

- **Node-stable CDT model:** capability derivation edges are tracked over stable CDT node IDs while CSpace slots map to nodes (`cdtSlotNode`/`cdtNodeSlot`); `cspaceMove` performs slot→node pointer transfer plus backpointer fixup instead of global edge rewrite, and `cspaceDeleteSlot` detaches slot↔node mappings to prevent stale CDT aliasing on slot reuse.
- Provide an opt-in strict variant of CDT-aware revoke that does not swallow deletion errors but surfaces the first descendant deletion failure for auditability and debugging.
- Record precise failing context (CDT node, projected slot when present, and concrete KernelError) so tooling/tests can assert and report offending slot/state.

## [0.12.1] - 2026-02-27

### Optimization work begins

- **Intrusive endpoint queues:** dual-queue wait lists now track `queuePrev`/`queuePPrev`/`queueNext` per waiting TCB to support O(1) arbitrary removal (`endpointQueueRemoveDual`).
- **Domain-aware scheduler policy:** selection is unified under active-domain filtering (`chooseThread`/`chooseThreadInDomain`), `kernelInvariant`/`canonicalSchedulerInvariantBundle` enforce `currentThreadInActiveDomain`, and regression coverage includes mixed runnable-set filtering plus `scheduleDomain` switch/tick consistency checks.

## [0.12.0] - 2026-02-26

### WS-E6 Model completeness and documentation (completed)

All 10 WS-E6 findings resolved with zero sorry/axiom. Synthesized from analysis of PRs #223, #224, and #225, selecting the best approach for each finding. This closes the entire WS-E portfolio.

- **M-03 (EDF tie-breaking):** Three-level scheduling comparison via `isBetterCandidate` (priority > deadline > FIFO). `Deadline` typed identifier. `TCB.deadline` field. `isBetterCandidate_irrefl` FIFO stability and `isBetterCandidate_asymm` strict ordering theorems. `edfCurrentHasEarliestDeadline` invariant predicate.
- **M-04 (Time-slice preemption):** `TCB.timeSlice` field (default 5). `defaultTimeSlice` constant. `timerTick` operation with decrement/reset+reschedule. `timeSlicePositive` invariant predicate.
- **M-05 (Domain scheduling):** `DomainScheduleEntry`, `filterByDomain`, `chooseThreadInDomain` (with fallback), `switchDomain`, `scheduleDomain`. `currentThreadInActiveDomain` invariant. Preservation theorems.
- **M-08 (Architecture assumption consumption):** Three consumption bridge theorems connecting structural axioms to adapter proofs. 4-step consumption chain documented.
- **F-17 (O(n) design decision ADR):** `docs/ON_DESIGN_DECISION_ADR.md` with rationale, scope note, complexity comparison, migration path.
- **L-01 (Unified API surface):** `apiInvariantBundle` alias, `apiInvariantBundle_default` theorem, entry-point stability table (30+ operations).
- **L-02 (Memory zero-default):** Comprehensive documentation and 4 theorems (`default_memory_returns_zero`, `default_registerFile_pc_zero`, `default_registerFile_sp_zero`, `default_timer_zero`).
- **L-03 (Monad helpers):** `KernelM.get/set/modify/liftExcept/throw` with 6 correctness theorems.
- **L-04 (toObjId documentation):** Design rationale documented. `toObjIdChecked` safe variant with `toObjIdChecked_eq_some_of_not_reserved` theorem.
- **L-05 (objectIndex monotonicity):** Design rationale documented. `storeObject_objectIndex_monotone` theorem.
- WS-E6 trace scenarios: EDF tie-breaking, timer tick, domain switching. 7 new fixture anchors.
- All documentation synchronized. WS-E6 marked COMPLETED across all surfaces.
- Bumped package version to **`0.12.0`** (minor version bump for WS-E portfolio completion).

## [0.11.12] - 2026-02-26

### WS-E5 Information-flow maturity (completed)

All 3 WS-E5 findings resolved with zero sorry/axiom. Synthesized from analysis of PRs #218, #219, and #220, selecting the best approach for each finding.

- **H-04 (Parameterized security labels):** Introduced `SecurityDomain` (Nat-indexed), `DomainFlowPolicy` with `canFlow`/`isReflexive`/`isTransitive`/`wellFormed` fields, and proofs `domainFlowsTo_refl`/`domainFlowsTo_trans`. Built-in policies: `allowAll` and `linearOrder` with well-formedness proofs. `GenericLabelingContext` with embedded policy field. `EndpointFlowPolicy` for per-endpoint flow overrides. `embedLegacyLabel` mapping legacy 2x2 lattice to 4-domain system with `embedLegacyLabel_preserves_flow` correctness proof. `threeDomainExample` with 3 validation theorems.
- **H-05 (Composed bundle-level non-interference):** `NonInterferenceStep` inductive with 5 constructors (`chooseThread`, `endpointSend`, `cspaceMint`, `cspaceRevoke`, `lifecycleRetype`). `step_preserves_projection` and `composedNonInterference_step` (primary IF-M4 theorem). `NonInterferenceTrace` for multi-step lift with `composedNonInterference_trace`. Abstract composition via `preservesLowEquivalence`/`compose_preservesLowEquivalence`. Error path preservation via `errorAction_preserves_lowEquiv`.
- **M-07 (Enforcement boundary specification):** `EnforcementClass` inductive (`policyGated`/`capabilityOnly`/`readOnly`). Exhaustive `enforcementBoundary` table (17 entries covering all kernel operations). `denied_preserves_state_*` for all 3 checked operations. `enforcement_sufficiency_*` complete-disjunction coverage proofs.
- Extended information-flow test suite with 24 new WS-E5 checks (H-04 + M-07 coverage). Total: 54 checks passing.
- Updated all canonical documentation: workstream plan, README, SELE4N_SPEC, DEVELOPMENT.md, CLAIM_EVIDENCE_INDEX, INFORMATION_FLOW_ROADMAP, GitBook chapters (01, 05, 12, 24, 32, README).
- Bumped package version to **`0.11.12`**.

## [0.11.11] - 2026-02-25

### Documentation and release metadata synchronization
- Bumped patch version to **`0.11.11`** in `lakefile.toml`.
- Updated version badges and current-version references in canonical docs (`README.md`, `docs/spec/SELE4N_SPEC.md`).
- Updated contributor guidance mirrors (`AGENTS.md`, `CLAUDE.md`) so project metadata matches the codebase.

## [0.11.10] - 2026-02-25

### WS-E4 preparation — proof infrastructure and documentation accuracy

Synthesized from analysis of PRs #207 and #208, selecting the best ideas from each. All changes maintain zero sorry/axiom.

- **CPtr sentinel infrastructure:** Added `CPtr.isReserved`, `CPtr.sentinel`, `CPtr.default_eq_sentinel`, `CPtr.sentinel_isReserved` to `Prelude.lean`, paralleling the existing ObjId/ThreadId/ServiceId sentinel convention (H-06). Prepares for seL4_CapNull (CPtr 0) modeling in WS-E4 capability operations.
- **ServiceId sentinel completion:** Added `ServiceId.sentinel`, `ServiceId.default_eq_sentinel`, `ServiceId.sentinel_isReserved` to `Prelude.lean`, closing a gap where ServiceId had `isReserved` but lacked the full sentinel infrastructure.
- **Machine-layer frame lemmas:** Added 13 read-after-write and frame theorems to `Machine.lean`: `readReg_writeReg_eq/ne`, `readMem_writeMem_eq/ne`, `writeReg_preserves_pc/sp`, `writeMem_preserves_regs/timer`, `setPC_preserves_memory/timer`, `tick_preserves_regs/memory`, `tick_timer_succ`. Foundation for architecture-boundary proofs in WS-E4.
- **State-layer frame lemmas:** Added `storeObject_irqHandlers_eq` and `storeObject_machine_eq` to `Model/State.lean`, proving `storeObject` preserves IRQ handler mappings and machine state.
- **Notification well-formedness theorems:** Added `notificationSignal_result_wellFormed_wake`, `notificationSignal_result_wellFormed_merge`, `notificationWait_result_wellFormed_badge`, `notificationWait_result_wellFormed_wait` to `IPC/Invariant.lean`. Building blocks for notification ipcInvariant preservation in WS-E4.
- **Strengthened `serviceRestart_error_discards_state`:** Upgraded from trivial `True` to invariant-preservation statement (proves `serviceLifecycleCapabilityInvariantBundle` preservation on error path).
- **`boundedAddressTranslation` docstring:** Annotated as forward declaration for WS-E6 (not yet integrated into `vspaceInvariantBundle`).
- **Documentation accuracy audit:** Fixed stale references in `docs/gitbook/README.md` (pointed to v0.11.0 baseline instead of v0.11.6), `CONTRIBUTING.md` (workstream plan link), and `docs/gitbook/05-specification-and-roadmap.md` (phase status). Updated `CLAUDE.md` known-large-file entries to accurate line counts.

### WS-E3 Kernel semantic hardening (completed)

All 6 WS-E3 findings resolved with zero sorry/axiom. Synthesized from analysis of PRs #201–#203, selecting the best approach for each finding.

- **H-06 (Sentinel IDs):** Established ID 0 as reserved sentinel for all identifier types. Added `isReserved`, `sentinel`, and `ObjId.valid` predicates on `ObjId`, `ThreadId`, `ServiceId`. Proved `ObjId.default_eq_sentinel`, `ThreadId.default_eq_sentinel`, `ObjId.sentinel_isReserved`, `ThreadId.sentinel_isReserved`, `ObjId.valid_iff_not_reserved`. Added `ThreadId.toObjId_injective` in Prelude for canonical placement.
- **H-07 (VSpace in composed bundle):** Added `vspaceInvariantBundle` as 7th conjunct to `proofLayerInvariantBundle` in `Architecture/Invariant.lean`. Added adapter preservation theorems (`advanceTimerState_preserves_vspaceInvariantBundle`, `writeRegisterState_preserves_vspaceInvariantBundle`).
- **H-08 (BFS fuel exhaustion):** Changed `serviceHasPathTo.go` fuel-exhaustion base case from `false` to `true` (conservative for cycle detection). Added soundness theorems: `serviceHasPathTo_fuel_zero_is_true`, `serviceHasPathTo_false_implies_not_fuel_exhaustion`, `serviceBfsFuel_adequate`, `serviceRegisterDependency_rejects_if_path_or_fuel_exhausted`.
- **H-09 (Thread blocking in IPC):** Endpoint operations now perform compound 3-step transitions: `storeObject` (endpoint update) → `storeTcbIpcState` (thread IPC state) → `removeRunnable`/`ensureRunnable` (scheduler). `removeRunnable` also clears `scheduler.current` when removing current thread. All IPC invariant preservation proofs, capability bundle proofs, scheduler bundle proofs, and information-flow non-interference proofs rewritten for compound transitions. Added comprehensive frame lemmas for `storeTcbIpcState`, `removeRunnable`, `ensureRunnable`.
- **M-09 (Metadata sync):** Proved `storeObject_metadata_sync_type_change` and `storeObject_metadata_sync_capref_at_stored` in `Model/State.lean`.
- **L-06 (Initialization proof):** Proved `default_systemState_lifecycleConsistent` and `default_system_state_proofLayerInvariantBundle` showing the empty state satisfies all composed invariants.
- Updated all canonical documentation: workstream plan, README, SELE4N_SPEC, DEVELOPMENT.md, CLAIM_EVIDENCE_INDEX, GitBook chapters (01, 05, 24, 32).
- Bumped package version to **`0.11.10`**.

## [0.11.7] - 2026-02-24

### WS-E1 Test infrastructure and CI hardening (completed)
- **F-14:** SHA-pinned all GitHub Actions across 4 workflow files (`lean_action_ci`, `nightly_determinism`, `lean_toolchain_update_proposal`, `platform_security_baseline`) to full 40-character commit hashes with version comments.
- **M-10:** Added parameterized test topologies in `MainTraceHarness.lean` — 3 configurations (minimal/medium/large) varying thread count, priority, CNode radix, and ASID count, exercised during `lake exe sele4n`.
- **M-11:** Added 5 runtime invariant check families to `InvariantChecks.lean`: CSpace slot coherency, capability rights structure, lifecycle metadata consistency, service graph acyclicity (BFS-based), and VSpace ASID uniqueness.
- **L-07:** Converted `main_trace_smoke.expected` fixture to structured `scenario_id | risk_class | expected_fragment` format. Backward-compatible with existing substring matching in `test_tier2_trace.sh`.
- **L-08:** Added theorem-body spot-check validation to `test_tier0_hygiene.sh` (verifies no `sorry` in invariant proof surface) and F-14 SHA-pin regression guard.
- Updated Tier 3 invariant surface script with WS-E1 anchor checks for new check families, topology builders, structured fixture format, and hygiene additions.
- Updated all canonical documentation surfaces: workstream plan, README, SELE4N_SPEC, DEVELOPMENT.md, CI_POLICY.md, GitBook chapters (07, 24, README).

### Lean toolchain upgrade (WS-B10, closes #182)
- Bumped Lean toolchain from `leanprover/lean4:v4.27.0` to `leanprover/lean4:v4.28.0` in `lean-toolchain`.
- Updated Lean version badge in `README.md`, toolchain reference in `CLAUDE.md`, and package version in `docs/spec/SELE4N_SPEC.md`.
- Bumped patch version to **`0.11.7`**.

## [0.11.6] - 2026-02-22

### Documentation optimization and context-pressure reduction
- Added `CLAUDE.md` with focused project guidance: build commands, source layout, key conventions, documentation rules, active workstream context, and PR checklist. Provides a concise onboarding surface that avoids requiring full documentation traversal.
- Added `--quiet`/`-q` flag to `scripts/setup_lean_env.sh` to suppress informational output during automated runs while preserving error messages. SessionStart hook updated to use `--quiet`.
- Fixed stale workstream status in `docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`: WS-D4 now correctly listed as completed.
- Fixed stale canonical source reference in `docs/DOCS_DEDUPLICATION_MAP.md`: "Current execution workstreams" row now points to the active `AUDIT_v0.11.0_WORKSTREAM_PLAN.md` instead of the historical `AUDIT_v0.9.32` plan.
- Tightened `CONTRIBUTING.md` to remove redundant prose and consolidate validation guidance.
- Bumped patch version to **`0.11.6`**.

## [0.11.5] - 2026-02-22

### Build environment hardening
- Fixed `scripts/setup_lean_env.sh` to work in proxy-restricted environments (e.g. Claude Code web sessions behind an egress gateway). The setup script now falls back to a manual `curl`-based download of the elan binary and Lean toolchain when elan's internal HTTP client cannot negotiate CONNECT tunnels through an egress proxy.
- Made `shellcheck` and `ripgrep` installation non-fatal in `setup_lean_env.sh`; both tools are optional for building and their absence is already handled gracefully by `test_tier0_hygiene.sh` fallback paths.
- Made `apt_update_once` tolerant of complete apt repository unavailability so the script continues to elan/lean installation instead of aborting.
- Added `.claude/settings.json` with a `SessionStart` hook that automatically runs `setup_lean_env.sh --build` on new Claude Code sessions, ensuring the Lean environment is provisioned and built without manual intervention.
- Bumped patch version to **`0.11.5`**.

## [0.11.3] - 2026-02-21

### WS-D3 proof gap closure (F-06, F-08, F-16)
- **F-06 (Badge-override safety):** Added three badge-safety theorems to `SeLe4n/Kernel/Capability/Invariant.lean`: `mintDerivedCap_rights_attenuated_with_badge_override` (rights attenuation holds regardless of badge), `mintDerivedCap_target_preserved_with_badge_override` (target identity preserved regardless of badge), and `cspaceMint_badge_override_safe` (composed kernel-operation-level proof that badge override cannot escalate privilege). TPI-D04 closed.
- **F-08 (VSpace success preservation):** Added `vspaceMapPage_success_preserves_vspaceInvariantBundle` and `vspaceUnmapPage_success_preserves_vspaceInvariantBundle` to `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean`. Supporting infrastructure: `resolveAsidRoot_some_implies`, `resolveAsidRoot_of_unique_root`, `storeObject_objectIndex_eq_of_mem`, and `vspaceAsidRootsUnique` moved to `VSpace.lean`; seven VSpaceRoot helper theorems added to `Model/Object.lean` (`mapPage_asid_eq`, `unmapPage_asid_eq`, `lookup_eq_none_not_mem`, `mapPage_noVirtualOverlap`, `unmapPage_noVirtualOverlap`, `lookup_mapPage_ne`, `lookup_unmapPage_ne`). TPI-D05 closed.
- **TPI-001 (VSpace round-trip theorems):** Four round-trip theorems proved in `VSpaceInvariant.lean`: `vspaceLookup_after_map`, `vspaceLookup_map_other`, `vspaceLookup_after_unmap`, `vspaceLookup_unmap_other`. All proved without `sorry`. TPI-001 obligation from WS-C fully discharged.
- **F-16 (Proof classification docstrings):** Added module-level `/-! ... -/` docstrings to all seven `Invariant.lean` files (Scheduler, IPC, Capability, Lifecycle, InformationFlow, Service, Architecture) and `VSpaceInvariant.lean`, classifying every theorem as substantive, error-case (trivially true), non-interference, badge-safety, structural/bridge, or round-trip.
- Updated Tier-3 invariant surface script with 20 new anchor checks for WS-D3 theorem symbols and docstring presence.
- Updated all canonical planning docs, tracked proof issues, claim-evidence index, development guide, spec, GitBook chapters (12, 32), and documentation sync matrix to reflect WS-D3 completion.
- Bumped patch version to **`0.11.3`**.

## [0.11.1] - 2026-02-19

### WS-D2 information-flow enforcement and proof completion
- Implemented policy-checked kernel operation wrappers in `SeLe4n/Kernel/InformationFlow/Enforcement.lean`: `endpointSendChecked`, `cspaceMintChecked`, `serviceRestartChecked` (F-02), with correctness theorems for allowed/denied cases and reflexive self-domain flow.
- Extended non-interference proof surface in `SeLe4n/Kernel/InformationFlow/Invariant.lean` with five transition-level theorems (F-05): `chooseThread_preserves_lowEquivalent` (TPI-D01), `cspaceMint_preserves_lowEquivalent`, `cspaceRevoke_preserves_lowEquivalent` (TPI-D02), `lifecycleRetypeObject_preserves_lowEquivalent` (TPI-D03), plus shared `storeObject_at_unobservable_preserves_lowEquivalent` infrastructure.
- Added `flowDenied` error variant to `KernelError` and preservation helper lemmas to `Model/State.lean` and `Capability/Operations.lean` supporting the new proof decompositions.
- Extended `tests/InformationFlowSuite.lean` with 4 enforcement boundary tests covering same-domain pass-through and cross-domain flow denial for `endpointSendChecked` and `cspaceMintChecked`.
- Closed proof obligations TPI-D01, TPI-D02, TPI-D03; marked WS-D2 and Phase P2 as completed across all canonical planning, spec, and GitBook documentation.
- Bumped patch version to **`0.11.1`**.

## [0.11.0] - 2026-02-19

### WS-C8 post-merge audit refinement and minor release
- Performed an end-to-end documentation/codebase synchronization audit after WS-C8 completion and corrected residual status drift in the seLe4n spec (`WS-C portfolio` summary now consistently states WS-C1..WS-C8 completed).
- Refined carried-forward proof-issue tracker wording to reflect that WS-C execution is complete and obligations remain intentionally tracked post-closeout.
- Revalidated docs automation + smoke/full/nightly experimental gates to confirm runtime, proof-surface, and documentation anchors are synchronized.
- Bumped minor version to **`0.11.0`** and synchronized version markers in root/spec metadata.

## [0.10.8] - 2026-02-19

### WS-C8 documentation and GitBook consolidation completion
- Marked WS-C8 as completed across canonical planning docs, root guides, and GitBook mirrors so active portfolio status is consistently closed (WS-C1..WS-C8 complete).
- Added a canonical claim/evidence audit index (`docs/CLAIM_EVIDENCE_INDEX.md`) plus a GitBook pointer chapter (`docs/gitbook/31-claim-vs-evidence-index.md`).
- Refreshed documentation ownership/synchronization matrices and planning companion links to include the new claim/evidence index.
- Bumped patch version to **`0.10.8`** and synchronized version markers.

## [0.10.7] - 2026-02-19

### Documentation correctness and WS-C7 refinement follow-up
- Audited and corrected remaining ADR/GitBook drift where WS-B1 material still implied bounded ASID discovery is current behavior.
- Amended VSpace ADR + GitBook mirror to explicitly record WS-C7 superseding the bounded scan with `SystemState.objectIndex` traversal in `resolveAsidRoot`.
- Synchronized root/spec version markers to **`0.10.7`**.
- Re-ran docs sync + full + nightly experimental validation to confirm end-to-end consistency.

## [0.10.6] - 2026-02-19

### Added
- Added WS-C7 architecture decision record for finite object-store migration staging and compatibility notes (`docs/FINITE_OBJECT_STORE_ADR.md`) with a synced GitBook completion chapter.

### Changed
- Migrated `ServiceId` from a `Nat` alias to a typed wrapper in `SeLe4n/Prelude.lean` to restore identifier-domain separation.
- Added finite `objectIndex` tracking to `SystemState` and `BootstrapBuilder`, and rewired VSpace ASID-root resolution to use indexed object discovery instead of bounded range scanning.
- Consolidated shared store-object helper lemmas into `Model/State.lean` and reused them from lifecycle invariant helpers.
- Updated active portfolio docs/GitBook to mark WS-C7 completed.
- Bumped patch version to **`0.10.6`** and synchronized version markers.

## [0.10.5] - 2026-02-19

### WS-C6 refinement follow-up: status precision + telemetry/doc anchor tightening
- Refined active-portfolio wording in root/spec docs so WS-C7 is explicitly marked as planned while WS-C8 remains in progress.
- Synchronized GitBook telemetry mirror wording to reflect nightly smoke flake probing defaulting to 3 attempts.
- Tightened Tier-3 documentation anchor check for `docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md` to require the current WS-C baseline string instead of broad historical alternates.
- Re-ran Tier 0-4 validation (`test_full` + `test_nightly`) to confirm full-codebase/docs/gitbook consistency after refinement.
- Bumped patch version to **`0.10.5`** and synchronized version markers.

## [0.10.4] - 2026-02-19

### WS-C6 CI and supply-chain hardening completion
- Hardened GitHub Actions cache isolation in the primary Lean CI and nightly workflows by adding `runner.arch` to cache keys/restore prefixes.
- Added defensive Lean release-tag format validation in `.github/workflows/lean_toolchain_update_proposal.yml` before using upstream tags in issue-search/query logic.
- Strengthened flake telemetry defaults by updating `scripts/ci_flake_probe.sh` to default to 3 attempts (with optional explicit override) and wiring nightly to use the stronger default.
- Tightened Tier-0 hygiene marker scanning to word-boundary matching so incidental substrings no longer trigger false positives.
- Marked WS-C6 as completed across the active workstream dashboard plus development/spec/README/GitBook/matrix mirrors and synchronized Tier-3 documentation anchors.
- Bumped patch version to **`0.10.4`** and synchronized version markers.

## [0.10.3] - 2026-02-19

### WS-C5 information-flow assurance completion
- Added service-level visibility control to the IF labeling context (`serviceLabelOf`) and updated observer projection so service status is filtered by clearance policy instead of being globally visible.
- Added `SeLe4n.Kernel.InformationFlow.Invariant.endpointSend_preserves_lowEquivalent`, a nontrivial endpoint-send preservation theorem over `lowEquivalent` under hidden sender/endpoint assumptions.
- Extended IF regression checks in `tests/InformationFlowSuite.lean` to cover service-visibility filtering and an executable theorem witness for endpoint-send low-equivalence preservation.
- Marked WS-C5 as completed in the active workstream plan, tracked-proof obligations, development guide, root README, documentation sync matrix, and GitBook workstream status chapter.
- Bumped patch version to **`0.10.3`** and synchronized root version markers.

## [0.10.2] - 2026-02-19

### WS-C4 hardening follow-up: invariant precision and negative-fixture cleanup
- Refined invariant utility API with `stateInvariantChecksFor`/`assertStateInvariantsFor` so suites can validate exact fixture object inventories instead of relying only on a broad discovery window.
- Removed negative-suite `invariantView` masking and reworked the empty-send endpoint case into a dedicated malformed test state, preserving strict invariant checks for all success-path fixtures.
- Updated generative and trace harness callers to use explicit invariant object sets for stronger test validity guarantees and clearer intent.
- Re-ran smoke/full/tier4 candidate gates to confirm deterministic behavior and documentation/test synchronization after the hardening refactor.
- Bumped patch version to **`0.10.2`** and synchronized root version markers.

## [0.10.1] - 2026-02-19

### WS-C4 test validity hardening + workstream status sync
- Added executable invariant check utilities for scheduler + IPC validity and reusable state assertions used by runtime suites.
- Hardened negative and generative trace suites with post-success invariant assertions while preserving explicit invalid-fixture negative coverage.
- Added baseline invariant assertions at main trace harness entry points.
- Marked WS-C4 as completed across the active audit plan, root docs, and GitBook mirrors; synchronized Tier-3 documentation anchors accordingly.
- Bumped patch version to **`0.10.1`** and synchronized root version markers.

## [0.10.0] - 2026-02-18

### WS-C3 completion hardening + docs-sync reliability + portfolio synchronization
- Finalized WS-C3 proof-surface cleanup by removing tautological determinism theorems from VSpace and IF projection modules, while preserving tracked semantic obligations in TPI-001/TPI-002.
- Added module-level WS-C3 notes in affected Lean modules to clarify determinism-as-meta-property guidance and prevent future tautological theorem regressions.
- Hardened Tier 3 anchors to assert both removal of deprecated tautological theorems and presence of WS-C3 proof-surface notes, alongside synchronized active-slice status anchors.
- Improved docs-sync reliability in non-login shells by sourcing `${HOME}/.elan/env` when available before probing `lake`, reducing unnecessary setup churn and external mirror warnings when Lean is already installed.
- Synchronized root docs and GitBook status text to reflect WS-C3 completion and current P1 continuation focus on WS-C4.
- Bumped minor version to **`0.10.0`** and synchronized root version marker in `README.md`.

## [0.9.29] - 2026-02-18

### WS-B10 docs-sync offline/restricted-environment fallback fix
- Updated `scripts/test_docs_sync.sh` to treat `setup_lean_env.sh` as **best-effort** by default when `lake` is missing, so docs-sync still validates navigation/link consistency on offline or restricted environments where Lean setup cannot complete.
- Added explicit strict mode: `DOCS_SYNC_REQUIRE_LEAN_SETUP=1` now makes setup failure fatal for environments that require Lean setup enforcement during docs-sync.
- Kept existing explicit opt-out: `DOCS_SYNC_SKIP_LEAN_SETUP=1` skips Lean setup and doc-gen4 probing intentionally.
- Synchronized testing docs (`docs/TESTING_FRAMEWORK_PLAN.md`, `docs/gitbook/07-testing-and-ci.md`) to describe best-effort vs strict behavior.
- Bumped patch version to **`0.9.29`** and synchronized root version marker in `README.md`.

## [0.9.28] - 2026-02-18

### WS-B10 docs-sync reliability refinement
- Refined `scripts/test_docs_sync.sh` so it now auto-runs `scripts/setup_lean_env.sh` when `lake` is missing (unless `DOCS_SYNC_SKIP_LEAN_SETUP=1`), making docs-sync behavior more deterministic in pre-build environments.
- Kept doc-gen behavior explicit: navigation/link checks remain mandatory, while doc-gen4 remains optional when the executable is unavailable.
- Synchronized testing documentation language in `docs/TESTING_FRAMEWORK_PLAN.md` and GitBook chapter 07 to reflect docs-sync auto-setup semantics.
- Bumped patch version to **`0.9.28`** and synchronized root version marker in `README.md`.

## [0.9.27] - 2026-02-18

### WS-B10 CI maturity upgrades completion
- Completed WS-B10 by codifying CI governance in `docs/CI_POLICY.md`, including explicit CodeQL informational/non-blocking policy rationale, toolchain automation references, and telemetry artifact expectations.
- Added automated dependency/update cadence controls via `.github/dependabot.yml` (GitHub Actions updates) and `.github/workflows/lean_toolchain_update_proposal.yml` (weekly Lean release drift proposals as issues).
- Implemented CI timing and flake telemetry capture using `scripts/ci_capture_timing.sh` and `scripts/ci_flake_probe.sh`, wired into `.github/workflows/lean_action_ci.yml`, `.github/workflows/nightly_determinism.yml`, and `.github/workflows/platform_security_baseline.yml`.
- Published telemetry baseline documentation in `docs/CI_TELEMETRY_BASELINE.md` with GitBook mirror `docs/gitbook/29-ci-maturity-and-telemetry-baseline.md`, and synchronized active-slice/workstream completion status across README/spec/development/workstream-plan/GitBook docs.
- Bumped patch version to **`0.9.27`** and synchronized root version marker in `README.md`.

## [0.9.26] - 2026-02-18

### WS-B9 bootstrap reproducibility fix (immutable elan installer URL)
- Fixed `scripts/setup_lean_env.sh` to use a commit-pinned `ELAN_INSTALLER_URL` for `elan-init.sh` instead of the moving `master` branch URL.
- Kept `ELAN_INSTALLER_SHA256` aligned with the pinned commit artifact so fresh bootstrap remains reproducible and does not break when upstream `master` changes.
- Clarified the hardening anchor comment to require intentional paired updates of installer URL and checksum.
- Bumped patch version to **`0.9.26`** and synchronized root version marker in `README.md`.

## [0.9.25] - 2026-02-18

### WS-B9 post-audit documentation synchronization hardening
- Corrected documentation-sync baseline drift by updating `docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md` to reflect WS-B9 completion in the active planning baseline summary.
- Updated GitBook chapter 25 (`docs/gitbook/25-documentation-sync-and-coverage-matrix.md`) to explicitly call out WS-B9 synchronization expectations.
- Extended Tier 3 anchor enforcement in `scripts/test_tier3_invariant_surface.sh` to require the updated documentation-sync baseline marker and added a targeted ShellCheck suppression (`SC2016`) for the literal regex line.
- Re-ran full validation gates (`test_fast`, `test_full`, default + experimental `test_nightly`) to verify end-to-end consistency.
- Bumped patch version to **`0.9.25`** and synchronized root version marker in `README.md`.

## [0.9.24] - 2026-02-18

### WS-B9 threat model and security hardening completion
- Published the canonical security baseline document at `docs/THREAT_MODEL.md` and added GitBook mirror chapter `docs/gitbook/28-threat-model-and-security-hardening.md`.
- Hardened bootstrap supply-chain behavior in `scripts/setup_lean_env.sh` by replacing remote `curl | sh` execution with temporary-file download + SHA-256 verification (`ELAN_INSTALLER_SHA256`) before installer execution.
- Expanded `.gitignore` to block common local secret/config files and scanner outputs from being committed.
- Synchronized active-slice/workstream status across README/spec/development/workstream-plan/GitBook pages to mark WS-B9 completed.
- Extended Tier 3 invariant/doc anchors to enforce WS-B9 security surfaces (threat model presence + setup checksum markers).
- Bumped patch version to **`0.9.24`** and synchronized root version marker in `README.md`.

## [0.9.23] - 2026-02-18

### WS-B8 post-review refinement and CI/doc-policy synchronization
- Refined CI branch-protection policy documentation (`docs/CI_POLICY.md`) so required checks now include `Docs Automation / Navigation + Links + DocGen Probe`, matching the live `lean_action_ci` workflow.
- Updated testing contract docs (`docs/TESTING_FRAMEWORK_PLAN.md`, `docs/gitbook/07-testing-and-ci.md`) to explicitly document Tier 0 docs-sync automation (`scripts/test_docs_sync.sh`) and its role in required CI coverage.
- Expanded Tier 3 doc anchors in `scripts/test_tier3_invariant_surface.sh` to enforce the new docs-automation required-check and testing-doc synchronization surfaces.
- Bumped patch version to **`0.9.23`** and synchronized root version marker in `README.md`.

## [0.9.22] - 2026-02-18

### WS-B8 documentation automation + consolidation completion
- Added deterministic documentation automation tooling: `scripts/generate_doc_navigation.py` (manifest-driven GitBook navigation generation), `scripts/check_markdown_links.py` (local markdown link validation), and `scripts/test_docs_sync.sh` (single docs-sync execution entrypoint).
- Added `docs/gitbook/navigation_manifest.json` as the single source for generated handbook navigation and regenerated `docs/gitbook/README.md` + `docs/gitbook/SUMMARY.md` from that manifest.
- Wired documentation automation into required validation surfaces by invoking `scripts/test_docs_sync.sh` from `scripts/test_tier0_hygiene.sh`, and by adding a `Docs Automation / Navigation + Links + DocGen Probe` CI lane in `.github/workflows/lean_action_ci.yml`.
- Published root↔GitBook dedup ownership guidance in `docs/DOCS_DEDUPLICATION_MAP.md` and GitBook chapter mirror `docs/gitbook/27-documentation-deduplication-map.md`.
- Added planning-doc synchronization checklist enforcement via `.github/pull_request_template.md` and synchronized active-slice/workstream status docs to mark WS-B8 completed.
- Bumped patch version to **`0.9.22`** and synchronized root version marker in `README.md`.

## [0.9.21] - 2026-02-18

### WS-B7 synchronization audit follow-up
- Corrected remaining GitBook planning drift for WS-B7 completion by updating chapter 24 Phase P2 status to include WS-B7 completion state.
- Extended Tier 3 doc anchors to enforce this chapter-24 Phase P2 synchronization in `scripts/test_tier3_invariant_surface.sh`, preventing regression in future doc updates.
- Re-ran full and nightly validation/audit lanes to confirm repository-wide determinism and documentation consistency remain intact.
- Bumped patch version to **`0.9.21`** and synchronized root version marker in `README.md`.

## [0.9.20] - 2026-02-18

### WS-B7 audit optimization and IF-M1 test-surface hardening
- Added executable IF-M1 runtime assertions in `tests/InformationFlowSuite.lean` and wired them into Tier 2 negative validation via `lake exe information_flow_suite` in `scripts/test_tier2_negative.sh`, strengthening regression coverage for label-flow and observer-projection behavior.
- Expanded Tier 3 invariant anchors to enforce the new IF runtime suite presence and Tier 2 wiring (`scripts/test_tier3_invariant_surface.sh`).
- Synchronized testing/docs/GitBook evidence for the strengthened WS-B7 validation surface (`docs/TESTING_FRAMEWORK_PLAN.md`, `docs/gitbook/07-testing-and-ci.md`, `docs/audits/AUDIT_v0.9.0_WORKSTREAM_PLAN.md`, `docs/gitbook/24-comprehensive-audit-2026-workstream-planning.md`).
- Bumped patch version to **`0.9.20`** and synchronized root version marker in `README.md`.

## [0.9.19] - 2026-02-18

### WS-B7 information-flow proof-track start completion
- Implemented IF-M1 formal baseline modules in `SeLe4n/Kernel/InformationFlow/Policy.lean` and `SeLe4n/Kernel/InformationFlow/Projection.lean`, including security-label lattice primitives, flow-relation algebraic lemmas, observer projection helpers, and low-equivalence scaffolding.
- Wired information-flow modules into the aggregate kernel API (`SeLe4n/Kernel/API.lean`) and expanded Tier 3 invariant/doc anchors in `scripts/test_tier3_invariant_surface.sh` to continuously enforce IF-M1 surface and WS-B7 status synchronization.
- Published IF-M1 theorem targets + assumptions ledger in `docs/IF_M1_BASELINE_PACKAGE.md`, marked WS-B7 complete in canonical planning/spec/development/README/GitBook pages, and added WS-B7 closure evidence sections in planning mirrors.
- Bumped patch version to **`0.9.19`** and synchronized root version marker in `README.md`.

## [0.9.18] - 2026-02-18

### WS-B6 audit hardening follow-up
- Hardened Tier 3 documentation-synchronization guards in `scripts/test_tier3_invariant_surface.sh` so active-slice/phase-status wording for WS-B6 completion is continuously checked across README/spec/development guide/GitBook pages.
- Re-ran fast/full/nightly validation lanes to confirm no behavioral regressions and deterministic test stability under the tightened documentation anchors.
- Bumped patch version to **`0.9.18`** and synchronized root version marker in `README.md`.

## [0.9.17] - 2026-02-18

### WS-B6 post-merge synchronization audit
- Performed a full repository audit pass after WS-B6 merge and revalidated all quality tiers, including nightly default and nightly experimental determinism lanes.
- Fixed remaining documentation/GitBook status drift so WS-B6 completion is reflected consistently in:
  - `docs/gitbook/01-project-overview.md`,
  - `docs/gitbook/06-development-workflow.md`,
  - `docs/DEVELOPMENT.md`.
- Updated next-workstream guidance to point to WS-B7 as the next unfinished stream.
- Bumped patch version to **`0.9.17`** and synchronized the root version marker in `README.md`.

## [0.9.16] - 2026-02-18

### WS-B6 IPC completeness with notifications
- Added notification-object IPC model coverage in `SeLe4n/Model/Object.lean`: `NotificationState`, `Notification`, `KernelObject.notification`, `KernelObjectType.notification`, and `ThreadIpcState.blockedOnNotification`.
- Implemented executable notification transitions in `SeLe4n/Kernel/IPC/Operations.lean` with `notificationWait`/`notificationSignal` semantics and explicit scheduler runnable-queue interactions.
- Extended IPC invariant surfaces (`SeLe4n/Kernel/IPC/Invariant.lean`) so global `ipcInvariant` now covers both endpoint and notification object classes.
- Expanded regression evidence with notification paths in `SeLe4n/Testing/MainTraceHarness.lean`, `tests/NegativeStateSuite.lean`, and `tests/fixtures/main_trace_smoke.expected`, and added WS-B6 Tier 3 anchors in `scripts/test_tier3_invariant_surface.sh`.
- Marked WS-B6 as completed across root docs/spec/development guide and GitBook planning mirrors.
- Bumped patch version to **`0.9.16`** and synchronized root version marker in `README.md`.

## [0.9.15] - 2026-02-18

### WS-B5 semantic-correctness refinement
- Corrected `CNode.resolveSlot` semantics so `depth` is interpreted as consumed bits with `depth >= radix`, guard width `depth - radix`, and guard comparison against extracted guard bits; removed the unreachable `slotOutOfRange` branch.
- Updated `cspaceResolvePath` error mapping to the refined `ResolveError` space and realigned WS-B5 negative tests (`tests/NegativeStateSuite.lean`) to validate true depth-mismatch and guard-mismatch paths under the corrected semantics.
- Refined main trace WS-B5 coverage to assert meaningful behaviors only: removed impossible radix-0 depth-mismatch source branch and strengthened deep CNode success/guard-mismatch paths with valid pointers/depths.
- Bumped patch version to **`0.9.15`** and synchronized root version marker in `README.md`.

## [0.9.14] - 2026-02-18

### WS-B5 trace/invariant hardening follow-up
- Fixed WS-B5 trace semantics to avoid misleading "unexpected" alias output by making alias-path behavior explicit in `SeLe4n/Testing/MainTraceHarness.lean` and anchoring deep-path success with a valid guard/radix CPtr.
- Expanded Tier 2 fixture coverage by adding source/deep CSpace path expectations in `tests/fixtures/main_trace_smoke.expected` so WS-B5 path traversal outputs are regression-checked.
- Added Tier 3 invariant/doc anchors for WS-B5 (`ResolveError`, `resolveSlot`, `cspaceResolvePath`, `cspaceLookupPath`, and canonical WS-B5 completion header) in `scripts/test_tier3_invariant_surface.sh`.
- Bumped package patch version to **`0.9.14`** and synchronized root version marker in `README.md`.

## [0.9.13] - 2026-02-18

### WS-B5 CSpace guard/radix semantics completion
- Implemented executable guard/radix pointer traversal for CNodes via `CNode.resolveSlot` in `SeLe4n/Model/Object.lean`, including explicit depth mismatch and guard mismatch failure branches.
- Added path-addressed CSpace APIs (`CSpacePathAddr`, `cspaceResolvePath`, `cspaceLookupPath`) in `SeLe4n/Kernel/Capability/Operations.lean` so resolution semantics are exercised independently from direct slot lookup.
- Extended malformed-state coverage in `tests/NegativeStateSuite.lean` with WS-B5 path-resolution success + failure checks, and synchronized active-slice status/closure evidence in README/spec/development/workstream-plan/GitBook docs.
- Bumped package patch version to **`0.9.13`** and synchronized root version marker in `README.md`.

## [0.9.12] - 2026-02-18

### WS-B documentation/test-sync audit hardening
- Audited and corrected stale testing/hardware-direction status language so active-slice references consistently describe Comprehensive Audit 2026-02 WS-B execution rather than post-M7 next-slice wording.
- Added Tier 3 WS-B4 closure anchors in `scripts/test_tier3_invariant_surface.sh` that assert wrapper-structure presence for `DomainId`, `Priority`, `Irq`, `Badge`, `ASID`, `VAddr`, and `PAddr`.
- Bumped package patch version to **`0.9.12`** and synchronized root version marker in `README.md`.

## [0.9.11] - 2026-02-18

### Documentation synchronization hardening (WS-B4 follow-through)
- Audited and corrected stale GitBook/archive status language so active-slice references now consistently point to the Comprehensive Audit 2026-02 WS-B portfolio and mark older M7/post-M7 transition pages as historical context.
- Updated historical audit metadata pointers in `docs/audits/AUDIT_v0.9.0.md` so readers are directed to the current comprehensive-audit baseline and workstream execution backbone.
- Bumped package patch version to **`0.9.11`** and synchronized root version marker in `README.md`.

## [0.9.10] - 2026-02-18

### WS-B4 completion / remaining wrapper migration
- Upgraded `DomainId`, `Priority`, `Irq`, `Badge`, `ASID`, `VAddr`, and `PAddr` in `SeLe4n/Prelude.lean` from `Nat` aliases to dedicated wrapper structures with explicit migration helpers (`ofNat`/`toNat`) and compatibility instances (`OfNat`, `ToString`).
- Added a Tier 0 WS-B4 regression guard in `scripts/test_tier0_hygiene.sh` that fails if any of the migrated wrappers regress to `abbrev ... := Nat`.
- Synchronized active-slice status across root docs/spec/development guide/GitBook and canonical workstream planning docs to mark WS-B4 complete.

# Changelog

## 2026-02-19 — WS-C4 test validity hardening + documentation sync

- Completed **WS-C4 (Test validity hardening)** by adding executable invariant checks, asserting invariant validity at test fixture entry points, and enforcing post-success invariant checks in the negative state suite and trace probe.
- Hardened `MainTraceHarness` by asserting baseline and post-schedule invariant validity before running the smoke trace sequence.
- Updated active workstream status references across root docs and GitBook pages to mark WS-C4 as completed and reflect the next active execution focus.
- Bumped patch version to **`0.10.1`** and synchronized root version markers.

## [0.9.9] - 2026-02-17

### WS-B3 scenario-function decomposition and end-to-end sync audit
- Refined `SeLe4n/Testing/MainTraceHarness.lean` by decomposing the large monolithic `runMainTraceFrom` body into dedicated scenario functions (`runCapabilityAndArchitectureTrace`, `runServiceAndStressTrace`, `runLifecycleAndEndpointTrace`) while preserving stable trace output ordering and semantics.
- Re-ran complete repository validation (fast/smoke/full/nightly default+experimental and `audit_testing_framework`) to verify deterministic trace behavior and full documentation/test anchor consistency.
- Bumped package patch version to **`0.9.9`** and synchronized root version markers.

## [0.9.8] - 2026-02-17

### WS-B3 post-merge audit and synchronization hardening
- Removed an unused `TraceStep` alias from `SeLe4n/Testing/MainTraceHarness.lean` to keep the extracted harness surface minimal and intentional.
- Synchronized remaining GitBook active-slice status text (`docs/gitbook/README.md`) so WS-B3 completion state matches README/spec/development/workstream-plan snapshots.
- Re-ran full validation coverage (`test_fast`, `test_smoke`, `test_full`, default+experimental `test_nightly`, and `audit_testing_framework`) to verify full-repository consistency.
- Bumped package patch version to **`0.9.8`** and synchronized root version markers.

## [0.9.7] - 2026-02-17

### WS-B3 main trace harness refactor completion
- Refactored the executable trace harness by extracting orchestration from `Main.lean` into `SeLe4n/Testing/MainTraceHarness.lean`, keeping scenario execution composable and auditable while retaining deterministic behavior.
- Replaced ad hoc bootstrap state construction with list-driven builder composition using `SeLe4n/Testing/StateBuilder.lean` in the main harness bootstrap path.
- Updated audit/spec/development/README/GitBook status tracking to mark WS-B3 completed and record closure evidence.
- Bumped package patch version to **`0.9.7`** and synchronized root version markers.

## [0.9.6] - 2026-02-17

### WS-B2 negative-suite correctness hardening
- Refined `tests/NegativeStateSuite.lean` endpoint coverage to test both `.endpointStateMismatch` (idle endpoint receive) and `.endpointQueueEmpty` (send-state empty queue) on explicit fixtures, removing the prior mislabeled assertion gap.
- Re-ran full repository validation (`test_fast`, `test_smoke`, `test_full`, default/experimental `test_nightly`, and `audit_testing_framework`) to ensure code/docs/gitbook/test contracts remain synchronized and deterministic.
- Bumped package patch version to **`0.9.6`** and synchronized root version markers.

## [0.9.5] - 2026-02-17

### WS-B2 generative + negative testing expansion completion
- Added reusable bootstrap-state builder DSL in `SeLe4n/Testing/StateBuilder.lean` and a dedicated malformed-state executable suite in `tests/NegativeStateSuite.lean` (wired as `lake exe negative_state_suite`).
- Extended smoke/full gates with `scripts/test_tier2_negative.sh` so negative-path assertions are required alongside trace fixtures.
- Expanded nightly experimental candidates to persist per-seed stochastic probe logs and a replay manifest (`tests/artifacts/nightly/trace_sequence_probe_manifest.csv`) for deterministic triage.
- Synchronized active-slice documentation and GitBook mirrors to mark WS-B2 as completed and record closure evidence in the comprehensive-audit workstream plan.
- Bumped package patch version to **`0.9.5`** and synchronized root version markers.

## [0.9.4] - 2026-02-17

### Bootstrap reliability + doc-sync hardening follow-up
- Hardened `scripts/setup_lean_env.sh` apt bootstrap behavior: if `apt-get update` fails due an unavailable third-party source, the script now retries using primary distro sources only so required setup dependencies can still install deterministically.
- Updated developer workflow docs and GitBook mirror to document the new setup fallback behavior and keep contributor guidance aligned with executable setup semantics.
- Bumped package patch version to **`0.9.4`** and synchronized root version marker.

## [0.9.3] - 2026-02-17

### WS-B1 audit hardening and repository-wide synchronization pass
- Corrected WS-B1 ASID/root modeling by replacing the previous malformed `asidBoundToRoot` relation with a proper existential relation and documenting the explicit bounded discovery-window assumption in code and ADR.
- Added VSpace soundness/determinism anchors (`resolveAsidRoot_sound`, `vspaceLookup_deterministic`) and strengthened Tier-3 invariant-surface guards accordingly.
- Performed a full documentation/GitBook consistency pass so phase sequencing and active-slice wording consistently reflect `WS-B1 completed` status across spec/development/workflow pages.
- Updated audit index wording to align with the current `0.9.3` baseline and synchronized package version markers.

## [0.9.2] - 2026-02-17

### WS-B1 VSpace + memory model foundation completion
- Implemented first-class VSpace modeling with `VSpaceRoot` kernel objects, deterministic map/unmap/lookup transitions, and explicit failure modes for ASID binding, mapping conflicts, and translation faults.
- Added WS-B1 architecture invariant surface (`vspaceInvariantBundle`) and bounded translation predicate scaffold to anchor follow-on proof work.
- Extended `Main.lean` executable trace and Tier 2 fixture expectations with deterministic VSpace map→lookup→unmap→fault coverage.
- Published VSpace/memory abstraction ADR (`docs/VSPACE_MEMORY_MODEL_ADR.md`) and synchronized GitBook/state-tracking docs to mark WS-B1 completed in the active comprehensive-audit slice.
- Bumped package patch version from `0.9.1` to **`0.9.2`**.

## [0.9.1] - 2026-02-17

### Comprehensive-audit workstream execution kickoff readiness
- Expanded `docs/audits/AUDIT_v0.9.0_WORKSTREAM_PLAN.md` into a detailed execution contract with per-workstream goals, prerequisites, implementation slices, evidence contracts, and exit criteria for WS-B1..WS-B11.
- Added explicit portfolio readiness gates (G0 kickoff readiness and G1 hardware-entry readiness) and clarified that the current slice is centered on WS-B execution kickoff.
- Synchronized root README, audit index, and GitBook planning chapter wording so active-slice status consistently reflects comprehensive-audit workstream execution readiness.
- Bumped package patch version from `0.9.0` to **`0.9.1`**.

## [0.9.0] - 2026-02-17

### CI security-scan reliability follow-up
- Fixed Gitleaks shallow-clone ambiguous revision failures by setting `actions/checkout` `fetch-depth: 0` in the security baseline scan job.
- Fixed `Platform and Security Baseline` workflow permissions by adding `pull-requests: read`, resolving Gitleaks pull-request commit enumeration failures (`Resource not accessible by integration`) in the `Security Signal / Secret + Dependency + CodeQL` job.
- Updated `docs/CI_POLICY.md` to document the `pull-requests: read` requirement and rationale for the Gitleaks PR scan path.
- Made CodeQL analyze upload non-blocking (`continue-on-error: true`) to avoid failing the security lane when repository Code Scanning is not enabled.
- Added Tier 3 invariant/doc anchor coverage to ensure the workflow retains `pull-requests: read` in future refactors.
- Version marker remains `0.9.0` as the canonical minor-release target for this slice.


### M7 exit-gate closeout and next-slice activation
- Published formal M7 closeout artifact `docs/M7_CLOSEOUT_PACKET.md` and GitBook mirror `docs/gitbook/23-m7-remediation-closeout-packet.md`, including dependency owners, accepted residual risks, and exit-gate checklist evidence.
- Synchronized root docs/spec/development/testing/GitBook stage markers so M7 is completed baseline and post-M7 hardware-oriented next-slice execution is active.
- Expanded Tier-3 documentation anchors to validate closeout packet presence and stage-state synchronization as part of required full-suite checks.
- Bumped project version from `0.8.22` to **`0.9.0`** for the post-remediation minor release transition.

## [0.8.22] - 2026-02-17

### WS-A8 validation hardening and CI robustness
- Hardened `.github/workflows/platform_security_baseline.yml` so security scanning is skipped for fork-origin pull requests where `security-events: write` is unavailable, while keeping the ARM64 fast-gate lane active.
- Expanded test/docs synchronization by adding WS-A8 artifact anchor checks to `scripts/test_tier3_invariant_surface.sh` (workflow/job names, roadmap milestones, and cross-doc references).
- Updated testing docs (`docs/TESTING_FRAMEWORK_PLAN.md` and `docs/gitbook/07-testing-and-ci.md`) to explicitly include WS-A8 platform/security baseline automation in the CI/test contract narrative.
- Bumped package patch version to `0.8.22` and synchronized README version marker.

## [0.8.21] - 2026-02-17

### WS-A8 platform/security maturity completion
- Added `.github/workflows/platform_security_baseline.yml` to operationalize WS-A8 gates: an ARM64 architecture-targeted fast lane (`ubuntu-24.04-arm`) and automated baseline security scanning (Gitleaks, Trivy, CodeQL for workflow analysis).
- Published `docs/INFORMATION_FLOW_ROADMAP.md` with staged IF-M1..IF-M5 milestones, deliverables, and exit-evidence expectations for post-M7 information-flow proofs.
- Updated remediation/development/GitBook tracking docs to mark WS-A8 completed and synchronized CI policy/README references with the new security and roadmap artifacts.
- Bumped package patch version to `0.8.21` and synchronized the root README version marker.

## [0.8.20] - 2026-02-17

### Validation and documentation synchronization follow-up
- Refined nightly-testing documentation (`docs/TESTING_FRAMEWORK_PLAN.md` and `docs/gitbook/07-testing-and-ci.md`) to match mode-aware Tier 4 status behavior in `scripts/test_nightly.sh` (default extension-point guidance vs executed signal when `NIGHTLY_ENABLE_EXPERIMENTAL=1`).
- Re-validated smoke/full/nightly test tiers (default + experimental) to confirm repository and GitBook/testing docs remain synchronized with current M7 progress state.
- Bumped package patch version to `0.8.20` and synchronized the root README version marker.

## [0.8.19] - 2026-02-17

### Audit hardening follow-up
- Optimized `scripts/test_nightly.sh` reporting so Tier 4 status messaging is environment-aware: it now reports staged execution when `NIGHTLY_ENABLE_EXPERIMENTAL=1` and reports extension-point guidance only in default mode.
- Re-ran full validation coverage (`test_smoke`, `test_full`, default `test_nightly`, experimental `test_nightly`, `lake build`, and executable trace run) to confirm repository, docs, and GitBook remain synchronized with current M7/WS-A7 status.
- Bumped package patch version to `0.8.19` and synchronized the root README version marker.

## [0.8.18] - 2026-02-17

### WS-A7 proof maintainability completion
- Completed WS-A7 by introducing shared helper theorem `endpoint_store_preserves_schedulerInvariantBundle` in `SeLe4n/Kernel/IPC/Invariant.lean`, reducing repeated scheduler-bundle proof blocks across endpoint send/await/receive preservation theorems.
- Added concise theorem-purpose docstrings for the shared helper and endpoint scheduler-bundle preservation theorem entrypoints to improve proof-surface legibility for reviewers.
- Updated development guide and GitBook workstream status pages to mark WS-A7 completed and move active focus to WS-A8.
- Bumped package patch version to `0.8.18` and synchronized the root README version marker.

## [0.8.17] - 2026-02-17

### Documentation/GitBook sync audit hardening
- Closed remaining WS-A6-era documentation drift by marking WS-A4 as completed in `docs/M7_CLOSEOUT_PACKET.md` to match existing closure evidence and the active-slice status pages.
- Updated `docs/gitbook/13-future-slices-and-delivery-plan.md` so M7 workstream statuses are synchronized with current slice reality (WS-A1..WS-A6 completed, WS-A7 in progress, WS-A8 planned).
- Bumped package patch version to `0.8.17` and synchronized the root README version marker.

## [0.8.16] - 2026-02-17

### WS-A6 documentation IA completion
- Marked WS-A6 as completed across remediation planning and active-slice GitBook chapters with explicit closure evidence and DoD status updates.
- Added a contributor-first 5-minute onboarding path in `CONTRIBUTING.md`, synchronized root `README.md` start-here ordering, and mirrored the same quickstart flow in `docs/gitbook/README.md`.
- Updated M7 completion snapshot in `docs/DEVELOPMENT.md` to reflect WS-A6 closure and move active focus to WS-A7.

## [0.8.15] - 2026-02-17

### WS-A5 regression-guard refinement
- Added Tier 3 invariant/doc anchors for WS-A5 closure evidence: fixture-module presence, `Main.lean` fixture import, and hardware-boundary policy guard language.
- Preserved full Tier 0–4 validation after extending regression anchors.

## [0.8.14] - 2026-02-17

### WS-A5 audit follow-up hardening
- Hardened Tier 0 import-boundary hygiene to include a non-`rg` fallback scan path, preventing false failures in environments where ripgrep is unavailable.
- Tightened `docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md` wording so policy scope matches enforcement (`SeLe4n/Kernel`).

## [0.8.13] - 2026-02-17

### Hardware-boundary safety / WS-A5 completion
- Isolated permissive runtime contract fixtures into `SeLe4n/Testing/RuntimeContractFixtures.lean` and updated `Main.lean` to consume them from a testing-only module.
- Added Tier 0 hygiene boundary enforcement to fail if production modules under `SeLe4n/` reference test-only runtime contract fixtures.
- Added `docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md` and synchronized remediation/GitBook workstream status to mark WS-A5 complete.

## [0.8.12] - 2026-02-17

### Testing / WS-A4 completion hardening
- Expanded Tier 2 fixture-backed trace coverage in `Main.lean` + `tests/fixtures/main_trace_smoke.expected` to explicitly cover all audit-recommended scale categories: deep CNode radix shape, large runnable queue (10+), multiple IPC endpoints, service dependency chain depth-5, and boundary memory addresses.
- Kept Tier 2 scenario/risk tagging format for audit traceability while adding new WS-A4 scale scenarios under `WS-A4-SCALE-*` IDs.
- Revalidated Tier 0–4 scripts (including seeded `trace_sequence_probe`) with the expanded scenarios and refreshed M7 workstream documentation evidence.

All notable changes to this project are documented in this file.

## [0.8.10] - 2026-02-17

### WS-A3 regression-guard hardening
- Added Tier-3 invariant-surface guards that require explicit `ThreadId.toObjId` conversion entrypoint presence and fail if an implicit `ThreadId -> ObjId` coercion is reintroduced.
- Revalidated full Tier 0-4 test coverage (`test_fast`, `test_smoke`, `test_full`, `test_nightly` with experimental candidates) after introducing the new guard.

## [0.8.9] - 2026-02-17

### WS-A3 audit follow-up hardening
- Removed implicit `ThreadId -> ObjId` coercion and replaced it with explicit `ThreadId.toObjId` conversions at object-store boundaries to preserve stronger compile-time domain separation.
- Updated scheduler and IPC proof/operation call sites to use explicit conversion points and kept all invariant bundles compiling without placeholder debt.
- Synchronized GitBook planning chapters so WS-A3 completion state is consistent across current-slice and remediation overview pages.

## [0.8.8] - 2026-02-17

### M7 WS-A3 type-safety uplift
- Migrated `ThreadId`, `ObjId`, `CPtr`, and `Slot` from raw `Nat` aliases to dedicated wrapper types with migration helpers (`ofNat`/`toNat`) and typed bridge instances where object-store indexing is intentional.
- Updated scheduler/IPC invariant surfaces to keep thread-domain membership obligations typed as `ThreadId` while preserving object-store key discipline through `ObjId`.
- Updated active-slice docs/GitBook to mark WS-A3 completed and synced current development status snapshots.

## [0.8.7] - 2026-02-17

### Tooling setup optimization
- Refactored `scripts/setup_lean_env.sh` to share package-manager helpers and perform `apt-get update` at most once even when both `shellcheck` and `ripgrep` are missing.
- Preserved all existing installer behavior while reducing duplicated setup work/noise in cold environments.

## [0.8.6] - 2026-02-17

### Audit/Sync hardening
- Performed full post-WS-A2 repository validation sweep (`test_fast`, `test_smoke`, `test_full`, `test_nightly`) and confirmed all tiers pass without regressions.
- Synchronized roadmap and audit-context docs so M7 status explicitly reflects WS-A1/WS-A2 as completed while preserving historical audit snapshot intent.
- Clarified historical audit caveat language so architecture criticisms about IPC split are interpreted as pre-remediation findings, not current-state defects.

## [0.8.5] - 2026-02-17

### Architecture / API modularity (WS-A2)
- Split IPC transition semantics into `SeLe4n/Kernel/IPC/Operations.lean` and retained invariant/proof obligations in `SeLe4n/Kernel/IPC/Invariant.lean` to restore operations/invariant symmetry.
- Kept `SeLe4n/Kernel/API.lean` as the stable external facade while explicitly exporting IPC operations and invariant surfaces.
- Updated development documentation and GitBook architecture maps/workstream tracking to mark WS-A2 complete with closure evidence.

## [0.8.4] - 2026-02-17

### CI / Tooling reliability
- Updated `scripts/setup_lean_env.sh` to install `ripgrep` (`rg`) when missing, matching Tier-3/Tier-4 script requirements and preventing CI failures where `rg` is unavailable.

## [0.8.3] - 2026-02-17

### CI / Tooling reliability
- Fixed `scripts/setup_lean_env.sh` to source existing elan env before probing/installing, preventing redundant reinstall attempts in CI shells that do not persist PATH changes.
- Fixed `scripts/setup_lean_env.sh` to treat already-installed Lean toolchains as a success path, preventing CI failures when `leanprover/lean4:v4.27.0` is present.

## [0.8.2] - 2026-02-17

### Documentation
- Added root `CONTRIBUTING.md` pointer to canonical contributor workflow in `docs/DEVELOPMENT.md`.
- Added root `CHANGELOG.md` for chronological release notes and milestone-delivery traceability.
- Added post-audit remediation note in `docs/audits/AUDIT_v0.8.0.md` clarifying WS-A1 CI hardening landed after the audit snapshot.

### CI / Quality Gates
- Added Tier 3/WS-A1 documentation anchor checks for CI policy/workflow artifacts and root contributor/changelog discoverability in `scripts/test_tier3_invariant_surface.sh`.

## [0.8.1] - 2026-02-17

### CI / Quality Gates (WS-A1)
- Promoted Tier 3 (`test_full.sh`) into CI merge-gate flow.
- Added nightly determinism workflow running `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh`.
- Added canonical branch-protection policy doc `docs/CI_POLICY.md`.
- Added Lean/Lake cache restoration in CI workflows.

## [0.8.0] - 2026-02-17

### Baseline
- M6 complete / M7 active audit-remediation baseline.
