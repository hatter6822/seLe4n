# WS-AH Workstream Plan — Pre-Release Comprehensive Audit Remediation (v0.27.1)

**Created**: 2026-04-11
**Baseline version**: 0.27.1
**Baseline audit**: `docs/audits/AUDIT_v0.27.1_PRE_RELEASE_COMPREHENSIVE.md` (2 HIGH, 11 MEDIUM, 17 LOW, 14 INFO)
**Prior portfolios**: WS-AG (COMPLETE), WS-AF (COMPLETE), WS-AE (COMPLETE), WS-AD (COMPLETE), WS-AC (COMPLETE), WS-AB (COMPLETE), WS-AA (COMPLETE) — see `docs/WORKSTREAM_HISTORY.md`
**Hardware target**: Raspberry Pi 5 (ARM64)
**Constraint**: Zero sorry/axiom. All phases must pass `lake build` + `test_smoke.sh` at minimum.

---

## 1. Executive Summary

The v0.27.1 Pre-Release Comprehensive Audit identified 44 findings across the
full seLe4n codebase (2 HIGH, 11 MEDIUM, 17 LOW, 14 INFORMATIONAL). This
workstream plan addresses all actionable findings through 5 phases with 27
sub-tasks, after filtering out erroneous severity classifications,
already-tracked deferrals, and confirmed-correct design decisions.

### 1.1 Finding Disposition Summary

| Disposition | Count | Details |
|-------------|-------|---------|
| **Actionable (code change)** | 9 | H-01, H-02, M-01, M-02, M-03, L-02, L-04, L-08, L-14 (+ H-02 includes 14 stale version files) |
| **Documentation-only** | 8 | M-04, M-05, M-06, M-07, M-08, L-11, L-12, L-13 |
| **Overstated / reclassified** | 3 | M-09 → INFO, M-10 → already tracked, M-11 → INFO |
| **No-action (confirmed correct)** | 8 | L-01, L-03, L-05, L-06, L-07, L-09, L-15, L-17 |
| **Subsumed by other fix** | 1 | L-16 (fixed by M-03) |
| **Deferred (already tracked)** | 1 | L-10 (deferred to WS-V) |
| **Informational (no action)** | 14 | I-01 through I-14 |

### 1.2 Plan Structure

| Phase | Focus | Sub-tasks | Key Findings | Gate |
|-------|-------|-----------|-------------|------|
| AH1 | Critical IPC Dispatch Correctness | 5 | H-01, M-01 | `lake build` + `test_smoke.sh` |
| AH2 | IPC Donation Safety & Boot Pipeline | 7 | M-02, M-03, L-02, L-16 | `lake build` + `test_smoke.sh` |
| AH3 | Capability, Architecture & Decode Hardening | 3 | L-04, L-08, L-14 | `lake build` + `test_smoke.sh` |
| AH4 | Version Consistency & CI Automation | 6 | H-02, version drift | `cargo test` + version check |
| AH5 | Documentation, Testing & Closure | 6 | M-04–M-08, L-11–L-13, doc sync | `test_full.sh` + doc sync |

**Estimated scope**: ~300–450 new/modified lines of Lean, ~20 lines of Rust,
~200–300 lines of shell/CI scripts, ~400–600 lines of documentation changes.

**Total sub-tasks**: 27 (across 5 phases)

---

## 2. Finding Cross-Reference and Verification

Every finding from the baseline audit was independently re-verified against
source code before inclusion in this plan. This section classifies each finding
and provides the verification rationale.

### 2.1 Erroneous / Overstated Findings (3)

| Finding | Audit Severity | Actual | Rationale |
|---------|---------------|--------|-----------|
| M-09 | MEDIUM | **INFORMATIONAL** | `LabelingContextValid` as a deployment obligation is **identical to seL4's design**. The codebase already has `labelingContextValid_is_deployment_requirement` witness theorem (Composition.lean:694-695). No runtime enforcement is needed — this is the correct architecture for a separation kernel. Reclassified to INFORMATIONAL. |
| M-10 | MEDIUM | **ALREADY TRACKED** | CDT `descendantsOf` fuel sufficiency is already tracked as TPI-DOC and explicitly deferred to WS-V (Structures.lean:2234-2245, CrossSubsystem.lean:92-133). The current depth-1 proof (`descendantsOf_fuel_sufficiency`) is documented with its scope limitation. No new action required beyond existing deferral. |
| M-11 | MEDIUM | **INFORMATIONAL** | The audit itself confirms: "No user-facing operation uses the 2^52 default." The bare `vspaceMapPageChecked` helper is documented as "proof-layer default only" (VSpace.lean:54-59). The production dispatch path (`vspaceMapPageCheckedWithFlushFromState`) correctly reads `st.machine.physicalAddressWidth`. Internal-only proof helpers do not need platform-specific bounds. |

### 2.2 No-Action Findings (8 LOW + 14 INFORMATIONAL)

These findings describe confirmed-correct design patterns, seL4-matching
semantics, or invariant-protected code paths. No code or documentation changes
are needed.

| Finding | Rationale |
|---------|-----------|
| L-01 | `endpointQueueRemove` stale-read is safe under `tcbQueueChainAcyclic` invariant (predecessor ≠ successor). Comment WS-L1/L1-A explicitly documents the safety argument. |
| L-03 | `sender == receiver` is unreachable under `runnableThreadIpcReady` + `currentNotEndpointQueueHead` scheduler-IPC coherence invariants. A sender in `.ready` IPC state cannot be in a receive queue. |
| L-05 | RunQueue `size` is diagnostics-only (AF-40). Not referenced by scheduling selection logic. Proof-enforcement would add complexity with zero functional benefit. |
| L-06 | CBS integer truncation is standard practice. Per-context budget bounds (`budgetWithinBounds`) hold regardless of admission precision. Documented at Budget.lean:204-217. |
| L-07 | `schedContextUnbind` clearing current without rescheduling matches seL4 semantics. Dequeue-on-dispatch ensures the next `schedule` call will select correctly. |
| L-09 | `tlbBarrierComplete = True` is appropriate for the sequential abstract model. Hardware barrier correctness is enforced by Rust HAL wrappers (DSB ISH + ISB after every TLBI). |
| L-15 | `storeObject` VSpaceRoot ASID replacement is safe under `AsidManager` uniqueness invariant (`asidPoolUnique`). Each ASID maps to exactly one ObjId. |
| L-17 | Scheduling covert channel is accepted by design, matching seL4's domain scheduler visibility. Explicitly documented with `accepted_scheduling_covert_channel` bound theorem (Projection.lean:355-407). |
| I-01–I-14 | All 14 informational findings describe correct architectural properties (proven unreachability, deliberate dual dispatch, compile-time exhaustiveness, etc.). No action required. |

### 2.3 Subsumed Findings (1)

| Finding | Subsumed By | Rationale |
|---------|-------------|-----------|
| L-16 | M-03 | Default PA width 52 vs RPi5 44 is the same root cause as M-03 (`bootFromPlatform` not calling `applyMachineConfig`). Integrating `applyMachineConfig` into the boot pipeline (Phase AH2) eliminates both issues. |

### 2.4 Already-Deferred Findings (1)

| Finding | Deferral | Rationale |
|---------|----------|-----------|
| L-10 | WS-V | No minimum-configuration validation at boot. Already documented at Boot.lean:139-145 with explicit WS-V deferral annotation. `bootFromPlatformChecked` variant exists for production paths. |

### 2.5 Actionable Findings — Verification Summary

| Finding | Severity | Verified | Evidence | Phase |
|---------|----------|----------|----------|-------|
| H-01 | **HIGH** | ✓ Confirmed | Checked `.send` calls `endpointSendDualChecked` → `endpointSendDual` (no caps). Unchecked `.send` calls `endpointSendDualWithCaps` (with caps). `.call` is unaffected — both paths use WithCaps. API.lean:621 vs 820, Wrappers.lean:28-43. | AH1 |
| H-02 | **HIGH** | ✓ Confirmed | `KERNEL_VERSION = "0.26.8"` at boot.rs:11. lakefile.toml:8 = `"0.27.1"`. 13 additional files have stale version strings. | AH4 |
| M-01 | **MEDIUM** | ✓ Confirmed | `validateVSpaceMapPermsForMemoryKind` defined at SyscallArgDecode.lean:256, tested in DecodingSuite.lean:451, but zero calls from `.vspaceMap` dispatch arm in API.lean:459-467. Device memory could receive execute permission through the syscall path. | AH1 |
| M-02 | **MEDIUM** | ✓ Confirmed | `applyCallDonation` returns `SystemState` (Donation.lean:63). Error from `donateSchedContext` maps to `| .error _ => st`. Same pattern for `applyReplyDonation` (line 163). 5 call sites in API.lean. 3 preservation theorems need conditional postconditions. | AH2 |
| M-03 | **MEDIUM** | ✓ Confirmed | `bootFromPlatform` (Boot.lean:148) processes IRQ tables and objects only. `applyMachineConfig` (Boot.lean:326) is a separate function. Only 1 test caller manually chains them (NegativeStateSuite.lean:3312-3314). `PlatformConfig` lacks a `MachineConfig` field. | AH2 |
| M-04 | **MEDIUM** | ✓ Confirmed | `bootSafeObject` at Boot.lean:898: `(∀ vs, obj ≠ .vspaceRoot vs)`. Deliberate exclusion — ASID table registration unavailable at boot. Documentation-only action. | AH5 |
| M-05 | **MEDIUM** | ✓ Confirmed | Sim `registerContextStable := fun _ _ => True` vs RPi5 6-condition check. By design — documentation-only action. | AH5 |
| M-06 | **MEDIUM** | ✓ Confirmed | `resolveCapAddress` (Operations.lean:85-128) has no `hasRight` during traversal. Documented as U-M25 deliberate divergence. Documentation-only action (spec update). | AH5 |
| M-07 | **MEDIUM** | ✓ Confirmed | `projectKernelObject` strips `registerContext := default` but keeps `pendingMessage` (Projection.lean:185-201). Unreachable under NI invariants. Documentation-only action. | AH5 |
| M-08 | **MEDIUM** | ✓ Confirmed | Gap acknowledged at CrossSubsystem.lean:273-292. 10-predicate conjunction with 45 pairwise disjointness analyses. Documentation-only action. | AH5 |
| L-02 | **LOW** | ✓ Confirmed | `timeoutAwareReceive` returns `.completed IpcMessage.empty` for `pendingMessage = none` (Timeout.lean:131-133). Should return error to surface protocol violations. | AH2 |
| L-04 | **LOW** | ✓ Confirmed | `cspaceRevokeCdtStrict` removes CDT node (line 999) even when `cspaceDeleteSlotCore` fails (line 993). Capability slot persists without CDT tracking. | AH3 |
| L-08 | **LOW** | ✓ Confirmed | `setIPCBufferOp` (IpcBufferValidation.lean:92-110) uses struct-with syntax directly instead of `storeObject`. Duplicates object storage logic. | AH3 |
| L-14 | **LOW** | ✓ Confirmed | Hardcoded `65536` at SyscallArgDecode.lean:209 and 234. Should use `st.machine.maxASID` from `MachineConfig`. | AH3 |

### 2.6 Documentation-Only Findings

| Finding | Documentation Action | Phase |
|---------|---------------------|-------|
| M-04 | Add design-rationale comment explaining VSpaceRoot exclusion and ASID table dependency. Note integration timeline in spec. | AH5 |
| M-05 | Document sim contract testing limitations in `SELE4N_SPEC.md` platform testing section. Note which production properties are not exercisable under simulation. | AH5 |
| M-06 | Document authority surface delta vs seL4 in `SELE4N_SPEC.md` capability section. Quantify the additional authority paths from skipping intermediate CNode rights checks. | AH5 |
| M-07 | Add analysis comment at `projectKernelObject` explaining why `pendingMessage` visibility is unreachable under NI invariants. Reference `runnableThreadIpcReady` and endpoint queue domain constraints. | AH5 |
| M-08 | Update cross-subsystem composition documentation with current 10-predicate status and 45 pairwise disjointness coverage. Note remaining gap scope. | AH5 |
| L-11 | Add `Badge` constructor safety analysis comment. Reference `valid` predicate, `ofNatMasked`, and boundary enforcement at `cspaceMint`. | AH5 |
| L-12 | Document `maxControlledPriority := 0xFF` default rationale. Note that `setPriorityOp` MCP enforcement prevents privilege escalation regardless of default. | AH5 |
| L-13 | Document TPIDR_EL0 / TLS gap in spec with hardware integration timeline. Note `RegisterFile` scope (GPRs, PC, SP only) and future AG-phase requirement. | AH5 |

---

## 3. Phase AH1 — Critical IPC Dispatch Correctness (H-01, M-01)

**Objective**: Fix the two most security-critical dispatch path issues: the
checked `.send` path silently dropping capability transfer (H-01) and the
device-memory execute permission validation gap (M-01).

**Dependencies**: None (first phase).

**Gate**: `source ~/.elan/env && lake build` + `./scripts/test_smoke.sh`

### 3.1 Sub-tasks

#### AH1-A: Fix `endpointSendDualChecked` to include capability transfer (H-01)

**Finding**: H-01 — Checked `.send` drops IPC capability transfer
**File**: `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean`
**Type**: Multi-step operation

The current `endpointSendDualChecked` (Wrappers.lean:28-43) delegates to plain
`endpointSendDual`, which does NOT perform capability transfer. The fix modifies
the existing wrapper to compose the information-flow check with the WithCaps
variant, following the exact pattern already established by `endpointCallChecked`
(Wrappers.lean:494-509).

**Atomic steps**:

1. **Read current state**: Read Wrappers.lean lines 28-50 (current
   `endpointSendDualChecked`) and lines 494-515 (`endpointCallChecked` as
   template).

2. **Modify `endpointSendDualChecked`**: Change the function to:
   - Add three parameters: `endpointRights : AccessRightSet`,
     `senderCspaceRoot : SeLe4n.ObjId`, `receiverSlotBase : SeLe4n.Slot`
   - Change return type from `Kernel Unit` to `Kernel CapTransferSummary`
   - Retain the message bounds checks (WS-H12d/A-09)
   - Retain the `securityFlowsTo` information-flow check
   - On policy approval: delegate to `endpointSendDualWithCaps` (not
     `endpointSendDual`)
   - On policy denial: return `.error .flowDenied` (unchanged)

   **Before** (current broken code):
   ```lean
   def endpointSendDualChecked
       (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
       (sender : SeLe4n.ThreadId)
       (msg : IpcMessage := IpcMessage.empty) : Kernel Unit :=
     fun st =>
       if msg.registers.size > maxMessageRegisters then .error .ipcMessageTooLarge
       else if msg.caps.size > maxExtraCaps then .error .ipcMessageTooManyCaps
       else
       let senderLabel := ctx.threadLabelOf sender
       let endpointLabel := ctx.endpointLabelOf endpointId
       if securityFlowsTo senderLabel endpointLabel then
         endpointSendDual endpointId sender msg st
       else .error .flowDenied
   ```

   **After** (fixed):
   ```lean
   def endpointSendDualChecked
       (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
       (sender : SeLe4n.ThreadId) (msg : IpcMessage)
       (endpointRights : AccessRightSet)
       (senderCspaceRoot : SeLe4n.ObjId)
       (receiverSlotBase : SeLe4n.Slot) : Kernel CapTransferSummary :=
     fun st =>
       if msg.registers.size > maxMessageRegisters then .error .ipcMessageTooLarge
       else if msg.caps.size > maxExtraCaps then .error .ipcMessageTooManyCaps
       else
       let senderLabel := ctx.threadLabelOf sender
       let endpointLabel := ctx.endpointLabelOf endpointId
       if securityFlowsTo senderLabel endpointLabel then
         endpointSendDualWithCaps endpointId sender msg endpointRights
           senderCspaceRoot receiverSlotBase st
       else .error .flowDenied
   ```

3. **Verify import**: Confirm `endpointSendDualWithCaps` is accessible via
   existing `import SeLe4n.Kernel.IPC.DualQueue` (re-export hub imports
   `WithCaps`).

4. **Build module**: `lake build SeLe4n.Kernel.InformationFlow.Enforcement.Wrappers`

#### AH1-B: Update checked `.send` dispatch arm in API.lean (H-01)

**File**: `SeLe4n/Kernel/API.lean`, lines 812-822
**Type**: Atomic change

Update the `dispatchWithCapChecked` `.send` arm to pass the three additional
parameters now required by `endpointSendDualChecked`.

**Atomic steps**:

1. **Read current call site**: API.lean lines 810-825.

2. **Update call**: Pass `cap.rights`, `gate.cspaceRoot`, and
   `decoded.capRecvSlot` to `endpointSendDualChecked`, matching the unchecked
   path's parameter set (API.lean:613-624).

   **Before**:
   ```lean
   match endpointSendDualChecked ctx epId tid msg st with
   | .error e => .error e
   | .ok (_, st') => .ok ((), st')
   ```

   **After**:
   ```lean
   match endpointSendDualChecked ctx epId tid msg cap.rights gate.cspaceRoot
       decoded.capRecvSlot st with
   | .error e => .error e
   | .ok (_, st') => .ok ((), st')
   ```

3. **Build module**: `lake build SeLe4n.Kernel.API`

#### AH1-C: Update NI soundness theorems (H-01)

**Files**:
- `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` (3 theorems)
- `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean` (1 theorem)
**Type**: Multi-step operation

The signature change to `endpointSendDualChecked` invalidates 4 theorems that
reference it. Each must be updated to account for the new parameters and return
type.

**Atomic steps**:

1. **Update `endpointSendDualChecked_eq_endpointSendDual_when_allowed`**
   (Wrappers.lean:69-89): Rename to
   `endpointSendDualChecked_eq_endpointSendDualWithCaps_when_allowed`. Update
   the RHS to reference `endpointSendDualWithCaps` instead of
   `endpointSendDual`. Add the three new parameters to the theorem statement.

2. **Update `endpointSendDualChecked_flowDenied`** (Wrappers.lean:95-110):
   Add the three new parameters. The denial branch is unchanged (still returns
   `.error .flowDenied`), so the proof body may require only parameter
   threading.

3. **Update `endpointSendDualChecked_denied_preserves_state`**
   (Wrappers.lean:298-305): Add the three new parameters. Proof structure
   unchanged (denial path does not modify state).

4. **Update `enforcementSoundness_endpointSendDualChecked`**
   (Soundness.lean:344-358): Add three parameters. The soundness property
   (success implies `securityFlowsTo`) is unchanged — the flow check still
   gates the operation. Proof may need adjustment for `CapTransferSummary`
   return type.

5. **Verify coverage**: Check that `checkedDispatchEnforcementCoverage_complete`
   (Soundness.lean:719) still type-checks (it references
   `endpointSendDualChecked` in its enforcement boundary list).

6. **Build modules**:
   ```bash
   lake build SeLe4n.Kernel.InformationFlow.Enforcement.Wrappers
   lake build SeLe4n.Kernel.InformationFlow.Enforcement.Soundness
   ```

#### AH1-D: Wire `validateVSpaceMapPermsForMemoryKind` into `.vspaceMap` dispatch (M-01)

**Finding**: M-01 — Device memory could receive execute permission
**File**: `SeLe4n/Kernel/API.lean`, lines 459-467
**Type**: Atomic change

The `.vspaceMap` dispatch arm is **shared** between checked and unchecked paths
via `dispatchCapabilityOnly` (API.lean:431). A single insertion point fixes both
paths.

**Atomic steps**:

1. **Read current dispatch arm**: API.lean lines 459-467.

2. **Insert validation after decode, before map operation**:

   **Before**:
   ```lean
   | .ok args =>
       Architecture.vspaceMapPageCheckedWithFlushFromState args.asid args.vaddr
         args.paddr args.perms st
   ```

   **After**:
   ```lean
   | .ok args =>
       match Architecture.validateVSpaceMapPermsForMemoryKind args
           st.machine.memoryMap with
       | .error e => .error e
       | .ok validatedArgs =>
           Architecture.vspaceMapPageCheckedWithFlushFromState
             validatedArgs.asid validatedArgs.vaddr
             validatedArgs.paddr validatedArgs.perms st
   ```

3. **Verify import**: `validateVSpaceMapPermsForMemoryKind` is in
   `SeLe4n.Kernel.Architecture.SyscallArgDecode` which is already imported by
   API.lean via the Architecture namespace.

4. **Build module**: `lake build SeLe4n.Kernel.API`

#### AH1-E: Update test suites and fixtures (H-01, M-01)

**Files**:
- `SeLe4n/Testing/MainTraceHarness.lean` (trace harness calls)
- `tests/InformationFlowSuite.lean` (NI test cases)
- `tests/fixtures/main_trace_smoke.expected` (expected output)
**Type**: Multi-step operation

**Atomic steps**:

1. **Update MainTraceHarness**: Find all calls to `endpointSendDualChecked`
   (lines 459, 462, 600, 605, 634) and add the three new parameters using
   test-appropriate values (e.g., `AccessRightSet.all`, the test CSpace root,
   `Slot.ofNat 0`).

2. **Update InformationFlowSuite**: Update test cases at lines 215-250 and
   397-411 to pass the new parameters.

3. **Run trace harness**: `lake exe sele4n` and capture new output.

4. **Update fixture**: If trace output changed, update
   `tests/fixtures/main_trace_smoke.expected` with rationale comment.

5. **Run smoke tests**: `./scripts/test_smoke.sh`

---

## 4. Phase AH2 — IPC Donation Safety & Boot Pipeline (M-02, M-03, L-02, L-16)

**Objective**: Eliminate silent error swallowing in IPC donation wrappers,
integrate machine configuration into the boot pipeline to prevent PA width
misconfiguration, and fix the empty-message return in timeout-aware receive.

**Dependencies**: Phase AH1 (API.lean call sites overlap — donation wrappers are
called from the same dispatch functions modified in AH1).

**Gate**: `source ~/.elan/env && lake build` + `./scripts/test_smoke.sh`

### 4.1 Sub-tasks

#### AH2-A: Change `applyCallDonation` return type to `Except` (M-02)

**Finding**: M-02 — Donation wrappers silently swallow errors
**File**: `SeLe4n/Kernel/IPC/Operations/Donation.lean`, lines 63-82
**Type**: Multi-step operation

**Atomic steps**:

1. **Read current function**: Donation.lean lines 55-90.

2. **Change signature and body**:

   **Before**:
   ```lean
   def applyCallDonation (st : SystemState) (caller receiver : ThreadId)
       : SystemState :=
     -- ... lookup SchedContext ...
     match donateSchedContext st caller receiver clientScId with
     | .error _ => st
     | .ok st' => st'
   ```

   **After**:
   ```lean
   def applyCallDonation (st : SystemState) (caller receiver : ThreadId)
       : Except KernelError SystemState :=
     -- ... lookup SchedContext ...
     match donateSchedContext st caller receiver clientScId with
     | .error e => .error e
     | .ok st' => .ok st'
   ```

   For the early-exit paths (no SchedContext bound, caller not active, etc.),
   these should return `.ok st` (success with unmodified state) since they
   represent legitimate no-op conditions, not errors. Only propagate errors
   from the underlying `donateSchedContext` call.

3. **Build module**: `lake build SeLe4n.Kernel.IPC.Operations.Donation`

#### AH2-B: Change `applyReplyDonation` return type to `Except` (M-02)

**File**: `SeLe4n/Kernel/IPC/Operations/Donation.lean`, lines 163-172
**Type**: Multi-step operation

**Atomic steps**:

1. **Read current function**: Donation.lean lines 150-180.

2. **Change signature and body**: Same pattern as AH2-A.

   **Before**:
   ```lean
   def applyReplyDonation (st : SystemState) (replier : ThreadId)
       : SystemState :=
     -- ... lookup donated SchedContext ...
     match returnDonatedSchedContext st replier scId originalOwner with
     | .error _ => st
     | .ok st' => removeRunnable st' replier
   ```

   **After**:
   ```lean
   def applyReplyDonation (st : SystemState) (replier : ThreadId)
       : Except KernelError SystemState :=
     -- ... lookup donated SchedContext ...
     match returnDonatedSchedContext st replier scId originalOwner with
     | .error e => .error e
     | .ok st' => .ok (removeRunnable st' replier)
   ```

   Early-exit paths (no donation active, etc.) return `.ok st`.

3. **Build module**: `lake build SeLe4n.Kernel.IPC.Operations.Donation`

#### AH2-C: Update API.lean call sites for donation error handling (M-02)

**File**: `SeLe4n/Kernel/API.lean`
**Call sites**: Lines ~654, ~855, ~874, ~973, ~1588
**Type**: Multi-step operation

Each call site currently uses `let st'' := applyCallDonation ...` (a pure
binding). After the return type changes to `Except`, each must become an
error-propagating `match`.

**Atomic steps**:

1. **Update `.call` unchecked path** (API.lean:654):
   ```lean
   -- Before: let st'' := applyCallDonation st' tid receiverTid
   -- After:
   match applyCallDonation st' tid receiverTid with
   | .error e => .error e
   | .ok st'' => .ok ((), propagatePriorityInheritance st'' receiverTid)
   ```

2. **Update `.call` checked path** (API.lean:855): Same pattern.

3. **Update `.reply` checked path** (API.lean:874):
   ```lean
   match applyReplyDonation st' tid with
   | .error e => .error e
   | .ok st'' => .ok ((), revertPriorityInheritance st'' tid)
   ```

4. **Update `.replyRecv` checked path** (API.lean:973): Same pattern as `.reply`.

5. **Update proof context** (API.lean:1588): Adjust theorem equivalence proof
   to account for new `match` branches.

6. **Build module**: `lake build SeLe4n.Kernel.API`

#### AH2-D: Update donation preservation theorems (M-02)

**Files**:
- `SeLe4n/Kernel/IPC/Operations/Donation.lean` (3 theorems)
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (1 theorem)
**Type**: Multi-step operation

**Atomic steps**:

1. **Update `applyCallDonation_scheduler_eq`** (Donation.lean:128):
   Current: Unconditional `(applyCallDonation st ...).scheduler = st.scheduler`.
   New: Conditional on success:
   `applyCallDonation st ... = .ok st' → st'.scheduler = st.scheduler`.
   The early-exit `.ok st` paths trivially satisfy this. The
   `donateSchedContext` success path needs its existing scheduler-preservation
   lemma threaded through.

2. **Update `applyCallDonation_machine_eq`** (Donation.lean:574):
   Same pattern — conditional on success.

3. **Update `applyReplyDonation_machine_eq`** (Donation.lean:610):
   Same pattern — conditional on success.

4. **Update `applyCallDonation_preserves_projection`**
   (Operations.lean:2398): This information-flow theorem needs the success
   precondition. The existing proof structure should survive with an added
   `h : applyCallDonation ... = .ok st'` hypothesis.

5. **Build modules**:
   ```bash
   lake build SeLe4n.Kernel.IPC.Operations.Donation
   lake build SeLe4n.Kernel.InformationFlow.Invariant.Operations
   ```

#### AH2-E: Extend `PlatformConfig` with `MachineConfig` field (M-03, L-16)

**Finding**: M-03 — `bootFromPlatform` does not call `applyMachineConfig`
**File**: `SeLe4n/Platform/Boot.lean`
**Type**: Multi-step operation

Currently `PlatformConfig` contains only `irqTable` and `initialObjects`.
`MachineConfig` is applied separately, creating a gap where callers forget the
second step.

**Atomic steps**:

1. **Read current structure**: Boot.lean lines 35-50 (`PlatformConfig`).

2. **Add `machineConfig` field**:
   ```lean
   structure PlatformConfig where
     irqTable : List IrqEntry
     initialObjects : List ObjectEntry
     machineConfig : MachineConfig := {}  -- default preserves backward compat
   ```

   The default `MachineConfig := {}` uses Lean's default field values
   (physicalAddressWidth = 52, etc.), preserving backward compatibility for
   existing callers that don't pass it.

3. **Verify import**: `MachineConfig` is defined in `SeLe4n.Machine` which
   Boot.lean already imports.

4. **Build module**: `lake build SeLe4n.Platform.Boot`

#### AH2-F: Integrate `applyMachineConfig` into `bootFromPlatform` (M-03)

**File**: `SeLe4n/Platform/Boot.lean`, lines 148-151
**Type**: Atomic change

**Atomic steps**:

1. **Read current function**: Boot.lean lines 148-151.

2. **Add `applyMachineConfig` as final step**:

   **Before**:
   ```lean
   def bootFromPlatform (config : PlatformConfig) : IntermediateState :=
     let initial := mkEmptyIntermediateState
     let withIrqs := foldIrqs config.irqTable initial
     foldObjects config.initialObjects withIrqs
   ```

   **After**:
   ```lean
   def bootFromPlatform (config : PlatformConfig) : IntermediateState :=
     let initial := mkEmptyIntermediateState
     let withIrqs := foldIrqs config.irqTable initial
     let withObjects := foldObjects config.initialObjects withIrqs
     applyMachineConfig withObjects config.machineConfig
   ```

3. **Update callers**: Find all `bootFromPlatform` call sites. For callers that
   previously applied `applyMachineConfig` manually (NegativeStateSuite.lean:
   3312-3314), remove the now-redundant second step. For callers that pass
   `PlatformConfig` with default fields, the behavior is unchanged (default
   `MachineConfig` produces the same result as no `applyMachineConfig` call).

4. **Update `bootFromPlatformChecked`** (Boot.lean:242): This calls
   `bootFromPlatform` internally, so it automatically benefits from the fix.
   Verify no additional changes needed.

5. **Build module**: `lake build SeLe4n.Platform.Boot`

#### AH2-G: Fix `timeoutAwareReceive` empty message return (L-02)

**Finding**: L-02 — Returns empty message instead of error for missing pending
**File**: `SeLe4n/Kernel/IPC/Operations/Timeout.lean`, lines 131-133
**Type**: Atomic change

**Atomic steps**:

1. **Read current code**: Timeout.lean lines 125-140.

2. **Change empty-message path to error**:

   **Before**:
   ```lean
   | none => .ok (.completed IpcMessage.empty, st)
   ```

   **After**:
   ```lean
   | none => .error .ipcMessageEmpty
   ```

   This surfaces the protocol violation rather than masking it. Verify that
   `KernelError.ipcMessageEmpty` exists, or use an appropriate existing error
   variant (e.g., `.invalidState`).

3. **Check callers**: Search for `timeoutAwareReceive` callers and verify they
   handle the new error path. If callers expect success on this path (unlikely
   given the `none` case should be unreachable under invariants), add a
   comment explaining the invariant that prevents this path.

4. **Build module**: `lake build SeLe4n.Kernel.IPC.Operations.Timeout`

---

## 5. Phase AH3 — Capability, Architecture & Decode Hardening (L-04, L-08, L-14)

**Objective**: Fix three defense-in-depth issues: CDT-orphaned capabilities on
revocation failure, IPC buffer operation bypassing `storeObject`, and hardcoded
ASID limits in the decode layer.

**Dependencies**: Phase AH2 (Boot pipeline changes may affect
`storeObject`-related invariants).

**Gate**: `source ~/.elan/env && lake build` + `./scripts/test_smoke.sh`

### 5.1 Sub-tasks

#### AH3-A: Fix `cspaceRevokeCdtStrict` CDT-orphan on delete failure (L-04)

**Finding**: L-04 — CDT node removed despite capability slot deletion failure
**File**: `SeLe4n/Kernel/Capability/Operations.lean`, lines 982-1006
**Type**: Multi-step operation

When `cspaceDeleteSlotCore` fails for a descendant, the current code still
removes the CDT node (line 999), leaving the capability slot unreachable by
future CDT-based revocation. The fix preserves the CDT node on slot deletion
failure.

**Atomic steps**:

1. **Read current code**: Operations.lean lines 975-1010.

2. **Change error handling in the fold body**:

   **Before** (on delete failure):
   ```lean
   | .error err =>
       let failure := { ... }
       let stRemoved := { stAcc with cdt := stAcc.cdt.removeNode node }
       ({ report with firstFailure := some failure }, stRemoved)
   ```

   **After** (preserve CDT node on failure):
   ```lean
   | .error err =>
       let failure := { ... }
       -- AH3-A: Do NOT remove CDT node on slot deletion failure.
       -- The capability slot still exists and must remain CDT-trackable
       -- for future revocation attempts.
       ({ report with firstFailure := some failure }, stAcc)
   ```

3. **Assess invariant impact**: The CDT node remains, pointing to a slot whose
   capability may be in an inconsistent state. Verify that
   `cdtNodeSlotConsistency` invariant (if it exists) tolerates this. If the
   invariant requires CDT nodes to point to valid slots, document the tradeoff
   (CDT tracking preserved at the cost of a potentially-stale CDT-to-slot
   mapping).

4. **Build module**: `lake build SeLe4n.Kernel.Capability.Operations`

#### AH3-B: Refactor `setIPCBufferOp` to use `storeObject` (L-08)

**Finding**: L-08 — Manual state manipulation instead of `storeObject`
**File**: `SeLe4n/Kernel/Architecture/IpcBufferValidation.lean`, lines 92-110
**Type**: Multi-step operation

The current implementation manually replicates `storeObject` semantics. If
`storeObject` is later extended (e.g., ASID table updates, lifecycle hooks),
this operation would silently diverge.

**Atomic steps**:

1. **Read current code**: IpcBufferValidation.lean lines 90-115.

2. **Read `storeObject` signature**: State.lean lines 521-546.

3. **Refactor to use `storeObject`**:

   **Before**:
   ```lean
   | some (.tcb tcb) =>
     let tcb' := { tcb with ipcBuffer := addr }
     .ok { st with
       objects := st.objects.insert tid.toObjId (.tcb tcb')
       objectIndex := if st.objectIndexSet.contains tid.toObjId then st.objectIndex
                      else tid.toObjId :: st.objectIndex
       objectIndexSet := st.objectIndexSet.insert tid.toObjId
       lifecycle := { ... }
     }
   ```

   **After**:
   ```lean
   | some (.tcb tcb) =>
     let tcb' := { tcb with ipcBuffer := addr }
     storeObject tid.toObjId (.tcb tcb') st
   ```

4. **Verify equivalence**: The `storeObject` function (State.lean:521-546)
   handles `objects`, `objectIndex`, `objectIndexSet`, `lifecycle`, and
   `asidTable` updates. For a TCB-to-TCB store (not VSpaceRoot), the
   `asidTable` branch is a no-op (`| _ => cleared` where `cleared = st.asidTable`
   since the old object is also not a VSpaceRoot). Confirm the refactored
   version produces identical state.

5. **Check preservation theorems**: If `setIPCBufferOp` has dedicated
   preservation theorems that reason about the manual struct-with pattern,
   update them to use `storeObject` lemmas instead.

6. **Build module**: `lake build SeLe4n.Kernel.Architecture.IpcBufferValidation`

#### AH3-C: Replace hardcoded ASID 65536 with `st.machine.maxASID` (L-14)

**Finding**: L-14 — Architecture-independent decode hardcodes ARM64 ASID limit
**File**: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`, lines 209 and 234
**Type**: Multi-step operation

The decode functions `decodeVSpaceMapArgs` and `decodeVSpaceUnmapArgs` hardcode
`65536` (ARM64 16-bit ASID limit). This should read from `MachineConfig` for
platform independence.

**Atomic steps**:

1. **Read current code**: SyscallArgDecode.lean lines 205-215 and 230-240.

2. **Determine access path**: The decode functions operate on raw registers
   and do not currently receive `SystemState`. Two approaches:

   **Option A (minimal change)**: Add a `maxASID : Nat` parameter to both
   decode functions. The caller (API.lean dispatch arm) passes
   `st.machine.maxASID`.

   **Option B (state-threaded)**: Add `SystemState` parameter to the decode
   functions. More invasive but consistent with other state-aware decodes.

   **Recommended**: Option A — minimal parameter addition.

3. **Update `decodeVSpaceMapArgs`**:

   **Before**:
   ```lean
   if !asid.isValidForConfig 65536 then .error .asidNotBound
   ```

   **After**:
   ```lean
   if !asid.isValidForConfig maxASID then .error .asidNotBound
   ```

4. **Update `decodeVSpaceUnmapArgs`**: Same pattern.

5. **Update callers in API.lean**: The `.vspaceMap` and `.vspaceUnmap` dispatch
   arms call these decode functions. Thread `st.machine.maxASID` through:
   ```lean
   match decodeVSpaceMapArgs decoded st.machine.maxASID with
   ```

6. **Update theorem**: `validateVSpaceMapPermsForMemoryKind_device_noexec`
   and any decode-related theorems in `tests/DecodingSuite.lean` must pass
   the new parameter.

7. **Build modules**:
   ```bash
   lake build SeLe4n.Kernel.Architecture.SyscallArgDecode
   lake build SeLe4n.Kernel.API
   ```

---

## 6. Phase AH4 — Version Consistency & CI Automation (H-02, version drift)

**Objective**: Synchronize all version strings to `0.27.1` and add automated CI
enforcement to prevent future version drift.

**Dependencies**: None (independent of Lean code phases; can run in parallel
with AH1–AH3 if desired).

**Gate**: `cargo test --workspace` + `./scripts/test_smoke.sh` +
`./scripts/check_version_sync.sh` passes

### 6.1 Sub-tasks

#### AH4-A: Update `KERNEL_VERSION` in Rust HAL (H-02)

**Finding**: H-02 — UART boot banner prints wrong kernel version
**File**: `rust/sele4n-hal/src/boot.rs`, line 11
**Type**: Atomic change

**Atomic steps**:

1. **Update version string**:
   ```rust
   // Before:
   const KERNEL_VERSION: &str = "0.26.8";
   // After:
   const KERNEL_VERSION: &str = "0.27.1";
   ```

2. **Update comment** (if present) to say "matches Lean lakefile.toml".

3. **Run Rust tests**: `cd rust && cargo test --workspace`

4. **Run clippy**: `cd rust && cargo clippy --workspace -- -D warnings`

#### AH4-B: Update CLAUDE.md version references

**File**: `CLAUDE.md`, line 8
**Type**: Atomic change

Update the Lean toolchain / project version reference from `0.26.9` to the
current values. The line references "version 0.26.9" in the project description
header.

#### AH4-C: Update SELE4N_SPEC.md version

**File**: `docs/spec/SELE4N_SPEC.md`, line 52
**Type**: Atomic change

Update the "Package version" table entry from `0.27.0` to `0.27.1`.

#### AH4-D: Update all 10 i18n README version badges

**Files**: `docs/i18n/{ar,de,es,fr,hi,ja,ko,pt-BR,ru,zh-CN}/README.md`
**Type**: Batch operation (10 files, identical change)

All 10 files have the same badge on line 11:
```html
<img src="https://img.shields.io/badge/version-0.26.6-blue"
```

Update all to `0.27.1`:
```html
<img src="https://img.shields.io/badge/version-0.27.1-blue"
```

**Note**: Version references in documentation body tables (e.g., workstream
history ranges like "v0.26.0–v0.27.1") are historical records and should NOT
be updated — they correctly describe the version range of their respective
workstreams.

#### AH4-E: Create `scripts/check_version_sync.sh` CI validation

**File**: `scripts/check_version_sync.sh` (new file)
**Type**: Multi-step operation

Create a CI-safe shell script that validates version consistency across all
known version-bearing files against the canonical `lakefile.toml` version.

**Atomic steps**:

1. **Write the script**:
   - Extract canonical version from `lakefile.toml` via
     `grep '^version' lakefile.toml | sed 's/.*"\(.*\)"/\1/'`
   - Check `rust/sele4n-hal/src/boot.rs` KERNEL_VERSION matches
   - Check `rust/Cargo.toml` workspace version matches
   - Check all 10 i18n README badge versions match
   - Check `docs/spec/SELE4N_SPEC.md` package version table matches
   - Report mismatches with file:line and exit 1 on any failure

2. **Make executable**: `chmod +x scripts/check_version_sync.sh`

3. **Run shellcheck**: `shellcheck scripts/check_version_sync.sh`

4. **Test the script**: Run it against the current (pre-fix) state to verify
   it detects known mismatches. Then run again after AH4-A through AH4-D to
   verify all pass.

#### AH4-F: Integrate version check into Tier 0 hygiene

**File**: `scripts/test_tier0_hygiene.sh`
**Type**: Atomic change

Add `scripts/check_version_sync.sh` call to the Tier 0 hygiene check script
so it runs on every PR and push.

**Atomic steps**:

1. **Read current script**: `scripts/test_tier0_hygiene.sh`

2. **Add version sync check** after the existing website link check:
   ```bash
   echo "=== Version sync check ==="
   ./scripts/check_version_sync.sh || exit 1
   ```

3. **Run Tier 0**: `./scripts/test_tier0_hygiene.sh`

---

## 7. Phase AH5 — Documentation, Testing & Closure (M-04–M-08, L-11–L-13)

**Objective**: Document all findings that require specification or code-comment
updates, update test fixtures, synchronize all documentation, and pass the full
test gate.

**Dependencies**: All prior phases (AH1–AH4) complete.

**Gate**: `./scripts/test_full.sh` + `cargo test --workspace` +
`cargo clippy --workspace` + documentation sync verified

### 7.1 Sub-tasks

#### AH5-A: Document design-rationale findings in source code (M-04, M-07)

**Files**:
- `SeLe4n/Platform/Boot.lean`, line 898 (M-04)
- `SeLe4n/Kernel/InformationFlow/Projection.lean`, line 185 (M-07)
**Type**: Multi-step operation

**Atomic steps**:

1. **M-04 — VSpaceRoot boot exclusion**: Add a structured comment block at
   `bootSafeObject` (Boot.lean:898) explaining:
   - Why VSpaceRoots are excluded (ASID table registration requires a running
     kernel, not available during boot)
   - The tradeoff (all address spaces must be configured post-boot via syscalls)
   - Integration timeline (VSpaceRoot boot support planned for WS-V when ASID
     manager is wired into production)

2. **M-07 — pendingMessage NI visibility**: Add a security analysis comment at
   `projectKernelObject` TCB case (Projection.lean:185-201) explaining:
   - `pendingMessage` is technically visible in the projection
   - Exposure is unreachable under NI invariants: `runnableThreadIpcReady`
     ensures observable threads are in `.ready` IPC state (no pending message
     from cross-domain sources), and `currentNotEndpointQueueHead` prevents
     the current thread from being in an endpoint queue
   - Reference the specific invariant predicates that make this safe

#### AH5-B: Document spec-level findings (M-05, M-06, L-13)

**File**: `docs/spec/SELE4N_SPEC.md`
**Type**: Multi-step operation

**Atomic steps**:

1. **M-05 — Simulation contract limitations**: Add a "Platform Testing
   Limitations" subsection to the platform testing section documenting:
   - The sim permissive contract accepts all operations (`True` propositions)
   - The 6-condition RPi5 register context stability check is not exercisable
     under simulation
   - Recommendation: use the sim restrictive contract for property validation
     and RPi5 contract for production-representative testing

2. **M-06 — CNode intermediate rights divergence**: Add a "seL4 Divergences"
   subsection to the capability section documenting:
   - Intermediate CNode `Read` right is not checked during multi-level CSpace
     traversal (documented as U-M25 in source)
   - Authority surface is wider: a thread with only `Write` right on an
     intermediate CNode can still resolve capabilities through it
   - Rationale: operation-level enforcement (all leaf operations check rights)
     provides equivalent security for the single-resolution-per-syscall model
   - The delta is quantified: no additional operations become accessible (rights
     are still checked at the leaf), but the access path is broader

3. **L-13 — TPIDR_EL0 / TLS gap**: Add a note to the architecture model section:
   - `RegisterFile` covers GPRs (x0-x30), PC, and SP only
   - ARM64 TPIDR_EL0 (thread-local storage pointer) is not modeled
   - Required for hardware user-space TLS support
   - Integration timeline: future AG-phase when user-space binary loading is
     implemented

#### AH5-C: Document defense-in-depth findings in source code (M-08, L-11, L-12)

**Files**:
- `SeLe4n/Kernel/CrossSubsystem.lean`, lines 273-292 (M-08)
- `SeLe4n/Prelude.lean`, lines 510-532 (L-11)
- `SeLe4n/Model/Object/Types.lean`, line 531 (L-12)
**Type**: Multi-step operation

**Atomic steps**:

1. **M-08 — Cross-subsystem composition**: Update the existing gap
   documentation at CrossSubsystem.lean:273-292 with:
   - Current predicate count (10) and the 45 pairwise disjointness analyses
   - Specific remaining gap scenarios (IPC queue ↔ service registry, capability
     revocation ↔ service endpoints)
   - Assessment: frame lemmas cover all 33 kernel operations that modify
     `objects`; remaining gap is theoretical (no known concrete violation)

2. **L-11 — Badge constructor safety**: Add a safety analysis comment at
   `structure Badge` (Prelude.lean:510):
   - Direct `Badge.mk n` with `n ≥ 2^64` produces an invalid badge
   - `Badge.valid` predicate catches this at proof boundaries
   - `Badge.ofNatMasked` enforces word-size at construction
   - All kernel-facing badge operations (`cspaceMint`, IPC message delivery)
     use masked/validated badges
   - Risk: only internal test code could construct invalid badges; no user-facing
     path bypasses validation

3. **L-12 — maxControlledPriority default**: Add a design-rationale comment at
   `maxControlledPriority : SeLe4n.Priority := ⟨0xFF⟩` (Types.lean:531):
   - Default is maximally permissive (any priority assignable)
   - Safe because `setPriorityOp` enforces `newPrio ≤ caller.mcp` at the
     operation level, regardless of the target's MCP default
   - seL4 uses a restrictive default (0); seLe4n diverges for simpler boot
     configuration
   - Production deployments should set explicit MCP values during initialization

#### AH5-D: Update test fixtures and expected outputs

**Files**:
- `tests/fixtures/main_trace_smoke.expected`
- Any other fixture files affected by AH1–AH3 changes
**Type**: Multi-step operation

**Atomic steps**:

1. **Run trace harness**: `source ~/.elan/env && lake exe sele4n`
2. **Compare output**: `diff <(lake exe sele4n) tests/fixtures/main_trace_smoke.expected`
3. **Update fixture** if output changed, with a changelog comment explaining
   the reason for the change (e.g., "AH1: checked send now performs cap transfer")
4. **Run smoke tests**: `./scripts/test_smoke.sh`

#### AH5-E: Synchronize documentation

**Files**:
- `README.md` — metrics sync from `docs/codebase_map.json`
- `docs/DEVELOPMENT.md` — WS-AH portfolio status
- `docs/WORKSTREAM_HISTORY.md` — WS-AH entry
- `docs/CLAIM_EVIDENCE_INDEX.md` — if claims changed
- `docs/CHANGELOG.md` — new version entry
- `docs/codebase_map.json` — regenerate if Lean sources changed
- Affected GitBook chapters
**Type**: Multi-step operation

**Atomic steps**:

1. **Add WS-AH entry to WORKSTREAM_HISTORY.md**: Follow existing format with
   phase completion markers.

2. **Update DEVELOPMENT.md**: Add WS-AH portfolio status line.

3. **Add CHANGELOG entry**: Document all phases and sub-task completions.

4. **Regenerate codebase_map.json**: If any Lean module paths changed or new
   modules were added.

5. **Update README.md**: Sync any metrics that changed (module count, theorem
   count, etc.) from `docs/codebase_map.json`.

6. **Update CLAUDE.md**: Add WS-AH to the active workstream context section.

#### AH5-F: Final gate — full test suite

**Type**: Verification gate

**Atomic steps**:

1. **Full Lean build**: `source ~/.elan/env && lake build`
2. **Rust workspace**: `cd rust && cargo test --workspace && cargo clippy --workspace -- -D warnings`
3. **Full test suite**: `./scripts/test_full.sh`
4. **Sorry/axiom scan**: `grep -r 'sorry\|axiom\|admit' SeLe4n/ --include='*.lean' | grep -v '^\-\-' | grep -v 'comment'`
5. **Version sync**: `./scripts/check_version_sync.sh`
6. **Website links**: `./scripts/check_website_links.sh`

All 6 checks must pass. Zero sorry/axiom in production code.

---

## 8. Dependency Graph and Execution Order

```
AH4 (Version/CI)     AH1 (IPC Dispatch)
     |                     |
     |                     v
     |                AH2 (Donation/Boot)
     |                     |
     |                     v
     |                AH3 (Cap/Arch/Decode)
     |                     |
     v                     v
     +--------+------------+
              |
              v
         AH5 (Docs/Testing/Closure)
```

**Parallelism opportunity**: Phase AH4 (version/CI) is independent of Phases
AH1–AH3 (Lean code changes). These can execute concurrently. Phase AH5 depends
on all prior phases completing.

**Critical path**: AH1 → AH2 → AH3 → AH5

**Estimated phase sizes**:

| Phase | New/Modified Lean Lines | Rust/Shell Lines | Doc Lines | Files Touched |
|-------|------------------------|-----------------|-----------|---------------|
| AH1 | ~100–150 | 0 | 0 | 5–8 |
| AH2 | ~120–180 | 0 | 0 | 6–10 |
| AH3 | ~60–100 | 0 | 0 | 4–6 |
| AH4 | 0 | ~80–120 | ~30 | 16–18 |
| AH5 | ~20–40 | 0 | ~300–500 | 12–18 |

---

## 9. Risk Assessment

### 9.1 High-Risk Sub-tasks

| Sub-task | Risk | Mitigation |
|----------|------|------------|
| AH1-C (NI theorem updates) | Soundness theorems may require non-trivial proof restructuring when `endpointSendDualChecked` return type changes from `Unit` to `CapTransferSummary` | Follow `endpointCallChecked` theorem pattern as template; the information-flow property (success ⟹ `securityFlowsTo`) is structurally identical |
| AH2-D (Donation preservation theorems) | Conditional postconditions change proof obligations for `applyCallDonation_preserves_projection` | Early-exit `.ok st` paths satisfy preservation trivially (state unchanged); focus proof effort on the `donateSchedContext` success path |
| AH2-F (Boot pipeline change) | Existing callers may break if `PlatformConfig` constructor syntax changes | Default `machineConfig := {}` field preserves backward compatibility for all existing callers |

### 9.2 Low-Risk Sub-tasks

All version string updates (AH4-A through AH4-D) are mechanical text
replacements with no proof or compilation impact. Documentation updates
(AH5-A through AH5-C) add comments only and do not affect code semantics.

### 9.3 Rollback Strategy

Each phase produces a self-contained commit. If a phase introduces
regressions, revert the single phase commit. The dependency ordering ensures
later phases build on earlier ones, so rollback proceeds in reverse phase
order.

---

## 10. Appendix A — Complete Finding Disposition Matrix

| ID | Severity | Disposition | Phase | Rationale |
|----|----------|-------------|-------|-----------|
| H-01 | HIGH | **Fix** | AH1 | Checked `.send` drops cap transfer |
| H-02 | HIGH | **Fix** | AH4 | Stale KERNEL_VERSION |
| M-01 | MEDIUM | **Fix** | AH1 | Device memory execute permission gap |
| M-02 | MEDIUM | **Fix** | AH2 | Donation error swallowing |
| M-03 | MEDIUM | **Fix** | AH2 | Boot pipeline missing `applyMachineConfig` |
| M-04 | MEDIUM | **Doc** | AH5 | VSpaceRoot boot exclusion (design choice) |
| M-05 | MEDIUM | **Doc** | AH5 | Sim contract limitations (by design) |
| M-06 | MEDIUM | **Doc** | AH5 | CNode rights divergence (documented U-M25) |
| M-07 | MEDIUM | **Doc** | AH5 | pendingMessage NI visibility (invariant-protected) |
| M-08 | MEDIUM | **Doc** | AH5 | Cross-subsystem composition gap (partially mitigated) |
| M-09 | MEDIUM | **No-action** | — | Reclassified INFO; matches seL4 design |
| M-10 | MEDIUM | **No-action** | — | Already tracked as TPI-DOC; deferred to WS-V |
| M-11 | MEDIUM | **No-action** | — | Reclassified INFO; production path correct |
| L-01 | LOW | **No-action** | — | Safe under `tcbQueueChainAcyclic` invariant |
| L-02 | LOW | **Fix** | AH2 | Empty message masks protocol violations |
| L-03 | LOW | **No-action** | — | Protected by scheduler-IPC coherence invariants |
| L-04 | LOW | **Fix** | AH3 | CDT-orphaned capabilities on revoke failure |
| L-05 | LOW | **No-action** | — | Diagnostics only; not in selection path |
| L-06 | LOW | **No-action** | — | Standard CBS practice; documented |
| L-07 | LOW | **No-action** | — | Matches seL4 semantics |
| L-08 | LOW | **Fix** | AH3 | `setIPCBufferOp` bypasses `storeObject` |
| L-09 | LOW | **No-action** | — | Appropriate for sequential model |
| L-10 | LOW | **Deferred** | — | Already deferred to WS-V |
| L-11 | LOW | **Doc** | AH5 | Badge constructor safety analysis |
| L-12 | LOW | **Doc** | AH5 | maxControlledPriority default rationale |
| L-13 | LOW | **Doc** | AH5 | TPIDR_EL0 / TLS gap + timeline |
| L-14 | LOW | **Fix** | AH3 | Hardcoded ASID 65536 in decode |
| L-15 | LOW | **No-action** | — | Safe under AsidManager uniqueness |
| L-16 | LOW | **Subsumed** | AH2 | Fixed by M-03 boot pipeline integration |
| L-17 | LOW | **No-action** | — | Accepted covert channel; matches seL4 |
| I-01–I-14 | INFO | **No-action** | — | Architectural properties; no changes needed |

## Appendix B — Files Modified Per Phase

| Phase | Files |
|-------|-------|
| AH1 | `Wrappers.lean`, `Soundness.lean`, `API.lean`, `MainTraceHarness.lean`, `InformationFlowSuite.lean`, `main_trace_smoke.expected` |
| AH2 | `Donation.lean`, `API.lean`, `Operations.lean` (IF), `Boot.lean`, `Timeout.lean`, `NegativeStateSuite.lean`, `OperationChainSuite.lean` |
| AH3 | `Operations.lean` (Cap), `IpcBufferValidation.lean`, `SyscallArgDecode.lean`, `API.lean`, `DecodingSuite.lean` |
| AH4 | `boot.rs`, `CLAUDE.md`, `SELE4N_SPEC.md`, 10 i18n READMEs, `check_version_sync.sh` (new), `test_tier0_hygiene.sh` |
| AH5 | `Boot.lean`, `Projection.lean`, `SELE4N_SPEC.md`, `CrossSubsystem.lean`, `Prelude.lean`, `Types.lean`, `main_trace_smoke.expected`, `DEVELOPMENT.md`, `WORKSTREAM_HISTORY.md`, `CHANGELOG.md`, `codebase_map.json`, `README.md`, `CLAUDE.md` |

## Appendix C — Verification Commands Quick Reference

```bash
# Per-module build (mandatory before commit)
source ~/.elan/env && lake build <Module.Path>

# Tier 0+1: Hygiene + build
./scripts/test_fast.sh

# Tier 0-2: + trace + negative-state
./scripts/test_smoke.sh

# Tier 0-3: + invariant surface anchors
./scripts/test_full.sh

# Rust workspace
cd rust && cargo test --workspace && cargo clippy --workspace -- -D warnings

# Version sync (after AH4-E)
./scripts/check_version_sync.sh

# Sorry/axiom scan
grep -rn 'sorry\|axiom\|admit' SeLe4n/ --include='*.lean' | grep -v -- '--'
```
