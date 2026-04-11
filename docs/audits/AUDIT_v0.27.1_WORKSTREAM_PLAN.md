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

**Estimated scope**: ~360–560 new/modified lines of Lean (functions, theorems,
test sites), ~20 lines of Rust, ~80–120 lines of shell/CI scripts, ~300–500
lines of documentation changes.

**Total sub-tasks**: 27 (across 5 phases)

---

## 2. Finding Cross-Reference and Verification

Every finding from the baseline audit was independently re-verified against
source code before inclusion in this plan. This section classifies each finding
and provides the verification rationale.

### 2.1 Erroneous / Overstated Findings (3)

| Finding | Audit Severity | Actual | Rationale |
|---------|---------------|--------|-----------|
| M-09 | MEDIUM | **INFORMATIONAL** | `LabelingContextValid` as a deployment obligation is **identical to seL4's design**. The codebase already has `labelingContextValid_is_deployment_requirement` witness theorem (Composition.lean:753). No runtime enforcement is needed — this is the correct architecture for a separation kernel. Reclassified to INFORMATIONAL. |
| M-10 | MEDIUM | **ALREADY TRACKED** | CDT `descendantsOf` fuel sufficiency is already tracked as TPI-DOC and explicitly deferred to WS-V (Structures.lean:2234-2245, CrossSubsystem.lean:92-133). The current depth-1 proof (`descendantsOf_fuel_sufficiency`) is documented with its scope limitation. No new action required beyond existing deferral. |
| M-11 | MEDIUM | **INFORMATIONAL** | The audit itself confirms: "No user-facing operation uses the 2^52 default." The bare `vspaceMapPageChecked` helper is documented as "proof-layer default only" (VSpace.lean:54-59). The production dispatch path (`vspaceMapPageCheckedWithFlushFromState`) correctly reads `st.machine.physicalAddressWidth`. Internal-only proof helpers do not need platform-specific bounds. |

### 2.2 No-Action Findings (8 LOW + 14 INFORMATIONAL)

These findings describe confirmed-correct design patterns, seL4-matching
semantics, or invariant-protected code paths. No code or documentation changes
are needed.

| Finding | Rationale |
|---------|-----------|
| L-01 | `endpointQueueRemove` stale-read fallback is safe under `tcbQueueLinkIntegrity` invariant (doubly-linked consistency). Safety proven via `queueRemove_predecessor_exists` / `queueRemove_successor_exists` (AE4-E/U-24). |
| L-03 | `sender == receiver` is unreachable under `runnableThreadIpcReady` + `currentNotEndpointQueueHead` scheduler-IPC coherence invariants. A sender in `.ready` IPC state cannot be in a receive queue. |
| L-05 | RunQueue `size` is diagnostics-only (AF-40). Not referenced by scheduling selection logic. Proof-enforcement would add complexity with zero functional benefit. |
| L-06 | CBS integer truncation is standard practice. Per-context budget bounds (`budgetWithinBounds`) hold regardless of admission precision. Documented at Budget.lean:204-217. |
| L-07 | `schedContextUnbind` clearing current without rescheduling matches seL4 semantics. Dequeue-on-dispatch ensures the next `schedule` call will select correctly. |
| L-09 | `tlbBarrierComplete = True` is appropriate for the sequential abstract model. Hardware barrier correctness is enforced by Rust HAL wrappers (DSB ISH + ISB after every TLBI). |
| L-15 | `storeObject` VSpaceRoot ASID replacement is safe under `AsidManager` uniqueness invariant (`asidPoolUnique`). Each ASID maps to exactly one ObjId. |
| L-17 | Scheduling covert channel is accepted by design, matching seL4's domain scheduler visibility. Explicitly documented with `acceptedCovertChannel_scheduling` bound theorem (Projection.lean:355-407). |
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
**Type**: Multi-step operation (4 theorems, each independently compilable)

The signature change to `endpointSendDualChecked` (new params + return type
`Kernel CapTransferSummary`) invalidates 4 theorems. Each theorem requires a
specific modification strategy. The `endpointCallChecked` theorem family
(Soundness.lean:416-428) serves as the exact template — it already handles the
same parameter set and `CapTransferSummary` return type.

**Sub-step AH1-C-1: Update equivalence theorem** (Wrappers.lean:69-89)

Current theorem statement:
```lean
theorem endpointSendDualChecked_eq_endpointSendDual_when_allowed
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (st : SystemState)
    (hFlow : securityFlowsTo ... = true) :
    endpointSendDualChecked ctx endpointId sender msg st =
      endpointSendDual endpointId sender msg st
```

Changes:
- **Rename** to `endpointSendDualChecked_eq_endpointSendDualWithCaps_when_allowed`
- **Add 3 parameters**: `endpointRights : AccessRightSet`,
  `senderCspaceRoot : SeLe4n.ObjId`, `receiverSlotBase : SeLe4n.Slot`
- **RHS target**: change `endpointSendDual` → `endpointSendDualWithCaps`
  with the 3 new params threaded through
- **Proof body**: The existing tactic structure (`unfold`, `simp`, `split`)
  survives unchanged — the bounds-check if-branches are identical, and the
  flow-check success path now unfolds to `endpointSendDualWithCaps` instead
  of `endpointSendDual`. The `simp [*]` in the bounds-failure branches may
  need adjustment since `endpointSendDualWithCaps` has a different bounds
  check structure than `endpointSendDual`.
- **Fallback**: If `simp [*]` doesn't close the bounds-failure branches,
  use `unfold endpointSendDualWithCaps; simp [*]` (matching the current
  pattern with `endpointSendDual`).

**Sub-step AH1-C-2: Update flow-denied theorem** (Wrappers.lean:95-110)

Current statement proves: when `securityFlowsTo = false` and message is
in bounds, the checked send returns `.error .flowDenied`.

Changes:
- **Add 3 parameters** to the statement (same as AH1-C-1)
- **Proof body unchanged**: The denial branch is independent of the
  delegated function. The existing proof uses `IpcMessage.checkBounds_iff_bounded`
  to eliminate bounds checks, then `simp [hDeny]` to close the flow-denied case.
  These tactics do not reference `endpointSendDual` at all — they operate
  purely on the if-then-else structure of `endpointSendDualChecked`, which
  retains the same denial branch.

**Sub-step AH1-C-3: Update denied-preserves-state theorem** (Wrappers.lean:298-311)

Current statement:
```lean
theorem endpointSendDualChecked_denied_preserves_state ... :
    ¬∃ st', endpointSendDualChecked ctx endpointId sender msg st = .ok ((), st')
```

Changes:
- **Add 3 parameters** to the statement
- **Change existential type**: `¬∃ st', ... = .ok ((), st')` becomes
  `¬∃ (r : CapTransferSummary) st', ... = .ok (r, st')` since the return
  type is now `CapTransferSummary` (not `Unit`)
- **Proof body**: The existing proof eliminates bounds-check branches via
  `intro hc; simp [hc] at h` (contradicting the `.ok` assumption), then
  closes with `simp [hDeny] at h`. This tactic chain operates on the
  if-then-else structure only and does not reference the success-path
  delegate, so it survives unchanged.

**Sub-step AH1-C-4: Update enforcement soundness theorem** (Soundness.lean:344-358)

Template: `enforcementSoundness_endpointCallChecked` (Soundness.lean:416-428):
```lean
theorem enforcementSoundness_endpointCallChecked ... (r : CapTransferSummary)
    (st' : SystemState) (hStep : endpointCallChecked ... = .ok (r, st')) :
    securityFlowsTo ... = true := by
  unfold endpointCallChecked at hStep
  cases h : securityFlowsTo ... with
  | true => rfl
  | false => simp [h] at hStep
```

Changes:
- **Add 3 parameters + `r : CapTransferSummary`** to the statement
  (replacing the implicit `Unit` pairing)
- **Update hypothesis**: `hStep : endpointSendDualChecked ... = .ok (r, st')`
- **Proof body**: The current proof has extra bounds-check elimination
  (`simp only [show ¬(maxMessageRegisters < ...) from by intro h; simp [h]
  at hStep, ↓reduceIte] at hStep`). This is **required** because
  `endpointSendDualChecked` has bounds checks before the flow check, unlike
  `endpointCallChecked` which delegates to a function that handles bounds
  internally. The bounds-elimination lines survive unchanged (they reference
  the if-then-else structure, not the delegate function).

**Sub-step AH1-C-5: Verify coverage completeness** (Soundness.lean:~705-720)

`checkedDispatchEnforcementCoverage_complete` contains a string list of all
checked wrappers. `"endpointSendDualChecked"` appears in this list. Since we
are modifying (not renaming) the function, the string reference remains valid.
Verify this type-checks after the changes above.

**Sub-step AH1-C-6: Build both modules**:
```bash
source ~/.elan/env
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
- `SeLe4n/Testing/MainTraceHarness.lean` (5 call sites)
- `tests/InformationFlowSuite.lean` (4 call sites)
- `tests/TraceSequenceProbe.lean` (1 call site)
- `tests/fixtures/main_trace_smoke.expected` (expected output)
**Type**: Multi-step operation (10 call sites across 3 files)

All 10 call sites must add the three new parameters: `endpointRights`,
`senderCspaceRoot`, `receiverSlotBase`. Test code uses maximally-permissive
defaults to test the IPC path (not the rights-checking path).

**Standard test parameter values**:
```lean
-- endpointRights: full rights (test is not testing rights enforcement)
AccessRightSet.all
-- senderCspaceRoot: the test state's root CNode (typically ObjId.ofNat 0)
(ObjId.ofNat 0)
-- receiverSlotBase: slot 0 (first available receiver slot)
(Slot.ofNat 0)
```

**Sub-step AH1-E-1: MainTraceHarness (5 sites)**

| Line | Context | Notes |
|------|---------|-------|
| ~459 | First checked send test | Basic send with default message |
| ~462 | Second checked send test | Same test block, alternate path |
| ~600 | Cross-domain send test | Tests policy denial path (params still needed for signature match) |
| ~605 | Cross-domain alternate | Same test block |
| ~634 | End-to-end trace | Full dispatch integration test |

For each site, the existing `endpointSendDualChecked ctx epId tid msg st`
becomes `endpointSendDualChecked ctx epId tid msg AccessRightSet.all
(ObjId.ofNat 0) (Slot.ofNat 0) st`. The `st` argument stays last (Kernel
monad currying).

**Sub-step AH1-E-2: InformationFlowSuite (4 sites)**

| Line | Context | Notes |
|------|---------|-------|
| ~231 | Flow-allowed test | Expects `.ok` — will now return `CapTransferSummary` |
| ~246 | Flow-denied test | Expects `.error .flowDenied` — unchanged semantics |
| ~398 | Projection preservation test | Tests NI invariant through checked send |
| ~405 | Denied-preserves-state test | Tests no state change on denial |

The flow-denied tests (lines ~246, ~405) need parameter addition only — the
denial semantics are unchanged. The flow-allowed test (line ~231) may need
its result pattern updated from `(.ok ((), st'))` to `(.ok (_, st'))` or
`(.ok (r, st'))` to accommodate the `CapTransferSummary` return type.

**Sub-step AH1-E-3: TraceSequenceProbe (1 site)**

| Line | Context | Notes |
|------|---------|-------|
| ~187 | Sequence probe checked send | Add 3 parameters |

**Sub-step AH1-E-4: Run trace harness and update fixture**

1. `source ~/.elan/env && lake exe sele4n > /tmp/trace_output.txt 2>&1`
2. `diff /tmp/trace_output.txt tests/fixtures/main_trace_smoke.expected`
3. If output changed (likely — the checked send path now performs cap
   transfer via `ipcUnwrapCaps`, which may produce different trace lines),
   update the fixture with a header comment:
   ```
   # AH1: checked send now delegates to endpointSendDualWithCaps
   # (capability transfer is performed on rendezvous)
   ```

**Sub-step AH1-E-5: Run full smoke test gate**
```bash
./scripts/test_smoke.sh
```

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
**Type**: Multi-step operation (5 control-flow paths)

The function has 5 structural match arms covering all control-flow paths.
Each arm must be classified as either a legitimate no-op (returns `.ok st`)
or an error propagation (returns `.error e`).

**Path enumeration**:

| # | Condition | Current Return | New Return | Classification |
|---|-----------|---------------|------------|----------------|
| 1 | `lookupTcb st receiver = none` | `st` | `.ok st` | No-op: receiver not found (unreachable under invariants, defensive) |
| 2 | `receiverTcb.schedContextBinding ≠ .unbound` (wildcard `| _ => st`) | `st` | `.ok st` | No-op: receiver already has SC (covers `.bound` and `.donated`) |
| 3 | `lookupTcb st caller = none` | `st` | `.ok st` | No-op: caller not found (unreachable under invariants) |
| 4 | `callerTcb.schedContextBinding ≠ .bound` (wildcard `| _ => st`) | `st` | `.ok st` | No-op: caller has no SC to donate (covers `.unbound` and `.donated`) |
| 5a | `donateSchedContext ... = .error _` | `st` | `.error e` | **Error propagation** (the key fix) |
| 5b | `donateSchedContext ... = .ok st'` | `st'` | `.ok st'` | Success |

Only path 5a changes semantics. Paths 1-4 change from bare `st` to `.ok st`,
and path 5b from bare `st'` to `.ok st'`. Path 5a changes from silent
swallowing (`st`) to error propagation (`.error e`).

Note: Paths 2 and 4 are wildcard arms (`| _ => st`) that each collapse two
`SchedContextBinding` constructors. The path count (5 structural arms) matches
the source code exactly (Donation.lean:63-82).

**Atomic steps**:

1. **Read current function**: Donation.lean lines 55-90.

2. **Change signature**: `SystemState` → `Except KernelError SystemState`

3. **Change body** — apply the path classification above:
   ```lean
   def applyCallDonation
       (st : SystemState)
       (caller : SeLe4n.ThreadId) (receiver : SeLe4n.ThreadId)
       : Except KernelError SystemState :=
     match lookupTcb st receiver with
     | none => .ok st                          -- Path 1: no-op
     | some receiverTcb =>
       match receiverTcb.schedContextBinding with
       | .unbound =>
         match lookupTcb st caller with
         | none => .ok st                      -- Path 3: no-op
         | some callerTcb =>
           match callerTcb.schedContextBinding with
           | .bound clientScId =>
             match donateSchedContext st caller receiver clientScId with
             | .error e => .error e            -- Path 5a: ERROR PROPAGATION
             | .ok st' => .ok st'              -- Path 5b: success
           | _ => .ok st                       -- Path 4: no-op
       | _ => .ok st                           -- Path 2: no-op
   ```

4. **Build module**: `lake build SeLe4n.Kernel.IPC.Operations.Donation`

#### AH2-B: Change `applyReplyDonation` return type to `Except` (M-02)

**File**: `SeLe4n/Kernel/IPC/Operations/Donation.lean`, lines 163-172
**Type**: Multi-step operation (4 control-flow paths)

**Path enumeration**:

| # | Condition | Current Return | New Return | Classification |
|---|-----------|---------------|------------|----------------|
| 1 | `lookupTcb st replier = none` | `st` | `.ok st` | No-op: replier not found |
| 2 | `replierTcb.schedContextBinding ≠ .donated` | `st` | `.ok st` | No-op: no donation to return |
| 3a | `returnDonatedSchedContext ... = .error _` | `st` | `.error e` | **Error propagation** |
| 3b | `returnDonatedSchedContext ... = .ok st'` | `removeRunnable st' replier` | `.ok (removeRunnable st' replier)` | Success |

Only path 3a changes semantics: from silent swallowing to error propagation.

**Atomic steps**:

1. **Read current function**: Donation.lean lines 158-173.

2. **Change signature**: `SystemState` → `Except KernelError SystemState`

3. **Change body**:
   ```lean
   def applyReplyDonation (st : SystemState) (replier : SeLe4n.ThreadId)
       : Except KernelError SystemState :=
     match lookupTcb st replier with
     | none => .ok st                          -- Path 1: no-op
     | some replierTcb =>
       match replierTcb.schedContextBinding with
       | .donated scId originalOwner =>
         match returnDonatedSchedContext st replier scId originalOwner with
         | .error e => .error e                -- Path 3a: ERROR PROPAGATION
         | .ok st' => .ok (removeRunnable st' replier)  -- Path 3b: success
       | _ => .ok st                           -- Path 2: no-op
   ```

4. **Build module**: `lake build SeLe4n.Kernel.IPC.Operations.Donation`

#### AH2-C: Update API.lean call sites for donation error handling (M-02)

**File**: `SeLe4n/Kernel/API.lean`
**Type**: Multi-step operation (5 code sites + 1 indirect caller + 1 theorem)

There are 5 direct call sites in API.lean, 1 indirect wrapper in Donation.lean,
and 1 equivalence theorem that must be updated. Each `let st'' :=
applyCallDonation ...` (pure binding) becomes a `match ... with | .error e =>
.error e | .ok st'' => ...` (error propagation).

**Sub-step AH2-C-1: Unchecked `.call` path** (API.lean:~654)

```lean
-- BEFORE (line 654):
let st'' := applyCallDonation st' tid receiverTid
.ok ((), PriorityInheritance.propagatePriorityInheritance st'' receiverTid)

-- AFTER:
match applyCallDonation st' tid receiverTid with
| .error e => .error e
| .ok st'' =>
  .ok ((), PriorityInheritance.propagatePriorityInheritance st'' receiverTid)
```

**Sub-step AH2-C-2: Checked `.call` path** (API.lean:~855)

```lean
-- BEFORE (line 855):
let st'' := applyCallDonation st' tid receiverTid
.ok ((), PriorityInheritance.propagatePriorityInheritance st'' receiverTid)

-- AFTER:
match applyCallDonation st' tid receiverTid with
| .error e => .error e
| .ok st'' =>
  .ok ((), PriorityInheritance.propagatePriorityInheritance st'' receiverTid)
```

**Sub-step AH2-C-3: Checked `.reply` path** (API.lean:~874)

```lean
-- BEFORE (line 874):
let st'' := applyReplyDonation st' tid
.ok ((), PriorityInheritance.revertPriorityInheritance st'' tid)

-- AFTER:
match applyReplyDonation st' tid with
| .error e => .error e
| .ok st'' =>
  .ok ((), PriorityInheritance.revertPriorityInheritance st'' tid)
```

**Sub-step AH2-C-4: Checked `.replyRecv` path** (API.lean:~973)

Same pattern as AH2-C-3 — `applyReplyDonation` error propagation.

**Sub-step AH2-C-5: Unchecked `.reply` path — indirect via `endpointReplyWithDonation`**
(Donation.lean:~230-242)

The unchecked `.reply` arm (API.lean:~660-664) delegates to
`endpointReplyWithDonation`, which internally calls `applyReplyDonation`
(Donation.lean:238). This is an **indirect** call site that also needs updating:

```lean
-- BEFORE (Donation.lean:~238):
let st'' := applyReplyDonation st' replier
.ok ((), PriorityInheritance.revertPriorityInheritance st'' replier)

-- AFTER:
match applyReplyDonation st' replier with
| .error e => .error e
| .ok st'' =>
  .ok ((), PriorityInheritance.revertPriorityInheritance st'' replier)
```

Similarly, `endpointCallWithDonation` (Donation.lean:~219) calls
`applyCallDonation` as a `let` binding and must be updated:

```lean
-- BEFORE (Donation.lean:~219):
let st'' := applyCallDonation st' caller receiverTid

-- AFTER:
match applyCallDonation st' caller receiverTid with
| .error e => .error e
| .ok st'' => ...
```

**Sub-step AH2-C-6: Update equivalence theorem** (API.lean:~1567-1591)

`dispatchWithCap_call_uses_withCaps` (line 1567) contains a RHS that
references `applyCallDonation` as a `let` binding. After the return type
changes to `Except`, the theorem's RHS must use `match ... with` instead of
`let`. The proof body uses `simp [dispatchWithCap, ...]` — since the function
definitions change, the proof may need additional `unfold applyCallDonation`
steps or `simp` lemmas for the new `match` structure.

**Sub-step AH2-C-7: Build affected modules**:
```bash
source ~/.elan/env
lake build SeLe4n.Kernel.IPC.Operations.Donation
lake build SeLe4n.Kernel.API
```

#### AH2-D: Update donation preservation theorems (M-02)

**Files**:
- `SeLe4n/Kernel/IPC/Operations/Donation.lean` (3 theorems)
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (1 theorem)
**Type**: Multi-step operation (4 theorems, each with specific proof strategy)

All 4 theorems currently state unconditional properties of the form
`(applyCallDonation st ...).field = st.field`. After the return type changes
to `Except`, each becomes a conditional property: `applyCallDonation st ... =
.ok st' → st'.field = st.field`.

**Sub-step AH2-D-1: Update `applyCallDonation_scheduler_eq`** (Donation.lean:128-152)

Current statement (unconditional):
```lean
theorem applyCallDonation_scheduler_eq
    (st : SystemState) (caller receiver : SeLe4n.ThreadId) :
    (applyCallDonation st caller receiver).scheduler = st.scheduler
```

New statement (conditional on success):
```lean
theorem applyCallDonation_scheduler_eq
    (st : SystemState) (caller receiver : SeLe4n.ThreadId)
    (st' : SystemState)
    (h : applyCallDonation st caller receiver = .ok st') :
    st'.scheduler = st.scheduler
```

**Proof strategy**: The existing proof (lines 131-152) case-splits on
`lookupTcb` and `schedContextBinding`, producing `rfl` for every early-exit
path. After the change, the early-exit paths return `.ok st`, so each `rfl`
becomes: `cases h; rfl` (inject the `.ok` to extract `st' = st`, then `rfl`).
The donation success path currently uses `exact donateSchedContext_scheduler_eq
...` which already handles the `Except` form — thread `h` through to extract
the `donateSchedContext = .ok _` hypothesis.

**Sub-step AH2-D-2: Update `applyCallDonation_machine_eq`** (Donation.lean:574-598)

Same transformation as AH2-D-1. Current proof (lines 577-598) has identical
structure — case splits with `rfl` for early exits and
`donateSchedContext_machine_eq` for the success path. The same proof strategy
applies: inject `.ok` at each early-exit, thread the hypothesis through the
donation success path.

**Sub-step AH2-D-3: Update `applyReplyDonation_machine_eq`** (Donation.lean:610-629)

Current statement:
```lean
theorem applyReplyDonation_machine_eq
    (st : SystemState) (replier : SeLe4n.ThreadId) :
    (applyReplyDonation st replier).machine = st.machine
```

New statement:
```lean
theorem applyReplyDonation_machine_eq
    (st : SystemState) (replier : SeLe4n.ThreadId)
    (st' : SystemState)
    (h : applyReplyDonation st replier = .ok st') :
    st'.machine = st.machine
```

**Proof strategy**: Similar to AH2-D-1/2 but the success path has an extra
composition: `returnDonatedSchedContext` + `removeRunnable`. The existing proof
(lines 623-629) already handles this composition. The `.ok` injection at each
early exit is mechanical. The success path now wraps `removeRunnable st'
replier` in `.ok`, so the `have hRem := removeRunnable_machine_eq st' replier`
line remains valid after extracting `st'` from the `.ok`.

**Sub-step AH2-D-4: Update `applyCallDonation_preserves_projection`**
(Operations.lean:2398-2419+)

Current statement:
```lean
theorem applyCallDonation_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (caller receiver : SeLe4n.ThreadId)
    (...hypotheses...) :
    projectState ctx observer (applyCallDonation st caller receiver) =
    projectState ctx observer st
```

New statement — add success hypothesis:
```lean
theorem applyCallDonation_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (caller receiver : SeLe4n.ThreadId)
    (st' : SystemState)
    (hOk : applyCallDonation st caller receiver = .ok st')
    (...existing hypotheses...) :
    projectState ctx observer st' = projectState ctx observer st
```

**Proof strategy**: The existing proof unfolds `applyCallDonation` and
case-splits on lookups. For each early-exit returning `.ok st`, inject `hOk`
to extract `st' = st`, then `subst st'; simp`. For the donation success path,
the existing `storeObject_preserves_projection` chain remains valid after
extracting the concrete `st'` from the `.ok` wrapper. The key change is that
the proof now operates on `st'` (a named variable) rather than `(applyCallDonation
st caller receiver)` (a compound term), which may simplify some simp steps.

**Sub-step AH2-D-5: Build affected modules**:
```bash
source ~/.elan/env
lake build SeLe4n.Kernel.IPC.Operations.Donation
lake build SeLe4n.Kernel.InformationFlow.Invariant.Operations
```

#### AH2-E: Extend `PlatformConfig` with `MachineConfig` field (M-03, L-16)

**Finding**: M-03 — `bootFromPlatform` does not call `applyMachineConfig`
**File**: `SeLe4n/Platform/Boot.lean` + `SeLe4n/Machine.lean`
**Type**: Multi-step operation (prerequisite required)

Currently `PlatformConfig` contains only `irqTable` and `initialObjects`.
`MachineConfig` is applied separately, creating a gap where callers forget the
second step.

**CRITICAL PREREQUISITE — `defaultMachineConfig`**:

`MachineConfig` (Machine.lean:742-759) has 7 fields, but only `registerCount`
has a default value (`32`). The remaining 6 fields (`registerWidth`,
`virtualAddressWidth`, `physicalAddressWidth`, `pageSize`, `maxASID`,
`memoryMap`) have **no defaults**. Therefore `MachineConfig := {}` is
**invalid Lean** — it would fail to compile.

Before adding the field to `PlatformConfig`, we must create a default
configuration constant:

```lean
/-- AH2-E: Default machine configuration for use as a `PlatformConfig` default.
    These values represent the abstract model's defaults (not any specific
    hardware platform). Platform-specific deployments should always provide
    explicit values. -/
def defaultMachineConfig : MachineConfig where
  registerWidth        := 64      -- ARM64 default
  virtualAddressWidth  := 48      -- ARMv8 VA width
  physicalAddressWidth := 52      -- ARMv8 max PA width
  pageSize             := 4096    -- Standard 4K pages
  maxASID              := 65536   -- 16-bit ASID (ARM64)
  memoryMap            := []      -- No regions by default
  registerCount        := 32      -- ARM64 GPR count
```

These defaults match the existing `MachineState` defaults (e.g.,
`physicalAddressWidth := 52` at MachineState definition) and the hardcoded
values already used throughout the codebase (e.g., `65536` for ASID).

**Atomic steps**:

1. **Create `defaultMachineConfig` in Machine.lean**: Add the constant after
   the `MachineConfig` structure definition (Machine.lean:~760), before the
   `registerFileGPRCount_eq_registerCount_default` theorem.

2. **Build `SeLe4n.Machine`** to verify the constant compiles.

3. **Add `machineConfig` field to `PlatformConfig`** (Boot.lean:56-58):
   ```lean
   structure PlatformConfig where
     irqTable : List IrqEntry
     initialObjects : List ObjectEntry
     machineConfig : MachineConfig := defaultMachineConfig
   ```

4. **Verify backward compatibility**: Existing callers that construct
   `PlatformConfig` with `{ irqTable := ..., initialObjects := ... }` will
   silently pick up `defaultMachineConfig` — this is backward-compatible.
   The 21+ theorems that reference `bootFromPlatform` will see no signature
   change (only `PlatformConfig` gains a field with a default).

5. **Build module**: `lake build SeLe4n.Platform.Boot`

#### AH2-F: Integrate `applyMachineConfig` into `bootFromPlatform` (M-03)

**File**: `SeLe4n/Platform/Boot.lean`, lines 148-151
**Type**: Multi-step operation (function change + caller updates + theorem impact)

**Sub-step AH2-F-1: Modify `bootFromPlatform`** (Boot.lean:148-151)

Note: `applyMachineConfig` (Boot.lean:326-340) sets 7 `MachineState` fields
on the `IntermediateState`. Verify it accepts `IntermediateState` (not
`SystemState`) as input — if it takes `SystemState`, a type adapter may be
needed. Read Boot.lean:326-340 to confirm the exact signature.

```lean
-- BEFORE:
def bootFromPlatform (config : PlatformConfig) : IntermediateState :=
  let initial := mkEmptyIntermediateState
  let withIrqs := foldIrqs config.irqTable initial
  foldObjects config.initialObjects withIrqs

-- AFTER:
def bootFromPlatform (config : PlatformConfig) : IntermediateState :=
  let initial := mkEmptyIntermediateState
  let withIrqs := foldIrqs config.irqTable initial
  let withObjects := foldObjects config.initialObjects withIrqs
  applyMachineConfig withObjects config.machineConfig
```

**Sub-step AH2-F-2: Remove redundant manual `applyMachineConfig` calls**

Search for callers that manually chain `applyMachineConfig` after
`bootFromPlatform`. Known instance:
- `tests/NegativeStateSuite.lean:~3312-3314`: manually applies machine config
  after boot. Remove the redundant second step.

```bash
# Find all callers
grep -rn 'applyMachineConfig' SeLe4n/ tests/ --include='*.lean'
```

**Sub-step AH2-F-3: Verify `bootFromPlatformChecked` inherits the fix**

`bootFromPlatformChecked` (Boot.lean:242) calls `bootFromPlatform` internally.
Since we changed `bootFromPlatform` to call `applyMachineConfig`, the checked
variant automatically benefits. No additional changes needed — just verify
it compiles.

**Sub-step AH2-F-4: Assess theorem impact**

The 21+ theorems that reference `bootFromPlatform` may need updates since the
function body now includes an `applyMachineConfig` step. Key theorems:
- `bootFromPlatform_objects_match`: may need to account for machine config
  not changing objects
- `bootFromPlatformChecked_*`: should inherit from `bootFromPlatform` changes
- Any theorem using `unfold bootFromPlatform` will now see the extra step

For most theorems, `applyMachineConfig` only modifies `machine` state fields
(not `objects`, `cdt`, `scheduler`, etc.), so object/scheduler-related
theorems should survive with an additional `simp` step. Machine-state
theorems will need the `config.machineConfig` values threaded through.

**Sub-step AH2-F-5: Build module**:
```bash
source ~/.elan/env && lake build SeLe4n.Platform.Boot
```

#### AH2-G: Fix `timeoutAwareReceive` empty message return (L-02)

**Finding**: L-02 — Returns empty message instead of error for missing pending
**File**: `SeLe4n/Kernel/IPC/Operations/Timeout.lean`, lines 131-133
**Type**: Atomic change

**Error variant selection**: `KernelError.ipcMessageEmpty` does **not exist**
in the codebase (State.lean:34-84 enumerates all 49 variants). The appropriate
existing variant is `endpointQueueEmpty` (State.lean:43) — this semantically
matches "expected a pending message but found none", which is analogous to
"expected a queue entry but found none".

Alternative: use `illegalState` (State.lean:37) if the empty-pending-message
case represents a protocol violation (thread claimed to have completed IPC but
has no message). `endpointQueueEmpty` is more specific and preferred.

**Atomic steps**:

1. **Read current code**: Timeout.lean lines 125-135.

2. **Change empty-message path to error**:

   **Before** (Timeout.lean:133):
   ```lean
   | none => .ok (.completed IpcMessage.empty, st)
   ```

   **After**:
   ```lean
   -- AH2-G: Return error for missing pending message (protocol violation).
   -- Under normal IPC invariants, a thread reaching this point should always
   -- have a pendingMessage set by the sender. The `none` case indicates a
   -- violated IPC protocol — surface it as an error rather than silently
   -- returning an empty message.
   | none => .error .endpointQueueEmpty
   ```

3. **Check callers**: There are 2 known callers (MainTraceHarness.lean:~2562
   and ~2577). Both call `timeoutAwareReceive` in test contexts where the
   `pendingMessage = none` path should be unreachable (the test sets up a
   sender before the receiver). If either test hits this path and now fails,
   it reveals a test setup bug (missing sender) rather than a kernel issue.

4. **Update test expectations if needed**: If any test expects
   `.ok (.completed IpcMessage.empty, _)`, update it to either:
   - Fix the test setup to ensure a pending message exists, or
   - Expect `.error .endpointQueueEmpty` if testing the error path

5. **Build module**: `lake build SeLe4n.Kernel.IPC.Operations.Timeout`

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
**Type**: Multi-step operation (code fix + invariant analysis + theorem impact)

When `cspaceDeleteSlotCore` fails for a descendant, the current code still
removes the CDT node (line 999), leaving the capability slot unreachable by
future CDT-based revocation. The fix preserves the CDT node on slot deletion
failure.

**Sub-step AH3-A-1: Modify the error branch** (Operations.lean:993-1000)

The fold body at line 982 processes each CDT descendant node. The error
branch is at lines 993-1000:

```lean
-- BEFORE (lines 993-1000):
| .error err =>
    let failure : RevokeCdtStrictFailure := {
      offendingNode := node
      offendingSlot := some descAddr
      error := err
    }
    let stRemoved := { stAcc with cdt := stAcc.cdt.removeNode node }
    ({ report with firstFailure := some failure }, stRemoved)

-- AFTER:
| .error err =>
    let failure : RevokeCdtStrictFailure := {
      offendingNode := node
      offendingSlot := some descAddr
      error := err
    }
    -- AH3-A: Preserve CDT node on slot deletion failure.
    -- The capability slot still exists; removing its CDT node would
    -- make it unreachable by future revocation, creating an orphan.
    ({ report with firstFailure := some failure }, stAcc)
```

Note: The success branch (lines 1001-1004) correctly removes the CDT node
AFTER successful deletion — this is unchanged.

**Sub-step AH3-A-2: Assess `cdtMapsConsistent` invariant impact**

The CDT invariant `cdtMapsConsistent` (defined in Capability/Invariant/Defs.lean)
requires bidirectional consistency between CDT nodes and capability slots.
Preserving the CDT node on deletion failure is **invariant-correct**: the
slot still exists with its original capability, and the CDT node still points
to it. Removing the CDT node while the slot persists is what breaks the
invariant (creating an unreachable slot).

The fix **strengthens** the CDT invariant: after a failed revocation, the CDT
still accurately reflects which slots exist. Future revocation attempts can
retry the failed deletions.

**Sub-step AH3-A-3: Note on `firstFailure` early-exit**

The fold body has an early-exit guard (line 984-985): once `firstFailure` is
set, subsequent nodes are skipped (`(report, stAcc)`). This means only one
deletion failure is ever encountered per revocation attempt. The CDT node
preservation for that single failed node does not interact with subsequent
nodes — they are simply left untouched.

**Sub-step AH3-A-4: Check preservation theorem impact**

The `cspaceRevokeCdtStrict` preservation theorem (Capability/Invariant/
Preservation.lean:~993-1050) may reference the `removeNode` call in the error
branch. After the change, this branch no longer modifies `cdt`, so the proof
should simplify (the error branch is now a no-op on state). Read the theorem
to confirm.

**Sub-step AH3-A-5: Build module**:
```bash
source ~/.elan/env && lake build SeLe4n.Kernel.Capability.Operations
lake build SeLe4n.Kernel.Capability.Invariant.Preservation
```

#### AH3-B: Refactor `setIPCBufferOp` to use `storeObject` (L-08)

**Finding**: L-08 — Manual state manipulation instead of `storeObject`
**File**: `SeLe4n/Kernel/Architecture/IpcBufferValidation.lean`, lines 92-110
**Type**: Multi-step operation (refactor + equivalence verification + theorem update)

The current implementation manually replicates `storeObject` semantics. If
`storeObject` is later extended, this operation would silently diverge.

**Sub-step AH3-B-1: Confirm semantic equivalence**

The manual code (IpcBufferValidation.lean:100-109) updates 4 state fields:
```
objects      := st.objects.insert tid.toObjId (.tcb tcb')
objectIndex  := if st.objectIndexSet.contains ... then st.objectIndex else ...
objectIndexSet := st.objectIndexSet.insert tid.toObjId
lifecycle    := { objectTypes := ..., capabilityRefs := ... }
```

`storeObject` (State.lean:521-546) updates 5 fields: the same 4 above plus
`asidTable`. For a TCB-to-TCB update:
- `asidTable` clear step: `st.objects[tid.toObjId]?` is `some (.tcb ...)`, not
  `.vspaceRoot`, so `cleared = st.asidTable`
- `asidTable` set step: `.tcb tcb'` is not `.vspaceRoot`, so result is `cleared`
  = `st.asidTable` (unchanged)

Therefore `storeObject` produces **identical state** to the manual code for
TCB-to-TCB updates. The `asidTable` branch is a no-op.

However, `storeObject` also handles `lifecycle.capabilityRefs` via a
`cap.slots.fold` for CNode objects. For TCB objects, the `| _ => cleared`
branch clears capability refs for the object — which may differ from the
manual code's `capabilityRefs := st.lifecycle.capabilityRefs` (preserving
existing refs). **Verify this**: read `storeObject` lines 530-537 to confirm
whether `cleared` filters by `ref.cnode ≠ id` (which for a TCB would remove
any refs where the TCB is the cnode — TCBs are never cnodes, so this filter
is a no-op).

**Sub-step AH3-B-2: Apply the refactoring**

```lean
-- BEFORE (IpcBufferValidation.lean:98-109):
| some (.tcb tcb) =>
  let tcb' := { tcb with ipcBuffer := addr }
  .ok { st with
    objects := st.objects.insert tid.toObjId (.tcb tcb')
    objectIndex := if st.objectIndexSet.contains tid.toObjId then st.objectIndex
                   else tid.toObjId :: st.objectIndex
    objectIndexSet := st.objectIndexSet.insert tid.toObjId
    lifecycle := {
      objectTypes := st.lifecycle.objectTypes.insert tid.toObjId
        (KernelObject.tcb tcb').objectType
      capabilityRefs := st.lifecycle.capabilityRefs
    }
  }

-- AFTER:
| some (.tcb tcb) =>
  let tcb' := { tcb with ipcBuffer := addr }
  storeObject tid.toObjId (.tcb tcb') st
```

Note: `storeObject` returns `Kernel Unit` (i.e., `SystemState → Except
KernelError (Unit × SystemState)`). The current code returns `Except
KernelError SystemState`. Use pattern matching to adapt:
```lean
| some (.tcb tcb) =>
  let tcb' := { tcb with ipcBuffer := addr }
  match storeObject tid.toObjId (.tcb tcb') st with
  | .ok ((), st') => .ok st'
  | .error e => .error e
```

Or simplify: `storeObject` always returns `.ok` (it never errors), so we can
use `let (.ok ((), st')) := storeObject tid.toObjId (.tcb tcb') st; .ok st'`.

**Sub-step AH3-B-3: Update preservation theorems**

The cross-subsystem bridge theorem at CrossSubsystem.lean:~2202-2224
(`setIPCBufferOp_preserves_crossSubsystemInvariant`) reasons about the manual
struct-with pattern. After the refactoring, it should use
`storeObject_preserves_*` lemmas instead. This likely simplifies the proof
(reuses existing `storeObject` infrastructure instead of manual field reasoning).

**Sub-step AH3-B-4: Build module**:
```bash
source ~/.elan/env
lake build SeLe4n.Kernel.Architecture.IpcBufferValidation
lake build SeLe4n.Kernel.CrossSubsystem
```

#### AH3-C: Replace hardcoded ASID 65536 with `st.machine.maxASID` (L-14)

**Finding**: L-14 — Architecture-independent decode hardcodes ARM64 ASID limit
**File**: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`, lines 209 and 234
**Type**: Multi-step operation (2 functions + 2 dispatch callers + tests)

**Recommended approach**: Option A — add `maxASID : Nat` parameter to both
decode functions. This is minimal and avoids threading `SystemState` through
a pure decode layer.

**Sub-step AH3-C-1: Update `decodeVSpaceMapArgs`** (SyscallArgDecode.lean:201-224)

```lean
-- BEFORE (line 201):
def decodeVSpaceMapArgs (decoded : SyscallDecodeResult)
    : Except KernelError VSpaceMapArgs := do

-- AFTER:
def decodeVSpaceMapArgs (decoded : SyscallDecodeResult) (maxASID : Nat)
    : Except KernelError VSpaceMapArgs := do
```

And at line 209:
```lean
-- BEFORE:
if !asid.isValidForConfig 65536 then .error .asidNotBound

-- AFTER:
if !asid.isValidForConfig maxASID then .error .asidNotBound
```

**Sub-step AH3-C-2: Update `decodeVSpaceUnmapArgs`** (SyscallArgDecode.lean:228-243)

Same change:
```lean
-- BEFORE (line 228):
def decodeVSpaceUnmapArgs (decoded : SyscallDecodeResult)
    : Except KernelError VSpaceUnmapArgs := do

-- AFTER:
def decodeVSpaceUnmapArgs (decoded : SyscallDecodeResult) (maxASID : Nat)
    : Except KernelError VSpaceUnmapArgs := do
```

And at line 234: `65536` → `maxASID`.

**Sub-step AH3-C-3: Update dispatch callers in API.lean**

The `.vspaceMap` arm (API.lean:~462) and `.vspaceUnmap` arm (API.lean:~472)
both call these decode functions. Both arms are inside `dispatchCapabilityOnly`
which receives `SystemState` as `st`:

```lean
-- .vspaceMap arm (API.lean:~462) — BEFORE:
fun st => match decodeVSpaceMapArgs decoded with
-- AFTER:
fun st => match decodeVSpaceMapArgs decoded st.machine.maxASID with

-- .vspaceUnmap arm (API.lean:~472) — BEFORE:
fun st => match decodeVSpaceUnmapArgs decoded with
-- AFTER:
fun st => match decodeVSpaceUnmapArgs decoded st.machine.maxASID with
```

**Sub-step AH3-C-4: Update equivalence theorems**

The structural equivalence theorem `checkedDispatch_vspaceMap_eq_unchecked`
(API.lean:~1060-1065) and any related theorems that reference the decode
functions will need the `maxASID` parameter threaded through. Since both
checked and unchecked paths use the shared `dispatchCapabilityOnly` function
for `.vspaceMap`/`.vspaceUnmap`, the equivalence should survive with the
parameter addition.

**Sub-step AH3-C-5: Update DecodingSuite tests**

`tests/DecodingSuite.lean` tests `decodeVSpaceMapArgs` and
`decodeVSpaceUnmapArgs` directly. Each test call must pass a `maxASID`
value. Use `65536` (the ARM64 default) to keep existing test semantics:

```lean
-- BEFORE:
match decodeVSpaceMapArgs decoded with
-- AFTER:
match decodeVSpaceMapArgs decoded 65536 with
```

This maintains backward compatibility for tests while enabling platform
independence in production dispatch.

**Sub-step AH3-C-6: Build affected modules**:
```bash
source ~/.elan/env
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
**Type**: Multi-step operation (script creation + integration)

Create a CI-safe shell script following the project's existing patterns
(`check_website_links.sh`, `test_tier0_hygiene.sh`). The script validates
version consistency across all known version-bearing files against the
canonical `lakefile.toml` version.

**Full script specification**:

```bash
#!/usr/bin/env bash
# seLe4n — version sync check
# Validates that all version-bearing files match lakefile.toml
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

# Extract canonical version from lakefile.toml
CANONICAL=$(grep '^version' lakefile.toml | sed 's/.*"\(.*\)"/\1/')
if [[ -z "${CANONICAL}" ]]; then
  echo "ERROR: Could not extract version from lakefile.toml" >&2
  exit 1
fi

FAIL=0

check_file() {
  local file="$1" pattern="$2" label="$3"
  if [[ ! -f "${file}" ]]; then
    echo "WARN: ${file} not found (skipped)"
    return
  fi
  if ! grep -q "${CANONICAL}" <(grep "${pattern}" "${file}"); then
    local actual
    actual=$(grep "${pattern}" "${file}" | head -1)
    echo "MISMATCH: ${label}"
    echo "  Expected: ${CANONICAL}"
    echo "  Found:    ${actual}"
    echo "  File:     ${file}"
    FAIL=1
  fi
}

# 1. Rust HAL boot banner
check_file "rust/sele4n-hal/src/boot.rs" "KERNEL_VERSION" "Rust HAL KERNEL_VERSION"

# 2. Rust workspace Cargo.toml
check_file "rust/Cargo.toml" 'version\s*=' "Rust workspace version"

# 3. Spec document
check_file "docs/spec/SELE4N_SPEC.md" "Package version" "SELE4N_SPEC package version"

# 4. i18n README badges (10 files)
for lang in ar de es fr hi ja ko pt-BR ru zh-CN; do
  readme="docs/i18n/${lang}/README.md"
  check_file "${readme}" "version-" "i18n README (${lang})"
done

echo "Canonical version: ${CANONICAL}"
if [[ "${FAIL}" -eq 1 ]]; then
  echo "FAIL: Version sync check found mismatches." >&2
  exit 1
else
  echo "PASS: All version-bearing files match lakefile.toml."
fi
```

**Checked files** (14 total):

| # | File | Pattern | Notes |
|---|------|---------|-------|
| 1 | `rust/sele4n-hal/src/boot.rs` | `KERNEL_VERSION` | UART boot banner |
| 2 | `rust/Cargo.toml` | `version =` | Workspace version |
| 3 | `docs/spec/SELE4N_SPEC.md` | `Package version` | Spec table |
| 4–13 | `docs/i18n/*/README.md` | `version-` | Badge SVGs (10 files) |

**Atomic steps**:

1. **Write the script** (under 60 lines — safe for single Write call)
2. **Make executable**: `chmod +x scripts/check_version_sync.sh`
3. **Run shellcheck**: `shellcheck scripts/check_version_sync.sh`
4. **Pre-fix validation**: Run against current (stale) state — should report
   mismatches for `boot.rs`, i18n READMEs, spec, etc.
5. **Post-fix validation**: Run after AH4-A through AH4-D — should pass

#### AH4-F: Integrate version check into Tier 0 hygiene

**File**: `scripts/test_tier0_hygiene.sh`
**Type**: Atomic change

Add `scripts/check_version_sync.sh` call to the Tier 0 hygiene check script
so it runs on every PR and push.

**Atomic steps**:

1. **Read current script**: `scripts/test_tier0_hygiene.sh`, specifically the
   insertion region around the website link check (line 98).

2. **Insert after line 98** (after `run_check "HYGIENE" "${SCRIPT_DIR}/check_website_links.sh"`):
   ```bash
   # AH4-F: Version sync — validate all version-bearing files match lakefile.toml.
   run_check "HYGIENE" "${SCRIPT_DIR}/check_version_sync.sh"
   ```

   This follows the existing `run_check "HYGIENE"` pattern used by all other
   checks in the script. The `run_check` function handles pass/fail reporting
   and respects `CONTINUE_MODE`.

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
- `SeLe4n/Platform/Boot.lean`, line ~898 (M-04)
- `SeLe4n/Kernel/InformationFlow/Projection.lean`, line ~185 (M-07)
**Type**: Multi-step operation (2 comment insertions)

**Sub-step AH5-A-1: M-04 — VSpaceRoot boot exclusion** (Boot.lean:~898)

Insert comment block immediately above the `bootSafeObject` definition:
```lean
/-- M-04/AH5-A: Design rationale — VSpaceRoot exclusion from boot objects.
VSpaceRoots are excluded from `bootSafeObject` because ASID table registration
(`asidTable.insert asid id` in `storeObject`) requires a fully initialized
ASID manager, which is not available during the builder-phase boot sequence.

**Tradeoff**: All address spaces must be configured post-boot via `vspaceMap`
syscalls. This prevents pre-populating address space mappings during boot.

**Integration timeline**: VSpaceRoot boot support is planned for WS-V when the
ASID manager is wired into the `IntermediateState` builder operations. The
`AsidManager` type and `asidPoolUnique` invariant (AsidManager.lean) provide
the foundation — the missing piece is builder-phase ASID pool integration. -/
```

**Sub-step AH5-A-2: M-07 — pendingMessage NI visibility** (Projection.lean:~185)

Insert comment block at the `projectKernelObject` TCB case, immediately
before or after the `pendingMessage` field projection:
```lean
-- M-07/AH5-A: Security analysis — pendingMessage visibility in NI projection.
-- `pendingMessage` is technically visible in the projection (not stripped
-- like `registerContext`). However, cross-domain information leakage via
-- `pendingMessage` is unreachable under the NI invariant conjunction:
--
-- 1. `runnableThreadIpcReady`: observable threads are in `.ready` IPC state,
--    meaning they have no pending message from a cross-domain sender.
-- 2. `currentNotEndpointQueueHead`: the current thread is not in any endpoint
--    queue, preventing it from receiving cross-domain messages while observable.
-- 3. Domain scheduling: only threads in the current domain are observable,
--    and IPC messages across domains require a domain switch.
--
-- A formal proof that these invariants make `pendingMessage` exposure
-- unreachable is tracked for WS-V (non-interference refinement).
```

#### AH5-B: Document spec-level findings (M-05, M-06, L-13)

**File**: `docs/spec/SELE4N_SPEC.md`
**Type**: Multi-step operation (3 subsection insertions)

Read `docs/spec/SELE4N_SPEC.md` in chunks to locate the exact insertion points
for each subsection. The spec is ~969 lines with distinct sections for
platform, capability, and architecture.

**Sub-step AH5-B-1: M-05 — Simulation contract limitations**

Locate the "Platform" or "Platform Testing" section in the spec. Insert a
subsection:

```markdown
### Platform Testing Limitations (M-05)

The simulation platform contract (`Sim/Contract.lean`) uses permissive
`True` propositions for all runtime and boot obligations. This is by design
— simulation enables fast iteration and test execution without hardware.

**Limitations**:
- The RPi5 `registerContextStable` check (6 conditions: stack alignment,
  PC kernel range, budget positivity, SP mapped, return address valid,
  TLS pointer valid) is NOT exercisable under simulation
- Cache coherency model proofs (`CacheModel.lean`) are trivially satisfied
- Interrupt disable/enable semantics are sequential-model approximations

**Recommendation**: Use the `Sim.Restrictive` contract for property
validation (it imposes some structural constraints). For production-
representative testing, use the RPi5 contract (`RPi5/Contract.lean`).
```

**Sub-step AH5-B-2: M-06 — CNode intermediate rights divergence**

Locate the "Capability" section in the spec. Insert a subsection:

```markdown
### seL4 Divergence: CNode Intermediate Rights (M-06)

`resolveCapAddress` (Operations.lean:85-128) does NOT check `Read` rights
on intermediate CNode capabilities during multi-level CSpace traversal.
This diverges from seL4, which requires `Read` on each intermediate CNode.

**Impact**: A thread with only `Write` right on an intermediate CNode can
still resolve capabilities through it, broadening the access path. However,
no additional *operations* become accessible — rights are still checked at
the leaf capability by the individual operation handler.

**Rationale**: seLe4n uses a single-resolution-per-syscall model where each
syscall resolves exactly one capability path. The intermediate rights check
in seL4 guards against multi-hop traversals that could bypass CNode access
control; in seLe4n's flat model, this guard is redundant.

**Source annotation**: U-M25 (Operations.lean).
```

**Sub-step AH5-B-3: L-13 — TPIDR_EL0 / TLS gap**

Locate the "Architecture Model" section in the spec. Insert a note:

```markdown
### Architecture Gap: TPIDR_EL0 / TLS (L-13)

`RegisterFile` (Prelude.lean) models GPRs (x0-x30), PC, and SP only.
The ARM64 `TPIDR_EL0` register (thread-local storage pointer) is not
modeled. This register is required for user-space TLS support (e.g.,
`__thread` variables, Go runtime, Rust `thread_local!`).

**Integration timeline**: TPIDR_EL0 modeling is planned for a future
AG-phase when user-space binary loading and context switching of system
registers are implemented. The `TrapFrame` in `sele4n-hal` (272 bytes)
already has space for system register state; the Lean model needs a
corresponding `RegisterFile` extension.
```

#### AH5-C: Document defense-in-depth findings in source code (M-08, L-11, L-12)

**Files**:
- `SeLe4n/Kernel/CrossSubsystem.lean`, lines ~273-292 (M-08)
- `SeLe4n/Prelude.lean`, lines ~510-532 (L-11)
- `SeLe4n/Model/Object/Types.lean`, line ~531 (L-12)
**Type**: Multi-step operation (3 comment insertions at specific locations)

**Sub-step AH5-C-1: M-08 — Cross-subsystem composition gap**
(CrossSubsystem.lean:~273-292)

There is already a gap documentation block at this location. **Update** the
existing comment (do not add a duplicate) with:

```lean
-- M-08/AH5-C: Cross-subsystem composition coverage assessment.
-- Current: 10 predicates in `crossSubsystemInvariant`, yielding 45 pairwise
-- disjointness analyses (10 choose 2). Coverage:
--   - Frame lemmas: ALL 33 kernel operations that modify `objects` have per-
--     operation frame lemmas (AD4 portfolio, 2+33 bridge lemmas).
--   - Pairwise disjointness: most pairs are structurally disjoint (different
--     fields: scheduler vs objects vs cdt). Remaining gap scenarios:
--     (1) IPC queue membership ↔ service registry endpoint tracking
--     (2) Capability revocation ↔ service endpoint lifecycle
--   - Assessment: no known concrete violation. The gap is theoretical —
--     frame lemmas ensure each operation preserves all 10 predicates
--     individually. The missing piece is a formal proof that ALL 10
--     predicates compose correctly under arbitrary interleaving of all 33
--     operations (exponential combinatorics, deferred to WS-V).
```

**Sub-step AH5-C-2: L-11 — Badge constructor safety** (Prelude.lean:~510)

Insert comment block immediately above `structure Badge`:

```lean
-- L-11/AH5-C: Badge constructor safety analysis.
-- `Badge.mk n` with `n ≥ 2^64` produces an invalid badge (exceeds UInt64
-- word size). This is by design — Lean's Nat is unbounded, and `Badge` wraps
-- a Nat for proof convenience.
--
-- Safety layers:
-- 1. `Badge.valid` predicate: `b.val < 2^64` — used in proof obligations
-- 2. `Badge.ofNatMasked`: truncates to word size at construction
-- 3. `cspaceMint` (Operations.lean): uses masked badge from decoded syscall
-- 4. IPC message delivery: badge comes from stored Capability (already masked)
-- 5. Rust ABI: `Badge` is `u64` — hardware truncation at FFI boundary
--
-- Risk: only internal test code can construct `Badge.mk (2^64)` directly.
-- No user-facing syscall path bypasses `ofNatMasked` or `cspaceMint`.
-- BadgeOverflowSuite.lean (AG9-E) validates round-trip Nat↔UInt64 safety.
```

**Sub-step AH5-C-3: L-12 — maxControlledPriority default** (Types.lean:~531)

Insert comment block immediately above or beside the `maxControlledPriority`
field definition:

```lean
  -- L-12/AH5-C: Design rationale — maximally permissive MCP default.
  -- Default `0xFF` (255) allows any priority to be assigned without MCP
  -- restriction. This is safe because `setPriorityOp` (PriorityManagement.lean)
  -- enforces `newPrio ≤ caller.mcp` at the operation level — the target's own
  -- MCP is irrelevant to the authority check.
  --
  -- seL4 divergence: seL4 uses a restrictive default (0), requiring explicit
  -- MCP elevation before priority assignment. seLe4n's permissive default
  -- simplifies boot configuration: all threads can be assigned any priority
  -- without a separate MCP initialization step.
  --
  -- Production recommendation: set explicit MCP values during system
  -- initialization to enforce least-privilege priority assignment.
```

#### AH5-D: Update test fixtures and expected outputs

**Files**:
- `tests/fixtures/main_trace_smoke.expected`
- Any other fixture files affected by AH1–AH3 changes
**Type**: Multi-step operation

**Sub-step AH5-D-1: Identify affected fixtures**

Changes in AH1–AH3 that may alter trace output:
- **AH1 (H-01)**: Checked send now performs cap transfer — may change trace
  lines for IPC send operations (capability transfer summary output)
- **AH2-G (L-02)**: `timeoutAwareReceive` now errors instead of returning
  empty message — if any trace test hits this path, it will produce an error
  trace line instead of a success line
- **AH2-A/B (M-02)**: Donation error propagation — if any trace test triggers
  a donation error, it will now propagate instead of being swallowed

**Sub-step AH5-D-2: Generate new trace output**
```bash
source ~/.elan/env && lake exe sele4n > /tmp/new_trace.txt 2>&1
```

**Sub-step AH5-D-3: Compare and update**
```bash
diff /tmp/new_trace.txt tests/fixtures/main_trace_smoke.expected
```

If differences exist, update the fixture file with the new output. The
fixture file should not contain changelog comments — those go in the commit
message and CHANGELOG.md instead.

**Sub-step AH5-D-4: Run smoke tests**
```bash
./scripts/test_smoke.sh
```

#### AH5-E: Synchronize documentation

**Type**: Multi-step operation (6-8 files, ordered by dependency)

**Sub-step AH5-E-1: Regenerate `docs/codebase_map.json`**

If any Lean module paths changed or new definitions were added:
```bash
python3 scripts/generate_codebase_map.py > docs/codebase_map.json
```
This is the dependency root — README.md metrics and GitBook chapters
reference this file.

**Sub-step AH5-E-2: Update `docs/CHANGELOG.md`**

Add a new version entry at the top of the changelog. Follow existing format:
```markdown
## v0.27.2 — WS-AH: Pre-Release Comprehensive Audit Remediation

### Phase AH1: Critical IPC Dispatch Correctness (H-01, M-01)
- AH1-A: Fixed `endpointSendDualChecked` to delegate to
  `endpointSendDualWithCaps` (was `endpointSendDual`)
- AH1-B: Updated checked `.send` dispatch arm in API.lean
- AH1-C: Updated 4 NI soundness theorems for new signature
- AH1-D: Wired `validateVSpaceMapPermsForMemoryKind` into `.vspaceMap` dispatch
- AH1-E: Updated 10 test call sites across 3 files

### Phase AH2: IPC Donation Safety & Boot Pipeline (M-02, M-03, L-02)
[... per-sub-task entries ...]

### Phase AH3: Capability, Architecture & Decode Hardening (L-04, L-08, L-14)
[... per-sub-task entries ...]

### Phase AH4: Version Consistency & CI Automation (H-02)
[... per-sub-task entries ...]

### Phase AH5: Documentation, Testing & Closure
[... per-sub-task entries ...]
```

**Sub-step AH5-E-3: Update `docs/WORKSTREAM_HISTORY.md`**

Add WS-AH portfolio entry following existing format (copy structure from
WS-AG entry). Include phase completion dates, sub-task count, and gate criteria.

**Sub-step AH5-E-4: Update `docs/DEVELOPMENT.md`**

Add WS-AH portfolio status line in the "Completed Workstreams" section.

**Sub-step AH5-E-5: Update `README.md`**

Sync metrics from `docs/codebase_map.json`:
- Module count (if changed)
- Theorem count (if changed)
- Version badge (to `0.27.2` or whatever version AH produces)

**Sub-step AH5-E-6: Update `CLAUDE.md`**

Add WS-AH to the "Active workstream context" section, following the existing
format. Move it above the WS-AG entries. Update the version reference in the
project description header.

**Sub-step AH5-E-7: Update `docs/CLAIM_EVIDENCE_INDEX.md`**

Only update if claims changed. The H-01 fix (checked send now performs cap
transfer) may affect claims about information-flow enforcement completeness.
Check the index for any claims referencing `endpointSendDualChecked`.

**Sub-step AH5-E-8: Update affected GitBook chapters**

Check `docs/gitbook/12-proof-and-invariant-map.md` for references to theorems
modified in AH1-C and AH2-D. Update if needed (GitBook mirrors canonical docs).

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
| AH1 | ~100–160 (fn + 4 theorems + 10 test sites) | 0 | 0 | 7 |
| AH2 | ~150–220 (2 fn + 7 call sites + 4 theorems + boot + config) | 0 | 0 | 8 |
| AH3 | ~80–120 (3 fixes + 2 theorem updates) | 0 | 0 | 7 |
| AH4 | 0 | ~80–120 | ~30 | 16 |
| AH5 | ~30–60 (comments only) | 0 | ~300–500 | 12–18 |

---

## 9. Risk Assessment

### 9.1 High-Risk Sub-tasks

| Sub-task | Risk | Mitigation |
|----------|------|------------|
| AH1-C (NI theorem updates) | Soundness theorems may require non-trivial proof restructuring when `endpointSendDualChecked` return type changes from `Unit` to `CapTransferSummary` | Follow `endpointCallChecked` theorem pattern as template; the information-flow property (success ⟹ `securityFlowsTo`) is structurally identical |
| AH2-D (Donation preservation theorems) | Conditional postconditions change proof obligations for `applyCallDonation_preserves_projection` | Early-exit `.ok st` paths satisfy preservation trivially (state unchanged); focus proof effort on the `donateSchedContext` success path |
| AH2-E (defaultMachineConfig prerequisite) | `MachineConfig` has no defaults for 6/7 fields — `MachineConfig := {}` is invalid Lean | Create `defaultMachineConfig` constant with explicit values matching existing codebase defaults (PA=52, ASID=65536, etc.) |
| AH2-F (Boot pipeline change) | Existing callers may break if `PlatformConfig` constructor syntax changes | Default `machineConfig := defaultMachineConfig` field preserves backward compatibility for all existing callers |

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
| L-01 | LOW | **No-action** | — | Safe under `tcbQueueLinkIntegrity` invariant (AE4-E) |
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
| AH1 | `Wrappers.lean`, `Soundness.lean`, `API.lean`, `MainTraceHarness.lean`, `InformationFlowSuite.lean`, `TraceSequenceProbe.lean`, `main_trace_smoke.expected` |
| AH2 | `Machine.lean` (defaultMachineConfig), `Donation.lean`, `API.lean`, `Operations.lean` (IF), `Boot.lean`, `Timeout.lean`, `NegativeStateSuite.lean` |
| AH3 | `Operations.lean` (Cap), `Preservation.lean` (Cap), `IpcBufferValidation.lean`, `CrossSubsystem.lean`, `SyscallArgDecode.lean`, `API.lean`, `DecodingSuite.lean` |
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
