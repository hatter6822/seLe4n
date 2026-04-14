# Workstream Plan — WS-AJ: Post-Audit Comprehensive Remediation (v0.28.0)

**Audit source:** `docs/audits/AUDIT_v0.28.0_COMPREHENSIVE.md`
**Date:** 2026-04-14
**Version:** 0.28.0
**Workstream ID:** WS-AJ
**Phases:** 6 (AJ1–AJ6)
**Total sub-tasks:** 30

---

## 1. Executive Summary

This workstream resolves every actionable finding from the v0.28.0 comprehensive
audit. The audit reported 43 non-informational findings (3 HIGH, 21 MEDIUM,
19 LOW). Independent verification against the codebase confirmed:

- **41 findings are valid and actionable** (code change or documentation)
- **2 findings are erroneous** (L-01, L-17 — issues already fixed or nonexistent)
- **1 finding is partially true** (L-06 — VA checks exist but no PA bounds check)
- **1 audit metadata error** (executive summary claims 55/24M; actual is 52/21M)

The HIGH findings (H-01, H-02, H-03) concern large architectural integration
tasks — wiring orphaned hardware modules, activating budget-aware scheduling,
and connecting the FFI bridge. These are pre-hardware deployment requirements
that cannot be resolved in a single remediation phase. This workstream documents
clear activation roadmaps for these and defers their implementation to WS-V
(AG10: Hardware Integration).

The actionable items are organized into 30 sub-tasks across 6 phases, ordered
by severity and subsystem affinity:

| Phase | Focus | Sub-tasks | Findings Addressed |
|-------|-------|-----------|-------------------|
| AJ1 | IPC & Lifecycle Correctness | 6 | M-14, M-04, M-02, M-01, L-02, L-18 |
| AJ2 | Security & Information Flow | 4 | M-10, M-11, M-12, M-09 |
| AJ3 | Platform & Boot Pipeline | 6 | M-17, M-18, M-16, M-19, L-04, L-12 |
| AJ4 | Architecture Model Correctness | 4 | M-07, M-06, L-06, L-09 |
| AJ5 | Rust HAL Hardening | 4 | M-20, M-21, L-14, L-15 |
| AJ6 | Documentation, Testing & Closure | 6 | H-01–H-03, M-03/05/08/13/15, L-01/03/05/07/08/10/11/13/16/17/19, audit errata |


---

## 2. Audit Verification Results

Before planning remediation, every finding was independently verified against
the current codebase. This section documents discrepancies.

### 2.1 Erroneous Findings (2)

**L-01: `chooseThreadEffective` lacks preservation proofs — FALSE**

The audit claims no preservation proofs exist for `chooseThreadEffective`. This
is incorrect. `chooseThreadEffective_preserves_state` is proven in
`Scheduler/Operations/Selection.lean:459` and re-exported in
`Preservation.lean:3435` as `chooseThreadEffective_state_unchanged`. The
function is read-only (returns a `ThreadId` selection without modifying state),
so "preservation" is state equality, which is proven. **No action required.**

**L-17: FrozenOps `frozenQueuePopHead` stale `queuePPrev` — FALSE**

The audit claims the new head's `queuePPrev` still points to the old head after
pop. This was already fixed. `FrozenOps/Operations.lean:326-329` shows the
dequeued TCB is cleaned with `{ headTcb with queuePrev := none, queueNext :=
none, queuePPrev := none }`. The `queuePPrev` field is explicitly cleared, as
noted by the `U-H01` annotation. **No action required.**

### 2.2 Partially True Finding (1)

**L-06: IPC buffer physical address bounds not checked — PARTIALLY TRUE**

`IpcBufferValidation.lean:55-76` performs alignment, canonical address, VSpace
root validity, mapping existence (via `root.lookup`), and write permission
checks. The mapping lookup confirms the VA maps to something with write
permission, but no explicit PA range check against `physicalAddressBound`
exists. The validation is purely virtual-address-based. **Actionable — add PA
bounds check in Phase AJ4.**

### 2.3 Audit Metadata Corrections

The executive summary states "55 findings (24 Medium)" but the finding table
lists 52 entries: 3 HIGH + 21 MEDIUM + 19 LOW + 9 INFO = 52. The correct
totals are **52 findings with 21 Medium**. This will be corrected in the audit
errata (Phase AJ6).

### 2.4 Findings Confirmed as By-Design (No Code Change Required)

Several confirmed findings describe deliberate design decisions that are already
documented in the codebase. These require no code change, only acknowledgment
and optional documentation enhancement:

| Finding | Design Rationale |
|---------|-----------------|
| M-03 | `endpointQueueRemove` bypass is intentional (AF5-C/AF-06), preservation proof exists |
| M-05 | VSpaceARMv8 refinement proofs deferred to WS-V (orphaned module, H-01) |
| M-08 | ExceptionModel/InterruptDispatch orphaned (subset of H-01) |
| M-13 | `niStepCoverage` universal witness is intentional; real NI in `step_preserves_projection` |
| M-15 | `resolveCapAddress` rights divergence from seL4 is documented (U-M25) |
| L-03 | Notification LIFO matches seL4 semantics |
| L-05 | `objectIndex` append-only is documented design choice with growth analysis |
| L-07 | `tlbBarrierComplete := True` is placeholder for hardware binding (H-01 scope) |
| L-08 | `collectQueueMembers` fuel sufficiency deferred (TPI-DOC) |
| L-10 | `cspaceRevokeCdt` materialization is performance concern, not correctness |
| L-11 | Sim/RPi5 PA width gap is testing scope concern, not correctness |
| L-13 | `classifyMemoryRegion` base-only check is documented |
| L-16 | RadixTree `extractBits` offset generality is unused but harmless |
| L-19 | CDT acyclicity externalization is documented design choice |


---

## 3. Finding Disposition Matrix

Every non-informational finding is classified into one of four dispositions:

| Disposition | Count | Description |
|-------------|-------|-------------|
| **FIX** | 24 | Code change required in this workstream |
| **DOCUMENT** | 14 | Documentation-only (by-design, deferred, or activation roadmap) |
| **ERRONEOUS** | 2 | Finding does not reflect current codebase state |
| **DEFER+DOC** | 3 | Deferred to WS-V with activation roadmap documented here |

### 3.1 Full Disposition Table

| ID | Sev | Disposition | Phase | Summary |
|----|-----|-------------|-------|---------|
| H-01 | HIGH | DEFER+DOC | AJ6 | 7 orphaned architecture modules → WS-V activation roadmap |
| H-02 | HIGH | DEFER+DOC | AJ6 | Budget-aware scheduler dead code → WS-V activation plan |
| H-03 | HIGH | DEFER+DOC | AJ6 | FFI bridge orphaned → WS-V wiring plan |
| M-01 | MED | FIX | AJ1 | Reply/ReplyRecv structural equivalence theorem |
| M-02 | MED | FIX | AJ1 | Pre-send receiver linking theorem |
| M-03 | MED | DOCUMENT | AJ6 | endpointQueueRemove bypass (already documented) |
| M-04 | MED | FIX | AJ1 | Reply authorization replyTarget unreachability proof |
| M-05 | MED | DOCUMENT | AJ6 | VSpaceARMv8 refinement deferred (H-01 scope) |
| M-06 | MED | FIX | AJ4 | Wire targeted TLB flush into VSpace operations |
| M-07 | MED | FIX | AJ4 | Replace tautological pageTableWalk_deterministic |
| M-08 | MED | DOCUMENT | AJ6 | ExceptionModel/InterruptDispatch orphaned (H-01 scope) |
| M-09 | MED | FIX | AJ2 | ThreadId/SchedContextId namespace disjointness invariant |
| M-10 | MED | FIX | AJ2 | AccessRightSet.mk constructor → private |
| M-11 | MED | FIX | AJ2 | Strip pipBoost from NI projection |
| M-12 | MED | FIX | AJ2 | Strengthen isInsecureDefaultContext sentinel check |
| M-13 | MED | DOCUMENT | AJ6 | niStepCoverage universal witness (intentional) |
| M-14 | MED | FIX | AJ1 | cleanupDonatedSchedContext error propagation |
| M-15 | MED | DOCUMENT | AJ6 | resolveCapAddress rights divergence (documented) |
| M-16 | MED | FIX | AJ3 | Wire bootSafe validation into bootFromPlatformChecked |
| M-17 | MED | FIX | AJ3 | Propagate fromDtbFull fuel exhaustion error |
| M-18 | MED | FIX | AJ3 | Fix DTB PA width default (48 → platform-specific) |
| M-19 | MED | FIX | AJ3 | BootBoundaryContract substantive defaults |
| M-20 | MED | FIX | AJ5 | MMIO alignment → runtime assert! |
| M-21 | MED | FIX | AJ5 | Migrate static mut BOOT_UART_INNER |
| L-01 | LOW | ERRONEOUS | AJ6 | Preservation proofs exist (false finding) |
| L-02 | LOW | FIX | AJ1 | Remove dead endpointQueuePopHeadFresh |
| L-03 | LOW | DOCUMENT | AJ6 | LIFO starvation (seL4 design) |
| L-04 | LOW | FIX | AJ3 | interruptsEnabled default → false |
| L-05 | LOW | DOCUMENT | AJ6 | objectIndex append-only (documented) |
| L-06 | LOW | FIX | AJ4 | IPC buffer PA bounds check |
| L-07 | LOW | DOCUMENT | AJ6 | tlbBarrierComplete placeholder (H-01 scope) |
| L-08 | LOW | DOCUMENT | AJ6 | collectQueueMembers fuel (TPI-DOC deferred) |
| L-09 | LOW | FIX | AJ4 | TCB placeholder IDs → sentinel values |
| L-10 | LOW | DOCUMENT | AJ6 | cspaceRevokeCdt materialization (performance) |
| L-11 | LOW | DOCUMENT | AJ6 | Sim/RPi5 PA width gap (testing scope) |
| L-12 | LOW | FIX | AJ3 | Remove fromDtb dead stub |
| L-13 | LOW | DOCUMENT | AJ6 | classifyMemoryRegion base-only (documented) |
| L-14 | LOW | FIX | AJ5 | init_timer(0) → Result error |
| L-15 | LOW | FIX | AJ5 | increment_tick_count → pub(crate) |
| L-16 | LOW | DOCUMENT | AJ6 | extractBits offset generality (harmless) |
| L-17 | LOW | ERRONEOUS | AJ6 | Already fixed (false finding) |
| L-18 | LOW | FIX | AJ1 | endpointReceiveDualWithCaps error symmetry |
| L-19 | LOW | DOCUMENT | AJ6 | CDT acyclicity externalization (by design) |


---

## 4. Phase AJ1: IPC & Lifecycle Correctness

**Priority:** Critical — fixes potential security and correctness bugs
**Findings:** M-14, M-04, M-02, M-01, L-02, L-18
**Files modified:** `Lifecycle/Operations.lean`, `IPC/DualQueue/Transport.lean`,
`IPC/Operations/Donation.lean`, `IPC/DualQueue/WithCaps.lean`,
`IPC/DualQueue/Core.lean`, `API.lean`, preservation/invariant files
**Gate:** `lake build` + `test_smoke.sh` + zero sorry/axiom

### AJ1-A: `cleanupDonatedSchedContext` Error Propagation (M-14/MEDIUM)

**Problem:** `cleanupDonatedSchedContext` in `Lifecycle/Operations.lean:122-131`
returns `SystemState` and silently swallows `returnDonatedSchedContext` errors.
When retype destroys a TCB, a failed cleanup leaves the SchedContext's
`boundThread` pointing to the destroyed TCB — a dangling reference.

**Fix:**
1. Change return type from `SystemState` to `Except KernelError SystemState`.
2. Propagate the `.error` case to callers instead of returning `st` unchanged.
3. Update callers in `Lifecycle/Operations.lean` (`lifecycleRetypeObject` or
   `cleanupBeforeRetype`) to handle the error — either propagate further or
   fail the retype.
4. Update any preservation theorems that reference `cleanupDonatedSchedContext`
   to use conditional postconditions (match on `.ok st'`).

**Files:**
- `SeLe4n/Kernel/Lifecycle/Operations.lean` — return type change + caller update
- `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean` — frame lemmas
- `SeLe4n/Kernel/CrossSubsystem.lean` — if bridge lemmas reference this

**Estimated scope:** ~40 lines changed, ~20 lines new preservation lemmas

### AJ1-B: Reply Authorization Unreachability Proof (M-04/MEDIUM)

**Problem:** In `IPC/DualQueue/Transport.lean:1773-1775`, when a thread is in
`blockedOnReply` with `replyTarget = none`, ANY thread can reply (authorized
:= true). While `endpointCall` always sets `replyTarget := some receiver`,
making this path theoretically unreachable, there is no formal proof.

**Fix:**
1. Add theorem `blockedOnReply_has_replyTarget`: prove that under the IPC
   invariant (`ipcInvariantFull`), any thread in `blockedOnReply` state has
   `replyTarget = some _`. This should follow from the invariant's
   `waitingThreadsPendingMessageNone` or related predicates.
2. If the invariant does not currently guarantee this, extend
   `IPC/Invariant/Defs.lean` with a `blockedOnReplyHasTarget` predicate
   and prove preservation in `EndpointPreservation.lean`.
3. Add a comment at `Transport.lean:1773` cross-referencing the theorem.

**Files:**
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` — documentation annotation
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean` — new predicate (if needed)
- `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` — preservation

**Estimated scope:** ~30 lines new theorem + ~10 lines documentation

### AJ1-C: Pre-Send Receiver Linking Theorem (M-02/MEDIUM)

**Problem:** `endpointCallWithDonation` (Donation.lean:207-209) and
`endpointSendDualWithCaps` (WithCaps.lean:85-86) determine the receiver by
inspecting the endpoint BEFORE calling `endpointCall`/`endpointSendDual`. After
the call succeeds, donation is applied to this pre-inspected receiver. No
machine-checked proof links the pre-inspected receiver to the one actually
dequeued.

**Fix:**
1. Add theorem `endpointCall_dequeues_head`: prove that when `endpointCall`
   succeeds with a receiver endpoint, the dequeued thread is `receiveQ.head` of
   the pre-call state. This should follow from the implementation of
   `endpointSendDual`/`endpointCall` which explicitly pops `receiveQ.head`.
2. Cross-reference this theorem in `Donation.lean` and `WithCaps.lean` at the
   pre-send receiver identification sites.

**Files:**
- `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` — theorem definition
- `SeLe4n/Kernel/IPC/Operations/Donation.lean` — cross-reference annotation
- `SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean` — cross-reference annotation

**Estimated scope:** ~25 lines new theorem + ~6 lines annotations


### AJ1-D: Reply/ReplyRecv Structural Equivalence Theorem (M-01/MEDIUM)

**Problem:** The unchecked `.reply` path (API.lean:672-679) delegates to
`endpointReplyWithDonation` which handles donation return and PIP revert
internally. The checked `.reply` path (API.lean:882-897) calls
`endpointReplyChecked`, then `applyReplyDonation`, then
`revertPriorityInheritance` as separate steps. The existing structural
equivalence theorems (API.lean:1077-1200) cover 14 capability-only arms but
NOT `.reply` or `.replyRecv`. This asymmetry is unverified.

**Fix:**
1. Add theorem `dispatchReply_equivalence`: prove that the checked `.reply`
   path produces the same post-state as the unchecked path (modulo NI policy
   enforcement). This may require decomposing `endpointReplyWithDonation` into
   its constituent steps and showing equivalence.
2. Add theorem `dispatchReplyRecv_equivalence` for the `.replyRecv` arm.
3. If full equivalence is not feasible (checked path adds NI enforcement
   that changes observable behavior), document the precise semantic
   difference with a rationale annotation.

**Files:**
- `SeLe4n/Kernel/API.lean` — 2 new theorems (or 2 documented rationale blocks)
- `SeLe4n/Kernel/IPC/Operations/Donation.lean` — helper lemmas if needed

**Estimated scope:** ~60 lines (theorems or documentation)

### AJ1-E: Remove Dead `endpointQueuePopHeadFresh` (L-02/LOW)

**Problem:** `endpointQueuePopHeadFresh` in `IPC/DualQueue/Core.lean:292` is
defined but never called from any production or test path. It was added as a
"convenience wrapper" (AD2-A) but never adopted by callers.

**Fix:**
1. Remove `endpointQueuePopHeadFresh` from `Core.lean`.
2. Remove its re-export from `DualQueue.lean:18` if present.
3. Remove any references in `codebase_map.json` and documentation.
4. Verify no downstream breakage with `lake build`.

**Files:**
- `SeLe4n/Kernel/IPC/DualQueue/Core.lean` — delete function
- `SeLe4n/Kernel/IPC/DualQueue.lean` — remove re-export
- `docs/codebase_map.json` — update if referenced

**Estimated scope:** ~15 lines removed

### AJ1-F: Normalize `endpointReceiveDualWithCaps` Error Handling (L-18/LOW)

**Problem:** In `IPC/DualQueue/WithCaps.lean:139`, the receive path returns
`.error .invalidCapability` when the sender's CSpace root is missing. The send
path (line 107) silently returns `.ok ({ results := #[] }, st')` for the same
condition. This asymmetry could mask bugs on the send path.

**Fix:**
1. Align error handling: make the send path also return `.error
   .invalidCapability` when `lookupCspaceRoot` fails for the receiver, OR
   document the asymmetry with a rationale explaining why silent fallback is
   correct for sends (e.g., "sender can still send message content without
   capabilities; missing receiver CSpace is an infrastructure error").
2. If aligning to error: update callers and preservation theorems.
3. If documenting: add annotation explaining the asymmetry.

**Recommended approach:** Document with rationale annotation. The send-side
silent fallback is arguably correct — a send operation delivers the message
even if capability transfer fails (capabilities are optional extras). The
receive-side error is also correct — a receiver that cannot accept capabilities
due to missing CSpace root is in an inconsistent state.

**Files:**
- `SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean` — rationale annotation

**Estimated scope:** ~8 lines documentation


---

## 5. Phase AJ2: Security & Information Flow Hardening

**Priority:** High — addresses access control and information leakage gaps
**Findings:** M-10, M-11, M-12, M-09
**Files modified:** `Model/Object/Types.lean`, `InformationFlow/Projection.lean`,
`InformationFlow/Policy.lean`, `Prelude.lean`, `Model/State.lean`,
invariant/preservation files
**Gate:** `lake build` + `test_smoke.sh` + zero sorry/axiom

### AJ2-A: Make `AccessRightSet.mk` Constructor Private (M-10/MEDIUM)

**Problem:** `AccessRightSet.mk` (Types.lean:96) is public. Code can construct
`AccessRightSet.mk 999` with invalid high bits beyond the 5-bit range (read,
write, grant, grantReply, revoke). While membership queries only test bits 0-4,
the `union` operation propagates invalid bits. `CapDerivationTree.mk` is
already private, showing the pattern exists in the codebase.

**Fix:**
1. Add `private` to the `AccessRightSet` structure's `mk` constructor:
   `structure AccessRightSet where private mk :: bits : Nat`.
2. Add smart constructors: `AccessRightSet.ofBits (n : Nat) : AccessRightSet :=
   ⟨n &&& 0x1F⟩` (masks to 5 bits).
3. Update all call sites that currently use `AccessRightSet.mk` directly.
   Search for `.mk` and `⟨...⟩` constructor syntax on `AccessRightSet`.
4. Update test suites that construct `AccessRightSet` values.

**Files:**
- `SeLe4n/Model/Object/Types.lean` — private constructor + smart constructor
- All files constructing `AccessRightSet` directly (search required)
- Test suites using `AccessRightSet.mk`

**Estimated scope:** ~15 lines changed in Types.lean + call site updates

### AJ2-B: Strip `pipBoost` from NI Projection (M-11/MEDIUM)

**Problem:** `projectKernelObject` (Projection.lean:216-218) strips
`registerContext` and `schedContextBinding` from TCBs but does NOT strip
`pipBoost`. A cross-domain PIP boost reflects which thread holds a Reply on
behalf of a higher-priority client, potentially leaking timing information
about blocking relationships across security domains.

**Fix:**
1. Add `pipBoost := none` to the TCB projection in `projectKernelObject`:
   `.tcb { tcb with registerContext := default, schedContextBinding := .unbound,
   pipBoost := none }`.
2. Update `projectKernelObject_strips_register_context` and any related
   projection lemmas to account for the additional field stripping.
3. Update NI preservation theorems that depend on projection equality —
   the `pipBoost` field must now be shown irrelevant to projection in
   `InformationFlow/Invariant/Operations.lean`.
4. Verify all NI proofs still compile by building `SeLe4n.Kernel.InformationFlow`.

**Files:**
- `SeLe4n/Kernel/InformationFlow/Projection.lean` — add `pipBoost := none`
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` — proof updates
- `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean` — helper updates

**Risk:** This change affects all 35 NI operation proofs. Each proof that
currently reasons about TCB projection must be verified to not depend on
`pipBoost` visibility. If any proof breaks, it indicates a genuine NI gap
that the audit correctly identified.

**Estimated scope:** ~5 lines in Projection.lean + ~50-100 lines proof updates

### AJ2-C: Strengthen `isInsecureDefaultContext` (M-12/MEDIUM)

**Problem:** `isInsecureDefaultContext` (Policy.lean:273-277) only checks
sentinel entity ID 0 across four entity classes. A labeling context assigning
non-public labels to ID 0 but `publicLabel` to all other entities passes this
check while being functionally insecure.

**Fix:**
1. Extend the sentinel check to sample additional entity IDs. Add checks for
   IDs 1, 2, and 3 in each class — if ANY sampled entity has `publicLabel`,
   flag the context as insecure. This catches contexts that are "mostly public"
   while keeping the O(1) nature (fixed number of probes).
2. Add documentation clearly stating the check is a heuristic sentinel, not a
   comprehensive security validation. The `LabelingContextValid` deployment
   requirement (enforced at boot) is the real security gate; this is a
   defense-in-depth runtime check.
3. Add `isInsecureDefaultContext_soundness` documentation noting the false-
   negative rate and the design rationale for O(1) checking.

**Alternative considered:** Full iteration over all entities would provide
complete coverage but would change the O(1) guarantee to O(n) and
potentially impact syscall entry latency. The sentinel approach is the right
tradeoff for a runtime guard that supplements the boot-time validation.

**Files:**
- `SeLe4n/Kernel/InformationFlow/Policy.lean` — extend sentinel probes
- `SeLe4n/Kernel/API.lean` — no change (already calls `isInsecureDefaultContext`)
- Test sites — update `testLabelingContext` expected results if needed

**Estimated scope:** ~20 lines changed + ~10 lines documentation

### AJ2-D: ThreadId/SchedContextId Namespace Disjointness Invariant (M-09/MEDIUM)

**Problem:** Both `ThreadId.toObjId` and `SchedContextId.toObjId` (Prelude.lean)
perform identity mappings to the same `ObjId` namespace. A `ThreadId(5)` and
`SchedContextId(5)` map to the same `ObjId(5)`. No invariant guarantees
disjoint ID ranges. The allocator prevents collision in practice, but the
formal model lacks this guarantee.

**Fix:**
1. Add a `typedIdDisjointness` predicate to `Model/State.lean` or
   `CrossSubsystem.lean` that asserts: for every `ObjId` in the object store,
   if the stored object is a `.tcb`, then no `.schedContext` object exists at
   the same `ObjId`, and vice versa. Formally:
   `∀ oid, st.objects[oid]? = some (.tcb _) → st.objects[oid]? ≠ some (.schedContext _)`
   (This is trivially true since the object store maps each `ObjId` to exactly
   one `KernelObject` variant — it's a consequence of `RHTable` being a
   function. The real concern is about two typed IDs with the same `Nat` value
   both being "valid" — i.e., both having objects in the store.)
2. The actual invariant needed is: `storeObject` for a `.tcb` at `oid` is
   never called when `oid` already has a `.schedContext`, and vice versa.
   This is enforced by `retypeFromUntyped` which allocates fresh ObjIds via
   `allocateId`. Add theorem `allocateId_produces_fresh`: prove that
   `allocateId` returns an `ObjId` not currently in the object store.
3. Add a documentation annotation at the `toObjId` definitions in `Prelude.lean`
   cross-referencing this invariant.

**Files:**
- `SeLe4n/Prelude.lean` — documentation annotations
- `SeLe4n/Model/State.lean` or `SeLe4n/Kernel/CrossSubsystem.lean` — invariant
- `SeLe4n/Kernel/Lifecycle/Operations.lean` — `allocateId_produces_fresh`

**Estimated scope:** ~30 lines new invariant/theorem + ~10 lines annotations


---

## 6. Phase AJ3: Platform & Boot Pipeline

**Priority:** High — fixes boot safety and device-tree parsing correctness
**Findings:** M-17, M-18, M-16, M-19, L-04, L-12
**Files modified:** `Platform/DeviceTree.lean`, `Platform/Boot.lean`,
`Architecture/Assumptions.lean`, `Machine.lean`, platform contracts
**Gate:** `lake build` + `test_smoke.sh` + zero sorry/axiom

### AJ3-A: Propagate `fromDtbFull` Fuel Exhaustion Error (M-17/MEDIUM)

**Problem:** `fromDtbFull` (DeviceTree.lean:870-873) catches `parseFdtNodes`
fuel exhaustion (`.error .fuelExhausted`) but falls back to `nodes := []` and
returns `some dt` (success). Callers cannot distinguish "no devices" from
"parse failed." On a real DTB with many nodes, the kernel boots with empty
peripheral data (zero GIC addresses, zero timer frequency).

**Fix:**
1. Change `fromDtbFull` return type from `Option DeviceTree` to
   `Except DeviceTreeParseError DeviceTree`.
2. On `parseFdtNodes` returning `.error e`, propagate: `return .error e`.
3. On `parseFdtNodes` returning `.ok nodes`, continue to build the DeviceTree
   and return `.ok dt`.
4. Update all callers of `fromDtbFull`:
   - `Platform/Boot.lean` (`bootFromPlatform` or `bootFromPlatformChecked`)
   - Any test suite calling `fromDtbFull`
5. Update preservation lemmas if any reference `fromDtbFull` output.

**Files:**
- `SeLe4n/Platform/DeviceTree.lean` — return type change + error propagation
- `SeLe4n/Platform/Boot.lean` — caller update
- Test suites — caller updates

**Estimated scope:** ~15 lines changed + ~10 lines caller updates

### AJ3-B: Fix DTB PA Width Default (M-18/MEDIUM)

**Problem:** Both `fromDtbWithRegions` (DeviceTree.lean:390) and `fromDtbFull`
(DeviceTree.lean:849) default `physicalAddressWidth` to 48 bits. RPi5 BCM2712
has 44-bit PA width (Board.lean:122). If callers rely on the default, address
validation bounds are too permissive.

**Fix:**
1. Remove the default value from `physicalAddressWidth` parameter in both
   functions, making it a required parameter. This forces callers to explicitly
   specify the PA width for their platform.
2. Alternatively, change the default to match the most restrictive common
   target: `physicalAddressWidth : Nat := 44` (RPi5). This is safer — overly
   restrictive is better than overly permissive for address validation.
3. Update all callers to pass explicit PA width values:
   - Sim platform: pass 52
   - RPi5 platform: pass 44
   - Test suites: pass appropriate values

**Recommended approach:** Make the parameter required (no default). This
prevents silent misconfiguration on new platforms.

**Files:**
- `SeLe4n/Platform/DeviceTree.lean` — remove default value
- `SeLe4n/Platform/Boot.lean` — pass explicit PA width
- `SeLe4n/Platform/Sim/*.lean` — pass 52
- `SeLe4n/Platform/RPi5/*.lean` — pass 44
- Test suites — pass explicit values

**Estimated scope:** ~10 lines changed + ~8 call site updates

### AJ3-C: Wire `bootSafe` Validation into `bootFromPlatformChecked` (M-16/MEDIUM)

**Problem:** `bootToRuntime_invariantBridge_empty` (Boot.lean:497) proves the
full 10-component `proofLayerInvariantBundle` only for empty `PlatformConfig`.
For non-empty configs, the general bridge requires `config.bootSafe`. But
`bootFromPlatformChecked` validates `wellFormed` without checking `bootSafe`.
A malformed config could produce a state violating kernel invariants.

**Fix:**
1. Add `bootSafe` as a required field of `PlatformConfig` or as an additional
   validation predicate in `bootFromPlatformChecked`.
2. If `bootSafe` is a `Prop` (proof obligation), require callers to supply
   evidence: `bootFromPlatformChecked (config : PlatformConfig)
   (hSafe : config.bootSafe) : ...`.
3. If this is too restrictive for the simulation path (where `bootSafe` may
   be trivially true), add a `bootSafe := True` default that simulation
   overrides explicitly, and document the obligation.
4. Update `bootFromPlatformChecked` to check/require `bootSafe`.

**Files:**
- `SeLe4n/Platform/Boot.lean` — add bootSafe requirement
- Sim/RPi5 contract files — supply bootSafe evidence

**Estimated scope:** ~20 lines changed

### AJ3-D: BootBoundaryContract Substantive Defaults (M-19/MEDIUM)

**Problem:** `BootBoundaryContract` (Assumptions.lean:31-33) has
`objectStoreNonEmpty` and `irqRangeValid` defaulting to `True`. Neither Sim
nor RPi5 boot contracts override these, so they are vacuously satisfied.
The kernel could boot with zero objects (no idle thread).

**Fix:**
1. Replace `objectStoreNonEmpty : Prop := True` with a substantive default
   predicate. For example: `objectStoreNonEmpty (st : SystemState) : Prop :=
   st.objects.size > 0` (at minimum, the idle thread must exist).
2. Replace `irqRangeValid (irqCount : Nat) : Prop := True` with
   `irqRangeValid (irqCount : Nat) : Prop := irqCount ≤ maxIrqId` where
   `maxIrqId` is platform-specific.
3. Update Sim boot contract to prove the substantive predicates (should be
   trivial for simulation with its default object store).
4. Update RPi5 boot contract similarly.

**Files:**
- `SeLe4n/Kernel/Architecture/Assumptions.lean` — substantive defaults
- `SeLe4n/Platform/Sim/BootContract.lean` — prove new predicates
- `SeLe4n/Platform/RPi5/BootContract.lean` — prove new predicates

**Estimated scope:** ~25 lines changed + ~15 lines proofs

### AJ3-E: Fix `MachineState.interruptsEnabled` Default (L-04/LOW)

**Problem:** `MachineState.interruptsEnabled` (Machine.lean:404) defaults to
`true`. ARM64 boots with interrupts disabled (PSTATE.I = 1). The abstract
model's default contradicts hardware reality.

**Fix:**
1. Change default from `true` to `false`: `interruptsEnabled : Bool := false`.
2. Update `bootFromPlatform` or the boot sequence to explicitly enable
   interrupts at the appropriate point (after GIC initialization).
3. Grep for any code that relies on the default being `true` and update
   accordingly. Check test state builders.
4. Update preservation theorems that assume initial `interruptsEnabled = true`.

**Files:**
- `SeLe4n/Machine.lean` — default change
- `SeLe4n/Platform/Boot.lean` — explicit enable after GIC init
- Test suites and state builders — update if relying on default

**Estimated scope:** ~5 lines changed + ~10 lines caller updates

### AJ3-F: Remove `fromDtb` Dead Stub (L-12/LOW)

**Problem:** `DeviceTree.fromDtb` (DeviceTree.lean:152-153) unconditionally
returns `none`. The real implementation is `fromDtbFull`. The stub creates
API surface confusion with `fromDtbParsed` alias.

**Fix:**
1. Remove `fromDtb` function definition.
2. Remove `fromDtbParsed` alias if it exists.
3. Search for any callers (should be none — verified dead code).
4. Update `codebase_map.json` if referenced.

**Files:**
- `SeLe4n/Platform/DeviceTree.lean` — remove stub + alias
- `docs/codebase_map.json` — update

**Estimated scope:** ~10 lines removed


---

## 7. Phase AJ4: Architecture Model Correctness

**Priority:** Medium — fixes proof quality and validation gaps
**Findings:** M-07, M-06, L-06, L-09
**Files modified:** `Architecture/PageTable.lean`, `Architecture/VSpace.lean`,
`Architecture/TlbModel.lean`, `Architecture/IpcBufferValidation.lean`,
`Lifecycle/Operations.lean`
**Gate:** `lake build` + `test_smoke.sh` + zero sorry/axiom
**Note:** These files are partially in orphaned modules (H-01). Build
verification must target specific modules: `lake build SeLe4n.Kernel.Architecture.PageTable` etc.

### AJ4-A: Replace Tautological `pageTableWalk_deterministic` (M-07/MEDIUM)

**Problem:** `pageTableWalk_deterministic` (PageTable.lean:424-427) proves
`∃ result, f x = result ∧ ∀ result', f x = result' → result' = result`,
which is trivially true for ANY Lean pure function by `rfl`. The theorem proves
nothing specific about page table walks. Its docstring claims determinism, but
all pure Lean functions are deterministic by construction.

**Fix:**
1. Delete the tautological theorem `pageTableWalk_deterministic`.
2. Replace it with a meaningful theorem about `pageTableWalk`. Options:
   a. `pageTableWalk_level_decreasing`: prove that the recursive walk
      terminates by showing the level decreases at each step (already encoded
      in the structural recursion, but stating it explicitly documents the
      termination argument).
   b. `pageTableWalk_returns_aligned`: prove that a successful walk result
      address is page-aligned (4KB boundary).
   c. `pageTableWalk_valid_descriptor_propagation`: prove that valid
      descriptors at each level produce valid walk results.
3. Choose the replacement based on what provides the most useful assurance
   for the VSpaceARMv8 refinement proofs (M-05, deferred to WS-V).

**Recommended replacement:** `pageTableWalk_returns_aligned` — this provides
genuine functional correctness assurance and is useful for downstream proofs.

**Files:**
- `SeLe4n/Kernel/Architecture/PageTable.lean` — delete + replace

**Estimated scope:** ~15 lines (delete tautology + add meaningful theorem)

### AJ4-B: Wire Targeted TLB Flush into VSpace Operations (M-06/MEDIUM)

**Problem:** Both `vspaceMapPageWithFlush` and `vspaceUnmapPageWithFlush`
(VSpace.lean:174-194) flush the ENTIRE TLB via `adapterFlushTlb` after every
map/unmap operation. On RPi5 with multiple address spaces, this invalidates
all TLB entries across all ASIDs. Targeted `tlbFlushByASID` and
`tlbFlushByPage` functions exist with proofs in TlbModel.lean but are not
wired into the production VSpace operations.

**Fix:**
1. Change `vspaceMapPageWithFlush` to use `adapterFlushTlbByPage vaddr`
   instead of `adapterFlushTlb st'.tlb`. After a single page mapping,
   only that page's TLB entry needs invalidation.
2. Change `vspaceUnmapPageWithFlush` similarly.
3. Update the `TlbState` manipulation to use `tlbFlushByPage` from
   `TlbModel.lean` instead of `tlbFlushAll`.
4. Verify that `tlbFlushByPage` preserves `tlbConsistent` (should be proven
   in TlbModel.lean already via `tlbFlushByPage_preserves_consistency` or
   equivalent).
5. Update VSpace invariant proofs that depend on the full-flush semantics.

**Files:**
- `SeLe4n/Kernel/Architecture/VSpace.lean` — use targeted flush
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean` — proof updates
- `SeLe4n/Kernel/Architecture/TlbModel.lean` — verify bridge lemmas exist

**Estimated scope:** ~20 lines changed + ~15 lines proof updates

### AJ4-C: Add Physical Address Bounds to IPC Buffer Validation (L-06/LOW)

**Problem:** `IpcBufferValidation.lean:55-76` validates alignment, canonicity,
mapping existence, and write permission, but does not check that the mapped
physical address falls within `physicalAddressBound`. A mapped VA could
theoretically reference a PA outside the valid physical memory range.

**Fix:**
1. After the successful `root.lookup vaddr` call, add a check:
   `mappedPA.toNat < st.machine.physicalAddressBound`.
2. Return `.error .invalidArgument` if the PA is out of bounds.
3. Add preservation lemma `setIPCBufferOp_physicalAddress_bounded`:
   prove that after `setIPCBufferOp` succeeds, the IPC buffer's physical
   address is within bounds.

**Note:** This requires `VSpaceRoot.lookup` to return the physical address,
not just a boolean "mapped" result. Check the current `lookup` signature.
If `lookup` returns `Option PAddr`, this is straightforward. If it returns
`Bool`, the PA check must be deferred to a separate validation step.

**Files:**
- `SeLe4n/Kernel/Architecture/IpcBufferValidation.lean` — PA bounds check
- Possibly `SeLe4n/Kernel/Architecture/VSpace.lean` — if lookup signature changes

**Estimated scope:** ~15 lines changed

### AJ4-D: Guard TCB Placeholder IDs with Sentinel Values (L-09/LOW)

**Problem:** `objectOfTypeTag` (Lifecycle/Operations.lean:1270-1299) creates
TCBs with `tid := ThreadId.ofNat 0`, `cspaceRoot := ObjId.ofNat 0`,
`vspaceRoot := ObjId.ofNat 0`. These alias real objects at ID 0 if the TCB
is used before proper configuration.

**Fix:**
1. Use a dedicated sentinel value that cannot collide with real objects.
   Define `ThreadId.invalid : ThreadId := ThreadId.ofNat maxObjects` (or
   `Nat.maxVal` / a clearly out-of-range value) in `Prelude.lean`.
2. Similarly define `ObjId.invalid : ObjId := ObjId.ofNat maxObjects`.
3. Use these sentinels in `objectOfTypeTag`:
   `tid := ThreadId.invalid, cspaceRoot := ObjId.invalid, vspaceRoot :=
   ObjId.invalid`.
4. Add a guard in `threadConfigureOp` (or wherever TCBs are first used)
   that rejects threads with sentinel IDs, requiring explicit configuration.
5. Update test suites that create TCBs via `objectOfTypeTag`.

**Files:**
- `SeLe4n/Prelude.lean` — sentinel definitions
- `SeLe4n/Kernel/Lifecycle/Operations.lean` — use sentinels
- Test suites — update TCB creation

**Estimated scope:** ~15 lines new definitions + ~10 lines call site updates


---

## 8. Phase AJ5: Rust HAL Hardening

**Priority:** Medium — fixes runtime safety issues in hardware abstraction
**Findings:** M-20, M-21, L-14, L-15
**Files modified:** `rust/sele4n-hal/src/mmio.rs`, `rust/sele4n-hal/src/uart.rs`,
`rust/sele4n-hal/src/timer.rs`
**Gate:** `cargo test --workspace` + `cargo clippy --workspace` (0 warnings)

### AJ5-A: Promote MMIO Alignment to Runtime `assert!` (M-20/MEDIUM)

**Problem:** All four MMIO functions in `mmio.rs` (lines 41, 63, 83, 103) use
`debug_assert!` for alignment checks. In release builds, these are stripped.
Unaligned Device memory accesses on ARM64 cause a synchronous Data Abort
fault with no prior warning.

**Fix:**
1. Replace all four `debug_assert!` with `assert!`:
   - `mmio_read32` (line 41): `assert!(addr % 4 == 0, ...)`
   - `mmio_write32` (line 63): `assert!(addr % 4 == 0, ...)`
   - `mmio_read64` (line 83): `assert!(addr % 8 == 0, ...)`
   - `mmio_write64` (line 104): `assert!(addr % 8 == 0, ...)`
2. The runtime cost is negligible (single modulo check per MMIO operation)
   compared to the volatile memory access that follows.
3. Verify `cargo test --workspace` passes with the new assertions.

**Alternative considered:** Return `Result<u32, MmioError>` instead of
panicking. Rejected because: (a) MMIO functions are used in contexts where
error propagation is impractical (interrupt handlers, boot), and (b) a
misaligned MMIO access is a programming bug, not a runtime condition —
panic-on-invariant-violation is the correct Rust idiom.

**Files:**
- `rust/sele4n-hal/src/mmio.rs` — 4 line changes

**Estimated scope:** 4 lines changed

### AJ5-B: Migrate `static mut BOOT_UART_INNER` (M-21/MEDIUM)

**Problem:** `uart.rs:181` uses `static mut BOOT_UART_INNER`. While the
`UartLock` spinlock (AI1-D) provides practical safety, `static mut` is being
deprecated in future Rust editions and is technically unsound under Rust's
aliasing rules.

**Fix:**
1. Replace `static mut BOOT_UART_INNER: Uart = Uart::new(UART0_BASE)` with
   a safe pattern using `UnsafeCell` wrapped in a `Sync` newtype:
   ```rust
   struct UartInner(UnsafeCell<Uart>);
   unsafe impl Sync for UartInner {}
   static BOOT_UART_INNER: UartInner = UartInner(UnsafeCell::new(Uart::new(UART0_BASE)));
   ```
2. Update `with_boot_uart()` to access via `BOOT_UART_INNER.0.get()`
   instead of `core::ptr::addr_of_mut!(BOOT_UART_INNER)`.
3. Remove the `#[allow(static_mut_refs)]` if present.
4. Keep the `UART_LOCK` spinlock mechanism unchanged — it provides the
   actual mutual exclusion guarantee.

**Files:**
- `rust/sele4n-hal/src/uart.rs` — ~15 lines changed

**Estimated scope:** ~15 lines changed

### AJ5-C: Replace `init_timer(0)` Panic with Result (L-14/LOW)

**Problem:** `init_timer(0)` (timer.rs:129) panics via `assert!(tick_hz > 0)`
instead of returning a recoverable error. A kernel function should not panic
on invalid input.

**Fix:**
1. Change `init_timer` return type from `()` to `Result<(), TimerError>`.
2. Define `enum TimerError { ZeroTickHz }` (or use an existing error type).
3. Replace `assert!(tick_hz > 0, ...)` with:
   `if tick_hz == 0 { return Err(TimerError::ZeroTickHz); }`.
4. Update callers to handle the error (boot sequence should propagate or
   use a reasonable default).
5. Update tests.

**Files:**
- `rust/sele4n-hal/src/timer.rs` — return type change + error handling
- `rust/sele4n-hal/src/ffi.rs` — caller update (if applicable)
- Boot sequence callers

**Estimated scope:** ~15 lines changed

### AJ5-D: Restrict `increment_tick_count` Visibility (L-15/LOW)

**Problem:** `increment_tick_count` (timer.rs:179) is `pub` but only called
from `ffi.rs` within the same crate. External crates could call it, causing
double-counting of timer ticks.

**Fix:**
1. Change `pub fn increment_tick_count()` to `pub(crate) fn increment_tick_count()`.
2. Verify no external crate calls this function (should be crate-internal only).
3. Run `cargo test --workspace` to confirm no breakage.

**Files:**
- `rust/sele4n-hal/src/timer.rs` — 1 line change

**Estimated scope:** 1 line changed


---

## 9. Phase AJ6: Documentation, Testing & Closure

**Priority:** Standard — documentation sync, errata, and gate
**Findings:** H-01–H-03 (roadmaps), M-03/05/08/13/15 (by-design docs),
L-01/03/05/07/08/10/11/13/16/17/19 (by-design/erroneous docs), audit errata
**Files modified:** Documentation files, `CHANGELOG.md`, `CLAUDE.md`,
version-bearing files, audit file
**Gate:** `test_full.sh` + `cargo test --workspace` + `check_version_sync.sh`
+ zero sorry/axiom

### AJ6-A: HIGH Finding Activation Roadmaps (H-01, H-02, H-03)

Document clear activation plans for the three HIGH findings in a new section
of `SELE4N_SPEC.md` or in `DEVELOPMENT.md`:

**H-01 — Architecture Module Integration Roadmap:**
1. Create `SeLe4n/Kernel/Architecture/HardwareIntegration.lean` hub module
   that imports all 7 orphaned modules.
2. Wire `ExceptionModel.dispatchException` into the syscall entry path
   (requires breaking the ExceptionModel→API.lean→ExceptionModel import
   cycle via an interface abstraction).
3. Connect `VSpaceARMv8` as RPi5-specific `VSpaceBackend` instance via
   conditional platform selection.
4. Import `AsidManager` into VSpace subsystem for ASID allocation.
5. Import `TimerModel` into scheduler timer tick path.
6. Import `CacheModel` into Architecture invariant bundle.
7. Add test suites for all 7 modules (ArchitectureHardwareSuite).
8. **Dependency:** Requires resolving import cycle between ExceptionModel
   and API.lean before integration is possible.

**H-02 — Budget-Aware Scheduler Activation Plan:**
1. Update `API.lean` checked wrappers: `scheduleChecked` calls
   `scheduleEffective`, `handleYieldChecked` calls `handleYieldWithBudget`,
   `timerTickChecked` calls `timerTickWithBudget`.
2. Add preservation theorems for all three budget-aware operations in
   `Preservation.lean`.
3. Update NI proofs for the new operation semantics.
4. Add `SchedulerBudgetSuite.lean` test suite exercising CBS enforcement,
   budget consumption, replenishment queue, and timeout-on-budget-expiry.
5. **Dependency:** Preservation proofs must be complete before activation.

**H-03 — FFI Bridge Wiring Plan:**
1. Import `FFI.lean` from hardware-specific Architecture modules (or create
   a `Platform/HardwareBindings.lean` that selectively imports FFI).
2. Create `#if HARDWARE_BUILD` conditional or typeclass-based dispatch that
   selects FFI-backed implementations vs pure-function models.
3. Verify all 17 FFI function signatures still match `sele4n-hal/src/ffi.rs`.
4. **Dependency:** Requires H-01 (orphaned modules integrated first).

**Files:**
- `docs/spec/SELE4N_SPEC.md` — new §8.15 Hardware Integration Roadmap
- `docs/DEVELOPMENT.md` — activation plan summary

**Estimated scope:** ~80 lines documentation

### AJ6-B: By-Design Finding Documentation (10 findings)

Add brief documentation annotations (1-3 lines each) at the relevant code
locations for findings that are confirmed valid but represent intentional
design decisions. Each annotation should include the audit finding ID and
a one-sentence rationale:

| Finding | Location | Annotation |
|---------|----------|------------|
| M-03 | `IPC/DualQueue/Core.lean:491` | Already has AF5-C annotation — verify sufficient |
| M-05 | `Architecture/VSpaceARMv8.lean:357` | Already has deferral note — add AJ-M05 tag |
| M-08 | `Architecture/ExceptionModel.lean:1` | Add H-01 cross-reference header |
| M-13 | `InformationFlow/Invariant/Composition.lean:984` | Already documented — verify |
| M-15 | `Capability/Operations.lean:85` | Already has U-M25 — verify sufficient |
| L-03 | `Model/Object/Types.lean:671` | Add seL4 semantics rationale |
| L-05 | `Model/State.lean:234` | Already documented — verify sufficient |
| L-11 | `Platform/Sim/Contract.lean:47` | Add PA width divergence note |
| L-13 | `Platform/DeviceTree.lean:342` | Already documented — verify |
| L-19 | `Capability/Invariant/Preservation.lean:15` | Already documented — verify |

**Estimated scope:** ~20 lines annotations (most already have documentation)

### AJ6-C: Erroneous Finding Documentation and Audit Errata

1. Add errata section to `AUDIT_v0.28.0_COMPREHENSIVE.md` noting:
   - L-01 is FALSE (proofs exist in Selection.lean:459 and Preservation.lean:3435)
   - L-17 is FALSE (already fixed in Operations.lean:326-329)
   - Executive summary counts: 55→52 total, 24M→21M
2. Cross-reference the errata in the workstream plan (this document).

**Files:**
- `docs/audits/AUDIT_v0.28.0_COMPREHENSIVE.md` — errata appendix

**Estimated scope:** ~15 lines

### AJ6-D: Deferred Finding Documentation (4 findings)

Add TPI-DOC or deferral annotations for findings whose resolution requires
infrastructure not yet available:

| Finding | Deferral Target | Annotation Location |
|---------|----------------|-------------------|
| L-07 | WS-V (hardware binding) | `TlbModel.lean:357` |
| L-08 | WS-V (formal proof) | `CrossSubsystem.lean:136` |
| L-10 | WS-V (performance) | `Capability/Operations.lean:877` |
| L-16 | No action (harmless) | `RadixTree/Core.lean:32` |

**Estimated scope:** ~12 lines annotations


### AJ6-E: Test Fixture Verification and Documentation Sync

1. Verify `tests/fixtures/main_trace_smoke.expected` matches `lake exe sele4n`
   output after all code changes from AJ1–AJ5.
2. If fixture changes are needed, update with rationale.
3. Synchronize documentation:
   - `README.md` — metrics sync from `docs/codebase_map.json`
   - `docs/spec/SELE4N_SPEC.md` — new sections for H-01/H-02/H-03 roadmaps
   - `docs/DEVELOPMENT.md` — workstream status
   - `docs/CLAIM_EVIDENCE_INDEX.md` — if claims changed
   - `docs/WORKSTREAM_HISTORY.md` — WS-AJ entry
   - `docs/gitbook/12-proof-and-invariant-map.md` — if invariants changed
   - Regenerate `docs/codebase_map.json` if Lean sources changed
4. Update `CLAUDE.md` active workstream context with WS-AJ summary.

**Files:** All documentation files listed above

**Estimated scope:** ~60 lines documentation updates

### AJ6-F: Version Bump and Final Gate

1. Bump version 0.28.0 → 0.29.0 across all 15+ version-bearing files.
2. Run `scripts/check_version_sync.sh` to verify consistency.
3. Update `CHANGELOG.md` with WS-AJ phase summaries.
4. Run final gate:
   - `source ~/.elan/env && lake build` (full build)
   - `./scripts/test_full.sh` (Tier 0-3)
   - `cargo test --workspace` (Rust tests)
   - `cargo clippy --workspace` (0 warnings)
   - `./scripts/check_version_sync.sh` (version sync)
   - Verify zero sorry/axiom: `grep -r "sorry" SeLe4n/ --include="*.lean"`
5. If any gate step fails, fix and re-run.

**Files:** All version-bearing files (see `check_version_sync.sh` for list)

**Estimated scope:** ~30 lines version bumps + ~20 lines CHANGELOG


---

## 10. Dependency Graph and Execution Order

### 10.1 Inter-Phase Dependencies

```
AJ1 (IPC)  ──────────────────────────┐
AJ2 (Security) ──────────────────────┤
AJ3 (Platform) ──────────────────────┼──→ AJ6 (Documentation & Closure)
AJ4 (Architecture) ──────────────────┤
AJ5 (Rust HAL) ──────────────────────┘
```

Phases AJ1 through AJ5 are **mutually independent** — they modify disjoint
file sets and can be executed in any order or in parallel. Phase AJ6 depends
on ALL prior phases completing (documentation sync, fixture verification,
and final gate require all code changes to be in place).

### 10.2 Intra-Phase Dependencies

**AJ1:** Sub-tasks are independent. Recommended order: AJ1-A (most critical),
then AJ1-B, AJ1-C, AJ1-D in any order, then AJ1-E, AJ1-F (cleanup last).

**AJ2:** AJ2-A (AccessRightSet) should be done first — it changes a core type's
constructor visibility, which may affect AJ2-B and AJ2-C if they construct
AccessRightSet values. AJ2-D is independent.

**AJ3:** AJ3-A (fromDtbFull return type) should precede AJ3-B (PA width default)
since both modify `DeviceTree.lean` and AJ3-A changes the function signature
that AJ3-B's callers use. AJ3-C, AJ3-D, AJ3-E, AJ3-F are independent of each
other and of AJ3-A/B.

**AJ4:** AJ4-A and AJ4-B both modify Architecture files but are independent.
AJ4-C and AJ4-D modify different subsystems and are independent.

**AJ5:** All sub-tasks are independent (different Rust files).

### 10.3 Recommended Execution Sequence

For a single-agent serial execution:

```
AJ1-A → AJ1-B → AJ1-C → AJ1-D → AJ1-E → AJ1-F   (IPC correctness)
AJ5-A → AJ5-B → AJ5-C → AJ5-D                      (Rust HAL, fast wins)
AJ2-A → AJ2-B → AJ2-C → AJ2-D                      (Security hardening)
AJ3-A → AJ3-B → AJ3-C → AJ3-D → AJ3-E → AJ3-F    (Platform/boot)
AJ4-A → AJ4-B → AJ4-C → AJ4-D                      (Architecture)
AJ6-A → AJ6-B → AJ6-C → AJ6-D → AJ6-E → AJ6-F    (Closure)
```

Rationale: IPC correctness first (highest impact), then Rust HAL (fast, low
risk), then security hardening, platform, architecture, and documentation last.

For parallel execution with 3 agents:

```
Agent 1: AJ1 (IPC) → AJ3 (Platform) → AJ6-A/B/C/D
Agent 2: AJ2 (Security) → AJ4 (Architecture) → AJ6-E
Agent 3: AJ5 (Rust HAL) → AJ6-F (final gate)
```

---

## 11. Risk Assessment

### 11.1 High-Risk Sub-Tasks

| Sub-Task | Risk | Mitigation |
|----------|------|------------|
| AJ2-B (pipBoost NI) | Touches all 35 NI proofs | Build `SeLe4n.Kernel.InformationFlow` after change; if proofs break, they reveal genuine NI gaps |
| AJ1-A (cleanup error) | Changes return type propagation chain | Follow pattern from AH2-A/B (applyCallDonation Except change) |
| AJ3-A (fromDtbFull) | Changes return type used by boot | Follow pattern from AI4-B (parseFdtNodes Except change) |
| AJ2-A (private mk) | May break many call sites | Search-and-replace with smart constructor |

### 11.2 Low-Risk Sub-Tasks

| Sub-Task | Risk Level | Notes |
|----------|------------|-------|
| AJ1-E (remove dead code) | Very low | No callers to break |
| AJ5-A (debug→assert) | Very low | 4 lines, same semantics in debug builds |
| AJ5-D (pub→pub(crate)) | Very low | 1 line, crate-internal only |
| AJ3-F (remove stub) | Very low | Dead code removal |
| AJ6-* (documentation) | Very low | No code changes |

### 11.3 Proof Fragility Concerns

Several sub-tasks modify types or function signatures that could trigger
cascading proof breakage:

1. **AJ1-A** (cleanupDonatedSchedContext return type): Follow the established
   pattern from WS-AH Phase AH2 where `applyCallDonation` and
   `applyReplyDonation` were converted from `SystemState` to
   `Except KernelError SystemState`. The proof update pattern is well-
   understood.

2. **AJ2-B** (pipBoost in projection): This is the highest-risk change. The
   NI projection function is used by all 35 operation NI proofs. Adding
   `pipBoost := none` to the projection may require updating each proof to
   show that `pipBoost` changes are irrelevant to the security domain being
   projected. If ANY proof cannot be updated, it indicates a genuine
   cross-domain PIP information leak.

3. **AJ2-A** (AccessRightSet private mk): The smart constructor
   `AccessRightSet.ofBits` masks to 5 bits. Existing code that creates
   valid `AccessRightSet` values via `⟨bits⟩` syntax will need to use
   `AccessRightSet.ofBits bits`. This is a mechanical search-and-replace.

---

## 12. Gate Criteria

### 12.1 Per-Phase Gates

| Phase | Gate |
|-------|------|
| AJ1 | `source ~/.elan/env && lake build` + `./scripts/test_smoke.sh` |
| AJ2 | `lake build SeLe4n.Kernel.InformationFlow` + `test_smoke.sh` |
| AJ3 | `lake build SeLe4n.Platform.Boot` + `test_smoke.sh` |
| AJ4 | `lake build SeLe4n.Kernel.Architecture.PageTable` + `lake build SeLe4n.Kernel.Architecture.VSpace` + `test_smoke.sh` |
| AJ5 | `cargo test --workspace` + `cargo clippy --workspace` |
| AJ6 | `test_full.sh` + `cargo test --workspace` + `check_version_sync.sh` |

### 12.2 Final Gate (All Phases Complete)

```bash
# 1. Full Lean build
source ~/.elan/env && lake build

# 2. Full test suite
./scripts/test_full.sh

# 3. Rust tests and linting
cargo test --workspace
cargo clippy --workspace

# 4. Version sync
./scripts/check_version_sync.sh

# 5. Zero sorry/axiom
grep -rn "sorry" SeLe4n/ --include="*.lean" | grep -v "^--" | wc -l  # must be 0
grep -rn "axiom" SeLe4n/ --include="*.lean" | grep -v "^--" | wc -l  # must be 0

# 6. Fixture verification
lake exe sele4n 2>&1 | diff - tests/fixtures/main_trace_smoke.expected
```


---

## 13. Metrics Summary

### 13.1 Scope

| Metric | Value |
|--------|-------|
| Total audit findings | 52 (corrected from 55) |
| Erroneous findings | 2 (L-01, L-17) |
| Partially true findings | 1 (L-06) |
| Actionable code fixes | 24 |
| Documentation-only | 14 |
| Deferred to WS-V | 3 (H-01, H-02, H-03) |
| Phases | 6 |
| Sub-tasks | 30 |
| Estimated Lean lines changed | ~300 |
| Estimated Lean lines added (proofs/theorems) | ~200 |
| Estimated Rust lines changed | ~40 |
| Estimated documentation lines | ~200 |

### 13.2 Finding Severity Distribution After Verification

| Severity | Reported | Verified | Erroneous | Actionable (Code) | Doc-Only/Deferred |
|----------|----------|----------|-----------|-------------------|-------------------|
| HIGH | 3 | 3 | 0 | 0 (deferred to WS-V) | 3 |
| MEDIUM | 21 | 21 | 0 | 16 | 5 |
| LOW | 19 | 17 | 2 | 8 | 9 |
| INFO | 9 | 9 | 0 | 0 | 0 |
| **Total** | **52** | **50** | **2** | **24** | **17** |

---

## 14. Appendix: Workstream Naming Convention

This workstream follows the established naming convention:

- **WS-AJ** — alphabetical successor to WS-AI (v0.27.6 audit remediation)
- **Phase IDs** — AJ1 through AJ6
- **Sub-task IDs** — AJ1-A through AJ6-F
- **Finding cross-references** — each sub-task header includes the original
  audit finding ID (e.g., M-14/MEDIUM) for traceability

## 15. Appendix: Audit Source Cross-Reference

| Audit Section | Workstream Coverage |
|---------------|-------------------|
| §4 HIGH Findings | AJ6-A (roadmaps), deferred to WS-V |
| §5 MEDIUM Findings | AJ1 (M-01/02/04/14), AJ2 (M-09/10/11/12), AJ3 (M-16/17/18/19), AJ4 (M-06/07), AJ5 (M-20/21), AJ6-B (M-03/05/08/13/15) |
| §6 LOW Findings | AJ1 (L-02/18), AJ3 (L-04/12), AJ4 (L-06/09), AJ5 (L-14/15), AJ6-B/C/D (L-01/03/05/07/08/10/11/13/16/17/19) |
| §7 INFO Findings | No action required (positive findings) |
| §8 Cross-Cutting | Covered by aggregate phase work |
| §9 Recommendations | Priority 1→AJ6-A (deferred), Priority 2→AJ1+AJ2, Priority 3→AJ3+AJ4+AJ5, Priority 4→WS-V |

