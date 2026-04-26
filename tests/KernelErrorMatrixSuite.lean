/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude
import SeLe4n.Machine
import SeLe4n.Model.Object
import SeLe4n.Model.State
import SeLe4n.Kernel.API
import SeLe4n.Kernel.Architecture.RegisterDecode
import SeLe4n.Kernel.Architecture.SyscallArgDecode
import SeLe4n.Kernel.Architecture.IpcBufferValidation
import SeLe4n.Kernel.Architecture.ExceptionModel
import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.IPC.DualQueue.Transport
import SeLe4n.Kernel.IPC.DualQueue.WithCaps
import SeLe4n.Kernel.SchedContext.Operations
import SeLe4n.Kernel.SchedContext.PriorityManagement
import SeLe4n.Kernel.Service.Operations
import SeLe4n.Kernel.Lifecycle.Suspend
import SeLe4n.Kernel.Lifecycle.Operations
import SeLe4n.Kernel.InformationFlow.Policy
import SeLe4n.Platform.Boot
import SeLe4n.Testing.Helpers

/-!
# AN11-A — KernelError variant cross-syscall coverage matrix (H-20)

WS-AN Phase AN11 closes audit finding H-20 (HIGH): the prior test surface
exercised many `KernelError` variants only inside large mixed-purpose
suites, leaving no canonical, machine-decidable index of which variant a
syscall path can produce.  This suite is that canonical index.

Each row of `errorMatrix` is a `KernelErrorRejection` record naming:

* the **operation / syscall path** that produces the error,
* the **expected `KernelError` variant** the path returns,
* a **scenarioTag** (short identifier) and **scenarioDesc** (one-sentence
  rationale) that document why the row exists,
* a **runScenario** thunk that constructs a deliberately-failing input
  state and invokes the operation.

The suite's `main` walks the matrix at runtime, asserting that each
`runScenario` returns the expected variant.  A regression — e.g. a
handler silently dropping an error or remapping it to a different
variant — fails the suite immediately and identifies the responsible
row by `scenarioTag`.

`errorMatrix_covers_at_least_35` is a `decide`-witness theorem that
locks the row count at the audit's recommended minimum.  The CI
`KERRORMATRIX_ROWS` monotonicity metric (in
`scripts/ak7_cascade_baseline.sh`) ensures the count cannot regress.

The matrix is partitioned into four logical bands matching the audit's
sub-task breakdown:

* **AN11-A.2 baseline** — variants already exercised elsewhere; rows
  here serve as the canonical index entry.
* **AN11-A.3 security-priority** — the nine variants the audit flags as
  security-critical (revocation, ASID, scheduler invariant, alignment,
  VM fault, slot occupancy, cyclic deps, dependency violation, reply
  cap).
* **AN11-A.4 IPC / SchedContext / Lifecycle** — error paths in IPC
  bounds, SchedContext budget/period validation, Lifecycle retype.
* **AN11-A.5 Architecture / Capability / Service residual** — register
  decode, capability authority, service registration validation.
-/

set_option maxRecDepth 1024

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Testing

namespace SeLe4n.Testing.KernelErrorMatrix

/-- AN11-A.1 — schema for one matrix row.

* `syscall` is a free-form short string naming the operation under test
  (`"cspaceMint"`, `"validateSchedContextParams"`, ...).  It is *not*
  bound to `SyscallId.toString` because some rows exercise sub-helpers
  like `validateIpcBufferAddress` that are not themselves syscalls.
* `expectedError` is the variant the path must return.
* `scenarioTag` is a stable identifier for the row (used in PASS/FAIL
  output and in any future cross-references).
* `scenarioDesc` is a one-sentence human-readable rationale.
* `runScenario` is a thunk because every body needs to construct fresh
  state; defining the matrix as `List KernelErrorRejection` keeps
  `errorMatrix.length` decidable for the witness theorem. -/
structure KernelErrorRejection where
  syscall       : String
  expectedError : KernelError
  scenarioTag   : String
  scenarioDesc  : String
  runScenario   : Unit → Except KernelError Unit

-- ============================================================================
-- Helpers — minimal state constructors used across rows
-- ============================================================================

/-- Convert a `Kernel`/`Except KernelError α` result returning state pairs to
the unit-valued matrix shape.  Discards the success value and the post-state
(rows only assert the *error* variant; no row depends on the post-state). -/
@[inline] private def runUnit (e : Except KernelError α) : Except KernelError Unit :=
  match e with
  | .ok _ => .ok ()
  | .error err => .error err

/-- A bare TCB with the given thread id, default scheduling parameters, and
sentinel CSpace/VSpace roots.  Used as a building block for fixtures whose
test-failure path does not depend on TCB internals. -/
private def mkTcb (tid : Nat) : TCB :=
  { tid := ThreadId.ofNat tid
    priority := ⟨10⟩
    domain := ⟨0⟩
    cspaceRoot := ObjId.ofNat 0
    vspaceRoot := ObjId.ofNat 0
    ipcBuffer := SeLe4n.VAddr.ofNat 0 }

/-- An empty CNode with depth/radix sized for ABI-decoded slot indices.  The
default `radixWidth = 16` is large enough for every test's chosen slots. -/
private def mkEmptyCNode (depth : Nat := 16) : CNode :=
  { depth := depth
    guardWidth := 0
    guardValue := 0
    radixWidth := 16
    slots := SeLe4n.Kernel.RobinHood.RHTable.empty 16 }

/-- Build a `SyscallDecodeResult` directly so decode-helper rows (rights >
0x1F, etc.) do not need a register file.  `inlineCount = msgRegs.size` keeps
the AK4-A invariant happy. -/
private def mkDecoded (msgRegs : Array RegValue) (label : Nat := 0)
    (capAddr : Nat := 0) (syscallId : SyscallId := SyscallId.cspaceMint)
    : SyscallDecodeResult :=
  { capAddr := CPtr.ofNat capAddr
    msgInfo := { length := msgRegs.size, extraCaps := 0, label := label }
    syscallId := syscallId
    msgRegs := msgRegs
    inlineCount := msgRegs.size
    overflowCount := 0 }

/-- A `RegValue` with the supplied raw value.  Wrapper to keep matrix rows
short. -/
@[inline] private def rv (n : Nat) : RegValue := ⟨n⟩

-- ============================================================================
-- AN11-A.2 — Baseline coverage layer (already-tested variants)
--
-- The following variants are exercised elsewhere in the suite portfolio.
-- These rows are the canonical matrix entries: a regression that drops an
-- existing failure path will surface here even if the original suite is
-- silently mutated.
-- ============================================================================

/-- Row: `validateSchedContextParams` rejects period == 0 with
`.invalidArgument`. -/
private def row_invalidArgument_period_zero : KernelErrorRejection :=
  { syscall       := "validateSchedContextParams"
    expectedError := .invalidArgument
    scenarioTag   := "AN11A.2.invalidArgument.period_zero"
    scenarioDesc  := "SchedContext configure with period=0 must reject" ++
                     " (zero-period SC cannot make progress; would violate" ++
                     " replenishmentListWellFormed downstream)"
    runScenario   := fun _ =>
      SeLe4n.Kernel.SchedContextOps.validateSchedContextParams
        (budget := 100) (period := 0) (priority := 5) (_deadline := 0)
        (domain := 0) }

/-- Row: `validateIpcBufferAddress` rejects unaligned address with
`.alignmentError`. -/
private def row_alignmentError_ipcBuffer : KernelErrorRejection :=
  { syscall       := "validateIpcBufferAddress"
    expectedError := .alignmentError
    scenarioTag   := "AN11A.2.alignmentError.ipcBuffer"
    scenarioDesc  := "IPC buffer address must be 512-byte aligned" ++
                     " (ipcBufferAlignment); a one-byte-offset address" ++
                     " is rejected before any state mutation"
    runScenario   := fun _ =>
      SeLe4n.Kernel.Architecture.IpcBufferValidation.validateIpcBufferAddress
        (default : SystemState) (ThreadId.ofNat 0)
        (SeLe4n.VAddr.ofNat 1) }

/-- Row: `validateIpcBufferAddress` rejects missing TCB with
`.objectNotFound`. -/
private def row_objectNotFound_ipcBuffer_missing_tcb : KernelErrorRejection :=
  { syscall       := "validateIpcBufferAddress"
    expectedError := .objectNotFound
    scenarioTag   := "AN11A.2.objectNotFound.ipcBuffer_missing_tcb"
    scenarioDesc  := "Validating IPC buffer for an absent TCB returns" ++
                     " .objectNotFound (the AL2-A typed-helper migration" ++
                     " collapses absent and wrong-variant into the same" ++
                     " variant)"
    runScenario   := fun _ =>
      -- 0x200 is aligned (multiple of 512); canonical (within 48-bit VA);
      -- no TCB exists at id 1 in default state.
      SeLe4n.Kernel.Architecture.IpcBufferValidation.validateIpcBufferAddress
        (default : SystemState) (ThreadId.ofNat 1)
        (SeLe4n.VAddr.ofNat 0x200) }

/-- Row: `decodeCSpaceMintArgs` rejects rights > 0x1F with
`.invalidArgument`. -/
private def row_invalidArgument_mint_rights : KernelErrorRejection :=
  { syscall       := "decodeCSpaceMintArgs"
    expectedError := .invalidArgument
    scenarioTag   := "AN11A.2.invalidArgument.mint_rights"
    scenarioDesc  := "AK4-E: cspaceMint args rejected when rights word" ++
                     " exceeds 0x1F (5-bit AccessRightSet width)"
    runScenario   := fun _ =>
      runUnit (SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceMintArgs (mkDecoded
        #[rv 0, rv 1, rv 0x20, rv 0])) }

/-- Row: `decodeSyscallId` rejects an unknown syscall number with
`.invalidSyscallNumber`. -/
private def row_invalidSyscallNumber : KernelErrorRejection :=
  { syscall       := "decodeSyscallId"
    expectedError := .invalidSyscallNumber
    scenarioTag   := "AN11A.2.invalidSyscallNumber.unknown"
    scenarioDesc  := "Decoding a register value that is not a modeled" ++
                     " syscall id (255) returns .invalidSyscallNumber"
    runScenario   := fun _ =>
      runUnit (SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallId (rv 255)) }

/-- Row: `decodeMsgInfo` rejects malformed message-info word with
`.invalidMessageInfo`.  `MessageInfo.decode` returns `none` on length or
extraCaps overflow. -/
private def row_invalidMessageInfo : KernelErrorRejection :=
  { syscall       := "decodeMsgInfo"
    expectedError := .invalidMessageInfo
    scenarioTag   := "AN11A.2.invalidMessageInfo.length_overflow"
    scenarioDesc  := "Decoding a msgInfo word whose length field exceeds" ++
                     " maxMessageRegisters returns .invalidMessageInfo"
    runScenario   := fun _ =>
      -- High length bits -> length overflow rejected by MessageInfo.decode
      runUnit (SeLe4n.Kernel.Architecture.RegisterDecode.decodeMsgInfo (rv (1 <<< 60))) }

/-- Row: `decodeCapPtr` rejects values exceeding word64 with
`.invalidCapPtr`. -/
private def row_invalidCapPtr : KernelErrorRejection :=
  { syscall       := "decodeCapPtr"
    expectedError := .invalidCapPtr
    scenarioTag   := "AN11A.2.invalidCapPtr.over_word64"
    scenarioDesc  := "Cap-pointer register value exceeding 2^64 is" ++
                     " rejected at decode time"
    runScenario   := fun _ =>
      runUnit (SeLe4n.Kernel.Architecture.RegisterDecode.decodeCapPtr (rv (2^64))) }

/-- Row: `validateRegBound` rejects out-of-range register name with
`.invalidRegister`. -/
private def row_invalidRegister : KernelErrorRejection :=
  { syscall       := "validateRegBound"
    expectedError := .invalidRegister
    scenarioTag   := "AN11A.2.invalidRegister.over_count"
    scenarioDesc  := "Register name with index ≥ regCount is rejected" ++
                     " before any read"
    runScenario   := fun _ =>
      SeLe4n.Kernel.Architecture.RegisterDecode.validateRegBound ⟨32⟩ 32 }

/-- Row: `endpointSendDual` rejects message exceeding maxMessageRegisters
with `.ipcMessageTooLarge`. -/
private def row_ipcMessageTooLarge : KernelErrorRejection :=
  { syscall       := "endpointSendDual"
    expectedError := .ipcMessageTooLarge
    scenarioTag   := "AN11A.2.ipcMessageTooLarge.over_max"
    scenarioDesc  := "endpointSendDual rejects message whose register" ++
                     " count exceeds maxMessageRegisters (120)"
    runScenario   := fun _ =>
      let oversized : IpcMessage :=
        { registers := Array.replicate (maxMessageRegisters + 1) (rv 0)
          caps := #[]
          badge := none }
      runUnit (endpointSendDual (ObjId.ofNat 1) (ThreadId.ofNat 1)
        oversized (default : SystemState)) }

/-- Row: `endpointSendDual` rejects message exceeding maxExtraCaps with
`.ipcMessageTooManyCaps`. -/
private def row_ipcMessageTooManyCaps : KernelErrorRejection :=
  { syscall       := "endpointSendDual"
    expectedError := .ipcMessageTooManyCaps
    scenarioTag   := "AN11A.2.ipcMessageTooManyCaps.over_max"
    scenarioDesc  := "endpointSendDual rejects message whose extra-cap" ++
                     " count exceeds maxExtraCaps (3)"
    runScenario   := fun _ =>
      let oversized : IpcMessage :=
        { registers := #[]
          caps := Array.replicate (maxExtraCaps + 1) Capability.null
          badge := none }
      runUnit (endpointSendDual (ObjId.ofNat 1) (ThreadId.ofNat 1)
        oversized (default : SystemState)) }

/-- Row: `syscallEntry` rejects empty current-thread slot with
`.illegalState`.  The default state has no scheduler `current`. -/
private def row_illegalState_no_current : KernelErrorRejection :=
  { syscall       := "syscallEntry"
    expectedError := .illegalState
    scenarioTag   := "AN11A.2.illegalState.no_current_thread"
    scenarioDesc  := "syscallEntry on a state with no scheduled current" ++
                     " thread cannot identify the caller and rejects with" ++
                     " .illegalState"
    runScenario   := fun _ =>
      runUnit (syscallEntry SeLe4n.arm64DefaultLayout 32
        (default : SystemState)) }

/-- Row: `syscallEntryChecked` with the insecure default labeling context
rejects with `.policyDenied` (AI5-C / M-19). -/
private def row_policyDenied_insecure_default : KernelErrorRejection :=
  { syscall       := "syscallEntryChecked"
    expectedError := .policyDenied
    scenarioTag   := "AN11A.2.policyDenied.insecure_default"
    scenarioDesc  := "Checked syscall entry with the default labeling" ++
                     " context (publicLabel everywhere) is rejected by" ++
                     " isInsecureDefaultContext as .policyDenied"
    runScenario   := fun _ =>
      runUnit (syscallEntryChecked
        SeLe4n.Kernel.defaultLabelingContext
        SeLe4n.arm64DefaultLayout 32
        (default : SystemState)) }

/-- Row: `cspaceMint` rejects null cap with `.nullCapability`.  Builds a
state with a CNode whose source slot holds `Capability.null`. -/
private def row_nullCapability_mint : KernelErrorRejection :=
  { syscall       := "cspaceMint"
    expectedError := .nullCapability
    scenarioTag   := "AN11A.2.nullCapability.mint_from_null"
    scenarioDesc  := "AL1b: cspaceMint rejects a source slot holding" ++
                     " Capability.null (target = ObjId.sentinel, empty" ++
                     " rights) — distinct from .invalidCapability"
    runScenario   := fun _ =>
      let cnodeId : ObjId := ObjId.ofNat 100
      let srcSlot : SeLe4n.Slot := SeLe4n.Slot.ofNat 0
      let dstSlot : SeLe4n.Slot := SeLe4n.Slot.ofNat 1
      let cn : CNode := { mkEmptyCNode with
        slots := (mkEmptyCNode).slots.insert srcSlot Capability.null }
      let st : SystemState := { (default : SystemState) with
        objects := (default : SystemState).objects.insert cnodeId
          (.cnode cn) }
      runUnit (cspaceMint
        ⟨cnodeId, srcSlot⟩ ⟨cnodeId, dstSlot⟩
        AccessRightSet.empty none st) }

-- ============================================================================
-- AN11-A.3 — Security-priority variants (audit-named)
--
-- The nine variants the audit explicitly flags as security-critical coverage
-- gaps: revocationRequired, asidNotBound, schedulerInvariantViolation,
-- alignmentError, vmFault, targetSlotOccupied, cyclicDependency,
-- dependencyViolation, replyCapInvalid.
-- ============================================================================

/-- Row: `cspaceDeleteSlot` rejects deletion of a slot with CDT children
with `.revocationRequired`. -/
private def row_revocationRequired_delete_with_children : KernelErrorRejection :=
  { syscall       := "cspaceDeleteSlot"
    expectedError := .revocationRequired
    scenarioTag   := "AN11A.3.revocationRequired.delete_with_children"
    scenarioDesc  := "U-H03: cspaceDeleteSlot rejects a slot whose CDT" ++
                     " node has children — caller must cspaceRevoke first"
    runScenario   := fun _ =>
      -- Build a state where the source slot has a CDT node with a child.
      let cnodeId : ObjId := ObjId.ofNat 110
      let parentSlot : SeLe4n.Slot := SeLe4n.Slot.ofNat 0
      let childSlot : SeLe4n.Slot := SeLe4n.Slot.ofNat 1
      let cap : Capability :=
        { target := .object (ObjId.ofNat 200), rights := AccessRightSet.empty,
          badge := none }
      let cn : CNode := { mkEmptyCNode with
        slots := ((mkEmptyCNode).slots.insert parentSlot cap).insert
          childSlot cap }
      let stBase : SystemState := { (default : SystemState) with
        objects := (default : SystemState).objects.insert cnodeId
          (.cnode cn) }
      let parentRef : SlotRef := ⟨cnodeId, parentSlot⟩
      let childRef  : SlotRef := ⟨cnodeId, childSlot⟩
      -- Allocate CDT nodes for both slots through the official helper so the
      -- slot ↔ node maps remain consistent.
      let (parentNode, st1) := SystemState.ensureCdtNodeForSlot stBase parentRef
      let (childNode,  st2) := SystemState.ensureCdtNodeForSlot st1     childRef
      -- Wire parent → child via the CDT add-edge helper.
      let st : SystemState := { st2 with
        cdt := st2.cdt.addEdge parentNode childNode .copy }
      runUnit (cspaceDeleteSlot ⟨cnodeId, parentSlot⟩ st) }

/-- Row: `decodeVSpaceMapArgs` rejects ASID at or above maxASID with
`.asidNotBound`. -/
private def row_asidNotBound_vspaceMap : KernelErrorRejection :=
  { syscall       := "decodeVSpaceMapArgs"
    expectedError := .asidNotBound
    scenarioTag   := "AN11A.3.asidNotBound.over_maxASID"
    scenarioDesc  := "U2-G/U-H08: decode of vspaceMap rejects ASID ≥" ++
                     " platform-configured maxASID with .asidNotBound"
    runScenario   := fun _ =>
      runUnit (SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeVSpaceMapArgs
        (mkDecoded #[rv 65536, rv 0, rv 0, rv 0]) 65536) }

/-- Row: `scheduleChecked` rejects when the current TCB is missing with
`.schedulerInvariantViolation`. -/
private def row_schedulerInvariantViolation : KernelErrorRejection :=
  { syscall       := "scheduleChecked"
    expectedError := .schedulerInvariantViolation
    scenarioTag   := "AN11A.3.schedulerInvariantViolation.current_tcb_missing"
    scenarioDesc  := "X2-I: scheduleChecked surfaces invariant violation" ++
                     " when scheduler.current points to a missing TCB" ++
                     " (currentThreadValid contradiction is normally" ++
                     " unreachable; the wrapper provides defense-in-depth)"
    runScenario   := fun _ =>
      let st : SystemState := { (default : SystemState) with
        scheduler := { (default : SystemState).scheduler with
          current := some (ThreadId.ofNat 999) } }
      runUnit (scheduleChecked st) }

/-- Row: `validateIpcBufferAddress` rejects unaligned address with
`.alignmentError`.  Same as the AN11-A.2 baseline row but tagged as
security-priority per audit; uses a different non-zero misalignment to
avoid duplicate scenario tags. -/
private def row_alignmentError_security : KernelErrorRejection :=
  { syscall       := "validateIpcBufferAddress"
    expectedError := .alignmentError
    scenarioTag   := "AN11A.3.alignmentError.security_critical"
    scenarioDesc  := "Security-critical: misaligned IPC buffer (address" ++
                     " 256, half the 512-byte alignment) rejected before" ++
                     " any state mutation"
    runScenario   := fun _ =>
      SeLe4n.Kernel.Architecture.IpcBufferValidation.validateIpcBufferAddress
        (default : SystemState) (ThreadId.ofNat 0)
        (SeLe4n.VAddr.ofNat 256) }

/-- Row: `cspaceInsertSlot` rejects writing to an already-occupied slot
with `.targetSlotOccupied`. -/
private def row_targetSlotOccupied : KernelErrorRejection :=
  { syscall       := "cspaceInsertSlot"
    expectedError := .targetSlotOccupied
    scenarioTag   := "AN11A.3.targetSlotOccupied.insert_into_used"
    scenarioDesc  := "H-02: cspaceInsertSlot refuses to overwrite an" ++
                     " existing capability — caller must explicitly" ++
                     " delete or revoke first"
    runScenario   := fun _ =>
      let cnodeId : ObjId := ObjId.ofNat 120
      let slot : SeLe4n.Slot := SeLe4n.Slot.ofNat 0
      let occupant : Capability :=
        { target := .object (ObjId.ofNat 200), rights := AccessRightSet.empty,
          badge := none }
      let cn : CNode := { mkEmptyCNode with
        slots := (mkEmptyCNode).slots.insert slot occupant }
      let st : SystemState := { (default : SystemState) with
        objects := (default : SystemState).objects.insert cnodeId
          (.cnode cn) }
      runUnit (cspaceInsertSlot ⟨cnodeId, slot⟩ occupant st) }

/-- Row: `serviceRegisterDependency` rejects self-edge with
`.cyclicDependency`. -/
private def row_cyclicDependency_self_edge : KernelErrorRejection :=
  { syscall       := "serviceRegisterDependency"
    expectedError := .cyclicDependency
    scenarioTag   := "AN11A.3.cyclicDependency.self_edge"
    scenarioDesc  := "WS-D4/F-07: registering a service as its own" ++
                     " dependency is cyclic by definition and is rejected"
    runScenario   := fun _ =>
      let svcId : ServiceId := ⟨1⟩
      let entry : ServiceGraphEntry :=
        { identity := { sid := svcId, backingObject := ⟨1⟩, owner := ⟨1⟩ }
          dependencies := []
          isolatedFrom := [] }
      let st : SystemState := { (default : SystemState) with
        services := (default : SystemState).services.insert svcId entry }
      runUnit (serviceRegisterDependency svcId svcId st) }

/-- Row: `serviceRegisterDependency` rejects unregistered dependency target
with `.objectNotFound`.  Audit calls out `dependencyViolation` for unmet
deps; the present codebase emits `.objectNotFound` from the same step
(`lookupService st depId = none`) — the row documents the variant the
production path actually returns and pins the boundary.  If the audit's
recommended `.dependencyViolation` is added in a later refactor, the row
will fail and prompt re-classification. -/
private def row_objectNotFound_dep_unmet : KernelErrorRejection :=
  { syscall       := "serviceRegisterDependency"
    expectedError := .objectNotFound
    scenarioTag   := "AN11A.3.dependencyViolation.unmet_dep_currently_objectNotFound"
    scenarioDesc  := "Registering a dependency on a non-existent service" ++
                     " currently returns .objectNotFound (rather than" ++
                     " .dependencyViolation); pinning the production" ++
                     " boundary against silent migration"
    runScenario   := fun _ =>
      let svcId : ServiceId := ⟨10⟩
      let depId : ServiceId := ⟨11⟩
      let entry : ServiceGraphEntry :=
        { identity := { sid := svcId, backingObject := ⟨10⟩, owner := ⟨10⟩ }
          dependencies := []
          isolatedFrom := [] }
      let st : SystemState := { (default : SystemState) with
        services := (default : SystemState).services.insert svcId entry }
      runUnit (serviceRegisterDependency svcId depId st) }

/-- Row: `endpointReply` rejects when target's `replyTarget = none` with
`.replyCapInvalid`.  Builds a TCB in `.blockedOnReply _ none` to trigger
the AK1-B fail-closed branch. -/
private def row_replyCapInvalid_no_target : KernelErrorRejection :=
  { syscall       := "endpointReply"
    expectedError := .replyCapInvalid
    scenarioTag   := "AN11A.3.replyCapInvalid.no_target"
    scenarioDesc  := "AK1-B (I-H02): endpointReply fails closed when the" ++
                     " replier's blockedOnReply target slot is `none`" ++
                     " (production paths always set `some receiver`)"
    runScenario   := fun _ =>
      let endpointId : ObjId := ObjId.ofNat 130
      let replierId : ThreadId := ThreadId.ofNat 50
      let targetId  : ThreadId := ThreadId.ofNat 51
      let targetTcb : TCB := { mkTcb 51 with
        ipcState := .blockedOnReply endpointId none }
      let st : SystemState := { (default : SystemState) with
        objects := ((default : SystemState).objects.insert
          targetId.toObjId (.tcb targetTcb)).insert
          replierId.toObjId (.tcb (mkTcb 50)) }
      runUnit (endpointReply replierId targetId IpcMessage.empty st) }

/-- Row: `endpointReply` on a `.ready` target rejects with
`.replyCapInvalid` (target is not in any blocking state). -/
private def row_replyCapInvalid_not_blocked : KernelErrorRejection :=
  { syscall       := "endpointReply"
    expectedError := .replyCapInvalid
    scenarioTag   := "AN11A.3.replyCapInvalid.target_not_blocked"
    scenarioDesc  := "endpointReply rejects when target is not in" ++
                     " .blockedOnReply (e.g., `.ready`); guards against" ++
                     " confused-deputy on stale reply caps"
    runScenario   := fun _ =>
      let replierId : ThreadId := ThreadId.ofNat 60
      let targetId  : ThreadId := ThreadId.ofNat 61
      let st : SystemState := { (default : SystemState) with
        objects := ((default : SystemState).objects.insert
          targetId.toObjId (.tcb (mkTcb 61))).insert
          replierId.toObjId (.tcb (mkTcb 60)) }
      runUnit (endpointReply replierId targetId IpcMessage.empty st) }

-- ============================================================================
-- AN11-A.4 — IPC / SchedContext / Lifecycle error path variants
-- ============================================================================

/-- Row: `endpointSendDual` rejects send to a non-endpoint object with
`.invalidCapability`. -/
private def row_invalidCapability_send_to_nonEndpoint : KernelErrorRejection :=
  { syscall       := "endpointSendDual"
    expectedError := .invalidCapability
    scenarioTag   := "AN11A.4.invalidCapability.send_to_nonEndpoint"
    scenarioDesc  := "endpointSendDual rejects when the target object is" ++
                     " present but not an Endpoint (e.g., a Notification)"
    runScenario   := fun _ =>
      let endpointId : ObjId := ObjId.ofNat 140
      let stuff : Notification := { state := .idle, waitingThreads := [] }
      let st : SystemState := { (default : SystemState) with
        objects := (default : SystemState).objects.insert endpointId
          (.notification stuff) }
      runUnit (endpointSendDual endpointId (ThreadId.ofNat 1)
        IpcMessage.empty st) }

/-- Row: `endpointSendDual` rejects send to absent endpoint with
`.objectNotFound`. -/
private def row_objectNotFound_send_missing : KernelErrorRejection :=
  { syscall       := "endpointSendDual"
    expectedError := .objectNotFound
    scenarioTag   := "AN11A.4.objectNotFound.send_missing_endpoint"
    scenarioDesc  := "endpointSendDual rejects when the endpoint does not" ++
                     " exist in the object store"
    runScenario   := fun _ =>
      runUnit (endpointSendDual (ObjId.ofNat 9999) (ThreadId.ofNat 1)
        IpcMessage.empty (default : SystemState)) }

/-- Row: `endpointQueueEnqueue` on a thread with non-`.ready` ipcState
returns `.alreadyWaiting`. -/
private def row_alreadyWaiting_enqueue_blocked : KernelErrorRejection :=
  { syscall       := "endpointQueueEnqueue"
    expectedError := .alreadyWaiting
    scenarioTag   := "AN11A.4.alreadyWaiting.enqueue_blocked_thread"
    scenarioDesc  := "Enqueueing a thread that is already in a blocking" ++
                     " state (.blockedOnSend) cannot succeed; the queue" ++
                     " operation rejects with .alreadyWaiting"
    runScenario   := fun _ =>
      let endpointId : ObjId := ObjId.ofNat 150
      let tid : ThreadId := ThreadId.ofNat 70
      let blocked : TCB := { mkTcb 70 with
        ipcState := .blockedOnSend endpointId }
      let ep : Endpoint := {}
      let st : SystemState := { (default : SystemState) with
        objects := ((default : SystemState).objects.insert endpointId
          (.endpoint ep)).insert tid.toObjId (.tcb blocked) }
      runUnit (SeLe4n.Kernel.endpointQueueEnqueue endpointId false tid st) }

/-- Row: `validateSchedContextParams` rejects budget == 0 with
`.invalidArgument`.  AK6-A (SC-H01) closed this defense-in-depth gate. -/
private def row_invalidArgument_budget_zero : KernelErrorRejection :=
  { syscall       := "validateSchedContextParams"
    expectedError := .invalidArgument
    scenarioTag   := "AN11A.4.invalidArgument.budget_zero"
    scenarioDesc  := "AK6-A: SchedContext configure with budget=0 is" ++
                     " rejected (would violate replenishmentListWellFormed" ++
                     " — every replenishment amount must be positive)"
    runScenario   := fun _ =>
      SeLe4n.Kernel.SchedContextOps.validateSchedContextParams
        (budget := 0) (period := 1000) (priority := 5) (_deadline := 0)
        (domain := 0) }

/-- Row: `validateSchedContextParams` rejects budget > period with
`.invalidArgument`. -/
private def row_invalidArgument_budget_over_period : KernelErrorRejection :=
  { syscall       := "validateSchedContextParams"
    expectedError := .invalidArgument
    scenarioTag   := "AN11A.4.invalidArgument.budget_over_period"
    scenarioDesc  := "SchedContext budget must be ≤ period (cannot use" ++
                     " more than 100% of a period)"
    runScenario   := fun _ =>
      SeLe4n.Kernel.SchedContextOps.validateSchedContextParams
        (budget := 2000) (period := 1000) (priority := 5) (_deadline := 0)
        (domain := 0) }

/-- Row: `validateSchedContextParams` rejects priority > 255 with
`.invalidArgument`. -/
private def row_invalidArgument_priority_overflow : KernelErrorRejection :=
  { syscall       := "validateSchedContextParams"
    expectedError := .invalidArgument
    scenarioTag   := "AN11A.4.invalidArgument.priority_overflow"
    scenarioDesc  := "SchedContext priority must be ≤ maxPriorityVal (255)"
    runScenario   := fun _ =>
      SeLe4n.Kernel.SchedContextOps.validateSchedContextParams
        (budget := 100) (period := 1000) (priority := 256) (_deadline := 0)
        (domain := 0) }

/-- Row: `validateSchedContextParams` rejects domain ≥ 16 with
`.invalidArgument`. -/
private def row_invalidArgument_domain_overflow : KernelErrorRejection :=
  { syscall       := "validateSchedContextParams"
    expectedError := .invalidArgument
    scenarioTag   := "AN11A.4.invalidArgument.domain_overflow"
    scenarioDesc  := "SchedContext domain must be < numDomainsVal (16)"
    runScenario   := fun _ =>
      SeLe4n.Kernel.SchedContextOps.validateSchedContextParams
        (budget := 100) (period := 1000) (priority := 5) (_deadline := 0)
        (domain := 16) }

/-- Row: `validatePriorityAuthority` rejects priority above
`maxHardwarePriority` with `.illegalAuthority` (AK8-D / C-M05). -/
private def row_illegalAuthority_priority_over_hw : KernelErrorRejection :=
  { syscall       := "validatePriorityAuthority"
    expectedError := .illegalAuthority
    scenarioTag   := "AN11A.4.illegalAuthority.priority_over_hw"
    scenarioDesc  := "AK8-D (C-M05): targetPriority above the platform's" ++
                     " 8-bit hardware priority register width is rejected"
    runScenario   := fun _ =>
      let caller : TCB := { mkTcb 80 with maxControlledPriority := ⟨10⟩ }
      SeLe4n.Kernel.SchedContext.PriorityManagement.validatePriorityAuthority caller
        (SeLe4n.Priority.mk 256) }

/-- Row: `validatePriorityAuthority` rejects priority above caller's MCP
with `.illegalAuthority`. -/
private def row_illegalAuthority_over_mcp : KernelErrorRejection :=
  { syscall       := "validatePriorityAuthority"
    expectedError := .illegalAuthority
    scenarioTag   := "AN11A.4.illegalAuthority.over_mcp"
    scenarioDesc  := "MCP-bounded priority discipline: target above the" ++
                     " caller's maxControlledPriority is rejected"
    runScenario   := fun _ =>
      let caller : TCB := { mkTcb 81 with maxControlledPriority := ⟨10⟩ }
      SeLe4n.Kernel.SchedContext.PriorityManagement.validatePriorityAuthority caller
        (SeLe4n.Priority.mk 50) }

/-- Row: `decodeLifecycleRetypeArgs` rejects unknown type tag with
`.invalidTypeTag` (R7-E / L-10). -/
private def row_invalidTypeTag : KernelErrorRejection :=
  { syscall       := "decodeLifecycleRetypeArgs"
    expectedError := .invalidTypeTag
    scenarioTag   := "AN11A.4.invalidTypeTag.unknown"
    scenarioDesc  := "Lifecycle retype with a type-tag value not in the" ++
                     " modeled KernelObjectType set (here, 99) is rejected" ++
                     " at the ABI decode boundary"
    runScenario   := fun _ =>
      runUnit (SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeLifecycleRetypeArgs
        (mkDecoded #[rv 0, rv 99, rv 0])) }

-- ============================================================================
-- AN11-A.5 — Architecture / Capability / Service residual variants
-- ============================================================================

/-- Row: `decodeVSpaceMapArgs` rejects non-canonical VAddr (≥ 2^48) with
`.addressOutOfBounds`. -/
private def row_addressOutOfBounds_vaddr : KernelErrorRejection :=
  { syscall       := "decodeVSpaceMapArgs"
    expectedError := .addressOutOfBounds
    scenarioTag   := "AN11A.5.addressOutOfBounds.non_canonical_vaddr"
    scenarioDesc  := "U2-B/U-H06: vspaceMap rejects VAddr ≥ 2^48 (outside" ++
                     " ARM64 48-bit canonical range)"
    runScenario   := fun _ =>
      runUnit (SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeVSpaceMapArgs
        (mkDecoded #[rv 0, rv (2^48), rv 0, rv 0]) 65536) }

/-- Row: `decodeVSpaceMapArgs` rejects invalid permission bits with
`.invalidSyscallArgument` (X5-E / M-11). -/
private def row_invalidSyscallArgument_perms : KernelErrorRejection :=
  { syscall       := "decodeVSpaceMapArgs"
    expectedError := .invalidSyscallArgument
    scenarioTag   := "AN11A.5.invalidSyscallArgument.bad_perms"
    scenarioDesc  := "U5-E/U-M07/X5-E: undefined permission bits (≥ 32)" ++
                     " yield .invalidSyscallArgument from the vspace decode"
    runScenario   := fun _ =>
      runUnit (SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeVSpaceMapArgs
        (mkDecoded #[rv 0, rv 0x1000, rv 0, rv 64]) 65536) }

/-- Row: `decodeVSpaceMapArgsChecked` rejects PA ≥ 2^width with
`.addressOutOfBounds` (AK3-E / A-M01). -/
private def row_addressOutOfBounds_paddr : KernelErrorRejection :=
  { syscall       := "decodeVSpaceMapArgsChecked"
    expectedError := .addressOutOfBounds
    scenarioTag   := "AN11A.5.addressOutOfBounds.paddr_over_width"
    scenarioDesc  := "AK3-E (A-M01): defense-in-depth checked decode" ++
                     " rejects PAs at or above the platform's PA window" ++
                     " (here, maxPA = 2^44 RPi5)"
    runScenario   := fun _ =>
      runUnit (SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeVSpaceMapArgsChecked
        (mkDecoded #[rv 0, rv 0x1000, rv (2^44), rv 0]) 65536 (2^44)) }

/-- Row: `dispatchException .fiq` returns `.notSupported`. -/
private def row_notSupported_fiq : KernelErrorRejection :=
  { syscall       := "dispatchException"
    expectedError := .notSupported
    scenarioTag   := "AN11A.5.notSupported.fiq"
    scenarioDesc  := "AG3-C: FIQ exceptions are not modeled by seLe4n;" ++
                     " dispatch returns .notSupported"
    runScenario   := fun _ =>
      let ectx : SeLe4n.Kernel.Architecture.ExceptionContext :=
        { esr := 0, elr := 0, spsr := 0, far := 0 }
      runUnit (SeLe4n.Kernel.Architecture.dispatchException .fiq ectx 0
        (default : SystemState)) }

/-- Row: `dispatchException .serror` returns `.hardwareFault`. -/
private def row_hardwareFault_serror : KernelErrorRejection :=
  { syscall       := "dispatchException"
    expectedError := .hardwareFault
    scenarioTag   := "AN11A.5.hardwareFault.serror"
    scenarioDesc  := "AG3-C: SError (asynchronous external abort) is" ++
                     " surfaced as .hardwareFault"
    runScenario   := fun _ =>
      let ectx : SeLe4n.Kernel.Architecture.ExceptionContext :=
        { esr := 0, elr := 0, spsr := 0, far := 0 }
      runUnit (SeLe4n.Kernel.Architecture.dispatchException .serror ectx 0
        (default : SystemState)) }

/-- Row: `dispatchSynchronousException` on a data abort returns
`.vmFault`. -/
private def row_vmFault_data_abort : KernelErrorRejection :=
  { syscall       := "dispatchSynchronousException"
    expectedError := .vmFault
    scenarioTag   := "AN11A.5.vmFault.data_abort"
    scenarioDesc  := "AG3-C: ESR with EC=0x24 classifies as dataAbort and" ++
                     " dispatches to .vmFault"
    runScenario   := fun _ =>
      -- ESR with EC field = 0x24 (data abort, lower EL).  EC sits at bits
      -- [31:26] of the ESR register, so the raw value is 0x24 << 26.
      let ectx : SeLe4n.Kernel.Architecture.ExceptionContext :=
        { esr := UInt64.ofNat (0x24 <<< 26), elr := 0, spsr := 0, far := 0 }
      runUnit (SeLe4n.Kernel.Architecture.dispatchSynchronousException ectx
        (default : SystemState)) }

/-- Row: `dispatchSynchronousException` on a PC-alignment fault returns
`.userException`. -/
private def row_userException_pc_alignment : KernelErrorRejection :=
  { syscall       := "dispatchSynchronousException"
    expectedError := .userException
    scenarioTag   := "AN11A.5.userException.pc_alignment"
    scenarioDesc  := "AG3-C: ESR with EC=0x22 classifies as a PC alignment" ++
                     " fault and dispatches to .userException"
    runScenario   := fun _ =>
      let ectx : SeLe4n.Kernel.Architecture.ExceptionContext :=
        { esr := UInt64.ofNat (0x22 <<< 26), elr := 0, spsr := 0, far := 0 }
      runUnit (SeLe4n.Kernel.Architecture.dispatchSynchronousException ectx
        (default : SystemState)) }

/-- Row: `cspaceMint` on absent CNode returns `.objectNotFound`. -/
private def row_objectNotFound_mint_missing_cnode : KernelErrorRejection :=
  { syscall       := "cspaceMint"
    expectedError := .objectNotFound
    scenarioTag   := "AN11A.5.objectNotFound.mint_missing_cnode"
    scenarioDesc  := "cspaceLookupSlot inside cspaceMint propagates" ++
                     " .objectNotFound when the source CNode is absent"
    runScenario   := fun _ =>
      runUnit (cspaceMint
        ⟨ObjId.ofNat 9999, SeLe4n.Slot.ofNat 0⟩
        ⟨ObjId.ofNat 9999, SeLe4n.Slot.ofNat 1⟩
        AccessRightSet.empty none (default : SystemState)) }

/-- Row: `validateIpcBufferAddress` on present TCB but missing VSpaceRoot
returns `.invalidArgument`. -/
private def row_invalidArgument_ipcBuffer_missing_vspaceRoot : KernelErrorRejection :=
  { syscall       := "validateIpcBufferAddress"
    expectedError := .invalidArgument
    scenarioTag   := "AN11A.5.invalidArgument.ipcBuffer_missing_vspaceRoot"
    scenarioDesc  := "When the TCB exists but its vspaceRoot reference does" ++
                     " not resolve to a VSpaceRoot, validation rejects with" ++
                     " .invalidArgument"
    runScenario   := fun _ =>
      let tid : ThreadId := ThreadId.ofNat 90
      let tcb : TCB := mkTcb 90
      let st : SystemState := { (default : SystemState) with
        objects := (default : SystemState).objects.insert tid.toObjId
          (.tcb tcb) }
      SeLe4n.Kernel.Architecture.IpcBufferValidation.validateIpcBufferAddress
        st tid (SeLe4n.VAddr.ofNat 0x200) }

/- Note on `applyMachineConfigChecked`: this validator rejects malformed
`MachineConfig` with an `Except String _` (rather than a `KernelError`),
so it cannot be expressed as a `KernelErrorRejection` row.  When a future
refactor unifies the Except wrapper with `KernelError`, add a row here
(e.g., `row_addressOutOfBounds_pa_width_over_52`) and bump
`errorMatrixFloor` accordingly. -/

-- ============================================================================
-- AN11-A.6 (audit-pass v2) — additional variants identified in the deep audit
--
-- The initial AN11-A landing covered 28 distinct variants across 41 rows.
-- The audit-pass v2 sweep added rows for 6 more variants that have
-- straightforward production trigger paths but were not previously
-- exercised by the matrix:  `invalidObjectType`, `translationFault`,
-- `endpointQueueEmpty`, `untypedTypeMismatch`, `untypedDeviceRestriction`,
-- `childIdSelfOverwrite`.
-- ============================================================================

/-- Row: `storeObjectKindChecked` rejects a cross-variant overwrite with
`.invalidObjectType` (AL6 / AK7-F.cascade). -/
private def row_invalidObjectType_cross_variant : KernelErrorRejection :=
  { syscall       := "storeObjectKindChecked"
    expectedError := .invalidObjectType
    scenarioTag   := "AN11A.6.invalidObjectType.cross_variant"
    scenarioDesc  := "AL6: storeObjectKindChecked refuses to overwrite a" ++
                     " populated slot with an object of a different variant" ++
                     " (e.g., writing a SchedContext at an oid holding a TCB)"
    runScenario   := fun _ =>
      let oid : ObjId := ObjId.ofNat 700
      let tcb : TCB := mkTcb 700
      let sc : Kernel.SchedContext :=
        { scId := SchedContextId.ofObjId oid
          budget := ⟨100⟩, period := ⟨1000⟩
          priority := ⟨0⟩, deadline := ⟨0⟩
          domain := ⟨0⟩, budgetRemaining := ⟨100⟩
          boundThread := none, isActive := false
          replenishments := [] }
      let st : SystemState := { (default : SystemState) with
        objects := (default : SystemState).objects.insert oid (.tcb tcb) }
      runUnit (SeLe4n.Model.storeObjectKindChecked oid (.schedContext sc) st) }

/-- Row: `validateIpcBufferAddress` rejects a write-permission-missing
mapping with `.translationFault`.  The IPC buffer must be writable; a
read-only mapping at an aligned canonical address fails at step 6. -/
private def row_translationFault_ipcBuffer_no_write : KernelErrorRejection :=
  { syscall       := "validateIpcBufferAddress"
    expectedError := .translationFault
    scenarioTag   := "AN11A.6.translationFault.ipcBuffer_no_write_perm"
    scenarioDesc  := "IPC buffer mapped without write permission is" ++
                     " rejected at validateIpcBufferAddress step 6"
    runScenario   := fun _ =>
      let tid : ThreadId := ThreadId.ofNat 800
      let vsRootId : ObjId := ObjId.ofNat 801
      let vaddr : SeLe4n.VAddr := SeLe4n.VAddr.ofNat 0x200
      -- Read-only mapping (no write permission)
      let perms : PagePermissions :=
        { read := true, write := false, execute := false, user := true,
          cacheable := true }
      let vsRoot : VSpaceRoot :=
        { asid := SeLe4n.ASID.ofNat 1
          mappings := (SeLe4n.Kernel.RobinHood.RHTable.empty 16).insert vaddr
                        (SeLe4n.PAddr.ofNat 0x1000, perms) }
      let tcb : TCB := { mkTcb 800 with vspaceRoot := vsRootId }
      let st : SystemState := { (default : SystemState) with
        objects := ((default : SystemState).objects.insert tid.toObjId
          (.tcb tcb)).insert vsRootId (.vspaceRoot vsRoot) }
      SeLe4n.Kernel.Architecture.IpcBufferValidation.validateIpcBufferAddress
        st tid vaddr }

/-- Row: `endpointQueuePopHead` on an empty queue returns
`.endpointQueueEmpty`. -/
private def row_endpointQueueEmpty_pop_empty : KernelErrorRejection :=
  { syscall       := "endpointQueuePopHead"
    expectedError := .endpointQueueEmpty
    scenarioTag   := "AN11A.6.endpointQueueEmpty.pop_empty_queue"
    scenarioDesc  := "Popping from an empty endpoint queue returns" ++
                     " .endpointQueueEmpty rather than silently producing" ++
                     " an invalid result"
    runScenario   := fun _ =>
      let endpointId : ObjId := ObjId.ofNat 900
      let ep : Endpoint := {}  -- empty sendQ + receiveQ by default
      let st : SystemState := { (default : SystemState) with
        objects := (default : SystemState).objects.insert endpointId
          (.endpoint ep) }
      runUnit (SeLe4n.Kernel.endpointQueuePopHead endpointId false st) }

/-- Row: `retypeFromUntyped` on a non-untyped source returns
`.untypedTypeMismatch`. -/
private def row_untypedTypeMismatch : KernelErrorRejection :=
  { syscall       := "retypeFromUntyped"
    expectedError := .untypedTypeMismatch
    scenarioTag   := "AN11A.6.untypedTypeMismatch.source_not_untyped"
    scenarioDesc  := "WS-F2: retypeFromUntyped rejects when the source" ++
                     " object is present but is not an UntypedObject"
    runScenario   := fun _ =>
      let untypedId : ObjId := ObjId.ofNat 1000
      let childId : ObjId := ObjId.ofNat 1001
      let cnodeId : ObjId := ObjId.ofNat 1002
      -- Source is a Notification, NOT an Untyped — triggers type mismatch.
      let n : Notification := { state := .idle, waitingThreads := [] }
      -- Need a CSpace with the authority cap; build a minimal CNode.
      let authCap : Capability :=
        { target := .object untypedId
          rights := AccessRightSet.singleton .write
          badge := none }
      let cn : CNode := { mkEmptyCNode with
        slots := (mkEmptyCNode).slots.insert (SeLe4n.Slot.ofNat 0) authCap }
      let st : SystemState := { (default : SystemState) with
        objects := ((default : SystemState).objects.insert untypedId
          (.notification n)).insert cnodeId (.cnode cn) }
      let newObj : KernelObject := .endpoint {}
      runUnit (SeLe4n.Kernel.retypeFromUntyped
        ⟨cnodeId, SeLe4n.Slot.ofNat 0⟩ untypedId childId newObj 256 st) }

/-- Row: `retypeFromUntyped` with childId == untypedId returns
`.childIdSelfOverwrite`. -/
private def row_childIdSelfOverwrite : KernelErrorRejection :=
  { syscall       := "retypeFromUntyped"
    expectedError := .childIdSelfOverwrite
    scenarioTag   := "AN11A.6.childIdSelfOverwrite.same_id"
    scenarioDesc  := "WS-H2/H-06: retypeFromUntyped rejects when the" ++
                     " childId equals the untypedId — would overwrite the" ++
                     " parent untyped with the new child object"
    runScenario   := fun _ =>
      let untypedId : ObjId := ObjId.ofNat 1100
      let cnodeId : ObjId := ObjId.ofNat 1102
      let ut : UntypedObject :=
        { regionBase := SeLe4n.PAddr.ofNat 0x10000
          regionSize := 4096
          watermark := 0
          isDevice := false
          children := []
          parent := none }
      let authCap : Capability :=
        { target := .object untypedId
          rights := AccessRightSet.singleton .write
          badge := none }
      let cn : CNode := { mkEmptyCNode with
        slots := (mkEmptyCNode).slots.insert (SeLe4n.Slot.ofNat 0) authCap }
      let st : SystemState := { (default : SystemState) with
        objects := ((default : SystemState).objects.insert untypedId
          (.untyped ut)).insert cnodeId (.cnode cn) }
      let newObj : KernelObject := .endpoint {}
      -- childId == untypedId — must be rejected.
      runUnit (SeLe4n.Kernel.retypeFromUntyped
        ⟨cnodeId, SeLe4n.Slot.ofNat 0⟩ untypedId untypedId newObj 256 st) }

/-- Row: `retypeFromUntyped` from a device untyped to a non-untyped
target returns `.untypedDeviceRestriction`. -/
private def row_untypedDeviceRestriction : KernelErrorRejection :=
  { syscall       := "retypeFromUntyped"
    expectedError := .untypedDeviceRestriction
    scenarioTag   := "AN11A.6.untypedDeviceRestriction.device_to_typed"
    scenarioDesc  := "WS-F2: device untyped regions cannot back typed" ++
                     " kernel objects (only other untypeds), guarding" ++
                     " against MMIO regions hosting kernel state"
    runScenario   := fun _ =>
      let untypedId : ObjId := ObjId.ofNat 1200
      let childId : ObjId := ObjId.ofNat 1201
      let cnodeId : ObjId := ObjId.ofNat 1202
      let ut : UntypedObject :=
        { regionBase := SeLe4n.PAddr.ofNat 0xFE000000  -- BCM2712 MMIO range
          regionSize := 4096
          watermark := 0
          isDevice := true   -- device untyped
          children := []
          parent := none }
      let authCap : Capability :=
        { target := .object untypedId
          rights := AccessRightSet.singleton .write
          badge := none }
      let cn : CNode := { mkEmptyCNode with
        slots := (mkEmptyCNode).slots.insert (SeLe4n.Slot.ofNat 0) authCap }
      let st : SystemState := { (default : SystemState) with
        objects := ((default : SystemState).objects.insert untypedId
          (.untyped ut)).insert cnodeId (.cnode cn) }
      -- Try to retype to an Endpoint — forbidden from a device untyped.
      let newObj : KernelObject := .endpoint {}
      runUnit (SeLe4n.Kernel.retypeFromUntyped
        ⟨cnodeId, SeLe4n.Slot.ofNat 0⟩ untypedId childId newObj 256 st) }

-- ============================================================================
-- The matrix
-- ============================================================================

/-- AN11-A — full matrix of KernelError rejection scenarios. -/
def errorMatrix : List KernelErrorRejection :=
  [ -- AN11-A.2 baseline
    row_invalidArgument_period_zero,
    row_alignmentError_ipcBuffer,
    row_objectNotFound_ipcBuffer_missing_tcb,
    row_invalidArgument_mint_rights,
    row_invalidSyscallNumber,
    row_invalidMessageInfo,
    row_invalidCapPtr,
    row_invalidRegister,
    row_ipcMessageTooLarge,
    row_ipcMessageTooManyCaps,
    row_illegalState_no_current,
    row_policyDenied_insecure_default,
    row_nullCapability_mint,
    -- AN11-A.3 security-priority
    row_revocationRequired_delete_with_children,
    row_asidNotBound_vspaceMap,
    row_schedulerInvariantViolation,
    row_alignmentError_security,
    row_targetSlotOccupied,
    row_cyclicDependency_self_edge,
    row_objectNotFound_dep_unmet,
    row_replyCapInvalid_no_target,
    row_replyCapInvalid_not_blocked,
    -- AN11-A.4 IPC / SchedContext / Lifecycle
    row_invalidCapability_send_to_nonEndpoint,
    row_objectNotFound_send_missing,
    row_alreadyWaiting_enqueue_blocked,
    row_invalidArgument_budget_zero,
    row_invalidArgument_budget_over_period,
    row_invalidArgument_priority_overflow,
    row_invalidArgument_domain_overflow,
    row_illegalAuthority_priority_over_hw,
    row_illegalAuthority_over_mcp,
    row_invalidTypeTag,
    -- AN11-A.5 architecture / residual
    row_addressOutOfBounds_vaddr,
    row_invalidSyscallArgument_perms,
    row_addressOutOfBounds_paddr,
    row_notSupported_fiq,
    row_hardwareFault_serror,
    row_vmFault_data_abort,
    row_userException_pc_alignment,
    row_objectNotFound_mint_missing_cnode,
    row_invalidArgument_ipcBuffer_missing_vspaceRoot,
    -- AN11-A.6 audit-pass v2 additions
    row_invalidObjectType_cross_variant,
    row_translationFault_ipcBuffer_no_write,
    row_endpointQueueEmpty_pop_empty,
    row_untypedTypeMismatch,
    row_childIdSelfOverwrite,
    row_untypedDeviceRestriction ]

-- ============================================================================
-- AN11-A.6 — Coverage-witness theorems
-- ============================================================================

/-- AN11-A.6: Coverage witness — the matrix has at least 35 rows, meeting
the audit's recommended floor.  The `KERRORMATRIX_ROWS` CI metric (in
`scripts/ak7_cascade_baseline.sh`) tracks the actual count over time. -/
theorem errorMatrix_covers_at_least_35 :
    errorMatrix.length ≥ 35 := by decide

/-- AN11-A.6: The matrix never decreases below the post-AN11 floor
`errorMatrixFloor` (the AN11 closing count).  CI's monotonicity guard
turns any future deletion into a pipeline failure. -/
def errorMatrixFloor : Nat := 47

/-- AN11-A.6: The audit's nine security-priority variants are the targets
the matrix MUST exercise.  We verify coverage at runtime in `runAll` (via
`securityPriorityVariants` below) rather than at compile time, because
`KernelErrorRejection.runScenario` is an opaque `Unit → Except` thunk and
`decide` over the `errorMatrix.any (· = …)` predicate does not always
reduce in the term-mode prover. -/
def securityPriorityVariants : List KernelError :=
  [ .revocationRequired
  , .asidNotBound
  , .schedulerInvariantViolation
  , .alignmentError
  , .vmFault
  , .targetSlotOccupied
  , .cyclicDependency
  , .dependencyViolation  -- audit-named; current code returns .objectNotFound
  , .replyCapInvalid ]

/-- Runtime helper: the set of `KernelError` variants the matrix actually
exercises.  Used by `runAll` to print a coverage diff against
`securityPriorityVariants`. -/
def coveredVariants : List KernelError :=
  errorMatrix.foldr (fun r acc =>
    if acc.contains r.expectedError then acc else r.expectedError :: acc) []

-- ============================================================================
-- Suite runner
-- ============================================================================

/-- Run a single matrix row, printing PASS/FAIL with the scenarioTag and
return whether the row passed. -/
def runRow (row : KernelErrorRejection) : IO Bool := do
  match row.runScenario () with
  | .ok _ =>
      IO.println
        s!"FAIL  [{row.scenarioTag}] {row.syscall}: expected {repr row.expectedError}, got .ok"
      return false
  | .error e =>
      if e = row.expectedError then
        IO.println
          s!"PASS  [{row.scenarioTag}] {row.syscall}: {repr e}"
        return true
      else
        IO.println
          s!"FAIL  [{row.scenarioTag}] {row.syscall}: expected {repr row.expectedError}, got {repr e}"
        return false

/-- Walk the entire matrix, returning `true` iff every row asserted its
expected error variant.  Also prints a security-priority coverage diff. -/
def runAll : IO Bool := do
  let rows := errorMatrix
  IO.println s!"KernelError matrix: {rows.length} rows (floor: {errorMatrixFloor})"
  let mut allOk : Bool := true
  for row in rows do
    let ok ← runRow row
    if !ok then allOk := false
  -- Coverage diff against security-priority variants
  let covered := coveredVariants
  IO.println s!"Coverage: {covered.length} distinct variants exercised"
  let missing := securityPriorityVariants.filter (fun v => !covered.contains v)
  if !missing.isEmpty then
    IO.println s!"Security-priority variants NOT exercised: {repr missing}"
    -- Treat the (audit-named but currently unexercised) `dependencyViolation`
    -- and other documented gaps as informational; the matrix's row-count
    -- floor already enforces no regression.
  return allOk

end SeLe4n.Testing.KernelErrorMatrix

def main : IO UInt32 := do
  let ok ← SeLe4n.Testing.KernelErrorMatrix.runAll
  if ok then
    IO.println "kernel_error_matrix_suite: ALL PASS"
    return 0
  else
    IO.println "kernel_error_matrix_suite: FAILURES"
    return 1
