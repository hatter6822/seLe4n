-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.FFI
import SeLe4n.Testing.StateBuilder

/-!
# Syscall return ABI suite (WS-RA)

## RA.E.1 — the observable-failure witness, INVERTED at the flip

This suite landed before any of WS-RA's implementation, asserting the
defect (plan §1.2) as pre-migration witnesses: `syscallDispatchFromAbi`
ended with `encodeOk (readReturnValue st' tid)`, nothing wrote `gpr ⟨0⟩`,
and userspace's `decode_response` read `regs[0] != 0` as the error
discriminant — so a successful syscall's capability pointer decoded as a
`KernelError`, and the signal-before-wait badge round trip provably lost
the badge (SM9.C.0).

**The flip inverted every one of those assertions in the same commit that
changed the behaviour** — this file's history is the workstream's witness
that it fixed something observable.  What the same scenarios now assert:

* §4 — a successful `Unit` syscall returns the **zero frame** (`x0 = 0`,
  success label), which userspace decodes as a value, whatever the
  capability pointer was.
* §5 — the signal-before-wait badge round trip **delivers**: the wait's
  outcome carries the badge in `x0`, and `badge()` (which now reads `x0`)
  hands back exactly the signalled value.
* §6 — the bit-63 aliasing is structurally gone: two badges differing
  only at bit 63 produce two distinct frames, and the full-width badge
  survives the round trip.  The retired hazard stays on the record as
  `Architecture.bit63Encoding_not_injective_on_badges`.
* §7 — the blocked outcome: `.notificationWait` with no pending badge
  blocks the caller, and the boundary hands back `.blocks` — no frame
  exists for the caller (plan §3.5; delivery is the SM10.1 context
  restore's).

§2's decoder is a byte-faithful Lean mirror of the **new**
`rust/sele4n-abi/src/decode.rs` (the `AbiRoundtripSuite`
simulate-the-Rust-side idiom, in the return direction), so these round
trips exercise the same layout rules the real userspace decoder applies.

Plan: `docs/planning/SYSCALL_RETURN_ABI_PLAN.md` §1.2, RA.E.1, RA.E.2.
-/

namespace SeLe4n.Testing.SyscallReturnAbi

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Platform.FFI

-- ============================================================================
-- §1  Surface anchors — the convention's seam
-- ============================================================================

#check @SeLe4n.Platform.FFI.syscallDispatchFromAbi
#check @SeLe4n.Platform.FFI.syscallReturnOutcome
#check @SeLe4n.Platform.FFI.readReturnValue
#check @SeLe4n.Platform.FFI.readReturnValue_eq_readReturnFrame_x0
#check @SeLe4n.Kernel.Architecture.SyscallOutcome
#check @SeLe4n.Kernel.Architecture.errorFrame
#check @SeLe4n.Kernel.Architecture.errorLabel_never_zero
#check @SeLe4n.Kernel.Architecture.writeReturnFrameToTcb
#check @SeLe4n.Kernel.Architecture.readReturnFrame_writeReturnFrame
#check @SeLe4n.Kernel.Architecture.bit63Encoding_not_injective_on_badges
-- RA.B.5b — the blocked-waiter staging seam
#check @SeLe4n.Kernel.Architecture.stageWokenDelivery
#check @SeLe4n.Kernel.Architecture.stageWokenSendCompletion
#check @SeLe4n.Kernel.Architecture.stageWokenSendCompletion_stages_zero
#check @SeLe4n.Kernel.Architecture.blockedReturn_staged_in_waiter_frame
#check @SeLe4n.Kernel.Architecture.blockedUnitReturn_staged_in_sender_frame
-- PR #866 round-2 — the transfer-honesty surface (installed, never requested)
#check @SeLe4n.Model.CapTransferSummary.installedCount
#check @SeLe4n.Kernel.Architecture.returnMessageInfo_extraCaps_le_installed
#check @SeLe4n.Kernel.Architecture.returnMessageInfo_extraCaps_zero
-- RA.B.8 — the per-arm shape-coherence family (over the live dispatch arms)
#check @SeLe4n.Kernel.dispatchArm_notificationWait_matches_returnShape
#check @SeLe4n.Kernel.dispatchArm_serviceQuery_matches_returnShape
#check @SeLe4n.Kernel.dispatchArm_receive_matches_returnShape
#check @SeLe4n.Kernel.dispatchArm_replyRecv_matches_returnShape
#check @SeLe4n.Kernel.dispatchArm_call_frame_delivered_by_reply

private def assertBool (label : String) (b : Bool) : IO Unit :=
  if b then IO.println s!"  PASS: {label}"
  else throw (IO.userError s!"  FAIL: {label}")

-- ============================================================================
-- §2  Byte-faithful mirror of the NEW `decode.rs::decode_response`
-- ============================================================================

/-- What the post-flip Rust userspace decoder concludes from the post-trap
register file.  Mirrors the WS-RA `decode_response` exactly:

* `x1` must decode as a well-formed `MessageInfo` (fail-closed
  `InvalidMessageInfo` otherwise — the RA.C.7 width guard);
* a label below `errorLabelBase` → a delivery: `x0` is the full-width
  value, `regs[2..5]` the message registers, and the label is the delivered
  message's own (`0` on every kernel path but a fault delivery — ABI v3,
  WS-RR RR4);
* a label at or above `errorLabelBase` → `KernelError` discriminant
  `label - errorLabelBase`, unknown discriminants collapsing to an error
  either way. -/
inductive RustDecoded where
  | err (disc : Nat)
  | errUndecodableX1
  | ok (x0 : UInt64) (msgRegs : Array UInt64)
  deriving Repr, DecidableEq

private def rustDecodeResponse (regs : Array UInt64) : RustDecoded :=
  match MessageInfo.decode regs[1]!.toNat with
  | none => .errUndecodableX1
  | some mi =>
      if Kernel.Architecture.errorLabelBase ≤ mi.label then
        .err (mi.label - Kernel.Architecture.errorLabelBase)
      else .ok regs[0]! #[regs[2]!, regs[3]!, regs[4]!, regs[5]!]

/-- The post-trap register file after the WS-RA writeback: the trap layer
restores the full six-register frame for a `returns` outcome (`trap.rs`'s
`set_return_frame`). -/
private def postTrapRegs (f : Kernel.Architecture.SyscallReturnFrame) :
    Array UInt64 :=
  #[f.x0, f.x1, f.x2, f.x3, f.x4, f.x5]

-- ============================================================================
-- §3  Fixture — a state on which the live checked dispatch path SUCCEEDS
-- ============================================================================

private def callerTid : SeLe4n.ThreadId := ⟨900⟩
private def callerCn  : SeLe4n.ObjId    := ⟨901⟩
private def callerVsp : SeLe4n.ObjId    := ⟨902⟩
private def ntfnId    : SeLe4n.ObjId    := ⟨903⟩

/-- The capability pointer — **deliberately nonzero**: under the retired
convention a successful syscall handed this value back as its "return"
and userspace decoded it as a `KernelError`.  Slot 5 of a depth-4 /
radix-4 / guard-0 CNode resolves from CPtr 5. -/
private def capPtrValue : Nat := 5

private def signalledBadge : Nat := 42

private def ntfnCap : Capability :=
  { target := .object ntfnId,
    rights := AccessRightSet.ofList [.read, .write] }

/-- Every entity labelled `kernelTrusted` — distinguishable from
`publicLabel` at all three sentinel probes, so `isInsecureDefaultContext`
does not fire, and uniform, so every flow gate on the dispatch path is
reflexively satisfied. -/
private def trustedLabeling : LabelingContext :=
  { objectLabelOf   := fun _ => SecurityLabel.kernelTrusted
    threadLabelOf   := fun _ => SecurityLabel.kernelTrusted
    endpointLabelOf := fun _ => SecurityLabel.kernelTrusted
    serviceLabelOf  := fun _ => SecurityLabel.kernelTrusted }

private def witnessState : SystemState :=
  BootstrapBuilder.empty
    |>.withObject callerVsp (.vspaceRoot { asid := SeLe4n.ASID.ofNat 7, mappings := {} })
    |>.withObject callerCn (.cnode
        { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
          slots := SeLe4n.UniqueSlotMap.ofListWF
            [(SeLe4n.Slot.ofNat capPtrValue, ntfnCap)] })
    |>.withObject ntfnId (.notification
        { state := .idle, waitingThreads := SeLe4n.NoDupList.empty,
          pendingBadge := none, boundTCB := none })
    |>.withObject callerTid.toObjId (.tcb
        { tid := callerTid, priority := ⟨40⟩, domain := ⟨0⟩,
          cspaceRoot := callerCn, vspaceRoot := callerVsp,
          ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := .ready,
          threadState := .Running })
    |>.withRunnable [callerTid]
    |>.withCurrent (some callerTid)
    |>.build

/-- Drive the full FFI dispatch seam exactly as the export does: caller
resolved via `currentOnCore`, args staged by `writeFfiRegistersToTcb`, the
checked entry, and the WS-RA outcome exit (`syscallReturnOutcome`). -/
private def dispatchFromAbi (syscallId : Nat) (msgInfoRaw : UInt64)
    (x2 : UInt64) (st : SystemState) :
    Except KernelError (Kernel.Architecture.SyscallOutcome × SystemState) :=
  SeLe4n.Platform.FFI.syscallDispatchFromAbi trustedLabeling
    SeLe4n.Kernel.Concurrency.bootCoreId
    syscallId.toUInt32 msgInfoRaw
    capPtrValue.toUInt64 msgInfoRaw x2 0 0 0
    0 st

-- ============================================================================
-- §3b  Two-thread fixture — the RA.B.5b blocked orderings (wait-before-signal,
--       blocked receiver, blocked sender, reply delivery)
-- ============================================================================

private def peerTid  : SeLe4n.ThreadId := ⟨904⟩
private def epId     : SeLe4n.ObjId    := ⟨905⟩
private def replyRid : SeLe4n.ReplyId  := ⟨906⟩

private def epCapPtr    : Nat := 6
private def replyCapPtr : Nat := 7
private def epBadgeVal  : Nat := 9
private def replyBadgeVal : Nat := 3

private def epCap : Capability :=
  { target := .object epId,
    rights := AccessRightSet.ofList [.read, .write, .grant],
    badge := some (Badge.ofNatMasked epBadgeVal) }

private def replyCapability : Capability :=
  { target := .replyCap replyRid,
    rights := AccessRightSet.ofList [.read, .write, .grant],
    badge := some (Badge.ofNatMasked replyBadgeVal) }

private def selfTcbCapPtr : Nat := 8

/-- A capability to the caller's own TCB — the 9g self-suspend witness for
plan §3.5's parenthetical: a self-`.tcbSuspend` deschedules without
IPC-blocking, so its outcome is `returns` with the constructed unit frame
(the value the thread should observe when later resumed). -/
private def selfTcbCap : Capability :=
  { target := .object callerTid.toObjId,
    rights := AccessRightSet.ofList [.read, .write] }

private def epCapNoGrantPtr : Nat := 9
private def payloadCapPtr   : Nat := 10

/-- The same endpoint WITHOUT `.grant` — the 9h honesty witness's send cap:
a transfer through it is grant-denied while the message itself delivers. -/
private def epCapNoGrant : Capability :=
  { target := .object epId,
    rights := AccessRightSet.ofList [.read, .write],
    badge := some (Badge.ofNatMasked epBadgeVal) }

/-- The capability the 9h send carries as its ONE extra cap — a read cap on
the notification object (distinctive and harmless), resolved from the
sender's CSpace at `payloadCapPtr`. -/
private def payloadCapability : Capability :=
  { target := .object ntfnId,
    rights := AccessRightSet.ofList [.read] }

private def core1 : SeLe4n.Kernel.Concurrency.CoreId := ⟨1, by decide⟩

/-- The shared CNode with all the capabilities (the §3 notification cap,
the endpoint and reply caps the blocked orderings need, and the 9h
transfer pair: the no-grant endpoint cap + the payload cap).  Slot 0 is
deliberately free — it is the default `capRecvSlot` the granted transfer
installs into. -/
private def sharedCn : SeLe4n.Model.CNode :=
  { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
    slots := SeLe4n.UniqueSlotMap.ofListWF
      [(SeLe4n.Slot.ofNat capPtrValue, ntfnCap),
       (SeLe4n.Slot.ofNat epCapPtr, epCap),
       (SeLe4n.Slot.ofNat replyCapPtr, replyCapability),
       (SeLe4n.Slot.ofNat selfTcbCapPtr, selfTcbCap),
       (SeLe4n.Slot.ofNat epCapNoGrantPtr, epCapNoGrant),
       (SeLe4n.Slot.ofNat payloadCapPtr, payloadCapability)] }

/-- Two threads on two cores: `callerTid` current on the boot core (the
thread that blocks), `peerTid` current on core 1 (the thread whose
syscall unblocks it) — so both legs run through the live per-core
dispatch with no scheduler surgery between them. -/
private def twoThreadState : SystemState :=
  let base := BootstrapBuilder.empty
    |>.withObject callerVsp (.vspaceRoot { asid := SeLe4n.ASID.ofNat 7, mappings := {} })
    |>.withObject callerCn (.cnode sharedCn)
    |>.withObject ntfnId (.notification
        { state := .idle, waitingThreads := SeLe4n.NoDupList.empty,
          pendingBadge := none, boundTCB := none })
    |>.withObject epId (.endpoint {})
    |>.withObject callerTid.toObjId (.tcb
        { tid := callerTid, priority := ⟨40⟩, domain := ⟨0⟩,
          cspaceRoot := callerCn, vspaceRoot := callerVsp,
          ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := .ready,
          threadState := .Running })
    |>.withObject peerTid.toObjId (.tcb
        { tid := peerTid, priority := ⟨40⟩, domain := ⟨0⟩,
          cspaceRoot := callerCn, vspaceRoot := callerVsp,
          ipcBuffer := SeLe4n.VAddr.ofNat 8192, ipcState := .ready,
          threadState := .Running })
    |>.withRunnable [callerTid]
    |>.withCurrent (some callerTid)
    |>.build
  { base with scheduler := base.scheduler.setCurrentOnCore core1 (some peerTid) }

/-- The reply-delivery fixture: `callerTid` already `.blockedOnReply` (a
completed `.call` rendezvous) linked to the reply object `peerTid` holds
the capability for — the state from which `.reply` / `.replyRecv` deliver
`.call`'s `.message` frame (§3.5: a call never returns at its own
boundary). -/
private def replyPendingState : SystemState :=
  let base := BootstrapBuilder.empty
    |>.withObject callerVsp (.vspaceRoot { asid := SeLe4n.ASID.ofNat 7, mappings := {} })
    |>.withObject callerCn (.cnode sharedCn)
    |>.withObject ntfnId (.notification
        { state := .idle, waitingThreads := SeLe4n.NoDupList.empty,
          pendingBadge := none, boundTCB := none })
    |>.withObject epId (.endpoint {})
    |>.withObject callerTid.toObjId (.tcb
        { tid := callerTid, priority := ⟨40⟩, domain := ⟨0⟩,
          cspaceRoot := callerCn, vspaceRoot := callerVsp,
          ipcBuffer := SeLe4n.VAddr.ofNat 4096,
          ipcState := .blockedOnReply epId (some peerTid),
          threadState := .BlockedReply,
          replyObject := some replyRid })
    |>.withObject peerTid.toObjId (.tcb
        { tid := peerTid, priority := ⟨40⟩, domain := ⟨0⟩,
          cspaceRoot := callerCn, vspaceRoot := callerVsp,
          ipcBuffer := SeLe4n.VAddr.ofNat 8192, ipcState := .ready,
          threadState := .Running })
    |>.withObject replyRid.toObjId (.reply
        { replyId := replyRid, caller := some callerTid })
    |>.build
  { base with scheduler := base.scheduler.setCurrentOnCore core1 (some peerTid) }

/-- The `dispatchFromAbi` driver generalised to an executing core and the
full inline register window — the RA.B.5b scenarios interleave syscalls
from two cores. -/
private def dispatchFromAbiOn (core : SeLe4n.Kernel.Concurrency.CoreId)
    (syscallId : Nat) (msgInfoRaw : UInt64) (capPtr : UInt64)
    (x2 x3 x4 : UInt64) (st : SystemState) :
    Except KernelError (Kernel.Architecture.SyscallOutcome × SystemState) :=
  SeLe4n.Platform.FFI.syscallDispatchFromAbi trustedLabeling core
    syscallId.toUInt32 msgInfoRaw capPtr msgInfoRaw x2 x3 x4 0
    0 st

-- ============================================================================
-- §4  INVERTED witness A — a successful Unit syscall decodes as a VALUE
-- ============================================================================

/-- `.notificationSignal` (a `Unit`-returning syscall) through the live
checked dispatch.  Pre-flip this returned the caller's capability pointer
(5), which the old decoder read as `KernelError` discriminant 5.  Now:
the boundary composes the **zero frame** — `x0 = 0`, success label —
whatever the staged registers hold (`frameForShape`'s constructed read),
and the decoder reads a value. -/
private def runUnitReturnWitness : IO Unit := do
  IO.println "-- §4 inverted witness A: successful Unit syscall decodes as a value"
  -- MessageInfo {length := 1, extraCaps := 0, label := 0} encodes to 1;
  -- x2 carries the badge argument for the signal.
  let msgInfoRaw : UInt64 := 1
  match dispatchFromAbi SyscallId.notificationSignal.toNat msgInfoRaw
      signalledBadge.toUInt64 witnessState with
  | .error e =>
      assertBool s!"the signal dispatch reaches the FFI seam (got .error {reprStr e})" false
  | .ok (outcome, st') => do
      -- Control: the syscall genuinely succeeded — the badge landed.
      assertBool "control: the signal committed (pendingBadge = 42)"
        (match st'.getNotification? ntfnId with
          | some n => n.pendingBadge == some (Badge.ofNatMasked signalledBadge)
          | none => false)
      match outcome with
      | .blocks =>
          assertBool "a signal never blocks the signaller" false
      | .returns frame => do
          assertBool "FLIPPED: the Unit frame is the zero frame, not the cap pointer"
            (frame == .zero && frame.x0 != capPtrValue.toUInt64)
          assertBool "FLIPPED: userspace decodes the success as a VALUE (0)"
            (rustDecodeResponse (postTrapRegs frame) == .ok 0 #[0, 0, 0, 0])

-- ============================================================================
-- §5  INVERTED witness B — signal-before-wait DELIVERS the badge (SM9.C.0)
-- ============================================================================

/-- The ordinary badge round trip: signal 42, then `.notificationWait`.
Pre-flip the badge was consumed and delivered nowhere (the register file
provably nowhere contained 42, and `badge()` read the caller's own `x1`).
Now the wait's arm stages `returnFrameOfBadge`, the boundary reads it
back, and `badge()` — reading `x0` — hands back exactly 42. -/
private def runBadgeDeliveryWitness : IO Unit := do
  IO.println "-- §5 inverted witness B: the signal-before-wait badge round trip DELIVERS"
  let msgInfoRaw : UInt64 := 1
  match dispatchFromAbi SyscallId.notificationSignal.toNat msgInfoRaw
      signalledBadge.toUInt64 witnessState with
  | .error e =>
      assertBool s!"the signal leg dispatches (got .error {reprStr e})" false
  | .ok (_, stSignalled) => do
      -- The wait leg: msgInfo {length := 0} encodes to 0.
      match dispatchFromAbi SyscallId.notificationWait.toNat 0 0 stSignalled with
      | .error e =>
          assertBool s!"the wait leg dispatches (got .error {reprStr e})" false
      | .ok (outcome, st') => do
          assertBool "control: the wait consumed the pending badge"
            (match st'.getNotification? ntfnId with
              | some n => n.pendingBadge == none
              | none => false)
          match outcome with
          | .blocks =>
              assertBool "a pending badge means the wait returns, not blocks" false
          | .returns frame => do
              assertBool "FLIPPED: the wait's frame carries the badge in x0"
                (frame.x0 == signalledBadge.toUInt64)
              assertBool "FLIPPED: x1 is the success label (badge shape has no message)"
                (frame.x1 == 0)
              match rustDecodeResponse (postTrapRegs frame) with
              | .ok x0 _ =>
                  assertBool "FLIPPED: badge() reads x0 = 42 — delivered end to end"
                    (x0 == signalledBadge.toUInt64)
              | _ =>
                  assertBool "the delivered badge must decode as a success" false

-- ============================================================================
-- §6  INVERTED witness C — full-width badges survive; the aliasing is gone
-- ============================================================================

/-- Pre-flip `encodeOk` masked bit 63, collapsing distinct badges.  The
frame convention carries `x0` at full width: two badges differing only at
bit 63 produce two distinct frames, and the high badge survives the
decode round trip bit for bit.  The retired hazard stays on the record as
`Architecture.bit63Encoding_not_injective_on_badges`. -/
private def runFullWidthBadgeWitness : IO Unit := do
  IO.println "-- §6 inverted witness C: full-width badges survive, the bit-63 aliasing is gone"
  let lowBadge  : UInt64 := 0x42
  let highBadge : UInt64 := 0x8000000000000042
  assertBool "control: the two badge values are distinct"
    (lowBadge != highBadge)
  let lowFrame := Kernel.Architecture.returnFrameOfBadge (Badge.ofNatMasked lowBadge.toNat)
  let highFrame := Kernel.Architecture.returnFrameOfBadge (Badge.ofNatMasked highBadge.toNat)
  assertBool "FLIPPED: the two frames are distinct (no masking anywhere)"
    (lowFrame != highFrame)
  assertBool "FLIPPED: the high badge survives the decode round trip bit for bit"
    (rustDecodeResponse (postTrapRegs highFrame) == .ok highBadge #[0, 0, 0, 0])

-- ============================================================================
-- §7  The blocked outcome — no frame exists for a blocked caller
-- ============================================================================

/-- `.notificationWait` on an idle notification (no pending badge): the
caller blocks, and the boundary's outcome is `.blocks` — the badge does
not exist yet, no frame may be written for the caller, and the staged
frame is the unblocking transition's to write with delivery at the
SM10.1 context restore (plan §3.5). -/
private def runBlockedOutcomeWitness : IO Unit := do
  IO.println "-- §7 the blocked outcome: a wait with no pending badge blocks, no frame"
  match dispatchFromAbi SyscallId.notificationWait.toNat 0 0 witnessState with
  | .error e =>
      assertBool s!"the blocking wait dispatches (got .error {reprStr e})" false
  | .ok (outcome, st') => do
      assertBool "control: the caller is blocked on the notification"
        (match st'.objects[callerTid.toObjId]? with
          | some (.tcb tcb) => tcb.ipcState == .blockedOnNotification ntfnId
          | _ => false)
      assertBool "the outcome is .blocks — no frame exists for the caller"
        (outcome == .blocks)

-- ============================================================================
-- §7b  RA.B.5b pure scenarios (shared by the §9 assertions and the §8 fixture)
-- ============================================================================

/-- Read a thread's staged frame out of a scenario state. -/
private def stagedFrame (st : SystemState) (tid : SeLe4n.ThreadId) :
    Kernel.Architecture.SyscallReturnFrame :=
  Kernel.Architecture.readReturnFrame st tid

/-- 9a: wait-before-signal.  The caller blocks on the idle notification
(core 0); the peer signals badge 42 (core 1); the caller's staged frame is
the badge frame.  Returns (pre-signal staged x0, post-signal frame). -/
private def waitThenSignalScenario :
    Except KernelError (UInt64 × Kernel.Architecture.SyscallReturnFrame) := do
  let (out1, st1) ← dispatchFromAbiOn SeLe4n.Kernel.Concurrency.bootCoreId
    SyscallId.notificationWait.toNat 0 capPtrValue.toUInt64 0 0 0 twoThreadState
  if out1 != .blocks then throw .illegalState
  let preStagedX0 := (stagedFrame st1 callerTid).x0
  let (_, st2) ← dispatchFromAbiOn core1
    SyscallId.notificationSignal.toNat 1 capPtrValue.toUInt64
    signalledBadge.toUInt64 0 0 st1
  pure (preStagedX0, stagedFrame st2 callerTid)

/-- 9b: blocked receiver.  The caller blocks in `.receive` on the empty
endpoint (core 0); the peer sends `[7, 8]` under the badge-9 endpoint cap
(core 1); the caller's staged frame is the message frame. -/
private def receiveThenSendScenario :
    Except KernelError (Kernel.Architecture.SyscallReturnFrame) := do
  let (out1, st1) ← dispatchFromAbiOn SeLe4n.Kernel.Concurrency.bootCoreId
    SyscallId.receive.toNat 0 epCapPtr.toUInt64 0 0 0 twoThreadState
  if out1 != .blocks then throw .illegalState
  let (_, st2) ← dispatchFromAbiOn core1
    SyscallId.send.toNat 2 epCapPtr.toUInt64 7 8 0 st1
  pure (stagedFrame st2 callerTid)

/-- 9c: blocked plain sender.  The peer's send parks (no receiver, core 1);
the caller's `.receive` consumes it (core 0) — the caller's own outcome is
the message frame (the immediate half), and the completed **sender**'s
staged frame is the zero frame (unit success).  Returns (pre-receive
sender staged x0, the receive outcome, post-receive sender frame). -/
private def sendThenReceiveScenario :
    Except KernelError (UInt64 × Kernel.Architecture.SyscallOutcome ×
      Kernel.Architecture.SyscallReturnFrame) := do
  let (out1, st1) ← dispatchFromAbiOn core1
    SyscallId.send.toNat 2 epCapPtr.toUInt64 7 8 0 twoThreadState
  if out1 != .blocks then throw .illegalState
  let preStagedX0 := (stagedFrame st1 peerTid).x0
  let (out2, st2) ← dispatchFromAbiOn SeLe4n.Kernel.Concurrency.bootCoreId
    SyscallId.receive.toNat 0 epCapPtr.toUInt64 0 0 0 st1
  pure (preStagedX0, out2, stagedFrame st2 peerTid)

/-- 9d: the reply delivery — `.call`'s `.message` frame.  The caller is
already `.blockedOnReply` linked to the reply object; the peer replies
`[21, 22]` through the badge-3 reply cap (core 1); the caller's staged
frame is the reply message frame.  Returns (the caller's post ipcState is
`.ready`, its staged frame). -/
private def replyDeliveryScenario :
    Except KernelError (Bool × Kernel.Architecture.SyscallReturnFrame) := do
  let (_, st1) ← dispatchFromAbiOn core1
    SyscallId.reply.toNat 2 replyCapPtr.toUInt64 21 22 0 replyPendingState
  let ready := match st1.getTcb? callerTid with
    | some tcb => tcb.ipcState == .ready
    | none => false
  pure (ready, stagedFrame st1 callerTid)

/-- 9e: `.replyRecv` — the compound arm's reply leg stages the previous
caller's frame through `replyRecvBody`'s own composition (a distinct call
site from 9d's `.reply` arm); the receive leg blocks the server (empty
endpoint), so the server's own outcome is `.blocks`. -/
private def replyRecvDeliveryScenario :
    Except KernelError (Kernel.Architecture.SyscallOutcome ×
      Kernel.Architecture.SyscallReturnFrame) := do
  let (out1, st1) ← dispatchFromAbiOn core1
    SyscallId.replyRecv.toNat 3 epCapPtr.toUInt64
    replyCapPtr.toUInt64 31 32 replyPendingState
  pure (out1, stagedFrame st1 callerTid)

/-- 9f: `.serviceQuery` — the `.word` shape end to end (the one value
shape the blocked orderings do not exercise): a service registered on the
endpoint, resolved through the endpoint capability, its `ServiceId` staged
as the caller's return word and carried in the outcome frame — the answer
the pre-WS-RA arm computed and discarded. -/
private def queriedSid : Nat := 77

private def serviceQueryScenario :
    Except KernelError (Kernel.Architecture.SyscallOutcome × SystemState) := do
  let iface : InterfaceSpec :=
    { ifaceId := ⟨910⟩, methodCount := 1, maxMessageSize := 64,
      maxResponseSize := 64, requiresGrant := false }
  let ((), st1) ← Kernel.registerInterface iface twoThreadState
  let ((), st2) ← Kernel.registerService
    { sid := ⟨queriedSid⟩, iface := iface, endpointCap := epCap } st1
  dispatchFromAbiOn SeLe4n.Kernel.Concurrency.bootCoreId
    SyscallId.serviceQuery.toNat 0 epCapPtr.toUInt64 0 0 0 st2

/-- 9g: a **self**-`.tcbSuspend` — §3.5's parenthetical, witnessed: the
caller deschedules itself but does not IPC-block (`ipcState` stays
`.ready`), so the outcome is `returns` with the **constructed** unit
frame — which is also the value it should observe when later resumed. -/
private def selfSuspendScenario :
    Except KernelError (Kernel.Architecture.SyscallOutcome × SystemState) :=
  dispatchFromAbiOn SeLe4n.Kernel.Concurrency.bootCoreId
    SyscallId.tcbSuspend.toNat 0 selfTcbCapPtr.toUInt64 0 0 0 twoThreadState

/-- 9h: capability-transfer honesty (PR #866 round-2).  The caller blocks
in `.receive`; the peer sends body `[7]` plus ONE extra capability
(`payloadCapPtr`, resolved through the sender's own CSpace) under the
endpoint cap at `epPtr`.  The woken receiver's staged `x1` must report
the **installed** count — `0` when the transfer was grant-denied (however
many caps the delivered message still carries), `1` when it landed in the
receive slot.  Returns (staged frame, delivered `pendingMessage` cap
count, receive-slot-0 occupied?). -/
private def capsSendScenario (epPtr : Nat) :
    Except KernelError
      (Kernel.Architecture.SyscallReturnFrame × Nat × Bool) := do
  let (out1, st1) ← dispatchFromAbiOn SeLe4n.Kernel.Concurrency.bootCoreId
    SyscallId.receive.toNat 0 epCapPtr.toUInt64 0 0 0 twoThreadState
  if out1 != .blocks then throw .illegalState
  -- msgInfo {length := 1, extraCaps := 1}: MR0 (x2) is the body word 7,
  -- MR1 (x3) the extra-cap address (`decodeExtraCapAddrs` reads
  -- `msgRegs[length + i]`).
  let msgInfoRaw : UInt64 := (1 + (1 <<< 7) : Nat).toUInt64
  let (_, st2) ← dispatchFromAbiOn core1
    SyscallId.send.toNat msgInfoRaw epPtr.toUInt64 7 payloadCapPtr.toUInt64 0 st1
  let deliveredCaps := match st2.getTcb? callerTid with
    | some tcb => (tcb.pendingMessage.map (·.caps.size)).getD 0
    | none => 0
  let slot0Occupied := match st2.objects[callerCn]? with
    | some (.cnode c) => (c.slots[SeLe4n.Slot.ofNat 0]?).isSome
    | _ => false
  pure (stagedFrame st2 callerTid, deliveredCaps, slot0Occupied)

-- ============================================================================
-- §10  WS-SM SM9.A.10 — the audit reads return their computed word, end to end
-- ============================================================================
--
-- The reason the audit accessors needed WS-RA to land first.  Before the return
-- frame existed, `dispatchWithCapChecked` was `Kernel Unit` and the boundary took
-- its success value from registers no transition wrote — so a reader would have
-- gated correctly, computed correctly, and handed the caller back its **own**
-- preloaded `x0` (the capability pointer).  These assertions drive the full FFI
-- seam and check the value that comes out is the value the kernel selected.

/-- The audit capability's CNode slot — distinct from the notification cap's, so
the caller holds both and the two are told apart by *target*. -/
private def auditCapPtr : Nat := 7

private def auditCap : Capability :=
  { target := .auditTrail, rights := AccessRightSet.ofList [.read, .write] }

/-- A capability with every right, targeting an ordinary object — the shape every
thread holds to its own TCB.  The confused-deputy negative: it must be rejected
on the audit syscalls even though it carries `read` and `write`. -/
private def ordinaryCapPtr : Nat := 8

/-- PR #870 round 5: an ordinary-object capability with **no rights at all** —
wrong on both axes.  The ordering witness: before round 5 the full lookup's
rights gate answered this `.illegalAuthority` before the arm could inspect the
target; the target-first contract answers `.invalidCapability`, whatever the
rights. -/
private def rightlessCapPtr : Nat := 9

/-- PR #870 round 5: an audit-trail capability carrying only `.read` — right
kind, insufficient right for a drain.  The second gate's witness: the target
check passes, the ARM's rights check refuses `.illegalAuthority`. -/
private def readOnlyAuditCapPtr : Nat := 10

/-- The deployment that names an audit monitor.  `trustedLabeling` puts every
subject at `kernelTrusted`, which embeds to domain 3, so the caller dominates the
configured clearance and qualifies. -/
private def auditLabeling : LabelingContext :=
  { trustedLabeling with
    auditMonitorClearance := some (embedLegacyLabel SecurityLabel.kernelTrusted) }

/-- The same deployment with no monitor named — the fail-closed default. -/
private def auditUnconfiguredLabeling : LabelingContext := trustedLabeling

/-- Two recorded downgrades, well-formed at epoch 0. -/
private def auditTrailFixture : SeLe4n.Kernel.DeclassificationAuditLog :=
  [ { srcDomain := embedLegacyLabel SecurityLabel.kernelTrusted
      dstDomain := embedLegacyLabel SecurityLabel.publicLabel
      targetObject := ntfnId, authorizationBasis := .policyRule
      timestamp := 0, originatingCore := SeLe4n.Kernel.Concurrency.bootCoreId
      actor := { subject := callerTid, domain := embedLegacyLabel SecurityLabel.kernelTrusted }
      predecessorTags := SeLe4n.Kernel.DeclassificationTaint.empty }
  , { srcDomain := embedLegacyLabel SecurityLabel.kernelTrusted
      dstDomain := embedLegacyLabel SecurityLabel.publicLabel
      targetObject := callerVsp, authorizationBasis := .policyRule
      timestamp := 1, originatingCore := SeLe4n.Kernel.Concurrency.bootCoreId
      actor := { subject := callerTid,
                 domain := embedLegacyLabel SecurityLabel.kernelTrusted }
      predecessorTags := SeLe4n.Kernel.DeclassificationTaint.singleton 0 } ]

/-- `witnessState` with the audit capability minted, an ordinary all-rights
capability alongside it, and a two-entry trail already recorded. -/
private def auditWitnessState : SystemState :=
  { (BootstrapBuilder.empty
      |>.withObject callerVsp (.vspaceRoot { asid := SeLe4n.ASID.ofNat 7, mappings := {} })
      |>.withObject callerCn (.cnode
          { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
            slots := SeLe4n.UniqueSlotMap.ofListWF
              [(SeLe4n.Slot.ofNat capPtrValue, ntfnCap),
               (SeLe4n.Slot.ofNat auditCapPtr, auditCap),
               (SeLe4n.Slot.ofNat ordinaryCapPtr,
                 { target := .object ntfnId,
                   rights := AccessRightSet.ofList AccessRight.all }),
               (SeLe4n.Slot.ofNat rightlessCapPtr,
                 { target := .object ntfnId,
                   rights := AccessRightSet.ofList [] }),
               (SeLe4n.Slot.ofNat readOnlyAuditCapPtr,
                 { target := .auditTrail,
                   rights := AccessRightSet.ofList [.read] })] })
      |>.withObject ntfnId (.notification
          { state := .idle, waitingThreads := SeLe4n.NoDupList.empty,
            pendingBadge := none, boundTCB := none })
      |>.withObject callerTid.toObjId (.tcb
          { tid := callerTid, priority := ⟨40⟩, domain := ⟨0⟩,
            cspaceRoot := callerCn, vspaceRoot := callerVsp,
            ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := .ready,
            threadState := .Running })
      |>.withRunnable [callerTid]
      |>.withCurrent (some callerTid)
      |>.build) with declassificationAuditLog := auditTrailFixture }

/-- Drive the FFI seam with three inline message registers and a chosen
capability pointer — the audit reads' operand shape. -/
private def dispatchAudit (ctx : LabelingContext) (syscallId : Nat) (capPtr : Nat)
    (regCount : Nat) (r0 r1 r2 : Nat) (st : SystemState) :
    Except KernelError (Kernel.Architecture.SyscallOutcome × SystemState) :=
  -- `MessageInfo {length, extraCaps := 0, label := 0}` encodes to `length`
  -- (the §4 note pins the same identity for length 1).
  let msgInfoRaw : UInt64 := regCount.toUInt64
  SeLe4n.Platform.FFI.syscallDispatchFromAbi ctx
    SeLe4n.Kernel.Concurrency.bootCoreId
    syscallId.toUInt32 msgInfoRaw
    capPtr.toUInt64 msgInfoRaw r0.toUInt64 r1.toUInt64 r2.toUInt64 0
    0 st

/-- The `x0` a completed dispatch hands back, or `none` if it blocked/errored. -/
private def auditReturnedWord
    (r : Except KernelError (Kernel.Architecture.SyscallOutcome × SystemState)) :
    Option UInt64 :=
  match r with
  | .ok (.returns f, _) => some f.x0
  | _ => none

-- ============================================================================
-- §8  Golden fixture — the deterministic return-ABI trace (RA.E.4)
-- ============================================================================

private def hex (v : UInt64) : String :=
  s!"0x{String.ofList (Nat.toDigits 16 v.toNat)}"

private def frameCells (f : Kernel.Architecture.SyscallReturnFrame) : String :=
  s!"x0={hex f.x0} x1={hex f.x1} x2={hex f.x2} x3={hex f.x3} x4={hex f.x4} x5={hex f.x5}"

private def decodeCell (f : Kernel.Architecture.SyscallReturnFrame) : String :=
  match rustDecodeResponse (postTrapRegs f) with
  | .ok x0 _ => s!"decode=ok value={hex x0}"
  | .err d => s!"decode=err disc={d}"
  | .errUndecodableX1 => "decode=invalidMessageInfo"

private def outcomeLine (tag : String)
    (r : Except KernelError (Kernel.Architecture.SyscallOutcome × SystemState)) : String :=
  match r with
  | .error e => s!"[ret-abi] {tag}: dispatch-error {reprStr e}"
  | .ok (.blocks, _) => s!"[ret-abi] {tag}: outcome=blocks tag=1 (no frame for the caller)"
  | .ok (.returns f, _) =>
      s!"[ret-abi] {tag}: outcome=returns tag=0 {frameCells f} {decodeCell f}"

/-- The trace, computed from the live dispatch decisions — every line an
observable of the §4-§7 scenarios plus the error carriage and the version
pin, so any change in the return convention diverges the fixture. -/
private def returnAbiTraceLines : List String :=
  let signalMsgInfo : UInt64 := 1
  let signalled :=
    dispatchFromAbi SyscallId.notificationSignal.toNat signalMsgInfo
      signalledBadge.toUInt64 witnessState
  let waitAfterSignal :=
    match signalled with
    | .ok (_, st) => dispatchFromAbi SyscallId.notificationWait.toNat 0 0 st
    | e => e
  -- 57 = the full `KernelError` enumeration (discriminants 0..56, the newest
  -- being SM9.C's `.declassificationDeniedAtReceiver` at 56).  The boundary
  -- conjunct pins the count from above: when a 58th variant lands,
  -- `ofDiscriminant? 57` stops being `none`, the fixture line diverges, and
  -- this range has to move with it rather than silently under-covering.
  let labelRoundtrips :=
    (List.range 57).all fun d =>
      match SeLe4n.Model.KernelError.ofDiscriminant? d with
      | some e => Kernel.Architecture.ofErrorLabel? (Kernel.Architecture.errorLabel e) == some e
      | none => false
  let labelBoundary := (SeLe4n.Model.KernelError.ofDiscriminant? 57).isNone
  [ s!"[ret-abi] abi-version: {Kernel.Architecture.syscallAbiVersion}"
  , outcomeLine "unit signal (cap ptr 5)" signalled
  , outcomeLine "badge wait after signal 42" waitAfterSignal
  , outcomeLine "blocking wait (idle notification)"
      (dispatchFromAbi SyscallId.notificationWait.toNat 0 0 witnessState)
  , outcomeLine "abi mismatch (msgInfo 0xAAAA, x1 = msgInfo forced unequal)"
      (SeLe4n.Platform.FFI.syscallDispatchFromAbi trustedLabeling
        SeLe4n.Kernel.Concurrency.bootCoreId
        SyscallId.notificationSignal.toNat.toUInt32 0xAAAA
        capPtrValue.toUInt64 0xBBBB 0 0 0 0 0 witnessState)
  , s!"[ret-abi] error labels: all 57 discriminants round-trip = {labelRoundtrips}; 57 unassigned = {labelBoundary}"
  , s!"[ret-abi] full-width badge frame: " ++
      frameCells (Kernel.Architecture.returnFrameOfBadge
        (Badge.ofNatMasked 0x8000000000000042))
  -- RA.B.5b: the blocked orderings' staged frames, computed from the live
  -- two-core scenarios (§7b) — the unblocking syscall's staging is now an
  -- observable of the fixture.
  , (match waitThenSignalScenario with
     | .ok (_, f) => s!"[ret-abi] staged wait-before-signal badge frame: {frameCells f}"
     | .error e => s!"[ret-abi] staged wait-before-signal badge frame: dispatch-error {reprStr e}")
  , (match receiveThenSendScenario with
     | .ok f => s!"[ret-abi] staged blocked-receiver message frame: {frameCells f}"
     | .error e => s!"[ret-abi] staged blocked-receiver message frame: dispatch-error {reprStr e}")
  , (match sendThenReceiveScenario with
     | .ok (_, _, f) => s!"[ret-abi] staged completed-sender unit frame: {frameCells f}"
     | .error e => s!"[ret-abi] staged completed-sender unit frame: dispatch-error {reprStr e}")
  -- RA.B.8: the `.word` shape's live outcome (the fourth value shape,
  -- completing the fixture's coverage of the value surface).
  , outcomeLine "word query (registered service 77)" serviceQueryScenario
  -- WS-SM SM9.A.10: the two audit accessors, the sixth and seventh members of
  -- the value-returning surface.  Recorded here rather than only asserted,
  -- because "the reader hands back a word it computed rather than the caller's
  -- own `x0`" is exactly the kind of claim a fixture makes checkable in a diff.
  , outcomeLine "audit status (visible length 2, monitor)"
      (dispatchAudit auditLabeling SyscallId.auditRead.toNat auditCapPtr 3
        (Kernel.encodeAuditReadOp .status).1 0 0 auditWitnessState)
  , outcomeLine "audit drain of one entry (new visible length 1)"
      (dispatchAudit auditLabeling SyscallId.auditDrain.toNat auditCapPtr 1
        1 0 0 auditWitnessState)
  -- PR #866 round-2: the transfer-honesty observable — a grant-denied
  -- transfer's staged frame reports extraCaps 0 (x1 = 1, length only),
  -- however many caps the delivered message still carries.
  , (match capsSendScenario epCapNoGrantPtr with
     | .ok (f, _, _) => s!"[ret-abi] staged grant-denied transfer frame (installed extraCaps 0): {frameCells f}"
     | .error e => s!"[ret-abi] staged grant-denied transfer frame (installed extraCaps 0): dispatch-error {reprStr e}")
  ]

private def fixturePath : String := "tests/fixtures/syscall_return_abi.expected"

/-- §8: print the deterministic return-ABI trace and verify it byte-for-byte
against the golden fixture.  The lines print before the (strict)
verification, so the fixture is regenerable via
`lake exe syscall_return_abi_suite | grep '^\[ret-abi\]'` (brackets escaped —
see the SmpIpcSuite note). -/
private def runTraceFixtureCheck : IO Unit := do
  IO.println "-- §8 deterministic return-ABI trace (RA.E.4 fixture)"
  for l in returnAbiTraceLines do
    IO.println l
  let expectedContent := String.intercalate "\n" returnAbiTraceLines ++ "\n"
  let fixtureExists ← System.FilePath.pathExists fixturePath
  if !fixtureExists then
    IO.println s!"  FAIL: golden fixture {fixturePath} not found"
    IO.println s!"        regenerate: lake exe syscall_return_abi_suite | grep '^\\[ret-abi\\]' > {fixturePath}"
    throw (IO.userError s!"missing fixture {fixturePath}")
  let actual ← IO.FS.readFile fixturePath
  if actual == expectedContent then
    IO.println s!"  PASS: return-ABI trace matches golden fixture {fixturePath}"
  else
    IO.println s!"  FAIL: return-ABI trace differs from golden fixture {fixturePath}"
    IO.println s!"        regenerate: lake exe syscall_return_abi_suite | grep '^\\[ret-abi\\]' > {fixturePath}"
    IO.println s!"        (then refresh {fixturePath}.sha256 — see tests/fixtures/README.md)"
    throw (IO.userError "return-ABI trace fixture mismatch")

-- ============================================================================
-- §9  RA.B.5b — the blocked orderings: the unblocking syscall stages the
--      woken thread's frame (delivery is the SM10.1 context restore)
-- ============================================================================

private def runBlockedWaiterStagingWitnesses : IO Unit := do
  IO.println "-- §9 RA.B.5b: the unblocking syscall stages the blocked waiter's frame"
  -- 9a — wait-before-signal (the acceptance-gate split's staged half)
  match waitThenSignalScenario with
  | .error e => assertBool s!"9a dispatches (got .error {reprStr e})" false
  | .ok (preX0, frame) => do
      assertBool "9a control: pre-signal the blocked waiter's staged x0 is its own cap ptr (stale args — the §3.5 hazard)"
        (preX0 == capPtrValue.toUInt64)
      assertBool "9a: the signal staged the badge frame into the waiter (x0 = 42)"
        (frame.x0 == signalledBadge.toUInt64)
      assertBool "9a: the staged x1 is the success label"
        (frame.x1 == 0)
      assertBool "9a: the staged frame decodes as the badge, end to end"
        (rustDecodeResponse (postTrapRegs frame) == .ok signalledBadge.toUInt64 #[0, 0, 0, 0])
  -- 9b — blocked receiver woken by a send
  match receiveThenSendScenario with
  | .error e => assertBool s!"9b dispatches (got .error {reprStr e})" false
  | .ok frame => do
      assertBool "9b: the send staged the message frame into the blocked receiver (x0 = badge 9)"
        (frame.x0 == epBadgeVal.toUInt64)
      assertBool "9b: the staged message registers are the sent payload (x2 = 7, x3 = 8)"
        (frame.x2 == 7 && frame.x3 == 8)
  -- 9c — blocked plain sender completed by a receive
  match sendThenReceiveScenario with
  | .error e => assertBool s!"9c dispatches (got .error {reprStr e})" false
  | .ok (preX0, out2, senderFrame) => do
      assertBool "9c control: pre-receive the parked sender's staged x0 is its own cap ptr"
        (preX0 == epCapPtr.toUInt64)
      assertBool "9c: the receive's own outcome is the consumed message (immediate half)"
        (match out2 with
          | .returns f => f.x0 == epBadgeVal.toUInt64 && f.x2 == 7 && f.x3 == 8
          | .blocks => false)
      assertBool "9c: the completed sender's staged frame is the unit zero frame"
        (senderFrame == .zero)
  -- 9d — the reply delivers `.call`'s frame
  match replyDeliveryScenario with
  | .error e => assertBool s!"9d dispatches (got .error {reprStr e})" false
  | .ok (ready, frame) => do
      assertBool "9d control: the reply woke the blocked caller (.ready)" ready
      assertBool "9d: the caller's staged frame is the reply message (x0 = reply-cap badge 3)"
        (frame.x0 == replyBadgeVal.toUInt64)
      assertBool "9d: the staged payload is the reply body (x2 = 21, x3 = 22)"
        (frame.x2 == 21 && frame.x3 == 22)
  -- 9e — replyRecv's own staging composition
  match replyRecvDeliveryScenario with
  | .error e => assertBool s!"9e dispatches (got .error {reprStr e})" false
  | .ok (out1, frame) => do
      assertBool "9e: the server's receive leg blocks (empty endpoint)"
        (out1 == .blocks)
      assertBool "9e: replyRecv staged the previous caller's frame (x2 = 31, x3 = 32, badge 3)"
        (frame.x0 == replyBadgeVal.toUInt64 && frame.x2 == 31 && frame.x3 == 32)
  -- 9f — the `.word` shape end to end (the value shape §9a-§9e do not cover)
  match serviceQueryScenario with
  | .error e => assertBool s!"9f dispatches (got .error {reprStr e})" false
  | .ok (out, st') => do
      assertBool "9f: the query's outcome carries the resolved ServiceId in x0"
        (match out with
          | .returns f => f.x0 == queriedSid.toUInt64 && f.x1 == 0
          | .blocks => false)
      assertBool "9f: the arm staged the word (the boundary read is of fresh data)"
        ((stagedFrame st' callerTid).x0 == queriedSid.toUInt64)
      assertBool "9f: the word decodes as a success value, end to end"
        (match out with
          | .returns f =>
              rustDecodeResponse (postTrapRegs f) == .ok queriedSid.toUInt64 #[0, 0, 0, 0]
          | .blocks => false)
  -- 9g — the self-suspend returns-unit split (§3.5's parenthetical)
  match selfSuspendScenario with
  | .error e => assertBool s!"9g dispatches (got .error {reprStr e})" false
  | .ok (out, st') => do
      assertBool "9g control: the self-suspend descheduled the caller (current cleared)"
        ((st'.scheduler.currentOnCore SeLe4n.Kernel.Concurrency.bootCoreId) == none)
      assertBool "9g control: the caller did NOT IPC-block (ipcState stays .ready)"
        (match st'.getTcb? callerTid with
          | some tcb => tcb.ipcState == .ready
          | none => false)
      assertBool "9g: a self-suspend RETURNS the constructed unit frame (not .blocks)"
        (out == .returns .zero)
  -- 9h — capability-transfer honesty (PR #866 round-2): the staged
  -- extraCaps is the INSTALLED count, never the requested one
  match capsSendScenario epCapNoGrantPtr with
  | .error e => assertBool s!"9h dispatches (got .error {reprStr e})" false
  | .ok (frame, deliveredCaps, slot0) => do
      -- PR #873 round 14: the message now carries **nothing**, where it used to
      -- carry the requested cap and have it denied at the unwrap.  Resolution
      -- mints a persistent CDT node per source slot and marks that slot as
      -- having a transfer in flight, so resolving for a sender that cannot
      -- transfer spent the bounded node counter and made `cspaceDeleteSlot`
      -- answer `.revocationRequired` for a derivation the unwrap was always
      -- going to deny.  The receiver could never see these caps anyway — the
      -- frame below reports extraCaps 0 either way — so carrying them bought
      -- nothing and cost a bounded resource.
      assertBool "9h control: a grant-denied send resolves NOTHING (caps.size = 0)"
        (deliveredCaps == 0)
      -- The honesty property this section is named for — extraCaps is the
      -- INSTALLED count, never the requested one — is pinned by the 9h+ positive
      -- control below, where a granting endpoint installs one and the frame
      -- reports one, against this arm where the request was 1 and the frame
      -- reports 0.  The two together are what make the staged count load-bearing.
      assertBool "9h: a grant-denied transfer stages extraCaps = 0 (x1 = length 1 only — the pre-fix frame read 1 + (1<<7))"
        (frame.x1 == 1)
      assertBool "9h: nothing landed in the receive slot"
        (!slot0)
      assertBool "9h: the message itself still delivers (x0 = badge 9, x2 = 7)"
        (frame.x0 == epBadgeVal.toUInt64 && frame.x2 == 7)
  match capsSendScenario epCapPtr with
  | .error e => assertBool s!"9h+ dispatches (got .error {reprStr e})" false
  | .ok (frame, _, slot0) => do
      assertBool "9h positive control: a granted transfer stages extraCaps = 1 (x1 = 1 + (1<<7))"
        (frame.x1 == (1 + (1 <<< 7) : Nat).toUInt64)
      assertBool "9h positive control: the transferred cap landed in receive slot 0"
        slot0

-- ============================================================================
-- §10  WS-SM SM9.A.10 — the audit reads return their computed word, end to end
--       (fixtures above §8, so the golden trace can record their outcomes)
-- ============================================================================

private def runAuditReadEndToEnd : IO Unit := do
  IO.println "-- §10 WS-SM SM9.A.10: the audit reads return their computed word"
  -- 10a — `status`: the visible length, through the real boundary.  The caller is
  -- the configured monitor, so its view is the whole two-entry trail.
  let statusResult := dispatchAudit auditLabeling
    SyscallId.auditRead.toNat auditCapPtr 3
    (Kernel.encodeAuditReadOp .status).1 0 0 auditWitnessState
  assertBool "10a: `status` returns the visible length (2), not the caller's own x0"
    (match auditReturnedWord statusResult with
     | none => false
     | some w =>
         Kernel.auditStatusVisibleLength w.toNat == 2 &&
         w != capPtrValue.toUInt64)
  assertBool "10a: …and the monitor's status carries the global epoch (0 here)"
    (match auditReturnedWord statusResult with
     | none => false
     | some w => Kernel.auditStatusGeneration w.toNat == 0)
  -- 10b — a record field: entry 1's `targetObject`, chunked.  The value the
  -- kernel selected, not the operand the caller supplied.
  let (fieldOp, fieldIdx, fieldChunk) := Kernel.encodeAuditReadOp (.field 1 .targetObject 0)
  let fieldResult := dispatchAudit auditLabeling
    SyscallId.auditRead.toNat auditCapPtr 3 fieldOp fieldIdx fieldChunk auditWitnessState
  assertBool "10b: a field read returns the SELECTED entry's value"
    (match auditReturnedWord fieldResult with
     | none => false
     | some w => w.toNat == callerVsp.val && w != capPtrValue.toUInt64)
  -- 10c — the confused-deputy gate at the boundary: an ordinary capability
  -- carrying EVERY right is rejected, because it does not target the trail.
  assertBool "10c: NEGATIVE — an all-rights capability to an ordinary object is rejected"
    (match dispatchAudit auditLabeling SyscallId.auditRead.toNat ordinaryCapPtr 3
        (Kernel.encodeAuditReadOp .status).1 0 0 auditWitnessState with
     | .ok (.returns f, _) =>
         -- the boundary reports the error through x1's offset label
         f.x1 != 0
     | _ => false)
  -- 10d — the drain returns the new visible length, and the trail really shrank.
  let drainResult := dispatchAudit auditLabeling
    SyscallId.auditDrain.toNat auditCapPtr 1 1 0 0 auditWitnessState
  assertBool "10d: the drain returns the new visible length (1)"
    (match auditReturnedWord drainResult with
     | none => false
     | some w => w == 1)
  assertBool "10d: …and the committed state really lost the drained prefix"
    (match drainResult with
     | .ok (_, st) =>
         st.declassificationAuditLog.length == 1 &&
         st.declassificationAuditEpoch == 1
     | _ => false)
  -- 10e — the load-bearing negative on the drain gate: with NO configured
  -- monitor the same call fails closed, and the trail is untouched.
  assertBool "10e: NEGATIVE — an unconfigured deployment cannot drain"
    (match dispatchAudit auditUnconfiguredLabeling
        SyscallId.auditDrain.toNat auditCapPtr 1 1 0 0 auditWitnessState with
     | .ok (.returns f, st) =>
         f.x1 != 0 && st.declassificationAuditLog.length == 2
     | _ => false)
  -- 10f — PR #870 round 2: the load-bearing negative on the READ gate, at the
  -- full ABI seam.  The audit capability is provisioned (same CSpace, same
  -- slot) and the caller is the same trusted subject 10a serves — only the
  -- configuration differs — and with no monitor named the read fails closed
  -- instead of serving a partial-reader view.  Before round 2 this exact call
  -- SUCCEEDED, which is what falsified "an unconfigured deployment has no
  -- audit reader" in the deployment shape that provisions a capability.
  assertBool "10f: NEGATIVE — an unconfigured deployment cannot read, even holding the audit capability"
    (match dispatchAudit auditUnconfiguredLabeling
        SyscallId.auditRead.toNat auditCapPtr 3
        (Kernel.encodeAuditReadOp .status).1 0 0 auditWitnessState with
     | .ok (.returns f, st) =>
         f.x1 != 0 && st.declassificationAuditLog.length == 2 &&
         st.declassificationAuditEpoch == 0
     | _ => false)
  -- 10g — PR #870 round 5: **the ordering contract at the full ABI seam.**  A
  -- capability wrong on BOTH axes — ordinary target, no rights at all — is
  -- refused for its TARGET (`.invalidCapability`), not for its rights.  Before
  -- round 5 the full lookup's rights gate front-ran the arm and this exact
  -- call answered `.illegalAuthority`; the load-bearing negative pins that
  -- error out.
  assertBool "10g: a both-axes-wrong capability is refused for its TARGET — invalidCapability, not illegalAuthority"
    (match dispatchAudit auditLabeling SyscallId.auditRead.toNat rightlessCapPtr 3
        (Kernel.encodeAuditReadOp .status).1 0 0 auditWitnessState with
     | .ok (.returns f, _) =>
         f.x1 == (Kernel.Architecture.errorFrame KernelError.invalidCapability).x1 &&
         f.x1 != (Kernel.Architecture.errorFrame KernelError.illegalAuthority).x1
     | _ => false)
  -- 10h — the order's other half: an AUDIT capability carrying only `.read`
  -- passes the target gate and is refused by the ARM's rights check on a
  -- drain — `.illegalAuthority`, from the second gate, with the trail intact.
  assertBool "10h: a read-only audit capability passes the target gate and fails the drain's rights gate"
    (match dispatchAudit auditLabeling SyscallId.auditDrain.toNat readOnlyAuditCapPtr 1
        1 0 0 auditWitnessState with
     | .ok (.returns f, st) =>
         f.x1 == (Kernel.Architecture.errorFrame KernelError.illegalAuthority).x1 &&
         st.declassificationAuditLog.length == 2
     | _ => false)

-- ============================================================================
-- Runner
-- ============================================================================

def runSyscallReturnAbiChecks : IO Unit := do
  IO.println "===================================================="
  IO.println "Syscall return ABI suite (WS-RA)"
  IO.println "RA.E.1 witnesses, INVERTED at the flip: each scenario"
  IO.println "asserted the defect pre-migration and now asserts the"
  IO.println "seL4 convention; the inversion diff is the workstream's"
  IO.println "evidence that it fixed something observable."
  IO.println "===================================================="
  runUnitReturnWitness
  runBadgeDeliveryWitness
  runFullWidthBadgeWitness
  runBlockedOutcomeWitness
  runBlockedWaiterStagingWitnesses
  runAuditReadEndToEnd
  runTraceFixtureCheck
  IO.println "===================================================="
  IO.println "All syscall-return-ABI checks PASS (post-flip convention holds)."

end SeLe4n.Testing.SyscallReturnAbi

def main : IO Unit :=
  SeLe4n.Testing.SyscallReturnAbi.runSyscallReturnAbiChecks
