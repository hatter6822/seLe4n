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
  exists for the caller (plan §3.5; delivery is the SM10.E context
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
* label `0` → success: `x0` is the full-width value, `regs[2..5]` the
  message registers;
* label `n + 1` → `KernelError` discriminant `n`, unknown discriminants
  collapsing to an error either way. -/
inductive RustDecoded where
  | err (disc : Nat)
  | errUndecodableX1
  | ok (x0 : UInt64) (msgRegs : Array UInt64)
  deriving Repr, DecidableEq

private def rustDecodeResponse (regs : Array UInt64) : RustDecoded :=
  match MessageInfo.decode regs[1]!.toNat with
  | none => .errUndecodableX1
  | some mi =>
      match mi.label with
      | 0 => .ok regs[0]! #[regs[2]!, regs[3]!, regs[4]!, regs[5]!]
      | n + 1 => .err n

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
          ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := .ready })
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
SM10.E context restore (plan §3.5). -/
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
  IO.println "===================================================="
  IO.println "All syscall-return-ABI checks PASS (post-flip convention holds)."

end SeLe4n.Testing.SyscallReturnAbi

def main : IO Unit :=
  SeLe4n.Testing.SyscallReturnAbi.runSyscallReturnAbiChecks
