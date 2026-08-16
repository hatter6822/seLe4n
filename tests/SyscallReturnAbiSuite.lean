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

## RA.E.1 — the observable-failure witness, written before the fix

The kernel writes exactly one register on syscall exit — `x0` — and the value
it writes is not a return value: `syscallDispatchFromAbi` ends with
`encodeOk (readReturnValue st' tid)`, `readReturnValue` reads
`tcb.registerContext.gpr ⟨0⟩`, and the only writer of that slot is
`writeFfiRegistersToTcb`, which staged the caller's **incoming** `x0` — the
capability pointer.  Compose with userspace's `decode_response`
(`rust/sele4n-abi/src/decode.rs`), where `regs[0] != 0` *is* the error
discriminant, and a **successful** syscall whose capability pointer is nonzero
decodes as a `KernelError`.

This suite makes that §1.2 derivation an executable observation.  Because CI
cannot carry a red test, the witness assertions are **inverted**: each §4/§5
check asserts the *defective* behaviour as a pre-migration witness, in the
repo's load-bearing-negative idiom.  The WS-RA flip PR must break every one of
them and invert the assertions to the correct seL4 convention in the same
commit that changes the behaviour — that inversion diff is the workstream's
witness that it fixed something observable.

* §1 — surface anchors for the pre-migration encode/read seam.
* §2 — a byte-faithful Lean mirror of the Rust decoder (the
  `AbiRoundtripSuite` simulate-the-Rust-side idiom, in the return direction).
* §3 — the fixture: one caller, one CNode, one notification, everything the
  live checked dispatch path needs to *succeed*.
* §4 — pre-migration witness A: a successful `Unit` syscall returns the
  caller's capability pointer, which userspace decodes as a `KernelError`.
* §5 — pre-migration witness B: the signal-before-wait badge round trip loses
  the badge (the SM9.C.0 defect) — the wait succeeds, the badge is consumed,
  and the register file hands back the caller's own `x1` as the "badge".
* §6 — pre-migration witness C: `encodeOk` masks bit 63, so two distinct
  valid badges alias (the RA.A.8 motivation, computed).

Plan: `docs/planning/SYSCALL_RETURN_ABI_PLAN.md` §1.2, RA.E.1.
-/

namespace SeLe4n.Testing.SyscallReturnAbi

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Platform.FFI

-- ============================================================================
-- §1  Surface anchors — the pre-migration seam this suite witnesses
-- ============================================================================

#check @SeLe4n.Platform.FFI.syscallDispatchFromAbi
#check @SeLe4n.Platform.FFI.readReturnValue
#check @SeLe4n.Platform.FFI.encodeOk
#check @SeLe4n.Platform.FFI.encodeError
#check @SeLe4n.Platform.FFI.encodeOk_high_bit_clear
#check @SeLe4n.Platform.FFI.encodeError_high_bit_set

private def assertBool (label : String) (b : Bool) : IO Unit :=
  if b then IO.println s!"  PASS: {label}"
  else throw (IO.userError s!"  FAIL: {label}")

-- ============================================================================
-- §2  Byte-faithful mirror of `rust/sele4n-abi/src/decode.rs::decode_response`
-- ============================================================================

/-- What the Rust userspace decoder concludes from the post-trap register
file.  Mirrors `decode_response` exactly (decode.rs:31-54, pre-migration):

* `regs[0] != 0` → an error; `regs[0] > u32::MAX` → the V1-A overflow
  rejection (`InvalidSyscallNumber`), else `KernelError::from_u32(regs[0])`
  with unknown discriminants collapsing to `UnknownKernelError` — either way
  an `Err`, which this mirror folds into `.err` / `.errOverflow`.
* `regs[0] == 0` → success; `x1` is the badge-or-msginfo word and
  `regs[2..5]` the message registers. -/
inductive RustDecoded where
  | err (disc : UInt32)
  | errOverflow
  | ok (x1 : UInt64) (msgRegs : Array UInt64)
  deriving Repr, DecidableEq

/-- The decoder itself.  `regs` is the register file as userspace sees it
after `eret` — i.e. after the trap layer's writeback, which today is
`frame.set_x0(retval)` and nothing else (`trap.rs:214-217`), so
`regs[1..5]` are the caller's own pre-syscall values. -/
private def rustDecodeResponse (regs : Array UInt64) : RustDecoded :=
  let r0 := regs[0]!
  if r0 != 0 then
    if r0 > 0xFFFFFFFF then .errOverflow
    else .err r0.toUInt32
  else
    .ok regs[1]! #[regs[2]!, regs[3]!, regs[4]!, regs[5]!]

/-- The post-trap register file: the dispatch result lands in `x0`, every
other register keeps the caller's staged value (`trap.rs` writes back
nothing else pre-migration). -/
private def postTrapRegs (dispatchResult : UInt64)
    (x1 x2 x3 x4 x5 : UInt64) : Array UInt64 :=
  #[dispatchResult, x1, x2, x3, x4, x5]

-- ============================================================================
-- §3  Fixture — a state on which the live checked dispatch path SUCCEEDS
-- ============================================================================

private def callerTid : SeLe4n.ThreadId := ⟨900⟩
private def callerCn  : SeLe4n.ObjId    := ⟨901⟩
private def callerVsp : SeLe4n.ObjId    := ⟨902⟩
private def ntfnId    : SeLe4n.ObjId    := ⟨903⟩

/-- The capability pointer — **deliberately nonzero**, because the defect this
suite witnesses is that a successful syscall hands the caller's `x0` back and
`x0` on entry is this pointer.  Slot 5 of a depth-4 / radix-4 / guard-0 CNode
resolves from CPtr 5 (`resolveCapAddress`: slotIndex = addr % 16). -/
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
checked entry, and the pre-migration `encodeOk (readReturnValue …)` exit. -/
private def dispatchFromAbi (syscallId : Nat) (msgInfoRaw : UInt64)
    (x2 : UInt64) (st : SystemState) :
    Except KernelError (UInt64 × SystemState) :=
  SeLe4n.Platform.FFI.syscallDispatchFromAbi trustedLabeling
    SeLe4n.Kernel.Concurrency.bootCoreId
    syscallId.toUInt32 msgInfoRaw
    capPtrValue.toUInt64 msgInfoRaw x2 0 0 0
    0 st

-- ============================================================================
-- §4  PRE-MIGRATION WITNESS A — a successful `Unit` syscall decodes as error
-- ============================================================================

/-- `.notificationSignal` (a `Unit`-returning syscall — seL4's Signal has no
result) through the live checked dispatch: CSpace resolution at CPtr 5,
rights gate, flow gates, `notificationSignalBoundCrossCoreDispatch`.  The
model transition **succeeds** — and the encoded return word is the caller's
capability pointer, which the Rust decoder reads as `KernelError`
discriminant 5.

**Every assertion below is inverted**: it pins the defect.  The WS-RA flip
must break each one and replace it with the correct-convention assertion. -/
private def runUnitReturnWitness : IO Unit := do
  IO.println "-- §4 witness A: successful Unit syscall decodes as KernelError"
  -- MessageInfo {length := 1, extraCaps := 0, label := 0} encodes to 1;
  -- x2 carries the badge argument for the signal.
  let msgInfoRaw : UInt64 := 1
  match dispatchFromAbi SyscallId.notificationSignal.toNat msgInfoRaw
      signalledBadge.toUInt64 witnessState with
  | .error e =>
      assertBool s!"the signal dispatch reaches the FFI seam (got .error {reprStr e})" false
  | .ok (encoded, st') => do
      -- Control: the syscall genuinely succeeded — the badge landed.
      assertBool "control: the signal committed (pendingBadge = 42)"
        (match st'.getNotification? ntfnId with
          | some n => n.pendingBadge == some (Badge.ofNatMasked signalledBadge)
          | none => false)
      -- The defect, part 1: the kernel's return word is the caller's own
      -- capability pointer, not 0.
      assertBool "PRE-MIGRATION: the encoded return word IS the cap pointer (5)"
        (encoded == capPtrValue.toUInt64)
      -- The defect, part 2: userspace decodes that success as a KernelError
      -- whose discriminant is the capability pointer.
      assertBool "PRE-MIGRATION: userspace decodes the success as .err 5"
        (rustDecodeResponse
          (postTrapRegs encoded msgInfoRaw signalledBadge.toUInt64 0 0 0)
          == RustDecoded.err capPtrValue.toUInt32)

-- ============================================================================
-- §5  PRE-MIGRATION WITNESS B — signal-before-wait loses the badge (SM9.C.0)
-- ============================================================================

/-- The ordinary badge round trip: signal 42, then `.notificationWait`.  The
wait **succeeds** and consumes the pending badge — `notificationWaitOnCore`
returns `.ok (some 42)` — and both live arms discard it, so the register
file the caller reads back contains no trace of it: `x0` is the cap pointer
(decoded as an error), and `x1` — where `sele4n-sys::notification_wait`'s
`resp.badge()` looks — is the caller's own msgInfo word, `0`. -/
private def runBadgeLossWitness : IO Unit := do
  IO.println "-- §5 witness B: the signal-before-wait badge round trip loses the badge"
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
      | .ok (encoded, st') => do
          assertBool "control: the wait consumed the pending badge"
            (match st'.getNotification? ntfnId with
              | some n => n.pendingBadge == none
              | none => false)
          assertBool "PRE-MIGRATION: the wait's return word is the cap pointer, not the badge"
            (encoded == capPtrValue.toUInt64 && encoded != signalledBadge.toUInt64)
          -- What `notification_wait` actually hands back: `badge()` reads x1,
          -- and the kernel never wrote x1, so the "badge" is the caller's own
          -- msgInfo word.
          match rustDecodeResponse (postTrapRegs encoded 0 0 0 0 0) with
          | .ok x1 _ =>
              assertBool "unreachable pre-migration: nonzero x0 cannot decode .ok"
                (x1 == 0 && false)
          | .errOverflow =>
              assertBool "unreachable: the cap pointer fits u32" false
          | .err disc => do
              assertBool "PRE-MIGRATION: the wait decodes as an error, badge unrecoverable"
                (disc == capPtrValue.toUInt32)
              assertBool "PRE-MIGRATION: the register file nowhere contains the badge"
                (!(postTrapRegs encoded 0 0 0 0 0).contains signalledBadge.toUInt64)

-- ============================================================================
-- §6  PRE-MIGRATION WITNESS C — `encodeOk` aliases distinct badges (RA.A.8)
-- ============================================================================

/-- The bit-63 protocol's structural cost, computed: `encodeOk` masks bit 63
to keep success words disjoint from the error flag, so two *distinct* valid
badge values collide.  This is the motivation for retiring the protocol
rather than patching around it — with status moved to the `x1` label, `x0`
carries all 64 bits and the collision is structurally impossible. -/
private def runBadgeAliasingWitness : IO Unit := do
  IO.println "-- §6 witness C: encodeOk masks bit 63, aliasing distinct badges"
  let lowBadge  : UInt64 := 0x42
  let highBadge : UInt64 := 0x8000000000000042
  assertBool "control: the two badge values are distinct"
    (lowBadge != highBadge)
  assertBool "PRE-MIGRATION: encodeOk collapses them to the same word"
    (SeLe4n.Platform.FFI.encodeOk lowBadge ==
     SeLe4n.Platform.FFI.encodeOk highBadge)
  assertBool "PRE-MIGRATION: the high badge is truncated to its low 63 bits"
    (SeLe4n.Platform.FFI.encodeOk highBadge == lowBadge)

-- ============================================================================
-- Runner
-- ============================================================================

def runSyscallReturnAbiChecks : IO Unit := do
  IO.println "===================================================="
  IO.println "Syscall return ABI suite (WS-RA)"
  IO.println "RA.E.1 pre-migration witnesses: every PRE-MIGRATION"
  IO.println "assertion below pins the DEFECT and must be inverted"
  IO.println "by the flip PR in the same commit that fixes it."
  IO.println "===================================================="
  runUnitReturnWitness
  runBadgeLossWitness
  runBadgeAliasingWitness
  IO.println "===================================================="
  IO.println "All syscall-return-ABI checks PASS (pre-migration witnesses hold)."

end SeLe4n.Testing.SyscallReturnAbi

def main : IO Unit :=
  SeLe4n.Testing.SyscallReturnAbi.runSyscallReturnAbiChecks
