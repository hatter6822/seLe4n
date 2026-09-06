-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-RR RR7.12: PRODUCTION.  The declared-footprint bracket the live syscall
-- seam runs.  `SeLe4n/Kernel/SyscallDispatchEntry.lean` is the consumer.

import SeLe4n.Kernel.Concurrency.Locks.LockSetForSyscall
import SeLe4n.Platform.FFI

/-!
# WS-RR RR7.12 — the declared footprint, at the live syscall seam

SM3 built the per-object lock discipline and RR7.10/RR7.11 built the resolver
that turns *the syscall the dispatcher is about to run* into *the lock set that
syscall's footprint needs*.  What was still missing is the consumer: nothing on
the live path acquired a declared footprint except the raw `.tcbSuspend` seam,
so "per-object reader-writer fine locks" described one arm of thirty-five.

This module supplies it.  Three pieces, in the order the seam runs them.

## 1.  The entry's own decode, named once

`abiEntryPlan` is the prefix `syscallDispatchFromAbi` performs before it
dispatches: the ABI consistency check, the labeling-context guard, the caller
read off the executing core, the register spill into that caller's TCB, the
register-context read and the state-aware argument decode, and the IPC-buffer
TLB fill.  It returns the caller, the decode and **the state the dispatch runs
on** — and `abiEntryPlan_dispatches` is the anti-drift tie: whenever the plan
yields a triple, `syscallDispatchFromAbi` *is* `dispatchSyscallChecked` at that
same caller, that same decode and that same state.

Named once rather than recomputed, because a footprint resolved from a decode
the dispatch does not use is a footprint for a different operation — the defect
`declaredLockSetForEntry_binds_decode` exists to exclude, one layer down.

## 2.  The operands, from the capability the decode addresses

`abiEntryLockOperands` resolves the capability exactly as `dispatchSyscallChecked`
builds its `SyscallGate` — same root, same depth, same required right — and turns
its target into `SyscallLockOperands`.  It is fail-closed four times over:

* the caller must resolve to a TCB with a CNode root, since the footprint's CNode
  member *is* that root;
* the resolution must be **single-level** (`rootCn.depth = guardWidth +
  radixWidth`, and the resolved reference must land in the root).  A multi-level
  walk selects the target through interior CNodes the footprint holds no lock on,
  so a concurrent writer could redirect the resolution without conflicting with
  the declared set.  A `LockSet` is capped at `maxLockSetSize` and a CSpace path
  is not, so locking the path is not expressible and refusing is the honest
  answer;
* the capability must resolve, at the rights the syscall requires;
* a thread-directed target must pass `ThreadId.toValid?`, the sentinel guard the
  live arm applies before its handler runs.

`none` at any step means no operands, hence no footprint, hence the fallback.

## 3.  The revalidated bracket

`dispatchUnderDeclaredLockSet` resolves the footprint, acquires it, **re-resolves
at the state the growing phase ended in**, and refuses on any change; on a match
it runs the dispatch from that state and unwinds.  With no footprint declared it
runs the dispatch unbracketed — bit-identical to the pre-RR7.12 seam
(`dispatchUnderDeclaredLockSet_undeclared_eq_unbracketed`), which is what makes
this cut safe to land ahead of the remaining twenty-seven declarations.

Why re-resolve: the footprint's own CNode read lock is *in the set it returns*,
so it is acquired strictly after the read it protects.  Under the SM5.I global
kernel-entry lock no other core can commit in between — which is why this is not
a live defect today — but the guard is installed with the bracket rather than
after it, so removing that global lock does not silently open the window.
`SeLe4n/Kernel/InformationFlow/FineLockFlow.lean` carries the staged model of
this shape and the theorems about its information-flow behaviour; this is the
production instance at the ABI seam.

## What this does *not* change

The lock granularity that matters for concurrency is the granularity of the
**commit**, and `Platform.FFI.modifyGetKernelState` is still one global
read-modify-write over a single `SystemState`.  So the SM5.I kernel-entry ticket
lock stays, and what this buys is the model-level property the SM3 theorems were
always about: the transition the kernel runs runs inside its declared footprint.
See `rust/sele4n-hal/src/kernel_entry.rs`.
-/

namespace SeLe4n.Kernel

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId LockSet lockSetForSyscall SyscallLockOperands
  withLockSet acquireAll unwindAll lockSetHeld)

-- ============================================================================
-- §1  The entry's own decode, named once
-- ============================================================================

/-- **WS-RR RR7.12**: the prefix `Platform.FFI.syscallDispatchFromAbi` runs
before it dispatches, as a value.

Returns the caller, the decoded syscall, and **the state the dispatch runs on** —
the register-spilled, IPC-buffer-TLB-filled state, not the entry's raw
pre-state.  Every rejection the prefix can take is a `none` here, so a plan that
resolves is a syscall that will reach `dispatchSyscallChecked`.

The point of naming it is `abiEntryPlan_dispatches` below: a footprint resolved
from a decode the dispatch does not use is a footprint for a different
operation. -/
def abiEntryPlan (ctx : LabelingContext) (executingCore : CoreId)
    (syscallId : UInt32) (msgInfo x0 x1 x2 x3 x4 x5 : UInt64) (st : SystemState) :
    Option (SeLe4n.ThreadId × SyscallDecodeResult × SystemState) :=
  if msgInfo != x1 then none
  else if isInsecureDefaultContext ctx then none
  else
    match st.scheduler.currentOnCore executingCore with
    | none => none
    | some tid =>
      let stRegs := Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5
      match lookupThreadRegisterContext tid stRegs with
      | .error _ => none
      | .ok (regs, _) =>
        match SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
                stRegs tid SeLe4n.arm64DefaultLayout regs 32 with
        | .error _ => none
        | .ok decoded =>
          some (tid, decoded,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore
              stRegs executingCore tid decoded.overflowCount)

/-- **WS-RR RR7.12 (the anti-drift tie)**: whenever the plan resolves, the live
ABI dispatch **is** `dispatchSyscallChecked` at that caller, that decode and
that state.

This is what makes a footprint resolved from `abiEntryPlan` a footprint for the
operation the kernel executes.  A new validation step in the prefix, or a
normalisation applied to the decode, stops this elaborating rather than silently
leaving the bracket around a different syscall. -/
theorem abiEntryPlan_dispatches (ctx : LabelingContext) (executingCore : CoreId)
    (syscallId : UInt32) (msgInfo x0 x1 x2 x3 x4 x5 : UInt64)
    (ipcBufferAddr elr spsr spEl0 x30 : UInt64) (st : SystemState)
    (tid : SeLe4n.ThreadId) (decoded : SyscallDecodeResult) (stFilled : SystemState)
    (h : abiEntryPlan ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st
          = some (tid, decoded, stFilled)) :
    Platform.FFI.syscallDispatchFromAbi ctx executingCore syscallId msgInfo
        x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st
      = (match dispatchSyscallChecked ctx decoded tid stFilled with
         | .error ke =>
             match Platform.FFI.syscallCapFaultOf SeLe4n.arm64DefaultLayout
                 (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5)
                 tid ke with
             | some fault =>
                 .ok (.faulted,
                      Platform.FFI.deliverSyscallCapFault ctx executingCore
                        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5)
                        tid fault
                        (Platform.FFI.syscallWindow syscallId x0 x1 x2 x3 x4 x5
                          ipcBufferAddr spEl0 x30) elr spsr)
             | none =>
                 .ok (.returns (Architecture.errorFrame ke),
                      Platform.FFI.recordSyscallRefusal ctx executingCore syscallId tid ke x0
                        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5))
         | .ok ((), st') =>
             .ok (Platform.FFI.syscallReturnOutcome syscallId st' tid, st')) := by
  unfold abiEntryPlan at h
  unfold Platform.FFI.syscallDispatchFromAbi
  by_cases hAbi : msgInfo != x1
  · rw [if_pos hAbi] at h; exact absurd h (by simp)
  · rw [if_neg hAbi] at h
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hAbi
    rw [if_neg (by simpa using hAbi)]
    by_cases hCtx : isInsecureDefaultContext ctx
    · rw [if_pos hCtx] at h; exact absurd h (by simp)
    · rw [if_neg hCtx] at h
      cases hCur : st.scheduler.currentOnCore executingCore with
      | none => rw [hCur] at h; exact absurd h (by simp)
      | some tid' =>
        rw [hCur] at h
        simp only at h
        cases hRegs : lookupThreadRegisterContext tid'
            (Platform.FFI.writeFfiRegistersToTcb st tid' syscallId x0 x1 x2 x3 x4 x5) with
        | error e => rw [hRegs] at h; exact absurd h (by simp)
        | ok regsPair =>
          obtain ⟨regs, _⟩ := regsPair
          rw [hRegs] at h
          simp only at h
          cases hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
              (Platform.FFI.writeFfiRegistersToTcb st tid' syscallId x0 x1 x2 x3 x4 x5)
              tid' SeLe4n.arm64DefaultLayout regs 32 with
          | error e => rw [hDec] at h; exact absurd h (by simp)
          | ok decoded' =>
            rw [hDec] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hTid, hDecoded, hFilled⟩ := h
            subst hTid; subst hDecoded; subst hFilled
            -- `syscallEntryChecked` reads the caller off the **spilled** state;
            -- the spill frames the scheduler, so it reads the same caller.
            have hSched := Platform.FFI.writeFfiRegistersToTcb_scheduler st tid'
              syscallId x0 x1 x2 x3 x4 x5
            simp only [syscallEntryChecked, hCtx, hSched, hCur, hRegs, hDec,
              Bool.false_eq_true, if_false]
            rfl

-- ============================================================================
-- §2  The operands, from the capability the decode addresses
-- ============================================================================

/-- **WS-RR RR7.12**: the caller's TCB and root CNode, under the single-level
resolution guard.

Returns the `SyscallGate` `dispatchSyscallChecked` builds — same root, same
depth, same required right — paired with the caller's TCB, or `none` where a
footprint must not be declared.

The guard is `rootCn.depth = rootCn.guardWidth + rootCn.radixWidth` together with
the resolved reference landing back in the root.  `resolveCapAddress` consumes
`guardWidth + radixWidth` bits per hop and recurses while any remain, so a root
that consumes them all cannot descend at all — checking the final `ref.cnode`
alone would accept a path that leaves the root and cycles back to it, and the
lookup would still have read an unlocked child CNode on the way.

Why refuse rather than widen: the footprint's only CNode member is the caller's
**root** (every `lockSet_*` takes one `cnodeRootObjId`), a `LockSet` is capped at
`maxLockSetSize`, and a CSpace path is bounded only by the address width.  So a
multi-level resolution cannot be covered by any declared footprint, and a
declared footprint that does not cover the read selecting its own target is the
false footprint this whole family exists to refuse.  A refused entry declares
nothing and the seam keeps the coarser serialisation it already has. -/
def abiEntryGate (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (s : SystemState) :
    Option (TCB × SyscallGate) :=
  match s.getTcb? tid with
  | none => none
  | some tcb =>
    match s.getCNode? tcb.cspaceRoot with
    | none => none
    | some rootCn =>
      if rootCn.depth ≠ rootCn.guardWidth + rootCn.radixWidth then none
      else
        match resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth s with
        | .error _ => none
        | .ok ref =>
          if ref.cnode ≠ tcb.cspaceRoot then none
          else
            some (tcb,
              { callerId := tid, cspaceRoot := tcb.cspaceRoot,
                capAddr := decoded.capAddr, capDepth := rootCn.depth,
                requiredRight := syscallRequiredRight decoded.syscallId })

/-- **WS-RR RR7.12**: the message a sending arm's footprint is a function of.

Built exactly as the live `.send` / `.call` arms build theirs — the same
`extractMessageRegisters`, the same `decodeExtraCapAddrs`, the same
`resolveExtraCaps` at the same root, depth and grant bit — and then the
resolution's **state is discarded**.

Discarding it is the point.  `resolveExtraCaps` mints a CDT node per resolved
source slot, which is a commitment; the footprint only needs to know *whether*
capabilities travel and *where they land*, which is a function of the resolved
array.  Resolving twice therefore costs a discarded allocation in the footprint
resolver and mints exactly once in the transition, rather than the resolver
committing state the bracket has not yet acquired locks for. -/
def abiEntryMessage (decoded : SyscallDecodeResult) (gate : SyscallGate)
    (cap : Capability) (s : SystemState) : IpcMessage :=
  let extraCapAddrs := Architecture.SyscallArgDecode.decodeExtraCapAddrs decoded
  let resolvedCaps :=
    (resolveExtraCaps gate.cspaceRoot extraCapAddrs gate.capDepth (cap.rights.mem .grant) s).1
  { registers := Architecture.RegisterDecode.extractMessageRegisters decoded.msgRegs decoded.msgInfo,
    caps := resolvedCaps, badge := cap.badge,
    capsGranted := cap.rights.mem .grant }

/-- **WS-RR RR7.12**: the operands the declared-footprint resolver takes, read
off the capability the decode addresses.

One arm per shape the resolver can express, and each names what its own live
dispatch arm names:

* thread-directed (`.tcbSuspend`) — the capability's object **as a thread**,
  through `ThreadId.toValid?`, the AL7-A sentinel guard the live arm applies
  through `validateThreadIdArg` before its handler runs.  Declaring a footprint
  for a syscall the dispatch will reject would have the bracket queue on locks
  for a call that cannot execute;
* endpoint-directed with a message (`.send`, `.call`) — the endpoint the
  capability names plus `abiEntryMessage`, because whether the receiver's CSpace
  root and the state-level lock are members turns on what the message carries;
* endpoint-directed without one (`.receive`, `.notificationSignal`,
  `.notificationWait`) — a receive's capabilities come from the *parked sender*,
  which the endpoint already names, and the two notification arms carry none.
  `.receive` additionally supplies the **server-supplied** Reply object, resolved
  through `resolveRecvReplyId` exactly as the live arm resolves it;
* reply-directed (`.reply`) — the Reply object the reply capability names;
* both (`.replyRecv`) — the endpoint it will receive on next *and* the reply
  object it answers first, resolved through `resolveReplyRecvReply`.

Every other syscall gets caller-only operands, which every undeclared arm
answers `none` to anyway — so this match says what each *declared* arm needs
rather than enumerating thirty-five cases, and a new declared arm that forgets
to add itself here gets the fail-closed answer. -/
def abiEntryLockOperands (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (s : SystemState) : Option SyscallLockOperands :=
  match abiEntryGate decoded tid s with
  | none => none
  | some (_, gate) =>
    match syscallLookupCap gate s with
    | .error _ => none
    | .ok (cap, _) =>
      match decoded.syscallId, cap.target with
      | .tcbSuspend, .object objId =>
          match (SeLe4n.ThreadId.ofNat objId.toNat).toValid? with
          | none => none
          | some valid => some (.ofThreadTarget tid valid.val)
      | .send, .object epId => some (.ofObjectTarget tid epId (some (abiEntryMessage decoded gate cap s)))
      | .call, .object epId => some (.ofObjectTarget tid epId (some (abiEntryMessage decoded gate cap s)))
      | .receive, .object epId =>
          match resolveRecvReplyId gate decoded s with
          | .error _ => none
          | .ok replyId? =>
              some { caller := tid, targetObject := some epId, targetReply := replyId? }
      | .notificationSignal, .object nId => some (.ofObjectTarget tid nId)
      | .notificationWait, .object nId => some (.ofObjectTarget tid nId)
      | .reply, .replyCap rid => some (.ofReplyTarget tid rid)
      | .replyRecv, .object epId =>
          match resolveReplyRecvReply gate decoded s with
          | .error _ => none
          | .ok (rid, _, _) => some (.ofReplyTarget tid rid (some epId))
      | _, _ => none

/-- **WS-RR RR7.12**: the footprint the live ABI seam declares.

`lockSetForSyscall` at the **decoded** syscall id, the caller the executing core
is running, and the operands that caller's capability names — every input
derived from the entry's own resolution rather than supplied alongside it.  A
caller cannot bracket one syscall's footprint around another's. -/
def declaredLockSetForAbiEntry (ctx : LabelingContext) (executingCore : CoreId)
    (syscallId : UInt32) (msgInfo x0 x1 x2 x3 x4 x5 : UInt64) (st : SystemState) :
    Option LockSet :=
  match abiEntryPlan ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st with
  | none => none
  | some (tid, decoded, stFilled) =>
    (abiEntryLockOperands decoded tid stFilled).bind
      (fun ops => lockSetForSyscall decoded.syscallId ops stFilled)

/-- **WS-RR RR7.12 (the binding, as a theorem)**: a declared footprint is
`lockSetForSyscall`'s output at the decode the dispatch runs, the caller the
executing core is running, and that caller's own operands — at the state the
dispatch runs on.

Stated rather than left to a reader of the definition, so a future cut that
reintroduces an independent argument has to break a proof to do it. -/
theorem declaredLockSetForAbiEntry_binds_decode (ctx : LabelingContext)
    (executingCore : CoreId) (syscallId : UInt32) (msgInfo x0 x1 x2 x3 x4 x5 : UInt64)
    (st : SystemState) (S : LockSet)
    (h : declaredLockSetForAbiEntry ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st
          = some S) :
    ∃ tid decoded stFilled ops,
      abiEntryPlan ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st
        = some (tid, decoded, stFilled) ∧
      abiEntryLockOperands decoded tid stFilled = some ops ∧
      lockSetForSyscall decoded.syscallId ops stFilled = some S := by
  unfold declaredLockSetForAbiEntry at h
  cases hPlan : abiEntryPlan ctx executingCore syscallId msgInfo x0 x1 x2 x3 x4 x5 st with
  | none => rw [hPlan] at h; exact absurd h (by simp)
  | some triple =>
    obtain ⟨tid, decoded, stFilled⟩ := triple
    rw [hPlan] at h
    simp only at h
    cases hOps : abiEntryLockOperands decoded tid stFilled with
    | none => rw [hOps] at h; exact absurd h (by simp)
    | some ops =>
      rw [hOps] at h
      simp only [Option.bind_some] at h
      exact ⟨tid, decoded, stFilled, ops, rfl, hOps, h⟩

/-- **WS-RR RR7.12 (the sentinel guard, as a theorem)**: a capability naming the
sentinel thread yields no operands, so no footprint is declared for it. -/
theorem abiEntryLockOperands_tcbSuspend_target_valid (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (s : SystemState) (ops : SyscallLockOperands)
    (t : SeLe4n.ThreadId)
    (hSid : decoded.syscallId = .tcbSuspend)
    (h : abiEntryLockOperands decoded tid s = some ops)
    (hT : ops.targetThread = some t) :
    t ≠ SeLe4n.ThreadId.sentinel := by
  unfold abiEntryLockOperands at h
  cases hGate : abiEntryGate decoded tid s with
  | none => rw [hGate] at h; exact absurd h (by simp)
  | some pair =>
    obtain ⟨_, gate⟩ := pair
    rw [hGate] at h
    simp only at h
    cases hLk : syscallLookupCap gate s with
    | error e => rw [hLk] at h; exact absurd h (by simp)
    | ok capPair =>
      obtain ⟨cap, _⟩ := capPair
      rw [hLk, hSid] at h
      simp only at h
      -- Only the `.object` arm survives: a suspend names a TCB object, and the
      -- guard is `ThreadId.toValid?`, whose witness carries the refusal.
      cases hTgt : cap.target with
      | cnodeSlot _ => rw [hTgt] at h; exact absurd h (by simp)
      | replyCap _ => rw [hTgt] at h; exact absurd h (by simp)
      | auditTrail => rw [hTgt] at h; exact absurd h (by simp)
      | object objId =>
      rw [hTgt] at h
      simp only at h
      cases hV : (SeLe4n.ThreadId.ofNat objId.toNat).toValid? with
      | none => rw [hV] at h; exact absurd h (by simp)
      | some valid =>
        rw [hV] at h
        simp only [Option.some.injEq] at h
        subst h
        have ht : t = valid.val := by
          simpa [SyscallLockOperands.ofThreadTarget] using hT.symm
        rw [ht]
        exact valid.property

/-- **WS-RR RR7.12**: the caller in the operands is the thread the executing core
is running — not a value a caller supplied.

The footprint's CNode member is that thread's CSpace root and its TCB member is
that thread's TCB, so a caller field that could name anything else would declare
a footprint for a different principal.  Trivial by construction, and stated
because "by construction" is what a refactor removes. -/
theorem abiEntryLockOperands_caller (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (s : SystemState) (ops : SyscallLockOperands)
    (h : abiEntryLockOperands decoded tid s = some ops) :
    ops.caller = tid := by
  unfold abiEntryLockOperands at h
  cases hGate : abiEntryGate decoded tid s with
  | none => rw [hGate] at h; exact absurd h (by simp)
  | some pair =>
    obtain ⟨_, gate⟩ := pair
    rw [hGate] at h
    simp only at h
    cases hLk : syscallLookupCap gate s with
    | error e => rw [hLk] at h; exact absurd h (by simp)
    | ok capPair =>
      obtain ⟨cap, _⟩ := capPair
      rw [hLk] at h
      simp only at h
      split at h <;> try split at h
      all_goals
        first
          | (rw [← Option.some.inj h]; rfl)
          | rw [← Option.some.inj h]
          | exact absurd h (by simp)

-- ============================================================================
-- §3  The revalidated bracket
-- ============================================================================

/-- **WS-RR RR7.12**: what a bracketed step can do.

Three outcomes, because they oblige the caller differently and collapsing any
two of them loses something.  `undeclared` did not acquire and has nothing to
release — the caller keeps its coarser serialisation, which is always sound.
`refused` **did** acquire, so it carries the state with the footprint unwound;
returning a refusal without the unwinding would strand the footprint on
`lockCore` and block every later user of those objects.  `committed` ran the
step from the state the growing phase ended in and released after it. -/
inductive LockBracketOutcome (α : Type) where
  /-- No footprint is declared for this operation; the step ran unbracketed. -/
  | undeclared (result : α × SystemState)
  /-- A footprint was acquired and the guard then refused; the state carries the
  footprint **unwound** — released where it was granted, withdrawn where it was
  only queued. -/
  | refused (unwound : SystemState)
  /-- The guard passed; the step ran under the footprint, which was then
  released. -/
  | committed (result : α × SystemState)

/-- **WS-RR RR7.12**: run a step inside its declared footprint, revalidating.

Resolve, acquire, **re-resolve at the state the growing phase ended in**, and
refuse on any change; on a match run the step from that state and unwind.

Two conditions, both necessary.  The resolution must not have moved — the
footprint's own CNode read lock is a member of the set it returns, so it is
acquired strictly after the read it protects, and another core could replace the
caller's capability in between.  And the acquired state must actually **hold**
the footprint: `withLockSet`'s growing phase runs the action whether or not it
was granted (`lockSetAcquiredState_does_not_grant_when_contended`), so a step
that ran on a contended footprint would have no exclusion at all.

The step runs from `acquired`, not from `st` — re-running it from `st` would
discard exactly the growing phase whose grant the guard just checked.

`unwindAll` rather than `releaseAll` on the refusal path (WS-LC LC4): a release
is the identity for a non-holder, so a release-only unwind leaves every
*contended* member of the footprint still queued on `lockCore`. -/
def runUnderDeclaredLockSet {α : Type} (declared : SystemState → Option LockSet)
    (lockCore : CoreId) (step : SystemState → α × SystemState) (st : SystemState) :
    LockBracketOutcome α :=
  match declared st with
  | none => .undeclared (step st)
  | some S =>
    let acquired := acquireAll lockCore S.lockAcquireSequence st
    if declared acquired = some S ∧ lockSetHeld lockCore S acquired then
      let (v, post) := step acquired
      .committed (v, unwindAll lockCore S.lockAcquireSequence.reverse post)
    else
      .refused (unwindAll lockCore S.lockAcquireSequence.reverse acquired)

/-- **WS-RR RR7.12 (the fallback is exactly today's behaviour)**: with no
footprint declared, the bracket is the bare step.

This is what makes installing the bracket safe ahead of the remaining
twenty-seven declarations: every syscall whose footprint is still `none` runs
bit-identically to the pre-RR7.12 seam, on the pre-state, with no lock written.
Definitional, so a refactor that starts acquiring *something* on the undeclared
path stops this elaborating. -/
@[simp] theorem runUnderDeclaredLockSet_undeclared {α : Type}
    (declared : SystemState → Option LockSet) (lockCore : CoreId)
    (step : SystemState → α × SystemState) (st : SystemState)
    (h : declared st = none) :
    runUnderDeclaredLockSet declared lockCore step st = .undeclared (step st) := by
  unfold runUnderDeclaredLockSet
  rw [h]

/-- **WS-RR RR7.12**: on the committed arm the step ran from the **acquired**
state and the returned state is that step's post-state, unwound. -/
theorem runUnderDeclaredLockSet_committed {α : Type}
    (declared : SystemState → Option LockSet) (lockCore : CoreId)
    (step : SystemState → α × SystemState) (st : SystemState) (S : LockSet)
    (hDecl : declared st = some S)
    (hGuard : declared (acquireAll lockCore S.lockAcquireSequence st) = some S ∧
      lockSetHeld lockCore S (acquireAll lockCore S.lockAcquireSequence st)) :
    runUnderDeclaredLockSet declared lockCore step st
      = .committed ((step (acquireAll lockCore S.lockAcquireSequence st)).1,
          unwindAll lockCore S.lockAcquireSequence.reverse
            (step (acquireAll lockCore S.lockAcquireSequence st)).2) := by
  unfold runUnderDeclaredLockSet
  rw [hDecl]
  simp only [if_pos hGuard]

/-- **WS-RR RR7.12 (a refusal commits nothing but the unwinding)**: the state a
refusal carries is the pre-state with the footprint acquired and then unwound —
the step never ran, so no transition was committed.

The load-bearing negative.  A guard that refused *after* running the step would
be worse than no guard at all: the operation would have committed on a
resolution the guard judged stale. -/
theorem runUnderDeclaredLockSet_refused {α : Type}
    (declared : SystemState → Option LockSet) (lockCore : CoreId)
    (step : SystemState → α × SystemState) (st : SystemState) (S : LockSet)
    (hDecl : declared st = some S)
    (hGuard : ¬ (declared (acquireAll lockCore S.lockAcquireSequence st) = some S ∧
      lockSetHeld lockCore S (acquireAll lockCore S.lockAcquireSequence st))) :
    runUnderDeclaredLockSet declared lockCore step st
      = .refused (unwindAll lockCore S.lockAcquireSequence.reverse
          (acquireAll lockCore S.lockAcquireSequence st)) := by
  unfold runUnderDeclaredLockSet
  rw [hDecl]
  simp only [if_neg hGuard]

/-- **WS-RR RR7.12**: the bracket's committed arm **is** `withLockSet` at the
acquired state.

The tie back to SM3: every 2PL, serializability and observer-atomicity theorem
`withLockSet` carries is about this composition, so a caller reading
`.committed` is reading the state those theorems describe.  A revalidating
bracket cannot simply *be* `withLockSet` — it has to look at the acquired state
before deciding — but its accepting path is the same acquire / act / unwind, and
this says so definitionally. -/
theorem runUnderDeclaredLockSet_committed_eq_withLockSet {α : Type}
    (declared : SystemState → Option LockSet) (lockCore : CoreId)
    (step : SystemState → SystemState × α) (st : SystemState) (S : LockSet)
    (hDecl : declared st = some S)
    (hGuard : declared (acquireAll lockCore S.lockAcquireSequence st) = some S ∧
      lockSetHeld lockCore S (acquireAll lockCore S.lockAcquireSequence st)) :
    runUnderDeclaredLockSet declared lockCore
        (fun s => ((step s).2, (step s).1)) st
      = .committed ((withLockSet S lockCore step st).2, (withLockSet S lockCore step st).1) := by
  unfold runUnderDeclaredLockSet withLockSet
  rw [hDecl]
  simp only [if_pos hGuard]

end SeLe4n.Kernel
