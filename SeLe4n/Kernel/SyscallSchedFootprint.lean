-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore
import SeLe4n.Kernel.Lifecycle.Invariant.RetypeReservation
import SeLe4n.Kernel.Concurrency.Locks.LockSetForSyscall
import SeLe4n.Kernel.SyscallLockBracket
import SeLe4n.Kernel.SchedLockBracket
import SeLe4n.Kernel.Lifecycle.ResumeFootprint
import SeLe4n.Kernel.SchedContext.PriorityControlFootprint
import SeLe4n.Kernel.Scheduler.Operations.AffinityFootprint
import SeLe4n.Kernel.SchedContext.SchedContextFootprint
import SeLe4n.Kernel.Lifecycle.Operations.RetypeFootprint
import SeLe4n.Kernel.IPC.CrossCore.SuspendFootprint

/-!
# The syscall-level scheduler footprint — one footprint per arm, from the operands

`schedLockSetForSyscall` resolves a syscall's scheduler-domain footprint from
its operands by naming the per-transition footprint of the arm it dispatches
to; `declaredSchedulerLockSetForAbiEntry` reads the operands off the ABI
entry's decode; `unifiedLockSetForSyscall` and
`declaredUnifiedLockSetForAbiEntry` join that footprint with the object-domain
one into the single ladder the syscall seam declares
(`syscallDispatchBracket`, `SyscallDispatchEntry.lean`).

Each per-transition footprint this resolver names sits beside its transition
(`schedLockSet_endpointSendOnCore` in `EndpointSend.lean`,
`schedLockSet_suspendThreadOnCore` in `IPC/CrossCore/SuspendFootprint.lean`,
and so on).  Until WS-LS LS2.5 this module also held the lifecycle, priority,
affinity, SchedContext and retype arms' footprints, because `LockKey` and the
constructor `schedFootprintOfCores` were declared above those transitions'
modules; LS1.2 moved `LockKey` to `Concurrency/Locks/LockKey.lean` and LS2.5
moved the constructor to `Scheduler/SchedFootprint.lean`, so every one of them
now has its home and this module holds only what is stated at the syscall
level.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId
  LockKey LockSet)

-- ============================================================================
-- §1   The syscall-level resolver — one footprint per arm, from the operands
-- ============================================================================
--
-- WS-RR RR8.12 Cut C4.  `lockSetForSyscall` is the object domain's; this is the
-- scheduler domain's, and the two are deliberately the same shape: a `match`
-- over `SyscallId` dispatching to the arm's own resolved footprint, a boolean
-- inventory of which arms declare, and a negative over that inventory saying
-- every other arm declares nothing whatever the operands and whatever the state.
--
-- It is here rather than beside `lockSetForSyscall` for the reason this module
-- exists at all (see the header): `LockKey` is declared above every module
-- that holds a lifecycle, priority, affinity, SchedContext or retype
-- transition, so the arms' own footprints could not live beside them and this
-- resolver cannot live beside its object-domain twin.

open SeLe4n.Kernel.Concurrency (SyscallLockOperands)

/-- **WS-RR RR8.12 Cut C4: the scheduler-domain footprint the live syscall seam
declares**, at the decoded arm and the operands that arm's capability names.

Sixteen arms declare; the other nineteen answer `none`.  Each declared arm is
`LockSet.ofList?` of its own resolved footprint, and that constructor's
`Nodup` obligation is `schedFootprintOfCores_keys_nodup` — so it provably never
refuses a footprint this kernel declares, which the per-arm `_isSome_iff`
characterisations below state.

**Every arm reads the operands the transition reads, and nothing else.**  Where
an operand is absent the arm answers `none`, which is the fail-closed direction
`SyscallLockOperands` has had since WS-RR RR7.10 and the one this file's object
domain twin already takes for a `.send` with no message: defaulting would
declare a footprint for a *different* transition.  `.call` needs the invoked
capability's rights and the receiver's slot base because its write set re-runs
the dispatch; `.reply` needs the `MessageInfo` and the register payload because
`decodeFaultReply` reads them to tell a restart from an abandon, and the abandon
is the one core the dispatch-level footprint never names; `.tcbSetAffinity`
needs the destination core, whose own `Option` is the unpin request and so must
not be collapsed with "not supplied".

**`.notificationSignal` routes to the BOUND arm**, which is the one the live
dispatch takes — Cut 7's own note, and the reason
`schedLockSet_notificationSignalBoundOnCore` exists beside the unbound one.

**`.reply` routes to the ARM's footprint, not the dispatch's**
(`schedLockSet_replyTransferOnCore`): `v0.35.163` proved the abandon's home-core
member is one the dispatch never writes, so a resolver that named the dispatch's
would be short by it.

**Reachable from the ABI seam since Cut C4b** (§14's
`declaredSchedulerLockSetForAbiEntry`), which is what makes the paragraph above a
statement about the live entry rather than about a resolver nobody calls.  Cut
C4 shipped this with `abiEntryLockOperands` (`SyscallLockBracket.lean`) building
its operands for the object domain alone: it supplied none of the five fields
named above, so `.call`, `.reply`, `.replyRecv` and `.tcbSetAffinity` would each
have answered `none` — an *undeclared* arm, which the bracket treats as "no
exclusion established" and which is therefore sound, and which would have
silently dropped four arms out of the very coverage this workstream is building.
C4b extended that one builder rather than adding a second: **the two domains
share `abiEntryPlan` and `abiEntryLockOperands`**
(`declaredSchedulerLockSetForAbiEntry_shares_decode`), so the syscall id, the caller
and the operands each domain's footprint is a function of are one decode.  A
second builder is the shape that lets one domain's footprint be acquired around
the other domain's transition. -/
def schedLockSetForSyscall (sid : SyscallId) (ops : SyscallLockOperands)
    (executingCore : CoreId) (st : SystemState) : Option LockSet :=
  match sid with
  | .tcbSuspend =>
      ops.targetThread.bind fun victim =>
        victim.toValid?.bind fun vtid =>
          LockSet.ofList? (schedLockSet_suspendThreadOnCore st vtid executingCore)
  | .tcbResume =>
      ops.targetThread.bind fun target =>
        target.toValid?.bind fun vtid =>
          LockSet.ofList? (schedLockSet_resumeThreadOnCore st vtid executingCore)
  | .tcbSetPriority | .tcbSetMCPriority =>
      ops.targetThread.bind fun target =>
        LockSet.ofList? (schedLockSet_priorityControlOnCore st target executingCore)
  | .tcbSetAffinity =>
      ops.targetThread.bind fun target =>
        ops.affinity.bind fun newCore =>
          LockSet.ofList? (schedLockSet_setThreadCpuAffinityOnCore st target newCore)
  | .schedContextConfigure =>
      ops.targetObject.bind fun scObjId =>
        LockSet.ofList? (schedLockSet_schedContextConfigureOnCore st scObjId)
  | .schedContextBind =>
      ops.targetThread.bind fun target =>
        LockSet.ofList? (schedLockSet_schedContextBindOnCore st target)
  | .schedContextUnbind =>
      ops.targetObject.bind fun scObjId =>
        LockSet.ofList? (schedLockSet_schedContextUnbindOnCore st scObjId executingCore)
  | .lifecycleRetype =>
      ops.targetObject.bind fun target =>
        LockSet.ofList? (schedLockSet_lifecycleRetypeOnCore st target)
  | .notificationSignal =>
      ops.targetObject.bind fun nId =>
        LockSet.ofList? (schedLockSet_notificationSignalBoundOnCore st nId)
  | .notificationWait =>
      LockSet.ofList? (schedLockSet_notificationWaitOnCore executingCore)
  | .send =>
      ops.targetObject.bind fun epId =>
        LockSet.ofList? (schedLockSet_endpointSendOnCore st epId executingCore)
  -- **WS-LS LS2.3**: the receiver's CSpace root is read the way `.replyRecv`'s
  -- is (`abiEntrySchedReceiverCspaceRoot`), and the slot base is the syscall's
  -- own operand, because the footprint now re-runs the receive leg to read the
  -- chain walk's write set at the state the walk runs on.
  | .receive =>
      ops.targetObject.bind fun epId =>
        ops.receiverSlotBase.bind fun slotBase =>
          (st.getTcb? ops.caller).bind fun receiver =>
            LockSet.ofList?
              (schedLockSet_endpointReceiveOnCore st epId ops.caller ops.targetReply
                receiver.cspaceRoot slotBase executingCore)
  -- **WS-LS LS2.3**: read at the state the arm's own extra-capability
  -- resolution leaves.  `endpointCallDispatchWriteSet` re-runs the dispatch,
  -- and the dispatch reads the derivation nodes that resolution mints, so a
  -- footprint read before it would be a footprint for a leg run on a different
  -- derivation tree.  The root and depth are the caller's own, as the gate's
  -- are (`abiEntryGate_components`); the grant bit travels on the message.
  | .call =>
      ops.targetObject.bind fun epId =>
        ops.message.bind fun msg =>
          ops.endpointRights.bind fun rights =>
            ops.receiverSlotBase.bind fun slotBase =>
              (st.getTcb? ops.caller).bind fun callerTcb =>
                (st.getCNode? callerTcb.cspaceRoot).bind fun rootCn =>
                  LockSet.ofList?
                    (schedLockSet_endpointCallOnCore epId ops.caller msg rights slotBase
                      executingCore
                      (resolveExtraCaps callerTcb.cspaceRoot ops.extraCapAddrs rootCn.depth
                        msg.capsGranted st).2)
  | .reply =>
      ops.targetReply.bind fun rid =>
        (replyAnsweredCaller? st rid).bind fun answered =>
          ops.message.bind fun msg =>
            ops.replyMessageInfo.bind fun mi =>
              ops.replyRegisters.bind fun regs =>
                LockSet.ofList?
                  (schedLockSet_replyTransferOnCore ops.caller answered mi regs msg
                    executingCore st)
  | .replyRecv =>
      ops.targetObject.bind fun epId =>
        ops.targetReply.bind fun rid =>
          (replyAnsweredCaller? st rid).bind fun prevCaller =>
            (st.getTcb? ops.caller).bind fun receiver =>
              ops.message.bind fun msg =>
                ops.receiverSlotBase.bind fun slotBase =>
                  LockSet.ofList?
                    (schedLockSet_endpointReplyRecvOnCore epId ops.caller rid prevCaller msg
                      receiver.cspaceRoot slotBase executingCore st)
  | .cspaceMint | .cspaceCopy | .cspaceMove | .cspaceDelete | .cspaceRevoke
  | .untypedRetype | .untypedReset
  | .mintReplyCap
  | .vspaceMap | .vspaceUnmap | .vspaceUnifyInstruction
  | .serviceRegister | .serviceRevoke | .serviceQuery
  | .tcbSetIPCBuffer | .tcbSetFaultHandler | .tcbSetSpace | .pageTableMap | .pageTableUnmap
  | .tcbBindNotification | .tcbUnbindNotification
  | .declassify | .declassifySignal
  | .auditRead | .auditDrain => none

/-- **Cut C4**: the arms `schedLockSetForSyscall` declares a footprint for.

A second enumeration beside that `match`, and here for the same reason
`declaredFootprintSyscall` is: the negative below has to name a set.  What
matters is which way it can drift, and both are closed.  Converting an arm to a
footprint without listing it here breaks
`schedLockSetForSyscall_undeclared_none` at elaboration; listing an arm that
still answers `none` is refused by that arm's own `_isSome_iff`, which states
the exact operands under which it declares.

There are `SyscallId.count = 41` arms; **sixteen** declare and twenty-five
answer `none`.  *Which* of those twenty-five write a scheduler slot at all is this
enumeration's own open question — the arms above are the ones WS-RR RR8.12's
sequence identified, and a twenty-sixth found to write one is a footprint to
declare rather than a row to move.  `.cspaceRevoke` (`v0.35.190`) is in the
`none` group for the same reason its `.cspaceDelete` sibling is: the revocation
family writes CNodes, the derivation tree and in-flight messages, and no
run-queue or replenish-queue slot on any core.  `.untypedRetype` (`v0.36.5`) is
there too: a carve writes an untyped, a fresh frame, one CNode slot, the CDT and
a page of machine memory — no scheduler field at all.  `.untypedReset` (`v0.36.6`)
writes VSpace roots, TLB, shootdown and instruction-cache state, erased frames
and the untyped — the `.vspaceUnmap` arm's writes, per mapping, and no run-queue
or replenish-queue slot on any core (`untypedReset_ok_frame`: the scheduler is
unchanged).  `.tcbSetSpace` (`v0.36.11`) rewrites one suspended TCB's two root
fields and nothing else (`setThreadSpace_ok`: the post-state is the pre-state
with one object-table insert). -/
def declaredSchedFootprintSyscall : SyscallId → Bool
  | .tcbSuspend | .tcbResume
  | .tcbSetPriority | .tcbSetMCPriority | .tcbSetAffinity
  | .schedContextConfigure | .schedContextBind | .schedContextUnbind
  | .lifecycleRetype
  | .notificationSignal | .notificationWait
  | .send | .receive | .call | .reply | .replyRecv => true
  | .cspaceMint | .cspaceCopy | .cspaceMove | .cspaceDelete | .cspaceRevoke
  | .untypedRetype | .untypedReset
  | .mintReplyCap
  | .vspaceMap | .vspaceUnmap | .vspaceUnifyInstruction
  | .serviceRegister | .serviceRevoke | .serviceQuery
  | .tcbSetIPCBuffer | .tcbSetFaultHandler | .tcbSetSpace | .pageTableMap | .pageTableUnmap
  | .tcbBindNotification | .tcbUnbindNotification
  | .declassify | .declassifySignal
  | .auditRead | .auditDrain => false

/-- **Cut C4**: every arm this module has not declared is undeclared, whatever
the operands and whatever the state.

The load-bearing direction, and the object domain's own reason: a caller reading
`some S` treats `S` as the complete set of **cores** the transition writes, so
an arm that returned a footprint before its coverage proof existed would hand
out exclusion the runtime never established.  Adding the next declared arm must
change `declaredSchedFootprintSyscall`, and forgetting to stops this
elaborating. -/
theorem schedLockSetForSyscall_undeclared_none (sid : SyscallId)
    (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (h : declaredSchedFootprintSyscall sid = false) :
    schedLockSetForSyscall sid ops executingCore st = none := by
  cases sid <;> first | rfl | exact absurd h (by simp [declaredSchedFootprintSyscall])

/-! ### The per-arm characterisations

Each says exactly which operands its arm needs, which is what closes the other
direction of `declaredSchedFootprintSyscall`'s drift: an arm listed there that
had quietly become unconditionally `none` could not satisfy its own `iff`.

Two things they establish besides.  **`LockSet.ofList?` never refuses a
footprint this kernel declares** — every one of them is
`schedFootprintOfCores`, whose keys are `Nodup` by
`schedFootprintOfCores_keys_nodup` — so no arm's condition mentions the
constructor, and the fail-closed path exists for a footprint spelled some other
way.  And **the scheduler domain needs the caller's TCB on one arm only**,
`.replyRecv`, where the receiver's CSpace root enters the write set through the
capability transfer; the object domain needs it on all eight of its arms,
because there every footprint names the caller's CNode. -/

/-- `.notificationWait` declares unconditionally: its footprint is the executing
core's run-queue lock and nothing the state or the operands can withhold. -/
@[simp] theorem schedLockSetForSyscall_notificationWait_isSome
    (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState) :
    (schedLockSetForSyscall .notificationWait ops executingCore st).isSome := by
  simp [schedLockSetForSyscall, LockSet.ofList?, schedLockSet_notificationWaitOnCore,
    schedFootprintOfCores_keys_nodup]

/-- The four object-directed arms declare exactly when the operand naming the
object is supplied. -/
theorem schedLockSetForSyscall_objectDirected_isSome_iff
    (sid : SyscallId) (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (h : sid = .schedContextConfigure ∨ sid = .schedContextUnbind ∨
         sid = .lifecycleRetype ∨ sid = .notificationSignal ∨ sid = .send) :
    (schedLockSetForSyscall sid ops executingCore st).isSome ↔ ops.targetObject.isSome := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    (unfold schedLockSetForSyscall
     cases ops.targetObject <;>
       simp [LockSet.ofList?, schedLockSet_schedContextConfigureOnCore,
         schedLockSet_schedContextUnbindOnCore, schedLockSet_lifecycleRetypeOnCore,
         schedLockSet_notificationSignalBoundOnCore, schedLockSet_endpointSendOnCore,
         schedFootprintOfCores_keys_nodup])

/-- `.receive` needs the endpoint, the receiver's slot base and the receiver's
TCB (its CSpace root) — **WS-LS LS2.3**: its footprint re-runs the receive leg,
which reads all three. -/
theorem schedLockSetForSyscall_receive_isSome_iff
    (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState) :
    (schedLockSetForSyscall .receive ops executingCore st).isSome
      ↔ ops.targetObject.isSome ∧ ops.receiverSlotBase.isSome ∧
        (st.getTcb? ops.caller).isSome := by
  unfold schedLockSetForSyscall
  cases ops.targetObject <;> cases ops.receiverSlotBase <;> cases st.getTcb? ops.caller <;>
    simp [LockSet.ofList?, schedLockSet_endpointReceiveOnCore,
      schedFootprintOfCores_keys_nodup]

/-- The two thread-directed priority arms declare on the target alone. -/
theorem schedLockSetForSyscall_priority_isSome_iff
    (sid : SyscallId) (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (h : sid = .tcbSetPriority ∨ sid = .tcbSetMCPriority ∨ sid = .schedContextBind) :
    (schedLockSetForSyscall sid ops executingCore st).isSome ↔ ops.targetThread.isSome := by
  rcases h with rfl | rfl | rfl <;>
    (unfold schedLockSetForSyscall
     cases ops.targetThread <;>
       simp [LockSet.ofList?, schedLockSet_priorityControlOnCore,
         schedLockSet_schedContextBindOnCore, schedFootprintOfCores_keys_nodup])

/-- `.tcbSetAffinity` needs the destination core as well, and its outer `Option`
is the one that says whether the caller supplied it at all. -/
theorem schedLockSetForSyscall_tcbSetAffinity_isSome_iff
    (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState) :
    (schedLockSetForSyscall .tcbSetAffinity ops executingCore st).isSome
      ↔ ops.targetThread.isSome ∧ ops.affinity.isSome := by
  unfold schedLockSetForSyscall
  cases ops.targetThread <;> cases ops.affinity <;>
    simp [LockSet.ofList?, schedLockSet_setThreadCpuAffinityOnCore,
      schedFootprintOfCores_keys_nodup]

/-- The two thread-directed lifecycle arms need a target that is not the
reserved sentinel — the same promotion the transitions themselves perform, so
the footprint is declared exactly where the step can run. -/
theorem schedLockSetForSyscall_lifecycle_isSome_iff
    (sid : SyscallId) (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (h : sid = .tcbSuspend ∨ sid = .tcbResume) :
    (schedLockSetForSyscall sid ops executingCore st).isSome
      ↔ ∃ t, ops.targetThread = some t ∧ t.toValid?.isSome := by
  rcases h with rfl | rfl <;>
    (unfold schedLockSetForSyscall
     cases hT : ops.targetThread with
     | none => simp
     | some t =>
        cases hV : t.toValid? <;>
          simp [hV, LockSet.ofList?, schedLockSet_suspendThreadOnCore,
            schedLockSet_resumeThreadOnCore, schedFootprintOfCores_keys_nodup])

/-- `.call` needs the endpoint, the message, the invoked capability's rights,
the receiver's slot base, and (**WS-LS LS2.3**) the caller's TCB and CSpace
root — its write set re-runs the dispatch at the state the arm's
extra-capability resolution leaves, which reads all of them. -/
theorem schedLockSetForSyscall_call_isSome_iff
    (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState) :
    (schedLockSetForSyscall .call ops executingCore st).isSome
      ↔ ops.targetObject.isSome ∧ ops.message.isSome ∧ ops.endpointRights.isSome ∧
        ops.receiverSlotBase.isSome ∧
        ∃ callerTcb, st.getTcb? ops.caller = some callerTcb ∧
          (st.getCNode? callerTcb.cspaceRoot).isSome := by
  unfold schedLockSetForSyscall
  cases ops.targetObject <;> cases ops.message <;> cases ops.endpointRights <;>
    cases ops.receiverSlotBase <;> cases hT : st.getTcb? ops.caller <;>
      simp [LockSet.ofList?, schedLockSet_endpointCallOnCore,
        schedFootprintOfCores_keys_nodup]
  rename_i callerTcb
  cases st.getCNode? callerTcb.cspaceRoot <;> simp

/-- `.reply` needs the Reply object to resolve to an answered caller, and the
message, `MessageInfo` and register payload `decodeFaultReply` reads. -/
theorem schedLockSetForSyscall_reply_isSome_iff
    (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState) :
    (schedLockSetForSyscall .reply ops executingCore st).isSome
      ↔ (∃ rid, ops.targetReply = some rid ∧ (replyAnsweredCaller? st rid).isSome) ∧
        ops.message.isSome ∧ ops.replyMessageInfo.isSome ∧ ops.replyRegisters.isSome := by
  unfold schedLockSetForSyscall
  cases hR : ops.targetReply with
  | none => simp
  | some rid =>
      cases hA : replyAnsweredCaller? st rid <;>
        cases ops.message <;> cases ops.replyMessageInfo <;> cases ops.replyRegisters <;>
          simp [hA, LockSet.ofList?, schedLockSet_replyTransferOnCore,
            schedFootprintOfCores_keys_nodup]

/-- `.replyRecv` needs both targets, the answered caller, the caller's own TCB
(its CSpace root is what the capability transfer writes through), the message
and the receiver's slot base. -/
theorem schedLockSetForSyscall_replyRecv_isSome_iff
    (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState) :
    (schedLockSetForSyscall .replyRecv ops executingCore st).isSome
      ↔ ops.targetObject.isSome ∧
        (∃ rid, ops.targetReply = some rid ∧ (replyAnsweredCaller? st rid).isSome) ∧
        (st.getTcb? ops.caller).isSome ∧ ops.message.isSome ∧ ops.receiverSlotBase.isSome := by
  unfold schedLockSetForSyscall
  cases ops.targetObject with
  | none => simp
  | some _ =>
      cases hR : ops.targetReply with
      | none => simp
      | some rid =>
          cases hA : replyAnsweredCaller? st rid <;>
            cases st.getTcb? ops.caller <;> cases ops.message <;>
              cases ops.receiverSlotBase <;>
                simp [hA, LockSet.ofList?, schedLockSet_endpointReplyRecvOnCore,
                  schedFootprintOfCores_keys_nodup]

/-- **WS-LS LS2.3**: every scheduler footprint names the object-store table
write lock — each of the sixteen arms is `schedFootprintOfCores` of its own
core lists, and that constructor leads with the table lock
(`schedFootprintOfCores_contains_objStore_write`).  What makes the object
clause of `footprintCoversWrites` vacuous at the syscall seam, so the arms'
object writes (register spills, derivation nodes, delivered frames) need no
per-object member. -/
theorem schedLockSetForSyscall_contains_objStore_write (sid : SyscallId)
    (ops : SyscallLockOperands) (executingCore : CoreId) (st : SystemState) (S : LockSet)
    (hS : schedLockSetForSyscall sid ops executingCore st = some S) :
    (LockKey.objStore, Concurrency.AccessMode.write) ∈ S.pairs := by
  unfold schedLockSetForSyscall at hS
  cases sid <;> simp only [Option.bind_eq_some_iff, reduceCtorEq] at hS
  all_goals
    repeat' obtain ⟨_, _, hS⟩ := hS
    rw [LockSet.ofList?_pairs hS]
    simp only [schedLockSet_suspendThreadOnCore, schedLockSet_resumeThreadOnCore,
      schedLockSet_priorityControlOnCore, schedLockSet_setThreadCpuAffinityOnCore,
      schedLockSet_schedContextConfigureOnCore, schedLockSet_schedContextBindOnCore,
      schedLockSet_schedContextUnbindOnCore, schedLockSet_lifecycleRetypeOnCore,
      schedLockSet_notificationSignalBoundOnCore, schedLockSet_notificationWaitOnCore,
      schedLockSet_endpointSendOnCore, schedLockSet_endpointReceiveOnCore,
      schedLockSet_endpointCallOnCore, schedLockSet_replyTransferOnCore,
      schedLockSet_endpointReplyRecvOnCore]
    exact schedFootprintOfCores_contains_objStore_write _ _

-- ============================================================================
-- §2   The ABI entry's scheduler-domain footprint
-- ============================================================================

open SeLe4n.Kernel.Concurrency (LockSet lockSetForSyscall)

/-- **WS-RR RR8.12 Cut C4b: the scheduler-domain footprint the live ABI seam
declares** — `declaredLockSetForAbiEntry`'s twin, clause for clause.

`schedLockSetForSyscall` at the **decoded** syscall id, the caller the executing
core is running, and the operands that caller's capability names, every input
derived from the entry's own resolution rather than supplied alongside it.  A
caller cannot bracket one syscall's scheduler footprint around another's.

**It shares `abiEntryPlan` and `abiEntryLockOperands` with the object domain**
rather than re-deriving either, which is what makes "the two domains bracket the
same syscall" a fact rather than a hope: a decode that resolves differently for
the two would put one domain's footprint around the other domain's transition.
Cut C4b is what made that sharing possible — the builder now supplies the five
operands the scheduler footprints read and the eight arms the object domain
declares nothing for, so the two resolvers see one decode and disagree only
about which *locks* it implies. -/
def declaredSchedulerLockSetForAbiEntry (ctx : LabelingContext) (executingCore : CoreId)
    (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 : UInt64) (st : SystemState) :
    Option LockSet :=
  match abiEntryPlan ctx executingCore syscallId x0 x1 x2 x3 x4 x5 st with
  | none => none
  | some (tid, decoded, stFilled) =>
    (abiEntryLockOperands decoded tid stFilled).bind
      (fun ops => schedLockSetForSyscall decoded.syscallId ops executingCore stFilled)

/-- **Cut C4b**: an entry whose plan does not resolve declares nothing — the
fail-closed direction the object domain's resolver takes for the same reason,
and the one a bracket reads as "no exclusion established". -/
@[simp] theorem declaredSchedulerLockSetForAbiEntry_of_no_plan (ctx : LabelingContext)
    (executingCore : CoreId) (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 : UInt64)
    (st : SystemState)
    (h : abiEntryPlan ctx executingCore syscallId x0 x1 x2 x3 x4 x5 st = none) :
    declaredSchedulerLockSetForAbiEntry ctx executingCore syscallId x0 x1 x2 x3 x4 x5 st
      = none := by
  unfold declaredSchedulerLockSetForAbiEntry
  rw [h]

/-- **Cut C4b**: and an entry whose decoded arm is undeclared declares nothing,
whatever its operands resolve to.

The seam-level reading of `schedLockSetForSyscall_undeclared_none`, and the
statement a bracket needs: the nineteen arms this workstream has not given a
scheduler footprint fall back to the coarse serialisation rather than acquiring
a footprint nobody proved covers them. -/
theorem declaredSchedulerLockSetForAbiEntry_undeclared_none (ctx : LabelingContext)
    (executingCore : CoreId) (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 : UInt64)
    (st : SystemState) (tid : SeLe4n.ThreadId) (decoded : SyscallDecodeResult)
    (stFilled : SystemState)
    (hPlan : abiEntryPlan ctx executingCore syscallId x0 x1 x2 x3 x4 x5 st
      = some (tid, decoded, stFilled))
    (h : declaredSchedFootprintSyscall decoded.syscallId = false) :
    declaredSchedulerLockSetForAbiEntry ctx executingCore syscallId x0 x1 x2 x3 x4 x5 st
      = none := by
  unfold declaredSchedulerLockSetForAbiEntry
  rw [hPlan]
  simp only
  cases hOps : abiEntryLockOperands decoded tid stFilled with
  | none => rfl
  | some ops =>
      simp only [Option.bind_some]
      exact schedLockSetForSyscall_undeclared_none decoded.syscallId ops executingCore stFilled h

/-- **Cut C4b**: the two domains resolve ONE decode.

Stated rather than left to be read off two definitions: both resolvers run
`abiEntryPlan` and then `abiEntryLockOperands` on its answer, so the syscall id,
the caller and the operands each domain's footprint is a function of are the same
three values.  A decode resolved twice is the shape that lets one domain's
footprint be acquired around the other domain's transition. -/
theorem declaredSchedulerLockSetForAbiEntry_shares_decode (ctx : LabelingContext)
    (executingCore : CoreId) (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 : UInt64)
    (st : SystemState) (tid : SeLe4n.ThreadId) (decoded : SyscallDecodeResult)
    (stFilled : SystemState) (ops : SyscallLockOperands)
    (hPlan : abiEntryPlan ctx executingCore syscallId x0 x1 x2 x3 x4 x5 st
      = some (tid, decoded, stFilled))
    (hOps : abiEntryLockOperands decoded tid stFilled = some ops) :
    declaredLockSetForAbiEntry ctx executingCore syscallId x0 x1 x2 x3 x4 x5 st
        = lockSetForSyscall decoded.syscallId ops stFilled ∧
    declaredSchedulerLockSetForAbiEntry ctx executingCore syscallId x0 x1 x2 x3 x4 x5 st
        = schedLockSetForSyscall decoded.syscallId ops executingCore stFilled := by
  refine ⟨?_, ?_⟩
  · unfold declaredLockSetForAbiEntry
    rw [hPlan]
    simp only
    rw [hOps]
    rfl
  · unfold declaredSchedulerLockSetForAbiEntry
    rw [hPlan]
    simp only
    rw [hOps]
    rfl

/-- **Cut C4b**: the receiver CSpace root the `.replyRecv` footprint resolves IS
the root the live arm installs through.

The live arm hands `endpointReplyRecvOnCore` the **gate's** `cspaceRoot`; the scheduler
resolver has no gate to read, so it takes the caller's TCB at the same state.
`abiEntryLockOperands_caller` says that caller is the entry's own `tid`, and
`abiEntryGate_cspaceRoot` says the gate's root is that thread's — so the two are
one lookup rather than two readings of one question, which is the shape that
would let a footprint name a root the transition does not walk. -/
theorem abiEntrySchedReceiverCspaceRoot (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (s : SystemState) (ops : Concurrency.SyscallLockOperands)
    (tcb : TCB) (gate : SyscallGate)
    (hOps : abiEntryLockOperands decoded tid s = some ops)
    (hGate : abiEntryGate decoded tid s = some (tcb, gate)) :
    s.getTcb? ops.caller = some tcb ∧ gate.cspaceRoot = tcb.cspaceRoot := by
  obtain ⟨hLookup, hRoot, _⟩ := abiEntryGate_cspaceRoot decoded tid s tcb gate hGate
  rw [abiEntryLockOperands_caller decoded tid s ops hOps]
  exact ⟨hLookup, hRoot⟩

-- ============================================================================
-- §3   The UNIFIED syscall footprint — one ladder over both domains
-- ============================================================================

/-- **WS-RR RR8.12 Cut C6h: the syscall seam's UNIFIED footprint.**

One `LockSet` spanning both lock domains, which is what `LockKey` was
introduced for (SM5.A.2) and what the seam has never had.  The two domains are
not two lock *words*: `acquireLock`'s `.object` arm calls SM3.C's own
`acquireLockOnObject`, so a `.object` member writes exactly the state a `LockSet`
member writes.  Bracketing them separately would therefore acquire the table lock
**twice** on the five arms whose object footprint names `stateLevelLock`, and —
worse — would walk the SM0.I ladder backwards: the inner bracket's level-0 table
lock would be taken after the outer bracket's levels 1..9.  `lockAcquireSequence`
sorts one list, so one footprint is one ladder.

**WS-LS LS2.3** reshaped the arms around one rule: *a declared footprint is a
covered footprint*.  `BracketSpec.covers` is a proof field, so a footprint the
seam cannot prove covers the step is not one it may declare.

* **the scheduler domain declares nothing** — `none`, whatever the object domain
  says, and the bracket falls back to the unbracketed step.  Until LS2.3 an
  object-only answer was declared on its own; it named no run-queue lock, and
  every declared arm writes a scheduling slot, so that footprint could never
  carry the coverage proof the record now demands.  The scheduler domain is
  the one that names cores, and a footprint without a scheduler answer has no
  coverage claim to make.
* **the scheduler domain declares** — its footprint, with the object domain's
  members merged in by `LockSet.union` when it declares too (one key, one
  member, at the stronger of the two modes — **WS-LS LS1.2**), and with the
  **executing core's run-queue write lock** inserted by `LockSet.insertOrMerge`.

The last member is the seam's own: `syscallDispatchCrossCoreStep` follows every
arm with `scheduleLocalSuccessorFrom` and `settleResidencyOnCore` on the
executing core, which select a successor when the arm vacated it and defer a
thread still resident elsewhere — writes to that core's run queue and `current`
slot that are nobody's arm's.  Nine arms' own write sets already name the
executing core (`resumeThreadOnCoreWriteSet`, `priorityControlWriteSet`, …);
the others (`.tcbSetAffinity`, the two SchedContext arms directed at an object,
`.lifecycleRetype`, the rendezvous paths of the IPC arms) name only the
cores the arm moves, so the seam adds the lock its own tail needs rather than
widening sixteen per-arm sets for a write that is not theirs.  No replenish
member is added: the tail's scheduling points move no scheduling context
(`handleRescheduleSgiOnCore_replenishQueueOnCore`,
`deferResidentElsewhere`'s legs likewise). -/
def unifiedLockSetForSyscall (sid : SyscallId) (ops : Concurrency.SyscallLockOperands)
    (executingCore : CoreId) (st : SystemState) : Option LockSet :=
  match schedLockSetForSyscall sid ops executingCore st with
  | none => none
  | some S =>
    some ((match Concurrency.lockSetForSyscall sid ops st with
           | none => S
           | some O => S.union O).insertOrMerge (LockKey.runQueue executingCore)
            Concurrency.AccessMode.write)

/-- **Cut C6h**: an arm the scheduler domain does not declare yields no unified
footprint (**WS-LS LS2.3**: whatever the object domain declares).

The statement a bracket reads as "no exclusion established", and the one that
makes the fallback arm reachable rather than notional. -/
@[simp] theorem unifiedLockSetForSyscall_undeclared (sid : SyscallId)
    (ops : Concurrency.SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (hSched : schedLockSetForSyscall sid ops executingCore st = none) :
    unifiedLockSetForSyscall sid ops executingCore st = none := by
  unfold unifiedLockSetForSyscall
  rw [hSched]

/-- **Cut C6h**: where only the scheduler domain declares, the unified footprint
IS the scheduler footprint, plus the seam's own executing-core member
(**WS-LS LS2.3**) — no reordering, definitionally. -/
@[simp] theorem unifiedLockSetForSyscall_sched_only (sid : SyscallId)
    (ops : Concurrency.SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (S : LockSet)
    (hObj : Concurrency.lockSetForSyscall sid ops st = none)
    (hSched : schedLockSetForSyscall sid ops executingCore st = some S) :
    unifiedLockSetForSyscall sid ops executingCore st
      = some (S.insertOrMerge (LockKey.runQueue executingCore) Concurrency.AccessMode.write) := by
  unfold unifiedLockSetForSyscall
  rw [hSched, hObj]

/-- **WS-LS LS2.3**: a unified footprint is declared only over a scheduler one. -/
theorem unifiedLockSetForSyscall_some_imp_sched (sid : SyscallId)
    (ops : Concurrency.SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (U : LockSet) (hU : unifiedLockSetForSyscall sid ops executingCore st = some U) :
    ∃ S, schedLockSetForSyscall sid ops executingCore st = some S := by
  unfold unifiedLockSetForSyscall at hU
  cases hSched : schedLockSetForSyscall sid ops executingCore st with
  | none => rw [hSched] at hU; cases hU
  | some S => exact ⟨S, rfl⟩

/-- **Cut C6h**: every member the SCHEDULER domain declared is in the unified
footprint.

The direction the coverage family needs: `footprintCoversWrites` is stated
of the scheduler footprint, and it is the unified one the bracket acquires, so a
claim about the first has to reach the second.  Write membership is enough — the
predicate's three clauses are all of the form "a lock the footprint does **not**
name at `write`", and a merge only ever raises a mode
(`LockSet.mem_union_write_of_mem_write`, `LockSet.mem_insertOrMerge_write_of_mem_write`). -/
theorem mem_unifiedLockSetForSyscall_of_sched (sid : SyscallId)
    (ops : Concurrency.SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (S U : LockSet) (l : LockKey)
    (hSched : schedLockSetForSyscall sid ops executingCore st = some S)
    (hU : unifiedLockSetForSyscall sid ops executingCore st = some U)
    (hp : (l, Concurrency.AccessMode.write) ∈ S.pairs) :
    (l, Concurrency.AccessMode.write) ∈ U.pairs := by
  unfold unifiedLockSetForSyscall at hU
  rw [hSched] at hU
  cases hObj : Concurrency.lockSetForSyscall sid ops st with
  | none =>
      rw [hObj] at hU
      exact (Option.some.inj hU) ▸ LockSet.mem_insertOrMerge_write_of_mem_write S _ _ l hp
  | some O =>
      rw [hObj] at hU
      exact (Option.some.inj hU) ▸ LockSet.mem_insertOrMerge_write_of_mem_write (S.union O) _ _ l
        (LockSet.mem_union_write_of_mem_write S O l hp)

/-- **WS-LS LS2.3**: the seam's own member — the executing core's run-queue
write lock is in every unified footprint. -/
theorem mem_unifiedLockSetForSyscall_executingCore (sid : SyscallId)
    (ops : Concurrency.SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (U : LockSet) (hU : unifiedLockSetForSyscall sid ops executingCore st = some U) :
    (LockKey.runQueue executingCore, Concurrency.AccessMode.write) ∈ U.pairs := by
  unfold unifiedLockSetForSyscall at hU
  cases hSched : schedLockSetForSyscall sid ops executingCore st with
  | none => rw [hSched] at hU; cases hU
  | some S =>
      rw [hSched] at hU
      exact (Option.some.inj hU) ▸ LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-LS LS2.3**: and the table write lock — every scheduler footprint names
it (`schedLockSetForSyscall_contains_objStore_write`), and the unified one
keeps every write member of the scheduler's. -/
theorem mem_unifiedLockSetForSyscall_objStore (sid : SyscallId)
    (ops : Concurrency.SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (U : LockSet) (hU : unifiedLockSetForSyscall sid ops executingCore st = some U) :
    (LockKey.objStore, Concurrency.AccessMode.write) ∈ U.pairs := by
  obtain ⟨S, hSched⟩ := unifiedLockSetForSyscall_some_imp_sched sid ops executingCore st U hU
  exact mem_unifiedLockSetForSyscall_of_sched sid ops executingCore st S U _ hSched hU
    (schedLockSetForSyscall_contains_objStore_write sid ops executingCore st S hSched)

/-- **Cut C6h**: and every member the OBJECT domain declared is in it, at its own
mode or subsumed by a write.

The merge is what makes the disjunction necessary: a key the scheduler footprint
already names at `.write` keeps that mode (`LockSet.mem_union_of_mem_right`),
and the executing core's run-queue key is raised to `.write` by the seam's own
insertion (**WS-LS LS2.3**). -/
theorem mem_unifiedLockSetForSyscall_of_object (sid : SyscallId)
    (ops : Concurrency.SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (O U : LockSet) (l : LockKey) (m : Concurrency.AccessMode)
    (hObj : Concurrency.lockSetForSyscall sid ops st = some O)
    (hU : unifiedLockSetForSyscall sid ops executingCore st = some U)
    (hp : (l, m) ∈ O.pairs) :
    (l, m) ∈ U.pairs ∨
      (l, Concurrency.AccessMode.write) ∈ U.pairs := by
  unfold unifiedLockSetForSyscall at hU
  cases hSched : schedLockSetForSyscall sid ops executingCore st with
  | none => rw [hSched] at hU; cases hU
  | some S =>
      rw [hSched, hObj] at hU
      rw [← Option.some.inj hU]
      rcases LockSet.mem_union_of_mem_right S O l m hp with hIn | hIn
      · by_cases hl : l = LockKey.runQueue executingCore
        · subst hl
          exact Or.inr (LockSet.mem_insertOrMerge_write_self _ _)
        · exact Or.inl (LockSet.mem_insertOrMerge_of_mem_of_ne _ _ _ (l, m) hIn hl)
      · exact Or.inr (LockSet.mem_insertOrMerge_write_of_mem_write _ _ _ l hIn)

/-- **WS-RR RR8.12 Cut C6h: the arm's coverage claim reaches what the seam
ACQUIRES.**

The bridge the deletion of `UncoveredLockDomain.syscallSeamSchedulerDomain`
rests on.  Every per-arm coverage theorem in `SyscallSchedContainment` is stated
over `schedLockSetForSyscall`'s answer; what the bracket acquires is
`unifiedLockSetForSyscall`'s, which is that footprint with the object
domain's members merged in and the seam's executing-core member inserted.
`mem_unifiedLockSetForSyscall_of_sched` says every write member of the first
is one of the second, and coverage is monotone upward
(`footprintCoversWrites_mono`), so the claim travels without being restated
— which is what keeps "what does this arm's footprint cover" a single question.

Stated once and generically rather than sixteen times at the arms: an instance
per arm would be sixteen copies of one application, and the next declared arm
would owe a seventeenth.  **WS-LS LS2.3** discharges `hCover` at the seam
(`SyscallSeamCoverage.lean`) rather than assuming it. -/
theorem unifiedLockSetForSyscall_coversWrites (sid : SyscallId)
    (ops : Concurrency.SyscallLockOperands) (executingCore : CoreId) (st : SystemState)
    (S U : LockSet) (st₀ st₁ : SystemState)
    (hSched : schedLockSetForSyscall sid ops executingCore st = some S)
    (hU : unifiedLockSetForSyscall sid ops executingCore st = some U)
    (hCover : footprintCoversWrites S st₀ st₁) :
    footprintCoversWrites U st₀ st₁ :=
  footprintCoversWrites_mono S U st₀ st₁
    (fun l hl => mem_unifiedLockSetForSyscall_of_sched sid ops executingCore st S U l
      hSched hU hl)
    hCover

/-- **WS-RR RR8.12 Cut C6h: the unified footprint the live ABI seam declares.**

`declaredLockSetForAbiEntry`'s and `declaredSchedulerLockSetForAbiEntry`'s successor
at the seam, and their union by construction: it runs `abiEntryPlan` and
`abiEntryLockOperands` once — the same decode both single-domain resolvers read,
which `declaredSchedulerLockSetForAbiEntry_shares_decode` states — and hands the one
answer to `unifiedLockSetForSyscall`.

The two single-domain resolvers are **kept**, not retired: each is what its own
domain's theorems are stated over, and the relation below is what ties them to
what the seam acquires. -/
def declaredUnifiedLockSetForAbiEntry (ctx : LabelingContext) (executingCore : CoreId)
    (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 : UInt64) (st : SystemState) :
    Option LockSet :=
  match abiEntryPlan ctx executingCore syscallId x0 x1 x2 x3 x4 x5 st with
  | none => none
  | some (tid, decoded, stFilled) =>
    (abiEntryLockOperands decoded tid stFilled).bind
      (fun ops => unifiedLockSetForSyscall decoded.syscallId ops executingCore stFilled)

/-- **Cut C6h**: an entry whose plan does not resolve declares nothing — the
fail-closed direction both single-domain resolvers already take. -/
@[simp] theorem declaredUnifiedLockSetForAbiEntry_of_no_plan (ctx : LabelingContext)
    (executingCore : CoreId) (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 : UInt64)
    (st : SystemState)
    (h : abiEntryPlan ctx executingCore syscallId x0 x1 x2 x3 x4 x5 st = none) :
    declaredUnifiedLockSetForAbiEntry ctx executingCore syscallId x0 x1 x2 x3 x4 x5 st
      = none := by
  unfold declaredUnifiedLockSetForAbiEntry
  rw [h]

/-- **Cut C6h**: an entry undeclared in the scheduler domain declares nothing
(**WS-LS LS2.3**: whatever the object domain declares — a footprint without a
scheduler answer has no coverage claim to make, so the seam declares none).

The seam-level fallback condition. -/
theorem declaredUnifiedLockSetForAbiEntry_undeclared (ctx : LabelingContext)
    (executingCore : CoreId) (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 : UInt64)
    (st : SystemState)
    (hSched : declaredSchedulerLockSetForAbiEntry ctx executingCore syscallId
      x0 x1 x2 x3 x4 x5 st = none) :
    declaredUnifiedLockSetForAbiEntry ctx executingCore syscallId x0 x1 x2 x3 x4 x5 st
      = none := by
  unfold declaredUnifiedLockSetForAbiEntry
  unfold declaredSchedulerLockSetForAbiEntry at hSched
  rcases hPlan : abiEntryPlan ctx executingCore syscallId x0 x1 x2 x3 x4 x5 st with
    _ | ⟨tid, decoded, stFilled⟩
  · rfl
  · rw [hPlan] at hSched
    simp only at hSched ⊢
    rcases hOps : abiEntryLockOperands decoded tid stFilled with _ | ops
    · rfl
    · rw [hOps] at hSched
      simp only [Option.bind_some] at hSched ⊢
      exact unifiedLockSetForSyscall_undeclared decoded.syscallId ops executingCore
        stFilled hSched

/-- **Cut C6h**: the seam's unified footprint is the union of what the two
single-domain resolvers declare, at the decode all three share.

The relation that lets a claim stated over either single-domain footprint reach
the set the bracket acquires — stated rather than left to be read off three
definitions, which is the shape that lets one domain's footprint be acquired
around the other domain's transition. -/
theorem declaredUnifiedLockSetForAbiEntry_shares_decode (ctx : LabelingContext)
    (executingCore : CoreId) (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 : UInt64)
    (st : SystemState) (tid : SeLe4n.ThreadId) (decoded : SyscallDecodeResult)
    (stFilled : SystemState) (ops : Concurrency.SyscallLockOperands)
    (hPlan : abiEntryPlan ctx executingCore syscallId x0 x1 x2 x3 x4 x5 st
      = some (tid, decoded, stFilled))
    (hOps : abiEntryLockOperands decoded tid stFilled = some ops) :
    declaredUnifiedLockSetForAbiEntry ctx executingCore syscallId x0 x1 x2 x3 x4 x5 st
      = unifiedLockSetForSyscall decoded.syscallId ops executingCore stFilled := by
  unfold declaredUnifiedLockSetForAbiEntry
  rw [hPlan]
  simp only
  rw [hOps]
  rfl

end SeLe4n.Kernel
