-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SlotConfinement.Legs
import SeLe4n.Kernel.Lifecycle.ResumeFootprint
import SeLe4n.Kernel.Lifecycle.Operations.RetypeFootprint
import SeLe4n.Kernel.IPC.CrossCore.SuspendFootprint

/-!
# Per-core slot confinement — the live IPC and thread-state arms

The functions the syscall arms actually call, bounded by reducing each to
the legs of `SlotConfinement/Legs.lean`: §5b `.call`, §5c `.reply` and
§5c-bis the reply arm past its capability check, §5d `.replyRecv`,
§5e `.tcbSuspend`, §5f `.tcbResume`, §5g `.send`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)
open SeLe4n.Kernel.Lifecycle.Suspend
open SeLe4n.Kernel.PriorityInheritance

-- ============================================================================
-- §5b The live `.call` arm itself
-- ============================================================================
--
-- §5a bounds the legs. This section bounds `endpointCallCrossCoreDispatch` —
-- the function the live `.call` syscall arm actually calls — by reducing it to
-- its own intermediate states rather than taking them as parameters.

/-- SM8.B.2: IPC capability transfer is per-core silent. It rewrites the
receiver's CNode and the CDT, never a run queue and never a register bank, so it
contributes nothing to the cross-core `.call`'s write set. -/
theorem ipcUnwrapCaps_confinedToCores (msg : IpcMessage)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hStep : ipcUnwrapCaps msg receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (ipcUnwrapCaps_preserves_scheduler msg receiverRoot slotBase grantRight
      st st' summary hStep)
    (ipcUnwrapCaps_preserves_machine msg receiverRoot slotBase grantRight
      st st' summary hStep)

-- **WS-RR RR8.12 Cut C3a (`v0.35.163`)**: `endpointCallWithCapsOnCore_scheduler_eq`
-- moved to `IPC/CrossCore/EndpointCallDispatch.lean` §3, beside the leg it frames:
-- the `.call` footprint's exactness licence composes it, and a staged frame is one
-- a production footprint cannot read.  `endpointCallWithCapsOnCore_machine_eq`
-- below stays, having no production consumer.

/-- SM8.B.2: and the register banks, by the same case analysis. -/
theorem endpointCallWithCapsOnCore_machine_eq (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    (endpointCallWithCapsOnCore endpointId caller msg endpointRights
        receiverSlotBase executingCore st).1.machine
      = (endpointCallOnCore endpointId caller { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st).1.machine := by
  unfold endpointCallWithCapsOnCore
  cases hCall : endpointCallOnCore endpointId caller { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st with
  | mk stCall res =>
    cases res with
    | error e => rfl
    | ok sgi =>
      simp only []
      repeat' split
      all_goals first
        | rfl
        | (rename_i h; exact ipcUnwrapCaps_preserves_machine _ _ _ _ _ _ _ h)

/-- SM8.B.2: the **WithCaps** cross-core call — the form the live dispatch calls
— is confined to the bare call's write set. The extra leg is `ipcUnwrapCaps`,
which by the lemma above writes no core at all, so the two forms declare the
same per-core footprint.

Proved through the two frames rather than by re-walking the WithCaps branch
tree: confinement reads only `scheduler` and the register banks, and on both of
those the WithCaps post-state *is* the bare call's. -/
theorem endpointCallWithCapsOnCore_confinedToCores (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointCallWithCapsOnCore endpointId caller msg endpointRights
        receiverSlotBase executingCore st).1
      (endpointCallWriteSet st endpointId executingCore) := by
  have h := observableSlotsConfinedToCores_trans
    (endpointCallOnCore_confinedToCores endpointId caller { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st hObjInv)
    (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
      (endpointCallWithCapsOnCore_scheduler_eq endpointId caller msg endpointRights
        receiverSlotBase executingCore st)
      (endpointCallWithCapsOnCore_machine_eq endpointId caller msg endpointRights
        receiverSlotBase executingCore st))
  simpa using h

-- **WS-RR RR8.12 Cut C3a (`v0.35.163`)**: `endpointCallDispatchChainWriteSet` and
-- `endpointCallDispatchWriteSet` moved to `IPC/CrossCore/EndpointCallDispatch.lean`
-- §3, beside the dispatch they mirror, so the production scheduler footprint
-- `schedLockSet_endpointCallOnCore` can read them.  The confinement theorem below
-- stays here: `observableSlotsConfinedToCores` is this module's predicate.

/-- SM8.B.2 (**the live `.call` bound**): `endpointCallCrossCoreDispatch` — the
function `API.dispatchWithCap`'s `.call` arm routes through — writes no core
outside `endpointCallDispatchWriteSet`.

This is the theorem the composition rule §5a was missing. The proof splits on
exactly the scrutinees the dispatch splits on, so each branch's write set is the
one that branch's states justify: the fail-closed arms and the no-receiver arm
stop at the WithCaps post-state (`endpointCallWriteSet`), and the rendezvous arm
composes WithCaps, the per-core-silent donation and the chain walk at the
post-donation state — `endpointCallLive_confinedToCores` instantiated at the
receiver `ep.receiveQ.head` and the state `applyCallDonation` returns. -/
theorem endpointCallCrossCoreDispatch_confinedToCores (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointCallCrossCoreDispatch endpointId caller msg endpointRights
        receiverSlotBase executingCore st).1
      (endpointCallDispatchWriteSet endpointId caller msg endpointRights
        receiverSlotBase executingCore st) := by
  have hCaps := endpointCallWithCapsOnCore_confinedToCores endpointId caller msg
    endpointRights receiverSlotBase executingCore st hObjInv
  -- A core outside the union is outside the endpoint-call leg, which is what
  -- every arm short of the full rendezvous needs.
  have hWiden : ∀ (stPost : SystemState) (extra : List CoreId),
      observableSlotsConfinedToCores st stPost
        (endpointCallWriteSet st endpointId executingCore) →
      observableSlotsConfinedToCores st stPost
        (endpointCallWriteSet st endpointId executingCore ++ extra) :=
    fun _ _ h => observableSlotsConfinedToCores_mono
      (fun _ hc => List.mem_append.mpr (Or.inl hc)) h
  unfold endpointCallCrossCoreDispatch endpointCallDispatchWriteSet
    endpointCallDispatchChainWriteSet
  cases hWith : endpointCallWithCapsOnCore endpointId caller msg endpointRights
      receiverSlotBase executingCore st with
  | mk stWith res =>
    rw [hWith] at hCaps
    cases res with
    | error e => simp only []; exact hWiden _ _ hCaps
    | ok pair =>
      rcases pair with ⟨summary, sgi⟩
      simp only []
      cases hEp : st.getEndpoint? endpointId with
      | none => simp only []; exact hWiden _ _ hCaps
      | some ep =>
        simp only []
        cases hHead : ep.receiveQ.head with
        | none => simp only []; exact hWiden _ _ hCaps
        | some receiverTid =>
          simp only []
          cases hCallerV : SeLe4n.ThreadId.toValid? caller with
          | none => simp only []; exact hWiden _ _ hCaps
          | some callerV =>
            cases hRecvV : SeLe4n.ThreadId.toValid? receiverTid with
            | none => simp only []; exact hWiden _ _ hCaps
            | some receiverV =>
              simp only []
              cases hDon : applyCallDonationOnCore stWith callerV receiverV
                  (determineTargetCore st caller) (determineTargetCore st receiverTid) with
              | error e => simp only []; exact hWiden _ _ hCaps
              | ok stDon =>
                simp only []
                exact endpointCallLive_confinedToCores st stWith stDon endpointId
                  executingCore receiverTid hCaps
                  (applyCallDonationOnCore_confinedToCores stWith stDon callerV receiverV
                    (determineTargetCore st caller) (determineTargetCore st receiverTid) hDon)

/-- SM8.B.2: on the rendezvous path the live write set **is** the §5a union,
instantiated at the states the dispatch really produces. Stated separately so
the instantiation is visible rather than buried inside the proof above: the
chain start is the resolved receiver and the chain state is the post-donation
state, the two things the second review round said were being supplied by hand. -/
theorem endpointCallDispatchWriteSet_eq_live_of_rendezvous (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st stWith stDon : SystemState) (receiverTid : SeLe4n.ThreadId)
    (callerV receiverV : SeLe4n.ValidThreadId) (summary : CapTransferSummary)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hRecv : (match st.getEndpoint? endpointId with
              | some ep => ep.receiveQ.head
              | none => none) = some receiverTid)
    (hWith : endpointCallWithCapsOnCore endpointId caller msg endpointRights
      receiverSlotBase executingCore st = (stWith, .ok (summary, sgi)))
    (hCallerV : SeLe4n.ThreadId.toValid? caller = some callerV)
    (hRecvV : SeLe4n.ThreadId.toValid? receiverTid = some receiverV)
    (hDon : applyCallDonationOnCore stWith callerV receiverV
      (determineTargetCore st caller) (determineTargetCore st receiverTid) = .ok stDon) :
    endpointCallDispatchWriteSet endpointId caller msg endpointRights
        receiverSlotBase executingCore st
      = endpointCallLiveWriteSet st endpointId executingCore stDon receiverTid := by
  unfold endpointCallDispatchWriteSet endpointCallDispatchChainWriteSet endpointCallLiveWriteSet
  cases hEp : st.getEndpoint? endpointId with
  | none => rw [hEp] at hRecv; simp at hRecv
  | some ep =>
    rw [hEp] at hRecv
    simp only [] at hRecv
    simp only [hWith, hRecv, hCallerV, hRecvV, hDon]

-- ============================================================================
-- §5c The live `.reply` arm itself
-- ============================================================================
--
-- `API.dispatchWithCap`'s `.reply` arm does not call `endpointReplyOnCore`; it
-- calls `endpointReplyCrossCoreDispatch`, which runs the reply, then returns the
-- **recorded server's** donated SchedContext — descheduling that server on *its
-- own* core — then reverts the priority-inheritance chain from that server.
-- Legs two and three can each name a core the reply's own write set does not, so
-- §4's theorem never bounded the live arm (PR #861 review round 4).

-- **WS-RR RR8.12 Cut C3a (`v0.35.163`)**: `replyDonationDescheduleCores` moved to
-- `IPC/CrossCore/EndpointReplyDispatch.lean` §1, beside the two home resolvers it
-- sits with, so the production `.reply` write set can read it.  The confinement
-- theorem below stays here: `observableSlotsConfinedToCores` is this module's
-- predicate.

/-- SM8.B.2 / WS-RR RR2.8, corrected at `v0.35.37`: the cross-core donation
**return** writes at most the core the state **places** the returning server on.
Unlike the call-side `applyCallDonationOnCore` this is *not* per-core silent: the
now-passive server is descheduled where it actually sits, and the core list is
read off `descheduleAtPlacementCores` — the *same* resolver the step itself uses,
so the confinement claim and the transition cannot name different cores.

What this docstring said before is the finding this cut fixes.  It claimed the
server "is descheduled on its own core, which is precisely why
`endpointReplyCrossCoreDispatch` resolves `determineExecutingCore st expected`".
The first half was the intent and the second half did not deliver it:
`determineExecutingCore` finds a core the thread is *current* on and otherwise
answers `bootCoreId`, so a server that was **queued** — preempted, which is the
ordinary fate of a thread that is not running — was descheduled on a core it is
not on, and the step wrote nothing.  A justification that holds only when the
thread happens to be running is not a justification for a step whose whole
purpose is to stop it running.

The other two legs are silent — `returnDonatedSchedContext` moves `boundThread`
in the object store and leaves the scheduler and every register bank alone, and
the RR2.8 replenishment migration writes a queue SM8.A's
`onCore_perCore_independence` puts outside the observer's read set — so the whole
leg still collapses to the one deschedule, and at a replier the state places
nowhere the core list is empty because the step is the identity. -/
theorem applyReplyDonationOnCore_confinedToCores (st st' : SystemState)
    (rid : SeLe4n.ReplyId) (targetVtid : SeLe4n.ValidThreadId)
    (holderHome ownerHome : CoreId)
    (hStep : applyReplyDonationOnCore st rid targetVtid holderHome ownerHome = .ok st') :
    observableSlotsConfinedToCores st st' (replyDonationDescheduleCores st rid) := by
  rcases applyReplyDonationOnCore_ok_decompose st st' rid targetVtid holderHome
    ownerHome hStep with ⟨_, hEq⟩ | ⟨scId, holderVtid, n, stRet, hHead, _, hRet, hEq⟩
  · exact observableSlotsConfinedToCores_of_eq _ hEq
  · -- The core list is stated on the **pre**-state, which is the only state a
    -- caller holds.  That is sound because neither step before the deschedule
    -- moves a thread: the return writes objects alone and the migration writes
    -- replenish queues alone, so the two slices `placedCoreOf?` reads are fixed.
    let stMig : SystemState := migrateSchedContextReplenishment stRet scId holderHome ownerHome
    have hMig : ∀ c : CoreId,
        stMig.scheduler.runQueueOnCore c = stRet.scheduler.runQueueOnCore c
        ∧ stMig.scheduler.currentOnCore c = stRet.scheduler.currentOnCore c :=
      fun c => migrateSchedContextReplenishment_runQueue_current_eq stRet scId
        holderHome ownerHome c
    have hRetSched :=
      returnDonatedSchedContext_scheduler_eq st stRet _ _ _ n hRet
    have hList : replyDonationDescheduleCores st rid
        = descheduleAtPlacementCores st holderVtid.val := by
      unfold replyDonationDescheduleCores; rw [hHead]
    have hCores : descheduleAtPlacementCores stMig holderVtid.val
        = descheduleAtPlacementCores st holderVtid.val := by
      rw [descheduleAtPlacementCores_congr_of_runQueue_current_eq _ hMig]
      unfold descheduleAtPlacementCores
      rw [placedCoreOf?_congr_of_scheduler_eq _ hRetSched]
    rw [hEq, hList, ← hCores]
    exact observableSlotsConfinedToCores_trans
      (by
        simpa using observableSlotsConfinedToCores_trans
          (observableSlotsConfinedToCores_nil_of_scheduler_regs_eq hRetSched
            (fun _ => by rw [returnDonatedSchedContext_machine_eq st stRet _ _ _ n hRet]))
          (migrateSchedContextReplenishment_confinedToCores stRet scId holderHome ownerHome))
      (descheduleAtPlacement_confinedToCores stMig holderVtid.val)

-- **WS-RR RR8.12 Cut C3a (`v0.35.163`)**: `endpointReplyDispatchWriteSet` moved to
-- `IPC/CrossCore/EndpointReplyDispatch.lean` §6, beside the dispatch it mirrors, so
-- the production scheduler footprint `schedLockSet_endpointReplyOnCore` can read
-- it.  The confinement theorem below stays here: `observableSlotsConfinedToCores`
-- is this module's predicate.

/-- SM8.B.2 (**the live `.reply` bound**): `endpointReplyCrossCoreDispatch` — the
function `API.dispatchWithCap`'s `.reply` arm routes through — writes no core
outside `endpointReplyDispatchWriteSet`.

The proof splits on exactly the scrutinees the dispatch splits on, so each
branch's write set is the one that branch's states justify. The fail-closed arms
return the pre-state itself, so they are confined to `[]` and widen into
anything; the success arm composes the reply, the donation return and the chain
walk at the states the dispatch really produces. -/
theorem endpointReplyCrossCoreDispatch_confinedToCores (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointReplyCrossCoreDispatch replier target msg executingCore st).1
      (endpointReplyDispatchWriteSet replier target msg executingCore st) := by
  have hReply := endpointReplyOnCore_confinedToCores replier target msg executingCore st
    hObjInv
  unfold endpointReplyCrossCoreDispatch endpointReplyDispatchWriteSet
  cases hRep : endpointReplyOnCore replier target msg executingCore st with
  | mk st1 res =>
    rw [hRep] at hReply
    cases res with
    | error e => simp only []; exact observableSlotsConfinedToCores_of_eq _ rfl
    | ok replySgi? =>
      simp only []
      cases hSrv : recordedReplyServer? st target with
      | none => simp only []; exact observableSlotsConfinedToCores_of_eq _ rfl
      | some expected =>
        simp only []
        cases hEV : SeLe4n.ThreadId.toValid? expected with
        | none => simp only []; exact observableSlotsConfinedToCores_of_eq _ rfl
        | some _expectedV =>
          simp only []
          cases hRid : answeredReplyObject? st target with
          | none =>
            simp only []
            exact observableSlotsConfinedToCores_trans hReply
              (propagatePipChainCrossCore_confinedToCores executingCore
                st1.objectIndex.length st1 expected)
          | some rid =>
            simp only []
            cases hTV : SeLe4n.ThreadId.toValid? target with
            | none => simp only []; exact observableSlotsConfinedToCores_of_eq _ rfl
            | some targetV =>
              simp only []
              cases hDon : applyReplyDonationOnCore st1 rid targetV
                  (replyDonationHolderHome st1 rid target)
                  (replyDonationRecipientHome st1 rid target) with
              | error e => simp only []; exact observableSlotsConfinedToCores_of_eq _ rfl
              | ok st2 =>
                simp only []
                exact observableSlotsConfinedToCores_trans
                  (observableSlotsConfinedToCores_trans hReply
                    (applyReplyDonationOnCore_confinedToCores st1 st2 rid targetV
                      (replyDonationHolderHome st1 rid target)
                      (replyDonationRecipientHome st1 rid target) hDon))
                  (propagatePipChainCrossCore_confinedToCores executingCore
                    st2.objectIndex.length st2 expected)

-- ============================================================================
-- §5c-bis  WS-RR RR8.12 Cut C6d — the live `.reply` ARM's confinement
-- ============================================================================
--
-- §5c bounds `endpointReplyCrossCoreDispatch`.  The arm `API.dispatchWithCap`
-- actually runs is `replyTransferOnCore` — seL4's `doReplyTransfer` branch —
-- whose post-state is not the dispatch's: on an unfaulted caller it is the
-- dispatch's plus the delivered-message staging, and on a faulted one the
-- dispatch's plus the decoded outcome, which either installs a restart frame or
-- **deschedules** the faulted thread.  So §5c's confinement is a statement about
-- a different state, and nothing said the staging and the outcome write no
-- per-core slot outside the arm's own declared set — which is what
-- `schedLockSet_replyTransferOnCore` (`IPC/CrossCore/Fault.lean` §6) declares.
--
-- **What the extra core costs, measured rather than assumed.**  The abandon's
-- deschedule names `determineTargetCore st' faulted`, read at the dispatch's
-- post-state, and every arm on which the dispatch succeeds opens its write set
-- with `[determineTargetCore st target]`, read at the pre-state — and no step of
-- the dispatch writes a `cpuAffinity`.  So on this tree the appended core is a
-- **duplicate** of one the dispatch already names, which
-- `tests/FaultHandlingSuite.lean` §7c measures directly (the dispatch's set opens
-- with `c0`, and the abandon's is that set `++ [c0]`).  The arm's write set is
-- derived from the arm's own structure all the same, because a declaration
-- tightened to today's coincidence would become false the moment either side
-- moved; the coverage claim below is about the arm's post-state, which is where
-- the content is.
--
-- The three theorems below are the chain: the apply's own confinement at
-- `faultReplyApplyCores`, the fault reply's at `faultReplyWriteSet`, and the
-- seam's at `replyTransferWriteSet` — each stated at the write set that
-- *definition* derives, so the coverage theorem in `SyscallSchedContainment` is
-- one application of `footprintCoversWrites_of_confined` rather than a
-- second reading of the seam.

/-- **Cut C6d**: installing a restart frame is per-core silent.  The frame goes
into the faulted thread's own saved context — an object write — never into the
executing core's register bank, so the restart writes no observable per-core
slot at all. -/
theorem applyFaultRestart_confinedToCores (st : SystemState) (faulted : SeLe4n.ThreadId)
    (frame : Architecture.FaultRestartFrame) :
    observableSlotsConfinedToCores st (applyFaultRestart st faulted frame) [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (applyFaultRestart_scheduler_eq st faulted frame)
    (applyFaultRestart_machine_eq st faulted frame)

/-- **Cut C6d**: abandoning a fault writes core `cc`'s run-queue and current
slots and nothing else per-core — it is `removeRunnableOnCore` followed by an
object write, so its confinement is the deschedule's. -/
theorem faultAbandonOnCore_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (cc : CoreId) :
    observableSlotsConfinedToCores st (faultAbandonOnCore st tid cc) [cc] :=
  observableSlotsConfinedToCores_mono (fun _ hm => by simpa using hm)
    (observableSlotsConfinedToCores_trans
      (removeRunnableOnCore_confinedToCores st tid cc)
      (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
        (faultAbandonOnCore_scheduler_eq st tid cc)
        (faultAbandonOnCore_machine_eq st tid cc)))

/-- **Cut C6d**: the decoded outcome writes exactly the cores
`faultReplyApplyCores` names — none on a restart, the faulted thread's own home
core on an abandon.  The two arms are the definition's own two arms, so the
write set and the transition cannot disagree about which branch names a core. -/
theorem faultReplyApplyOnCore_confinedToCores (st : SystemState)
    (faulted : SeLe4n.ThreadId) (outcome : Architecture.FaultReplyOutcome) :
    observableSlotsConfinedToCores st (faultReplyApplyOnCore st faulted outcome)
      (faultReplyApplyCores st faulted outcome) := by
  unfold faultReplyApplyOnCore faultReplyApplyCores
  cases outcome with
  | restart frame => exact applyFaultRestart_confinedToCores st faulted frame
  | abandon =>
    exact faultAbandonOnCore_confinedToCores st faulted (determineTargetCore st faulted)

/-- **Cut C6d**: the fault reply writes no core outside `faultReplyWriteSet` —
the dispatch's own set at the empty message, then the outcome's, read at the
state the apply runs on.  Every arm on which the seam commits nothing returns
the pre-state and so is confined to `[]`, which widens into anything. -/
theorem faultReplyOnCore_confinedToCores (replier faulted : SeLe4n.ThreadId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (faultReplyOnCore replier faulted mi regs executingCore st).1
      (faultReplyWriteSet replier faulted mi regs executingCore st) := by
  have hDispatch := endpointReplyCrossCoreDispatch_confinedToCores replier faulted
    IpcMessage.empty executingCore st hObjInv
  unfold faultReplyOnCore faultReplyWriteSet
  cases hTcb : st.getTcb? faulted with
  | none => exact observableSlotsConfinedToCores_of_eq _ rfl
  | some tcb =>
    simp only []
    cases hPF : tcb.pendingFault with
    | none => simp only []; exact observableSlotsConfinedToCores_of_eq _ rfl
    | some tf =>
      simp only []
      cases hDisp : endpointReplyCrossCoreDispatch replier faulted IpcMessage.empty
          executingCore st with
      | mk stDisp res =>
        rw [hDisp] at hDispatch
        cases res with
        | error e => simp only []; exact observableSlotsConfinedToCores_of_eq _ rfl
        | ok sgi? =>
          simp only []
          exact observableSlotsConfinedToCores_trans hDispatch
            (faultReplyApplyOnCore_confinedToCores stDisp faulted
              (Architecture.decodeFaultReply tf.fault tf.context mi regs))

/-- **Cut C6d** (**the live `.reply` arm's bound**): `replyTransferOnCore` — the
transition `API.dispatchWithCap`'s `.reply` arm routes through — writes no core
outside `replyTransferWriteSet`.

The branch is the seam's own predicate `threadHasPendingFault`, so the bound and
the transition cannot disagree about which caller is faulted; the unfaulted arm
composes the dispatch with the delivered-message staging, which writes a
register *context* and no per-core slot. -/
theorem replyTransferOnCore_confinedToCores (replier callerTid : SeLe4n.ThreadId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (msg : IpcMessage)
    (executingCore : CoreId) (st st' : SystemState) (hObjInv : st.objects.invExt)
    (hStep : replyTransferOnCore replier callerTid mi regs msg executingCore st
      = .ok ((), st')) :
    observableSlotsConfinedToCores st st'
      (replyTransferWriteSet replier callerTid mi regs msg executingCore st) := by
  by_cases hF : threadHasPendingFault st callerTid = true
  · rw [replyTransferOnCore_of_fault replier callerTid mi regs msg executingCore st hF]
      at hStep
    rw [replyTransferWriteSet_of_fault replier callerTid mi regs msg executingCore st hF]
    have hFR := faultReplyOnCore_confinedToCores replier callerTid mi regs executingCore st
      hObjInv
    cases hFRO : faultReplyOnCore replier callerTid mi regs executingCore st with
    | mk stF res =>
      rw [hFRO] at hFR hStep
      cases res with
      | error e => simp only [] at hStep; exact absurd hStep (by simp)
      | ok out =>
        simp only [] at hStep
        have hEq : stF = st' := congrArg Prod.snd (Except.ok.inj hStep)
        subst hEq
        exact hFR
  · have hNF : threadHasPendingFault st callerTid = false := by
      simpa using hF
    rw [replyTransferOnCore_of_no_fault replier callerTid mi regs msg executingCore st hNF]
      at hStep
    rw [replyTransferWriteSet_of_no_fault replier callerTid mi regs msg executingCore st hNF]
    have hDispatch := endpointReplyCrossCoreDispatch_confinedToCores replier callerTid msg
      executingCore st hObjInv
    cases hDisp : endpointReplyCrossCoreDispatch replier callerTid msg executingCore st with
    | mk stDisp res =>
      rw [hDisp] at hDispatch hStep
      cases res with
      | error e => simp only [] at hStep; exact absurd hStep (by simp)
      | ok sgi? =>
        simp only [] at hStep
        have hEq : Architecture.stageDeliveredMessage stDisp callerTid 0 = st' :=
          congrArg Prod.snd (Except.ok.inj hStep)
        subst hEq
        exact observableSlotsConfinedToCores_mono (fun _ hm => by simpa using hm)
          (observableSlotsConfinedToCores_trans hDispatch
            (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
              (Architecture.stageDeliveredMessage_scheduler_eq stDisp callerTid 0)
              (Architecture.stageDeliveredMessage_machine_eq stDisp callerTid 0)))

-- ============================================================================
-- §5d The live `.replyRecv` arm itself
-- ============================================================================
--
-- `API.dispatchWithCap`'s `.replyRecv` arm routes to `endpointReplyRecvOnCore`, which is
-- the reply leg, `replyRecvPopDonation`, the receive leg **and**
-- `replyRecvPostReceiveDonation` — the last of which may donate the new client's
-- SchedContext, may deschedule the now-passive recorded server on its own core,
-- and always reverts the recorded server's priority-inheritance chain.  Until
-- `v0.36.49` that name denoted a two-leg composite (reply, then the bare receive
-- leg of §4a) no arm called, so the theorems below were about code that never
-- ran; the live body carries the name now and they bound the arm itself.
--
-- **WS-RM (`v0.35.6`)**: the pop sits *between* the two legs, matching
-- seL4-MCS's `doReplyTransfer` → `reply_remove` → `receiveIPC` order.  It writes
-- no core (`replyRecvPopDonation_confinedToCores`), so the arm's declared set is
-- unchanged by the move.

-- **WS-RR RR8.12 Cut 8b (`v0.35.145`)**: `replyRecvDescheduleAndWalkWriteSet` moved out of this module,
-- beside the transition it describes (since `v0.36.49` both live in
-- `IPC/CrossCore/EndpointReplyRecv.lean`).  A write set declared in a STAGED module is one the
-- production scheduler footprint cannot read, which is the layering rule Cuts 5
-- and 7 applied four times over.  The CONFINEMENT theorem stays here: it is an
-- SM8.B claim about `observableSlotsConfinedToCores`, which is this module's.

theorem replyRecvDescheduleAndWalk_confinedToCores (holder recordedServer : SeLe4n.ThreadId)
    (serverCore : CoreId) (st : SystemState) :
    observableSlotsConfinedToCores st
      (propagatePipChainCrossCore (descheduleAtPlacement st holder)
        recordedServer serverCore
        (descheduleAtPlacement st holder).objectIndex.length).1
      (replyRecvDescheduleAndWalkWriteSet holder recordedServer serverCore st) :=
  observableSlotsConfinedToCores_trans
    (descheduleAtPlacement_confinedToCores st holder)
    (propagatePipChainCrossCore_confinedToCores serverCore
      (descheduleAtPlacement st holder).objectIndex.length
      (descheduleAtPlacement st holder) recordedServer)

/-- **WS-RM (`v0.35.6`)**: the pop half writes **no** core.  Both its effects are
per-core silent — the donation return writes neither a scheduler slot nor the
machine, and SM8.A's `onCore_perCore_independence` puts the replenish queue
outside the observer's read set — so every core the fused resolution names comes
from its post-receive half.  That is what lets `endpointReplyRecvOnCore` move the pop to
the other side of the receive leg without its declared set changing. -/
theorem replyRecvPopDonation_confinedToCores (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId)
    (st st' : SystemState) (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (hStep : replyRecvPopDonation rid target st = .ok (returned?, st')) :
    observableSlotsConfinedToCores st st' [] := by
  unfold replyRecvPopDonation at hStep
  cases hHead : replyFrameHeadHolder? st rid with
  | none =>
      rw [hHead] at hStep
      have hEq : st = st' := (by simpa using hStep : none = returned? ∧ _).2
      rw [← hEq]; exact observableSlotsConfinedToCores_refl st []
  | some pair =>
    obtain ⟨oldScId, holder⟩ := pair
    rw [hHead] at hStep
    simp only [] at hStep
    cases hHV : holder.toValid? with
    | none => rw [hHV] at hStep; simp only [] at hStep; cases hStep
    | some holderV =>
      cases hTV : target.toValid? with
      | none => rw [hHV, hTV] at hStep; simp only [] at hStep; cases hStep
      | some targetV =>
        rw [hHV, hTV] at hStep
        simp only [] at hStep
        cases hRet : returnDonatedSchedContextResolved st holder oldScId
            (replyDonationRecipient st oldScId target) with
        | error e => rw [hRet] at hStep; simp only [] at hStep; cases hStep
        | ok st1' =>
          rw [hRet] at hStep
          obtain ⟨n, _, hPopN⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
          have hReturn : observableSlotsConfinedToCores st st1' [] :=
            observableSlotsConfinedToCores_nil_of_scheduler_except_reschedule_machine_eq
              (returnDonatedSchedContext_scheduler_eq st st1' _ _ _ n hPopN)
              (returnDonatedSchedContext_machine_eq st st1' _ _ _ n hPopN)
          have hEq : migrateSchedContextReplenishment st1' oldScId
              (determineTargetCore st holder)
                (determineTargetCore st (replyDonationRecipient st oldScId target)) = st' :=
            (by simpa using hStep : some (oldScId, holder) = returned? ∧ _).2
          rw [← hEq]
          simpa using observableSlotsConfinedToCores_trans hReturn
            (migrateSchedContextReplenishment_confinedToCores st1' oldScId _ _)

-- **WS-RR RR8.12 Cut 8b (`v0.35.145`)**: `replyRecvHolderDescheduleWriteSet` moved out of this module,
-- beside the transition it describes (since `v0.36.49` both live in
-- `IPC/CrossCore/EndpointReplyRecv.lean`).  A write set declared in a STAGED module is one the
-- production scheduler footprint cannot read, which is the layering rule Cuts 5
-- and 7 applied four times over.  The CONFINEMENT theorem stays here: it is an
-- SM8.B claim about `observableSlotsConfinedToCores`, which is this module's.

/-- ...and it stays inside them, by the same two facts the unconditional
deschedule above uses. -/
theorem replyRecvHolderDeschedule_confinedToCores (tid holder : SeLe4n.ThreadId)
    (st : SystemState) :
    observableSlotsConfinedToCores st
      (replyRecvHolderDeschedule tid holder st)
      (replyRecvHolderDescheduleWriteSet tid holder st) := by
  unfold replyRecvHolderDeschedule replyRecvHolderDescheduleWriteSet
  by_cases h : holder = tid
  · rw [if_pos h, if_pos h]; exact observableSlotsConfinedToCores_refl st []
  · rw [if_neg h, if_neg h]
    -- **One resolver, read by both.**  The transition and its footprint match
    -- because they are the same step, not two spellings that happen to agree.
    exact descheduleAtPlacement_confinedToCores st holder

-- **WS-RR RR8.12 Cut 8b (`v0.35.145`)**: `replyRecvPostReceiveDonationWriteSet` moved out of this module,
-- beside the transition it describes (since `v0.36.49` both live in
-- `IPC/CrossCore/EndpointReplyRecv.lean`).  A write set declared in a STAGED module is one the
-- production scheduler footprint cannot read, which is the layering rule Cuts 5
-- and 7 applied four times over.  The CONFINEMENT theorem stays here: it is an
-- SM8.B claim about `observableSlotsConfinedToCores`, which is this module's.

/-- SM8.B.2 / **WS-RM (`v0.35.6`)**: the post-receive half's per-core writes stay
inside its write set.  The re-donation and *its* replenishment migration are
per-core silent; what is not silent is the recorded server's deschedule and the
chain reversion, and both are named. -/
theorem replyRecvPostReceiveDonation_confinedToCores
    (tid recordedServer nextThread : SeLe4n.ThreadId) (serverCore : CoreId)
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (st st' : SystemState) (u : Unit)
    (hStep : replyRecvPostReceiveDonation tid recordedServer nextThread serverCore returned? st
      = .ok (u, st')) :
    observableSlotsConfinedToCores st st'
      (replyRecvPostReceiveDonationWriteSet tid recordedServer nextThread serverCore
        returned? st) := by
  have hOkInj : ∀ {a b : SystemState},
      (Except.ok ((), a) : Except KernelError (Unit × SystemState)) = .ok (u, b) → a = b := by
    intro a b h; simpa using h
  unfold replyRecvPostReceiveDonation at hStep
  unfold replyRecvPostReceiveDonationWriteSet
  cases returned? with
  | none =>
    simp only [] at hStep ⊢
    rw [← hOkInj hStep]
    exact propagatePipChainCrossCore_confinedToCores serverCore st.objectIndex.length st
      recordedServer
  | some pair =>
    obtain ⟨_scId, holder⟩ := pair
    simp only [] at hStep ⊢
    split
    · next hCall =>
      simp only [hCall, if_true] at hStep
      split
      · next e hDon => simp only [hDon] at hStep; exact absurd hStep (by simp)
      · next st2 hDon =>
        simp only [hDon] at hStep
        rw [← hOkInj hStep]
        -- Associated to the RIGHT so the declared set is `desched ++ ([] ++ pip)`,
        -- which is `desched ++ pip` definitionally; the left association would
        -- need `List.append_nil`.
        exact observableSlotsConfinedToCores_trans
          (replyRecvHolderDeschedule_confinedToCores tid holder st)
          (observableSlotsConfinedToCores_trans
            (applyRendezvousCallDonation_confinedToCores _ st2 _ _ hDon)
            (propagatePipChainCrossCore_confinedToCores serverCore
              st2.objectIndex.length st2 recordedServer))
    · next hCall =>
      simp only [hCall, Bool.false_eq_true, if_false] at hStep
      rw [← hOkInj hStep]
      exact replyRecvDescheduleAndWalk_confinedToCores holder recordedServer serverCore st

/-- SM8.B.2: a scheduler- and machine-preserving prefix can be dropped from a
confinement statement.

The composition shape the retype pipeline needs everywhere: only one of its
steps writes a scheduler slot, and the several around it must be discharged
without inflating the declared set (which `observableSlotsConfinedToCores_trans`
alone would do, leaving `[] ++ cs`). -/
theorem observableSlotsConfinedToCores_of_framed_prefix {st stMid st' : SystemState}
    {cs : List CoreId}
    (hSched : stMid.scheduler = st.scheduler) (hMach : stMid.machine = st.machine)
    (h : observableSlotsConfinedToCores stMid st' cs) :
    observableSlotsConfinedToCores st st' cs :=
  ⟨fun c hc => (h.runQueue c hc).trans (by rw [hSched]),
   fun c hc => (h.current c hc).trans (by rw [hSched]),
   fun c hc => (h.activeDomain c hc).trans (by rw [hSched]),
   fun c hc => (h.domainTimeRemaining c hc).trans (by rw [hSched]),
   fun c hc => (h.domainScheduleIndex c hc).trans (by rw [hSched]),
   fun c hc => (h.regs c hc).trans (by rw [hMach])⟩

/-- SM8.B.2: and the mirror — a framed **suffix** does not move the set either,
where "framed" here reaches only as far as the observer does.

The register-bank form rather than the whole-machine one, because the retype's
memory scrub writes `machine.memory` and the whole-machine version would be
false of it. -/
theorem observableSlotsConfinedToCores_of_framed_suffix_regs {st stMid st' : SystemState}
    {cs : List CoreId}
    (hSched : st'.scheduler = stMid.scheduler)
    (hRegs : ∀ c, st'.machine.regsOnCore c = stMid.machine.regsOnCore c)
    (h : observableSlotsConfinedToCores st stMid cs) :
    observableSlotsConfinedToCores st st' cs :=
  ⟨fun c hc => (by rw [hSched] : st'.scheduler.runQueueOnCore c = _).trans (h.runQueue c hc),
   fun c hc => (by rw [hSched] : st'.scheduler.currentOnCore c = _).trans (h.current c hc),
   fun c hc => (by rw [hSched] : st'.scheduler.activeDomainOnCore c = _).trans
     (h.activeDomain c hc),
   fun c hc => (by rw [hSched] : st'.scheduler.domainTimeRemainingOnCore c = _).trans
     (h.domainTimeRemaining c hc),
   fun c hc => (by rw [hSched] : st'.scheduler.domainScheduleIndexOnCore c = _).trans
     (h.domainScheduleIndex c hc),
   fun c hc => (hRegs c).trans (h.regs c hc)⟩

/-- SM8.B.2: the whole-machine instance of the suffix rule, for the steps that
frame `machine` outright. -/
theorem observableSlotsConfinedToCores_of_framed_suffix {st stMid st' : SystemState}
    {cs : List CoreId}
    (hSched : st'.scheduler = stMid.scheduler) (hMach : st'.machine = stMid.machine)
    (h : observableSlotsConfinedToCores st stMid cs) :
    observableSlotsConfinedToCores st st' cs :=
  ⟨fun c hc => (by rw [hSched] : st'.scheduler.runQueueOnCore c = _).trans (h.runQueue c hc),
   fun c hc => (by rw [hSched] : st'.scheduler.currentOnCore c = _).trans (h.current c hc),
   fun c hc => (by rw [hSched] : st'.scheduler.activeDomainOnCore c = _).trans
     (h.activeDomain c hc),
   fun c hc => (by rw [hSched] : st'.scheduler.domainTimeRemainingOnCore c = _).trans
     (h.domainTimeRemaining c hc),
   fun c hc => (by rw [hSched] : st'.scheduler.domainScheduleIndexOnCore c = _).trans
     (h.domainScheduleIndex c hc),
   fun c hc => (by rw [hMach] : st'.machine.regsOnCore c = _).trans (h.regs c hc)⟩

-- SM8.B.2, relocated at **WS-RR RR8.12**:
-- `endpointReceiveDualWithCapsOnCore_scheduler_eq` is declared in
-- `IPC/CrossCore/EndpointReply.lean`, beside the transition it frames — the
-- production replenish-queue frame the `.receive` scheduler footprint owes reads
-- it, and this module is staged.  A frame lemma about a production transition
-- belongs beside that transition, not in the staged surface that first happened
-- to need it.

/-- SM8.B.2 (PR #873 round 7): and the register banks, by the same case
analysis. -/
theorem endpointReceiveDualWithCapsOnCore_machine_eq (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    (endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
        receiverSlotBase executingCore st).1.machine
      = (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1.machine := by
  unfold endpointReceiveDualWithCapsOnCore
  cases hRecv : endpointReceiveDualOnCore endpointId receiver replyId executingCore st with
  | mk stRecv res =>
    cases res with
    | error e => rfl
    | ok pair =>
      obtain ⟨senderId, sgi⟩ := pair
      simp only []
      repeat' split
      all_goals first
        | rfl
        | (rename_i h; exact ipcUnwrapCaps_preserves_machine _ _ _ _ _ _ _ h)

/-- SM8.B.2 (**the live `.replyRecv` receive-leg bound**, PR #873 round 7): the
WithCaps per-core receive — the form `endpointReplyRecvOnCore` now runs — is confined to the
bare receive's write set. The capability install writes no core at all, so the
two forms declare the same per-core footprint and every pin taken against the
bare set still describes the live leg. -/
theorem endpointReceiveDualWithCapsOnCore_confinedToCores (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
        receiverSlotBase executingCore st).1
      (endpointReceiveDualWriteSet st endpointId executingCore) := by
  have h := observableSlotsConfinedToCores_trans
    (endpointReceiveDualOnCore_confinedToCores endpointId receiver replyId executingCore st
      hObjInv)
    (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
      (endpointReceiveDualWithCapsOnCore_scheduler_eq endpointId receiver replyId
        receiverCspaceRoot receiverSlotBase executingCore st)
      (endpointReceiveDualWithCapsOnCore_machine_eq endpointId receiver replyId
        receiverCspaceRoot receiverSlotBase executingCore st))
  simpa using h

-- **WS-RR RR8.12 Cut 8b (`v0.35.145`)**: `endpointReplyRecvWriteSet` moved out of this module,
-- beside the transition it describes (since `v0.36.49` both live in
-- `IPC/CrossCore/EndpointReplyRecv.lean`).  A write set declared in a STAGED module is one the
-- production scheduler footprint cannot read, which is the layering rule Cuts 5
-- and 7 applied four times over.  The CONFINEMENT theorem stays here: it is an
-- SM8.B claim about `observableSlotsConfinedToCores`, which is this module's.

/-- SM8.B.2 (**the live `.replyRecv` bound**): `endpointReplyRecvOnCore` — the function
`API.dispatchWithCap`'s `.replyRecv` arm routes through — writes no core outside
`endpointReplyRecvWriteSet`.

The reply leg, the donation pop, the receive leg and the post-receive
donation, at the states they really run at. The receive leg's
`objects.invExt` premise is discharged from the reply leg's own preservation
theorem rather than assumed, exactly as in §4a. -/
theorem endpointReplyRecvOnCore_confinedToCores (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId)
    (msg : IpcMessage) (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st st' : SystemState) (summary : CapTransferSummary)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg receiverCspaceRoot
        receiverSlotBase executingCore st
      = .ok (summary, st')) :
    observableSlotsConfinedToCores st st'
      (endpointReplyRecvWriteSet endpointId receiver replyId prevCaller msg receiverCspaceRoot
        receiverSlotBase executingCore st) := by
  have hReply := endpointReplyOnCore_confinedToCores receiver prevCaller msg executingCore st
    hObjInv
  have hInv1 : (endpointReplyOnCore receiver prevCaller msg executingCore st).1.objects.invExt :=
    endpointReplyOnCore_preserves_objects_invExt receiver prevCaller msg executingCore st hObjInv
  unfold endpointReplyRecvOnCore endpointReplyRecvWriteSet at *
  simp only [] at hStep
  cases hRep : endpointReplyOnCore receiver prevCaller msg executingCore st with
  | mk st1 res =>
    rw [hRep] at hReply hInv1 hStep
    cases res with
    | error e => simp only [] at hStep; exact absurd hStep (by simp)
    | ok replySgi =>
      simp only [] at hStep ⊢
      -- **WS-RM (`v0.35.6`)**: the pop, between the legs.
      cases hPop : replyRecvPopDonation replyId prevCaller st1 with
      | error e => rw [hPop] at hStep; exact absurd hStep (by simp)
      | ok popPair =>
        obtain ⟨returnedSc?, st1p⟩ := popPair
        rw [hPop] at hStep
        simp only [] at hStep ⊢
        have hPopConf := replyRecvPopDonation_confinedToCores
          replyId prevCaller st1 st1p returnedSc? hPop
        have hInv1p : st1p.objects.invExt :=
          replyRecvPopDonation_preserves_objects_invExt
            replyId prevCaller st1 st1p returnedSc? hInv1 hPop
        have hRecv := endpointReceiveDualWithCapsOnCore_confinedToCores endpointId receiver
          (some replyId) receiverCspaceRoot receiverSlotBase executingCore st1p hInv1p
        cases hRcv : endpointReceiveDualWithCapsOnCore endpointId receiver (some replyId)
            receiverCspaceRoot receiverSlotBase executingCore st1p with
        | mk st2 res2 =>
          rw [hRcv] at hRecv hStep
          cases res2 with
          | error e => simp only [] at hStep; exact absurd hStep (by simp)
          | ok pair =>
            rcases pair with ⟨nextThread, recvSummary, recvSgi⟩
            simp only [] at hStep ⊢
            -- WS-RA RA.B.5b: the body stages the woken caller's reply frame and
            -- the completed plain sender's unit frame after the donation; both
            -- stagers frame the scheduler and the machine, so the donation's
            -- confinement transports across them unchanged.
            cases hDon : replyRecvPostReceiveDonation receiver
                ((recordedReplyServer? st prevCaller).getD receiver) nextThread
                executingCore
                returnedSc? st2 with
            | error e =>
                rw [hDon] at hStep
                exact absurd hStep (by simp)
            | ok pair2 =>
              rcases pair2 with ⟨u2, st3⟩
              rw [hDon] at hStep
              simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
              have hConf := replyRecvPostReceiveDonation_confinedToCores receiver
                ((recordedReplyServer? st prevCaller).getD receiver) nextThread
                executingCore
                returnedSc? st2 st3 u2 hDon
              -- WS-OD OD3.14: the receive leg's priority hand-off is the fourth
              -- leg, read at the state it runs at.  On a non-delegated reply it is
              -- the identity and its declared set is empty.
              have hPip := applyReceiveLegPipHandoff_confinedToCores st3 receiver nextThread
                ((recordedReplyServer? st prevCaller).getD receiver) executingCore
              have hStaged : observableSlotsConfinedToCores st2 st'
                  (replyRecvPostReceiveDonationWriteSet receiver
                    ((recordedReplyServer? st prevCaller).getD receiver) nextThread
                    executingCore returnedSc? st2 ++
                    receiveLegPipHandoffWriteSet st3 receiver nextThread
                      ((recordedReplyServer? st prevCaller).getD receiver) executingCore) := by
                rw [← hStep.2]
                exact observableSlotsConfinedToCores_of_framed_suffix
                  (by rw [Architecture.stageWokenSendCompletion_scheduler_eq,
                          Architecture.stageDeliveredMessage_scheduler_eq])
                  (by rw [Architecture.stageWokenSendCompletion_machine_eq,
                          Architecture.stageDeliveredMessage_machine_eq])
                  (observableSlotsConfinedToCores_trans hConf hPip)
              exact observableSlotsConfinedToCores_trans hReply
                (observableSlotsConfinedToCores_trans
                  (by simpa using observableSlotsConfinedToCores_trans hPopConf hRecv) hStaged)

-- ============================================================================
-- §5e The live `.tcbSuspend` arm itself
-- ============================================================================
--
-- `API.dispatchCapabilityOnly`'s `.tcbSuspend` arm routes to `suspendThreadOnCore`,
-- which is `cancelIpcBlockingOnCore`'s teardown *plus* the priority-inheritance
-- chain reversion, the donation-cancellation arms, the home-core removal, the
-- running-core removal when the victim diverged from its home, and a scheduling
-- point on the executing core. §5's `cancelIpcBlockingOnCore_confinedToCores`
-- covers the first two of those, so it never bounded the live arm (PR #861
-- review round 4).
--
-- The leaf frames below are new: per-core confinement reads the domain slots and
-- the register banks, and the context switch had frames for neither.

-- SM8.B.2 note (PR #880 round 7): the preempt / switch **active-domain** frames
-- (`preemptCurrentOnCore_activeDomainOnCore`,
-- `switchToThreadOnCore_activeDomainOnCore_eq`) now live upstream in
-- `Scheduler/Operations/PerCoreSwitchToThread.lean` (the timer tick's local
-- replenish-wake reschedule arm needs them there); this module keeps only the
-- two domain-slot frames with no upstream counterpart.

theorem preemptCurrentOnCore_domainTimeRemainingOnCore (st : SystemState) (c c' : CoreId)
    (tid : SeLe4n.ThreadId) :
    (preemptCurrentOnCore st c tid).scheduler.domainTimeRemainingOnCore c'
      = st.scheduler.domainTimeRemainingOnCore c' := by
  simp only [preemptCurrentOnCore]; repeat' split
  all_goals first | rfl | simp only [SchedulerState.setCurrentOnCore_domainTimeRemainingOnCore,
      SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore]

theorem preemptCurrentOnCore_domainScheduleIndexOnCore (st : SystemState) (c c' : CoreId)
    (tid : SeLe4n.ThreadId) :
    (preemptCurrentOnCore st c tid).scheduler.domainScheduleIndexOnCore c'
      = st.scheduler.domainScheduleIndexOnCore c' := by
  simp only [preemptCurrentOnCore]; repeat' split
  all_goals first | rfl | simp only [SchedulerState.setCurrentOnCore_domainScheduleIndexOnCore,
      SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore]

theorem switchToThreadOnCore_domainTimeRemainingOnCore (st st' : SystemState) (c c' : CoreId)
    (tid : SeLe4n.ThreadId) (h : switchToThreadOnCore st c tid = .ok st') :
    st'.scheduler.domainTimeRemainingOnCore c' = st.scheduler.domainTimeRemainingOnCore c' := by
  unfold switchToThreadOnCore at h
  repeat' split at h
  all_goals try simp only [] at h
  all_goals first
    | (rw [Except.ok.injEq] at h
       subst h
       simp only [restoreIncomingContextOnCoreUnlessCurrent_scheduler,
         SchedulerState.setCurrentOnCore_domainTimeRemainingOnCore,
         SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore,
         preemptCurrentOnCore_domainTimeRemainingOnCore])
    | exact absurd h (by simp)

theorem switchToThreadOnCore_domainScheduleIndexOnCore (st st' : SystemState) (c c' : CoreId)
    (tid : SeLe4n.ThreadId) (h : switchToThreadOnCore st c tid = .ok st') :
    st'.scheduler.domainScheduleIndexOnCore c' = st.scheduler.domainScheduleIndexOnCore c' := by
  unfold switchToThreadOnCore at h
  repeat' split at h
  all_goals try simp only [] at h
  all_goals first
    | (rw [Except.ok.injEq] at h
       subst h
       simp only [restoreIncomingContextOnCoreUnlessCurrent_scheduler,
         SchedulerState.setCurrentOnCore_domainScheduleIndexOnCore,
         SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore,
         preemptCurrentOnCore_domainScheduleIndexOnCore])
    | exact absurd h (by simp)

/-- SM8.B.2: **a context switch on core `c` is confined to core `c`.** The
register-bank clause is the one that needed a new frame: SM5.I banks every
core's `RegisterFile` inside one `MachineState`, so a switch does write
`machine`, and "writes `machine`" is not the same as "is visible on every
core". -/
theorem switchToThreadOnCore_confinedToCores (st st' : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (h : switchToThreadOnCore st c tid = .ok st') :
    observableSlotsConfinedToCores st st' [c] :=
  ⟨fun c' hc => (switchToThreadOnCore_independent_of_other_core st c c' tid st'
      (fun he => hc (by simp [he])) h).2,
   fun c' hc => (switchToThreadOnCore_independent_of_other_core st c c' tid st'
      (fun he => hc (by simp [he])) h).1,
   fun c' _ => switchToThreadOnCore_activeDomainOnCore_eq st c tid st' c' h,
   fun c' _ => switchToThreadOnCore_domainTimeRemainingOnCore st st' c c' tid h,
   fun c' _ => switchToThreadOnCore_domainScheduleIndexOnCore st st' c c' tid h,
   fun c' hc => switchToThreadOnCore_machine_regsOnCore_ne st c c' tid st'
      (fun he => hc (by simp [he])) h⟩

/-- The drop of an out-of-domain incumbent writes only its own core's queue
and `current` slot and the incumbent's saved context. -/
theorem dropCurrentOnCore_confinedToCores (st : SystemState) (c : CoreId) :
    observableSlotsConfinedToCores st (dropCurrentOnCore st c) [c] :=
  ⟨fun c' hc => (dropCurrentOnCore_runQueueOnCore st c c').trans
      (preemptCurrentOnCore_runQueueOnCore_ne st c _ c' (fun he => hc (by simp [he]))),
   fun c' hc => dropCurrentOnCore_currentOnCore_ne st c c' (fun he => hc (by simp [he])),
   fun c' _ => by simp [dropCurrentOnCore, preemptCurrentOnCore_activeDomainOnCore],
   fun c' _ => by simp [dropCurrentOnCore, preemptCurrentOnCore_domainTimeRemainingOnCore],
   fun c' _ => by simp [dropCurrentOnCore, preemptCurrentOnCore_domainScheduleIndexOnCore],
   fun c' _ => by simp⟩

/-- SM8.B.2: the per-core reschedule handler is confined to the core it runs
on — it either idles that core, keeps its current thread, or switches it. -/
theorem handleRescheduleSgiOnCore_confinedToCores (st st' : SystemState) (c : CoreId)
    (h : handleRescheduleSgiOnCore st c = .ok st') :
    observableSlotsConfinedToCores st st' [c] := by
  unfold handleRescheduleSgiOnCore at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · rw [Except.ok.injEq] at h; subst h
      exact observableSlotsConfinedToCores_then_flagOnly
        (dropCurrentOnCore_confinedToCores st c)
        (clearReschedulePendingOnCore_confinedToCores _ c)
    · rw [Except.ok.injEq] at h; subst h
      exact observableSlotsConfinedToCores_widen_any (clearReschedulePendingOnCore_confinedToCores st c)
  · split at h
    · split at h
      · rename_i sSw hSw
        rw [Except.ok.injEq] at h; subst h
        exact observableSlotsConfinedToCores_then_flagOnly
          (switchToThreadOnCore_confinedToCores st sSw c _ hSw)
          (clearReschedulePendingOnCore_confinedToCores sSw c)
      · exact absurd h (by simp)
    · rw [Except.ok.injEq] at h; subst h
      exact observableSlotsConfinedToCores_widen_any (clearReschedulePendingOnCore_confinedToCores st c)

/-- SM8.B.2: the suspend pipeline's G7 scheduling point writes at most the
**executing** core. Its remote leg is an SGI *return value*, not a state
change: the home core is poked, and pokes are not writes. -/
theorem suspendRescheduleOnCore_confinedToCores (st st' : SystemState)
    (home executingCore : CoreId) (wasCurrentHome localDeboosted : Bool)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (h : suspendRescheduleOnCore st home executingCore wasCurrentHome localDeboosted
      = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st' [executingCore] := by
  unfold suspendRescheduleOnCore at h
  repeat' split at h
  all_goals first
    | (rw [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨hs, -⟩ := h
       subst hs
       first
         | exact handleRescheduleSgiOnCore_confinedToCores st _ executingCore (by assumption)
         | exact observableSlotsConfinedToCores_refl _ _)
    | exact absurd h (by simp)

/-- SM8.B.2: the priority ops' preemption seam writes at most the **executing**
core. Its remote leg is an SGI *return value*, not a state change: the running
core is poked, and pokes are not writes. Shared with the per-core SchedContext
unbind, whose demotion needs the same scheduling point. -/
theorem priorityRescheduleOnCore_confinedToCores (st st' : SystemState)
    (running? : Option CoreId) (executingCore : CoreId) (shouldPreempt : Bool)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (h : SchedContext.PriorityManagement.priorityRescheduleOnCore st running?
      executingCore shouldPreempt = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st' [executingCore] := by
  unfold SchedContext.PriorityManagement.priorityRescheduleOnCore at h
  repeat' split at h
  all_goals first
    | (rw [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨hs, -⟩ := h
       subst hs
       first
         | exact handleRescheduleSgiOnCore_confinedToCores st _ executingCore (by assumption)
         | exact observableSlotsConfinedToCores_refl _ _)
    | exact absurd h (by simp)

-- WS-RR RR8.12 Cut C3b-iii (`v0.35.169`): `threadOccupiedCores` moved to the
-- production `SeLe4n/Kernel/Lifecycle/Operations/RetypeFootprint.lean` (via
-- `SyscallSchedFootprint.lean` until WS-LS LS2.5) with the retype write
-- set that reads it.  Its lemma family stays here: those are about the destroy
-- sweep's confinement, which is this module's question.

/-- SM8.B.2: a core outside the occupancy set does not hold the thread. -/
theorem not_threadOccupiesCore_of_not_mem (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) (h : c ∉ threadOccupiedCores st tid) :
    threadOccupiesCore st tid c = false := by
  cases hOcc : threadOccupiesCore st tid c with
  | false => rfl
  | true =>
    exact absurd (List.mem_filter.mpr ⟨Concurrency.mem_allCores c, by simp [hOcc]⟩) h

/-- SM8.B.2 (**the destroy sweep's bound**): the sweep writes no core the thread
does not occupy.

All six observable slots: the two the guarded step writes come from the sweep's
closed forms (both keyed on the *pre-state* guard, which is what makes a
pre-state write set possible at all), the three domain slots from the round-35
fold frame, and the register banks because the sweep never touches `machine`. -/
theorem removeRunnableFromAllCores_confinedToCores (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    observableSlotsConfinedToCores st (removeRunnableFromAllCores st tid)
      (threadOccupiedCores st tid) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c hc
  · rw [removeRunnableFromAllCores_runQueueOnCore]
    simp [not_threadOccupiesCore_of_not_mem st tid c hc]
  · rw [removeRunnableFromAllCores_currentOnCore]
    have hOcc := not_threadOccupiesCore_of_not_mem st tid c hc
    unfold threadOccupiesCore at hOcc
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hOcc
    simp [hOcc.2]
  · exact removeRunnableFromAllCores_activeDomainOnCore st tid c
  · exact removeRunnableFromAllCores_domainTimeRemainingOnCore st tid c
  · exact removeRunnableFromAllCores_domainScheduleIndexOnCore st tid c
  · rw [removeRunnableFromAllCores_machine]

/-- SM8.B.2: occupancy is a scheduler read, so a scheduler-preserving prefix
does not move the write set.

Load-bearing for the retype: the sweep runs several steps into the cleanup
pipeline, but the write set is declared at the pipeline's **entry** state. The
two are the same set precisely because everything in between frames the
scheduler. -/
theorem threadOccupiedCores_congr {st st' : SystemState} (tid : SeLe4n.ThreadId)
    (h : st'.scheduler = st.scheduler) :
    threadOccupiedCores st' tid = threadOccupiedCores st tid := by
  unfold threadOccupiedCores threadOccupiesCore
  rw [h]

/-- `v0.35.164`: the occupancy set reads only the run queues and current slots, so
a step that keeps every one of those — the destroy path's reservation arm, which
may write a replenish queue — keeps the set, with no whole-scheduler equality. -/
theorem threadOccupiedCores_congr_of_runQueue_current {st st' : SystemState}
    (tid : SeLe4n.ThreadId)
    (h : ∀ c, st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c
      ∧ st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c) :
    threadOccupiedCores st' tid = threadOccupiedCores st tid := by
  unfold threadOccupiedCores
  apply List.filter_congr
  intro c _
  unfold threadOccupiesCore
  rw [(h c).1, (h c).2]

/-- SM8.B.2: **the TCB reference scrub's bound** — the destroy sweep, plus two
object-store sweeps that write no scheduler slot at all. -/
theorem cleanupTcbReferences_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId) :
    observableSlotsConfinedToCores st (cleanupTcbReferences st tid)
      (threadOccupiedCores st tid) :=
  observableSlotsConfinedToCores_of_framed_suffix
    (cleanupTcbReferences_scheduler_eq_removeRunnableFromAllCores st tid)
    (by rw [cleanupTcbReferences_machine_eq, removeRunnableFromAllCores_machine])
    (removeRunnableFromAllCores_confinedToCores st tid)

/-- SM8.B.2: clearing a suspended thread's transient fields is per-core silent —
it rewrites one TCB and touches neither the scheduler nor a register bank. -/
theorem clearPendingState_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId) :
    observableSlotsConfinedToCores st (clearPendingState st tid) [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (by unfold clearPendingState
        first | exact SystemState.updateTcb_scheduler _ _ _ | exact SystemState.updateTcb_machine _ _ _)
    (by unfold clearPendingState
        first | exact SystemState.updateTcb_machine _ _ _ | exact SystemState.updateTcb_scheduler _ _ _)

/-- SM8.B.2: the bound-SchedContext cancellation arm is per-core silent. It
unbinds the SC, purges the victim's replenishments from its home core's
**replenishment** queue and rewrites the TCB binding — and SM8.A's
`onCore_perCore_independence` puts the replenishment queue outside the
observer's read set entirely, so none of that is observable anywhere. -/
theorem cancelBoundDonationOnCore_confinedToCores (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (rqCore : CoreId)
    (h : cancelBoundDonationOnCore st tid tcb rqCore = .ok st') :
    observableSlotsConfinedToCores st st' [] := by
  refine ⟨fun c _ => (cancelBoundDonationOnCore_runQueue_current_eq st st' tid tcb rqCore c h).1,
          fun c _ => (cancelBoundDonationOnCore_runQueue_current_eq st st' tid tcb rqCore c h).2,
          ?_, ?_, ?_, ?_⟩
  all_goals intro c _
  all_goals (
    simp only [cancelBoundDonationOnCore] at h
    split at h
    · rw [Except.ok.injEq] at h
      subst h
      rw [SystemState.updateTcb_eq_objects_update, SystemState.updateSchedContext_eq_objects_update]
      try simp
    · exact absurd h (by simp))

-- WS-RR RR2.7: `migrateSchedContextReplenishment_confinedToCores` moved up to
-- §5, beside the donation legs that now compose it.

/-- SM8.B.2 (**the missing frame**): a run-queue migration writes the two cores
it names and nothing else.

`migrateRunQueueOnAffinityChange` had frames for `machine`, `objects`,
`getTcb`, `getSchedContext`, `replenishQueueOnCore` and `determineTargetCore`,
and a projection-preservation lemma — but nothing saying *which cores it leaves
alone*, which is exactly what confinement needs. Its absence is why
`.tcbSetAffinity` sat in the routing allowlist instead of carrying a proof.

Every arm but one returns the pre-state outright; the migrating arm is two
`setRunQueueOnCore` writes at `fromCore` and `toCore`, so a core outside the
pair sees neither, and the five non-run-queue slots are untouched on every
arm. -/
theorem migrateRunQueueOnAffinityChange_confinedToCores (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore : CoreId) :
    observableSlotsConfinedToCores st
      (migrateRunQueueOnAffinityChange st tid fromCore toCore) [fromCore, toCore] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
    obtain ⟨hf, ht⟩ := hc
    unfold migrateRunQueueOnAffinityChange
    split
    · rfl
    · split
      · rfl
      · split
        · simp [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne, Ne.symm hf, Ne.symm ht]
        · rfl
  all_goals intro c _
  all_goals (unfold migrateRunQueueOnAffinityChange; repeat' split)
  all_goals simp

/-- SM8.B.2: the donated-SchedContext cancellation arm is per-core silent for
the same reason — the SC returns to its owner in the object store and its
replenishments migrate between two cores' replenishment queues, neither of
which the observer reads. -/
theorem cancelDonatedDonationOnCore_confinedToCores (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : cancelDonatedDonationOnCore st tid tcb = .ok st') :
    observableSlotsConfinedToCores st st' [] := by
  unfold cancelDonatedDonationOnCore at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · next stCleanup hCleanup =>
      rw [Except.ok.injEq] at h
      subst h
      exact observableSlotsConfinedToCores_trans
        (observableSlotsConfinedToCores_nil_of_scheduler_except_reschedule_machine_eq
          (cleanupDonatedSchedContext_scheduler_eq st stCleanup tid hCleanup)
          (cleanupDonatedSchedContext_machine_eq st stCleanup tid hCleanup))
        (migrateSchedContextReplenishment_confinedToCores stCleanup _ _ _)
  · exact absurd h (by simp)

-- WS-RR RR8.12 Cut C3b-iv (`v0.35.170`): `suspendThreadOnCoreWriteSet` moved to
-- the production `SeLe4n/Kernel/IPC/CrossCore/SuspendFootprint.lean` (via
-- `SyscallSchedFootprint.lean` until WS-LS LS2.5), beside
-- `schedLockSet_suspendThreadOnCore`, whose run segment IS it -- the last of the
-- SM8.B write sets a production footprint needed and this module held.  Same
-- name, same namespace; the confinement theorems below stay here.

/-- SM8.B.2: marking the victim `.Inactive` is per-core silent — one object
store write. -/
theorem suspendInactiveStore_confinedToCores (s : SystemState) (tid : SeLe4n.ThreadId) :
    observableSlotsConfinedToCores s
      (s.updateTcb tid fun t => { t with threadState := .Inactive }) [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (SystemState.updateTcb_scheduler _ _ _) (SystemState.updateTcb_machine _ _ _)

/-- SM8.B.2: whichever donation-cancellation arm the victim's binding selects,
the step is per-core silent. -/
theorem suspendDonationArms_confinedToCores (s sD : SystemState) (tid : SeLe4n.ThreadId)
    (tcb' : TCB) (home : CoreId)
    (h : (match tcb'.schedContextBinding with
          | .unbound => (Except.ok s : Except KernelError SystemState)
          | .bound _ => cancelBoundDonationOnCore s tid tcb' home
          | .donated _ _ => cancelDonatedDonationOnCore s tid tcb') = .ok sD) :
    observableSlotsConfinedToCores s sD [] := by
  split at h
  · rw [Except.ok.injEq] at h; subst h; exact observableSlotsConfinedToCores_refl _ _
  · exact cancelBoundDonationOnCore_confinedToCores s sD tid tcb' home h
  · exact cancelDonatedDonationOnCore_confinedToCores s sD tid tcb' h

/-- `v0.35.164`: the destroy path's reservation arm is per-core silent — it is the
suspend's G3 match, named (`cancelDonationArmOnCore`), so this is
`suspendDonationArms_confinedToCores` at the thread's home core. -/
theorem cancelDonationArmOnCore_confinedToCores (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : cancelDonationArmOnCore st tid tcb = .ok st') :
    observableSlotsConfinedToCores st st' [] := by
  unfold cancelDonationArmOnCore at h
  exact suspendDonationArms_confinedToCores st st' tid tcb (determineTargetCore st tid) h

/-- `v0.35.165`: the destroy path's **SchedContext** release is per-core silent.

`releaseSchedContextBinding` clears the bound thread's binding, purges `scId`'s
replenishments and removes the index entry; none of those is one of the six
`observableSlotsConfinedToCores` slots — the replenish queue is deliberately not
among them (SM8.B.2), which is why this is `[]` rather than the purge core. -/
theorem releaseSchedContextBinding_confinedToCores (st : SystemState)
    (scId : SeLe4n.SchedContextId) (sc : SeLe4n.Kernel.SchedContext) :
    observableSlotsConfinedToCores st (releaseSchedContextBinding st scId sc) [] :=
  ⟨fun c _ => releaseSchedContextBinding_runQueueOnCore st scId sc c,
   fun c _ => releaseSchedContextBinding_currentOnCore st scId sc c,
   fun c _ => releaseSchedContextBinding_activeDomainOnCore st scId sc c,
   fun c _ => releaseSchedContextBinding_domainTimeRemainingOnCore st scId sc c,
   fun c _ => releaseSchedContextBinding_domainScheduleIndexOnCore st scId sc c,
   fun c _ => by rw [releaseSchedContextBinding_machine]⟩

/-- SM8.B.2 (**the live `.tcbSuspend` bound**): `suspendThreadOnCore` — the
function `API.dispatchCapabilityOnly`'s `.tcbSuspend` arm routes through —
writes no core outside `suspendThreadOnCoreWriteSet`.

Four of its steps are per-core silent (both donation arms, `clearPendingState`,
the `.Inactive` store); the four that are not are the teardown's own reclaim
step (**WS-RR RR8.12**; the holder deschedule since `v0.35.158`), the
priority-inheritance reversion, the placement dequeue and the G7 scheduling
point, and all four are named. The closing `mono`
is only re-ordering — the composition produces the cores in execution order, the
declared set lists them in reading order. -/
theorem suspendThreadOnCore_confinedToCores (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hStep : suspendThreadOnCore st vtid executingCore = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st'
      (suspendThreadOnCoreWriteSet st vtid executingCore) := by
  unfold suspendThreadOnCore at hStep
  unfold suspendThreadOnCoreWriteSet
  simp only [] at hStep
  split
  · next hTcb => simp only [hTcb] at hStep; exact absurd hStep (by simp)
  · next tcb hTcb =>
    simp only [hTcb] at hStep
    split
    · next hInact => simp only [hInact] at hStep; exact absurd hStep (by simp)
    · next hInact =>
      rw [if_neg hInact] at hStep
      have hCancel : observableSlotsConfinedToCores st
          (cancelIpcBlockingReclaimed vtid.val tcb st)
          (cancelUnboundHolderCore? st (cancelIpcBlockingMigrated vtid.val tcb st)
            vtid.val tcb).toList :=
        cancelIpcBlockingReclaimed_confinedToCores vtid.val tcb st
      -- The chain reversion, stated over the same `blockingServer` scrutinee the
      -- transition and the write set both read, so the two stay in step.
      have hPre : observableSlotsConfinedToCores st
          (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId =>
             (PriorityInheritance.propagatePipChainCrossCore
               (cancelIpcBlockingReclaimed vtid.val tcb st) serverId executingCore).1
           | none => cancelIpcBlockingReclaimed vtid.val tcb st)
          ((cancelUnboundHolderCore? st (cancelIpcBlockingMigrated vtid.val tcb st)
              vtid.val tcb).toList
            ++ match PriorityInheritance.blockingServer st vtid.val with
               | some serverId =>
                 pipChainWriteSet (cancelIpcBlockingReclaimed vtid.val tcb st) serverId
                   executingCore
                   (cancelIpcBlockingReclaimed vtid.val tcb st).objectIndex.length
               | none => []) := by
        cases hSrv : PriorityInheritance.blockingServer st vtid.val with
        | none => simpa only [List.append_nil] using hCancel
        | some serverId =>
          simp only []
          exact observableSlotsConfinedToCores_trans hCancel
            (propagatePipChainCrossCore_confinedToCores executingCore _ _ serverId)
      split at hStep
      · exact absurd hStep (by simp)
      · next stD hDonArm =>
        exact (observableSlotsConfinedToCores_trans
            (observableSlotsConfinedToCores_trans
              (observableSlotsConfinedToCores_trans
                (observableSlotsConfinedToCores_trans
                  (observableSlotsConfinedToCores_trans hPre
                    (suspendDonationArms_confinedToCores _ stD vtid.val _ _ hDonArm))
                  (descheduleAtPlacementCores_eq_toList st vtid.val ▸
                    descheduleAt_confinedToCores stD vtid.val (placedCoreOf? st vtid.val)))
                (clearPendingState_confinedToCores _ vtid.val))
              (suspendInactiveStore_confinedToCores _ vtid.val))
            (suspendRescheduleOnCore_confinedToCores _ st' _ executingCore _ _ sgi hStep))

-- ============================================================================
-- §5f The live `.tcbResume` arm
-- ============================================================================
--
-- PR #861 review round 10 found this arm calling the boot-pinned `resumeThread`
-- while `resumeThreadOnCore` sat unused: a thread homed on a secondary core was
-- resumed onto the **boot** run queue, where its own core would never dispatch
-- it. The arm is rerouted; this section is the audit the inventory was missing.

-- WS-RR RR8.12 Cut C3b-i (`v0.35.167`): `resumeThreadOnCoreWriteSet` moved to the
-- production `SeLe4n/Kernel/Lifecycle/ResumeFootprint.lean` (via
-- `SyscallSchedFootprint.lean` until WS-LS LS2.5), where the live
-- `.tcbResume` arm's resolved scheduler-domain footprint
-- (`schedLockSet_resumeThreadOnCore`) is `schedFootprintOfCores` of it.  A
-- production footprint cannot read a write set declared in a staged module, and
-- Cut 7's rule is that a footprint IS that write set rather than a second
-- resolution of the same cores.  Same name, same namespace; the confinement
-- theorems below stay here.

/-- SM8.B.2: the per-core resume's ready-restore leg is per-core silent — it
rewrites the victim's TCB (IPC fields, `threadState`, `pipBoost`) and touches
neither the scheduler nor any register bank. -/
theorem resumeReadyMidState_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId) :
    observableSlotsConfinedToCores st (resumeReadyMidState st tid) [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (resumeReadyMidState_scheduler_eq st tid)
    (resumeReadyMidState_machine_eq st tid)

/-- SM8.B.2 (**the live `.tcbResume` bound**): `resumeThreadOnCore` writes no
core outside `resumeThreadOnCoreWriteSet`.

Three legs: the silent ready-restore, the enqueue on the **home** core (read
from the pre-state, which is where the write set reads it), and — only when the
home core is the executing one — the inline reschedule. The remote path
returns an SGI rather than applying it, so it writes nothing further. -/
theorem resumeThreadOnCore_confinedToCores (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hStep : Lifecycle.Suspend.resumeThreadOnCore st vtid executingCore = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st'
      (resumeThreadOnCoreWriteSet st vtid executingCore) := by
  unfold Lifecycle.Suspend.resumeThreadOnCore at hStep
  simp only [] at hStep
  split at hStep
  · next tcb hTcb =>
    split at hStep
    · exact absurd hStep (by simp)
    · next hInactive =>
      have hPre : observableSlotsConfinedToCores st
          (enqueueRunnableOnCore (markKeyChangeFrom st (resumeReadyMidState st vtid.val) vtid.val)
            (determineTargetCore st vtid.val) vtid.val)
          [determineTargetCore st vtid.val] :=
        observableSlotsConfinedToCores_widen_cons
          (observableSlotsConfinedToCores_then_flagOnly
            (resumeReadyMidState_confinedToCores st vtid.val)
            (markKeyChangeFrom_confinedToCores st _ vtid.val))
          (enqueueRunnableOnCore_confinedToCores _ (determineTargetCore st vtid.val) vtid.val)
      split at hStep
      · -- LOCAL: the home core is the executing core, reschedule runs inline.
        -- `[target] ++ [executingCore]` *is* the declared set, definitionally.
        split at hStep
        · next st4 hResched =>
          rw [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨hs, -⟩ := hStep
          subst hs
          exact observableSlotsConfinedToCores_trans hPre
            (handleRescheduleSgiOnCore_confinedToCores _ st4 executingCore hResched)
        · exact absurd hStep (by simp)
      · -- REMOTE: the SGI is returned, not applied, so only the home core moves.
        rw [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨hs, -⟩ := hStep
        subst hs
        refine observableSlotsConfinedToCores_mono ?_ hPre
        intro c hc
        simp only [List.mem_singleton] at hc
        simp [resumeThreadOnCoreWriteSet, hc]
  · exact absurd hStep (by simp)

-- ============================================================================
-- §5g The live `.send` arm
-- ============================================================================
--
-- PR #861 review round 10 found this arm calling the boot-pinned
-- `endpointSendDualWithCaps`. Both of its scheduling effects target the boot
-- core: a rendezvous receiver is woken with `ensureRunnable` (so a receiver
-- homed elsewhere lands on a run queue its own core never dispatches from) and
-- a sender with nobody waiting is descheduled with `removeRunnable` (so a
-- sender blocking on a secondary core stays current and runnable there). The
-- arm is rerouted through `endpointSendDualWithCapsOnCore`; this section is the
-- per-core audit that reroute owes.

-- SM8.B.2, relocated at **WS-RR RR8.12**: `endpointSendWriteSet` is declared in
-- `IPC/CrossCore/EndpointSend.lean`, beside `endpointSendDualOnCore` and beside
-- the production scheduler-domain footprint `schedLockSet_endpointSendOnCore` that
-- reads it.  This module is staged and imports `Kernel.API`, so a core list
-- declared here is unreachable from the footprint the syscall seam brackets over.

/-- SM8.B.2 (**the bare cross-core send bound**): `endpointSendDualOnCore` writes
no core outside `endpointSendWriteSet`.

Rendezvous path: pop the receive queue, store the receiver's message, **wake it
on its home core** — `[] ++ [] ++ [receiverHome]`. Naming `receiverHome` at the
*pre-state* is what the §1a frame layer buys: neither the pop nor the store is a
migration, so the affinity the wake reads is the affinity the write set read.
Block path: enqueue the sender, store its blocked state, **deschedule it on its
own core** — `[] ++ [] ++ [executingCore]`. Every fail-closed arm returns the
pre-state and writes nothing. -/
theorem endpointSendDualOnCore_confinedToCores (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointSendDualOnCore endpointId sender msg executingCore st).1
      (endpointSendWriteSet st endpointId executingCore) := by
  unfold endpointSendDualOnCore endpointSendWriteSet endpointCallReceiver?
  split
  · exact observableSlotsConfinedToCores_of_eq _ rfl
  · split
    · exact observableSlotsConfinedToCores_of_eq _ rfl
    · cases hEp : st.getEndpoint? endpointId with
      | none =>
        simp only []
        split <;> exact observableSlotsConfinedToCores_of_eq _ rfl
      | some ep =>
        simp only []
        cases hHead : ep.receiveQ.head with
        | none =>
          -- Block path: the sender stops on the core it is running on.
          simp only []
          split
          · exact observableSlotsConfinedToCores_of_eq _ rfl
          · next st1 hEnq =>
            split
            · exact observableSlotsConfinedToCores_of_eq _ rfl
            · next st2 hMsg =>
              exact observableSlotsConfinedToCores_trans
                (observableSlotsConfinedToCores_trans
                  (endpointQueueEnqueue_confinedToCores endpointId false sender st st1 hEnq)
                  (storeTcbIpcStateAndMessage_confinedToCores st1 st2 sender _ _ hMsg))
                (removeRunnableOnCore_confinedToCores st2 sender executingCore)
        | some headRecv =>
          -- Rendezvous path: the receiver wakes on its own home core.
          simp only []
          -- PR #873 round 17: the arm resolves the sender before popping, so
          -- there is one more split than there used to be.
          split
          · exact observableSlotsConfinedToCores_of_eq _ rfl
          · split
            · exact observableSlotsConfinedToCores_of_eq _ rfl
            · next recvTid recvTcb st1 hPop =>
            split
            · exact observableSlotsConfinedToCores_of_eq _ rfl
            · next st2 hMsgR =>
              have hEpObj : st.objects[endpointId]? = some (.endpoint ep) :=
                (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hEp
              have hPopHead : ep.receiveQ.head = some recvTid := by
                have h := endpointQueuePopHead_returns_head endpointId true st ep recvTid
                  st1 hEpObj hPop
                simpa using h
              have hRecv : recvTid = headRecv := by
                rw [hHead] at hPopHead; simpa using hPopHead.symm
              have hInv1 : st1.objects.invExt :=
                endpointQueuePopHead_preserves_objects_invExt endpointId true st st1
                  recvTid recvTcb hObjInv hPop
              have hT1 : determineTargetCore st1 recvTid = determineTargetCore st recvTid :=
                endpointQueuePopHead_determineTargetCore_eq endpointId true st st1
                  recvTid recvTcb recvTid hObjInv hPop
              have hT2 : determineTargetCore st2 recvTid = determineTargetCore st1 recvTid :=
                storeTcbReceiveComplete_determineTargetCore_eq st1 st2 recvTid
                  (some msg) recvTid hInv1 hMsgR
              have hChain := observableSlotsConfinedToCores_widen_cons
                (observableSlotsConfinedToCores_trans
                  (endpointQueuePopHead_confinedToCores endpointId true st st1 recvTid hPop)
                  (storeTcbReceiveComplete_confinedToCores st1 st2 recvTid (some msg) hMsgR))
                (wakeThread_confinedToCores st2 recvTid executingCore)
              rw [hT2, hT1] at hChain
              rw [← hRecv]
              exact hChain

/-- SM8.B.2: the WithCaps send leaves the bare send's run queues in place — every
arm either *is* the bare send's post-state or is that state after an
`ipcUnwrapCaps`, which preserves the scheduler. -/
theorem endpointSendDualWithCapsOnCore_scheduler_eq (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    (endpointSendDualWithCapsOnCore endpointId sender msg endpointRights
        receiverSlotBase executingCore st).1.scheduler
      = (endpointSendDualOnCore endpointId sender { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st).1.scheduler := by
  unfold endpointSendDualWithCapsOnCore
  cases hSend : endpointSendDualOnCore endpointId sender { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st with
  | mk stSend res =>
    cases res with
    | error e => rfl
    | ok sgi =>
      simp only []
      repeat' split
      all_goals first
        | rfl
        | (rename_i h; exact ipcUnwrapCaps_preserves_scheduler _ _ _ _ _ _ _ h)

/-- SM8.B.2: and the register banks, by the same case analysis. -/
theorem endpointSendDualWithCapsOnCore_machine_eq (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    (endpointSendDualWithCapsOnCore endpointId sender msg endpointRights
        receiverSlotBase executingCore st).1.machine
      = (endpointSendDualOnCore endpointId sender { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st).1.machine := by
  unfold endpointSendDualWithCapsOnCore
  cases hSend : endpointSendDualOnCore endpointId sender { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st with
  | mk stSend res =>
    cases res with
    | error e => rfl
    | ok sgi =>
      simp only []
      repeat' split
      all_goals first
        | rfl
        | (rename_i h; exact ipcUnwrapCaps_preserves_machine _ _ _ _ _ _ _ h)

/-- SM8.B.2 (**the live unchecked `.send` bound**): the WithCaps cross-core send —
the form `dispatchWithCap_send_delegates` says the live arm calls — is confined to
the bare send's write set. The extra leg is `ipcUnwrapCaps`, which writes no core
at all, so the two forms declare the same per-core footprint. -/
theorem endpointSendDualWithCapsOnCore_confinedToCores (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointSendDualWithCapsOnCore endpointId sender msg endpointRights
        receiverSlotBase executingCore st).1
      (endpointSendWriteSet st endpointId executingCore) := by
  have h := observableSlotsConfinedToCores_trans
    (endpointSendDualOnCore_confinedToCores endpointId sender { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st hObjInv)
    (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
      (endpointSendDualWithCapsOnCore_scheduler_eq endpointId sender msg endpointRights
        receiverSlotBase executingCore st)
      (endpointSendDualWithCapsOnCore_machine_eq endpointId sender msg endpointRights
        receiverSlotBase executingCore st))
  simpa using h

/-- SM8.B.2 (**the live checked `.send` bound**): the flow-checked cross-core send
is confined to the same set. Its three gates — two bounds checks and the
`sender → endpoint` flow guard — each return the pre-state, which writes nothing;
past them it *is* the unchecked form. -/
theorem endpointSendCrossCoreDispatchChecked_confinedToCores (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointSendCrossCoreDispatchChecked ctx endpointId sender msg endpointRights
        receiverSlotBase executingCore st).1
      (endpointSendWriteSet st endpointId executingCore) := by
  unfold endpointSendCrossCoreDispatchChecked
  split
  · exact observableSlotsConfinedToCores_of_eq _ rfl
  · split
    · exact observableSlotsConfinedToCores_of_eq _ rfl
    · split
      · exact endpointSendDualWithCapsOnCore_confinedToCores endpointId sender msg
          endpointRights receiverSlotBase executingCore st hObjInv
      · exact observableSlotsConfinedToCores_of_eq _ rfl

end SeLe4n.Kernel
