-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM6.A cross-core IPC (runtime dispatch wiring
-- gated on the SM5.I FFI seam; see docs/planning/SMP_CROSS_CORE_IPC_PLAN.md).

import SeLe4n.Kernel.IPC.CrossCore.EndpointCall
import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.Concurrency.Locks.Serializability

/-!
# WS-SM SM6.A — Cross-core endpoint-call invariant preservation

`endpointCallOnCore` preserves the kernel's IPC invariants.  The structural
content is the **keystone** that the cross-core receiver wake
(`wakeThread`/`enqueueRunnableOnCore`) is *object-invisible* on the rendezvous
path: the receiver was already set `.ready` by the preceding
`storeTcbIpcStateAndMessage`, so the wake's `ipcState := .ready` write inserts
the *same* value it found — every object-store lookup is unchanged.  Since the
whole `ipcInvariantFull` bundle (15 conjuncts) and `ipcInvariant` are
**objects-only** predicates, the cross-core operation preserves exactly what the
single-core `endpointCall` preserves: it differs from `endpointCall` only in the
scheduler placement of the woken receiver / blocked caller, which the
object-only invariants do not read.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  `objects.invExt` preservation (object-store integrity)
-- ============================================================================

/-- WS-SM SM6.A.1: the cross-core endpoint call preserves object-store
integrity (`invExt`).  On every control path the post-state's object store is
either `st`'s (an error / no-op leaf) or the result of the
pop / store / wake / store / deschedule chain, each step of which preserves
`invExt`.  Unconditional: an error leaf returns the pre-state unchanged. -/
theorem endpointCallOnCore_preserves_objects_invExt
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    (endpointCallOnCore endpointId caller msg executingCore st).1.objects.invExt := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact hObjInv
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact hObjInv
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact hObjInv
  | some ep =>
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact hObjInv
      | ok st' =>
        simp only
        have h1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st' hObjInv hEnq
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact hObjInv
        | ok st'' =>
          simp only
          have h2 := storeTcbIpcStateAndMessage_preserves_objects_invExt st' st'' caller _ _ h1 hMsg
          show (removeRunnableOnCore st'' caller executingCore).objects.invExt
          rw [removeRunnableOnCore_preserves_objects]; exact h2
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact hObjInv
      | ok pair =>
        simp only
        have h1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact hObjInv
        | ok st2 =>
          simp only
          have h2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ _ h1 hMsg
          have hW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore h2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact hObjInv
          | ok st4 =>
            simp only
            have h4 := storeTcbIpcStateAndMessage_preserves_objects_invExt
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hW hCS
            show (removeRunnableOnCore st4 caller executingCore).objects.invExt
            rw [removeRunnableOnCore_preserves_objects]; exact h4

-- ============================================================================
-- §2  Keystone: the cross-core receiver wake is object-invisible
-- ============================================================================

/-- WS-SM SM6.A.1 (keystone): `enqueueRunnableOnCore` of a thread that is
**already `.ready`** is invisible to every object-store lookup.  The only object
the wake writes is the woken TCB, with `ipcState := .ready` — but it is already
`.ready`, so the inserted value equals the one already stored.  This is why the
cross-core receiver wake preserves every *objects-only* invariant: on the
rendezvous path the receiver was set `.ready` by the preceding store. -/
theorem enqueueRunnableOnCore_objects_getElem_eq_of_ready
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hReady : tcb.ipcState = .ready)
    (hInv : st.objects.invExt) (oid : SeLe4n.ObjId) :
    (enqueueRunnableOnCore st c tid).objects[oid]? = st.objects[oid]? := by
  -- (typed via `getTcb?_eq_some_iff`; the object-store lookup shape is inferred,
  -- so this proof writes no raw typed-id object-store lookup of its own).
  have hObjTcb := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
  have hVal : (KernelObject.tcb { tcb with ipcState := .ready }) = .tcb tcb := by rw [← hReady]
  unfold enqueueRunnableOnCore
  simp only [hTcb]
  split
  · rfl
  · show (st.objects.insert tid.toObjId (.tcb { tcb with ipcState := .ready }))[oid]?
        = st.objects[oid]?
    rw [hVal]
    by_cases hEq : oid = tid.toObjId
    · subst hEq
      rw [hObjTcb]
      simp only [RHTable_getElem?_eq_get?]
      exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId (.tcb tcb) hInv
    · simp only [RHTable_getElem?_eq_get?]
      exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId oid (.tcb tcb)
        (by simp only [beq_iff_eq]; exact fun h => hEq h.symm) hInv

/-- WS-SM SM6.A.1 (keystone, wake form): the cross-core `wakeThread` of an
already-`.ready` thread is invisible to every object-store lookup. -/
theorem wakeThread_objects_getElem_eq_of_ready
    (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hReady : tcb.ipcState = .ready)
    (hInv : st.objects.invExt) (oid : SeLe4n.ObjId) :
    (wakeThread st tid ec).1.objects[oid]? = st.objects[oid]? := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_objects_getElem_eq_of_ready st (determineTargetCore st tid) tid tcb
    hTcb hReady hInv oid

-- ============================================================================
-- §3  `ipcInvariant` (notification well-formedness) preservation
-- ============================================================================

/-- WS-SM SM6.A.1: the cross-core endpoint call preserves the notification
invariant.  Mirrors the single-core `endpointCall_preserves_ipcInvariant`, with
the receiver wake discharged through the §2 object-invisibility keystone (the
receiver is already `.ready` after the message store) and the caller deschedule
through `removeRunnableOnCore`'s object-store frame. -/
theorem endpointCallOnCore_preserves_ipcInvariant
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt) :
    ipcInvariant (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact hInv
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact hInv
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact hInv
  | some ep =>
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact hInv
      | ok st' =>
        simp only
        have hInv1 := endpointQueueEnqueue_preserves_ipcInvariant endpointId false caller st st' hInv hObjInv hEnq
        have hObj1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st' hObjInv hEnq
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact hInv
        | ok st'' =>
          simp only
          have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant st' st'' caller _ _ hInv1 hObj1 hMsg
          show ipcInvariant (removeRunnableOnCore st'' caller executingCore)
          exact fun oid ntfn h => hInv2 oid ntfn (by rwa [removeRunnableOnCore_preserves_objects] at h)
    | some _ =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact hInv
      | ok pair =>
        simp only
        have hInv1 := endpointQueuePopHead_preserves_ipcInvariant endpointId true st pair.2.2 pair.1 hInv hObjInv hPop
        have hObj1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact hInv
        | ok st2 =>
          simp only
          have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant pair.2.2 st2 pair.1 _ _ hInv1 hObj1 hMsg
          have hObj2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ _ hObj1 hMsg
          obtain ⟨tr, hTrGet, hTrReady⟩ :=
            storeTcbIpcStateAndMessage_getTcb?_ipcState pair.2.2 st2 pair.1 .ready (some msg) hObj1 hMsg
          have hInvW : ipcInvariant (wakeThread st2 pair.1 executingCore).1 :=
            fun oid ntfn h => hInv2 oid ntfn
              (by rwa [wakeThread_objects_getElem_eq_of_ready st2 pair.1 executingCore tr hTrGet hTrReady hObj2 oid] at h)
          have hObjW := wakeThread_preserves_objects_invExt st2 pair.1 executingCore hObj2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact hInv
          | ok st4 =>
            simp only
            have hInv4 := storeTcbIpcStateAndMessage_preserves_ipcInvariant
              (wakeThread st2 pair.1 executingCore).1 st4 caller _ _ hInvW hObjW hCS
            show ipcInvariant (removeRunnableOnCore st4 caller executingCore)
            exact fun oid ntfn h => hInv4 oid ntfn (by rwa [removeRunnableOnCore_preserves_objects] at h)

-- ============================================================================
-- §4  SM6.A.9 — invariant preservation *through* the 2PL lock bracket
-- ============================================================================

/-- WS-SM SM6.A.9 (atomicity, invariant form): under its `withLockSet` bracket
the cross-core endpoint call preserves object-store integrity **through the
entire 2PL acquire/release fold**, not merely the bare action.  Composes the
bare-action `endpointCallOnCore_preserves_objects_invExt` with the lock-acquire /
lock-release insensitivity of `invExt` via the SM3.C.8 metatheorem
`withLockSet_invariant_preserved`.  This is the substantive content behind
"atomic under lock-set": no lock-bookkeeping step of the bracket disturbs the
object-store well-formedness the transition relies on. -/
theorem endpointCallOnCore_withLockSet_preserves_objects_invExt
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (cnRoot : SeLe4n.ObjId)
    (receiver? : Option SeLe4n.ThreadId) (donatedSc? : Option SeLe4n.SchedContextId)
    (s : SystemState) (hObjInv : s.objects.invExt) :
    (withLockSet (lockSet_endpointCall caller cnRoot endpointId receiver? donatedSc?)
        executingCore (endpointCallOnCore endpointId caller msg executingCore) s).1.objects.invExt :=
  withLockSet_invariant_preserved _ executingCore _ s (fun st => st.objects.invExt) hObjInv
    (fun l m s' h => acquireLockOnObject_preserves_invExt s' executingCore l m h)
    (fun s' h => endpointCallOnCore_preserves_objects_invExt endpointId caller msg executingCore s' h)
    (fun l m s' h => releaseLockOnObject_preserves_invExt s' executingCore l m h)

end SeLe4n.Kernel
