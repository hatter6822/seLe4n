/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.Defs
import SeLe4n.Kernel.IPC.DualQueue.Transport

/-!
# V3-K: endpointQueueNoDup Preservation Proofs

Preservation proofs for `endpointQueueNoDup` across all IPC operations.
K-1 (no self-loops) follows from `tcbQueueChainAcyclic`. All new work targets K-2
(send/receive queue head disjointness).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

set_option linter.unusedVariables false

-- ============================================================================
-- Section 1: Primitive frame lemmas
-- ============================================================================

/-- V3-K-prim-1: Storing a non-endpoint, non-TCB object preserves endpointQueueNoDup.
Neither endpoint queues nor TCB queueNext fields change. -/
theorem storeObject_non_ep_non_tcb_preserves_endpointQueueNoDup
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hInv : endpointQueueNoDup st)
    (hObjInv : st.objects.invExt)
    (hNotEp : ∀ ep, obj ≠ .endpoint ep)
    (hNotTcb : ∀ tcb, obj ≠ .tcb tcb)
    (hStore : storeObject oid obj st = .ok ((), st')) :
    endpointQueueNoDup st' := by
  intro oid' ep' hEp'
  by_cases hEq : oid' = oid
  · -- Stored object is at oid' = oid, but obj is not an endpoint — contradiction
    have hObj := storeObject_objects_eq st st' oid obj hObjInv hStore
    rw [hEq] at hEp'; rw [hObj] at hEp'; cases hEp'
    exact absurd rfl (hNotEp ep')
  · have hFrame := storeObject_objects_ne st st' oid oid' obj hEq hObjInv hStore
    rw [hFrame] at hEp'
    have ⟨hK1, hK2⟩ := hInv oid' ep' hEp'
    constructor
    · intro tid tcb hTcb'
      by_cases hEqT : tid.toObjId = oid
      · have hObj := storeObject_objects_eq st st' oid obj hObjInv hStore
        rw [hEqT] at hTcb'; rw [hObj] at hTcb'; cases hTcb'
        exact absurd rfl (hNotTcb tcb)
      · have hFrameT := storeObject_objects_ne st st' oid tid.toObjId obj hEqT hObjInv hStore
        rw [hFrameT] at hTcb'
        exact hK1 tid tcb hTcb'
    · exact hK2

/-- V3-K-prim-2: storeTcbQueueLinks preserves endpointQueueNoDup.
Storing a TCB does not modify any endpoint object, so K-2 (queue head disjointness)
transfers directly. K-1 follows from post-state tcbQueueChainAcyclic. -/
theorem storeTcbQueueLinks_preserves_endpointQueueNoDup
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hInv : endpointQueueNoDup st)
    (hAcyclic : tcbQueueChainAcyclic st')
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    endpointQueueNoDup st' := by
  intro oid ep hEp
  -- Endpoint objects are unaffected by TCB stores: need oid ≠ tid.toObjId
  have hNe : oid ≠ tid.toObjId := by
    intro hEq; subst hEq
    unfold storeTcbQueueLinks at hStore
    cases hLk : lookupTcb st tid with
    | none => simp [hLk] at hStore
    | some tcb =>
      simp only [hLk] at hStore
      cases hSt : storeObject tid.toObjId (.tcb (tcbWithQueueLinks tcb prev pprev next)) st with
      | error e => simp [hSt] at hStore
      | ok pair =>
        simp only [hSt] at hStore
        have hEqSt := Except.ok.inj hStore; subst hEqSt
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hSt] at hEp
        cases hEp
  have hFrame := storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next oid hNe hObjInv hStore
  rw [hFrame] at hEp
  have ⟨_, hK2⟩ := hInv oid ep hEp
  exact ⟨fun tid' tcb' hTcb' => tcbQueueChainAcyclic_no_self_loop hAcyclic tid' tcb' hTcb', hK2⟩

/-- V3-K-prim-3: Storing an endpoint preserves endpointQueueNoDup when the new
endpoint's queue heads satisfy disjointness. -/
theorem storeObject_endpoint_preserves_endpointQueueNoDup
    (st st' : SystemState) (oid : SeLe4n.ObjId) (ep' : Endpoint)
    (hInv : endpointQueueNoDup st)
    (hAcyclic : tcbQueueChainAcyclic st')
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid (.endpoint ep') st = .ok ((), st'))
    (hDisjoint : ep'.sendQ.head = none ∨ ep'.receiveQ.head = none ∨
                 ep'.sendQ.head ≠ ep'.receiveQ.head) :
    endpointQueueNoDup st' := by
  intro oid' ep'' hEp'
  by_cases hEq : oid' = oid
  · have hObj := storeObject_objects_eq st st' oid _ hObjInv hStore
    rw [hEq] at hEp'; rw [hObj] at hEp'; cases hEp'
    exact ⟨fun tid tcb hTcb => tcbQueueChainAcyclic_no_self_loop hAcyclic tid tcb hTcb, hDisjoint⟩
  · have hFrame := storeObject_objects_ne st st' oid oid' _ hEq hObjInv hStore
    rw [hFrame] at hEp'
    have ⟨_, hK2⟩ := hInv oid' ep'' hEp'
    exact ⟨fun tid tcb hTcb => tcbQueueChainAcyclic_no_self_loop hAcyclic tid tcb hTcb, hK2⟩

end SeLe4n.Kernel
