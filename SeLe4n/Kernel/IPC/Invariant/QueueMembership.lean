import SeLe4n.Kernel.IPC.Invariant.Defs
import SeLe4n.Kernel.IPC.DualQueue.Transport

/-!
# V3-J: ipcStateQueueMembershipConsistent Preservation Proofs
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

set_option linter.unusedVariables false

-- ============================================================================
-- Section 1: Primitive frame lemmas
-- ============================================================================

/-- V3-J-prim-1: Storing a non-TCB, non-endpoint object preserves
ipcStateQueueMembershipConsistent. Requires that the pre-state at `oid` also
held neither an endpoint nor a TCB (mirroring the notification frame pattern
in `storeObject_notification_preserves_ipcStateQueueConsistent`). -/
theorem storeObject_non_ep_non_tcb_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hObjInv : st.objects.invExt)
    (hNotEp : ∀ ep, obj ≠ .endpoint ep)
    (hNotTcb : ∀ tcb, obj ≠ .tcb tcb)
    (hPrevNotEp : ∀ ep, st.objects[oid]? ≠ some (.endpoint ep))
    (hPrevNotTcb : ∀ tcb, st.objects[oid]? ≠ some (.tcb tcb))
    (hStore : storeObject oid obj st = .ok ((), st')) :
    ipcStateQueueMembershipConsistent st' := by
  have hFrame : ∀ x, x ≠ oid → st'.objects[x]? = st.objects[x]? :=
    fun x hNe => storeObject_objects_ne st st' oid x obj hNe hObjInv hStore
  have hEqAt : st'.objects[oid]? = some obj :=
    storeObject_objects_eq st st' oid obj hObjInv hStore
  intro tid tcb hTcb
  have hNeTid : tid.toObjId ≠ oid := by
    intro hEq; rw [hEq] at hTcb; rw [hEqAt] at hTcb; cases hTcb; exact absurd rfl (hNotTcb tcb)
  rw [hFrame tid.toObjId hNeTid] at hTcb
  have hPre := hInv tid tcb hTcb
  -- Helper: transfer blocking-case evidence from pre-state to post-state
  have transfer : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
    st.objects[epId]? = some (KernelObject.endpoint ep) →
    (ep.sendQ.head = some tid ∨
      ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
        st.objects[prev.toObjId]? = some (KernelObject.tcb prevTcb) ∧
        prevTcb.queueNext = some tid) →
    ∃ ep', st'.objects[epId]? = some (KernelObject.endpoint ep') ∧
      (ep'.sendQ.head = some tid ∨
        ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
          st'.objects[prev.toObjId]? = some (KernelObject.tcb prevTcb) ∧
          prevTcb.queueNext = some tid) := by
    intro epId ep hEp hReach
    have hNeEp : epId ≠ oid := by
      intro hEq; subst hEq; exact absurd hEp (hPrevNotEp ep)
    refine ⟨ep, by rw [hFrame epId hNeEp]; exact hEp, ?_⟩
    exact hReach.elim Or.inl (fun ⟨prev, prevTcb, hPrev, hNext⟩ => by
      have hNePrev : prev.toObjId ≠ oid := by
        intro hEq; subst hEq; exact absurd hPrev (hPrevNotTcb prevTcb)
      exact Or.inr ⟨prev, prevTcb, by rw [hFrame prev.toObjId hNePrev]; exact hPrev, hNext⟩)
  have transferRecv : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
    st.objects[epId]? = some (KernelObject.endpoint ep) →
    (ep.receiveQ.head = some tid ∨
      ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
        st.objects[prev.toObjId]? = some (KernelObject.tcb prevTcb) ∧
        prevTcb.queueNext = some tid) →
    ∃ ep', st'.objects[epId]? = some (KernelObject.endpoint ep') ∧
      (ep'.receiveQ.head = some tid ∨
        ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
          st'.objects[prev.toObjId]? = some (KernelObject.tcb prevTcb) ∧
          prevTcb.queueNext = some tid) := by
    intro epId ep hEp hReach
    have hNeEp : epId ≠ oid := by
      intro hEq; subst hEq; exact absurd hEp (hPrevNotEp ep)
    refine ⟨ep, by rw [hFrame epId hNeEp]; exact hEp, ?_⟩
    exact hReach.elim Or.inl (fun ⟨prev, prevTcb, hPrev, hNext⟩ => by
      have hNePrev : prev.toObjId ≠ oid := by
        intro hEq; subst hEq; exact absurd hPrev (hPrevNotTcb prevTcb)
      exact Or.inr ⟨prev, prevTcb, by rw [hFrame prev.toObjId hNePrev]; exact hPrev, hNext⟩)
  match hIpc : tcb.ipcState with
  | .blockedOnSend epId =>
    simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach⟩ := hPre
    exact transfer epId ep hEp hReach
  | .blockedOnReceive epId =>
    simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach⟩ := hPre
    exact transferRecv epId ep hEp hReach
  | .blockedOnCall epId =>
    simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach⟩ := hPre
    exact transfer epId ep hEp hReach
  | .ready => trivial
  | .blockedOnReply _ _ => trivial
  | .blockedOnNotification _ => trivial

-- ============================================================================
-- Section 2: Scheduler frame lemmas
-- ============================================================================

/-- Helper: pointwise object lookup equality implies `ipcStateQueueMembershipConsistent` transfer. -/
theorem ipcStateQueueMembershipConsistent_of_objects_eq
    (st st' : SystemState)
    (hLk : ∀ (x : SeLe4n.ObjId), st'.objects[x]? = st.objects[x]?)
    (hInv : ipcStateQueueMembershipConsistent st) :
    ipcStateQueueMembershipConsistent st' := by
  intro tid tcb hTcb
  rw [hLk] at hTcb
  have hPre := hInv tid tcb hTcb
  match hIpc : tcb.ipcState with
  | .blockedOnSend epId =>
    simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach⟩ := hPre
    exact ⟨ep, by rw [hLk]; exact hEp,
      hReach.elim Or.inl (fun ⟨prev, prevTcb, hPrev, hNext⟩ =>
        Or.inr ⟨prev, prevTcb, by rw [hLk]; exact hPrev, hNext⟩)⟩
  | .blockedOnReceive epId =>
    simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach⟩ := hPre
    exact ⟨ep, by rw [hLk]; exact hEp,
      hReach.elim Or.inl (fun ⟨prev, prevTcb, hPrev, hNext⟩ =>
        Or.inr ⟨prev, prevTcb, by rw [hLk]; exact hPrev, hNext⟩)⟩
  | .blockedOnCall epId =>
    simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach⟩ := hPre
    exact ⟨ep, by rw [hLk]; exact hEp,
      hReach.elim Or.inl (fun ⟨prev, prevTcb, hPrev, hNext⟩ =>
        Or.inr ⟨prev, prevTcb, by rw [hLk]; exact hPrev, hNext⟩)⟩
  | .ready => trivial
  | .blockedOnReply _ _ => trivial
  | .blockedOnNotification _ => trivial

/-- ensureRunnable preserves ipcStateQueueMembershipConsistent. -/
theorem ensureRunnable_preserves_ipcStateQueueMembershipConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : ipcStateQueueMembershipConsistent st) :
    ipcStateQueueMembershipConsistent (ensureRunnable st tid) :=
  ipcStateQueueMembershipConsistent_of_objects_eq st (ensureRunnable st tid)
    (fun x => congrArg (·.get? x) (ensureRunnable_preserves_objects st tid)) hInv

/-- removeRunnable preserves ipcStateQueueMembershipConsistent. -/
theorem removeRunnable_preserves_ipcStateQueueMembershipConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : ipcStateQueueMembershipConsistent st) :
    ipcStateQueueMembershipConsistent (removeRunnable st tid) :=
  ipcStateQueueMembershipConsistent_of_objects_eq st (removeRunnable st tid)
    (fun x => congrArg (·.get? x) (removeRunnable_preserves_objects st tid)) hInv

end SeLe4n.Kernel
