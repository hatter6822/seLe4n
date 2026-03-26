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

-- ============================================================================
-- Section 3: TCB-store primitives
-- ============================================================================

/-- storeTcbIpcStateAndMessage preserves ipcStateQueueMembershipConsistent
when the new ipcState does not create blocking dependencies. -/
theorem storeTcbIpcStateAndMessage_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState) (msg : Option IpcMessage)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hObjInv : st.objects.invExt)
    (hNotSend : ∀ epId, ipcState ≠ .blockedOnSend epId)
    (hNotRecv : ∀ epId, ipcState ≠ .blockedOnReceive epId)
    (hNotCall : ∀ epId, ipcState ≠ .blockedOnCall epId)
    (hStore : storeTcbIpcStateAndMessage st tid ipcState msg = .ok st') :
    ipcStateQueueMembershipConsistent st' := by
  unfold storeTcbIpcStateAndMessage at hStore
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStore
  | some tcb =>
    simp only [hLookup] at hStore
    cases hSt : storeObject tid.toObjId
        (.tcb { tcb with ipcState := ipcState, pendingMessage := msg }) st with
    | error e => simp [hSt] at hStore
    | ok pair =>
      simp only [hSt, Except.ok.injEq] at hStore; subst hStore
      have hFrame : ∀ x, x ≠ tid.toObjId → pair.2.objects[x]? = st.objects[x]? :=
        fun x hNe => storeObject_objects_ne st pair.2 tid.toObjId x _ hNe hObjInv hSt
      have hEqAt := storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hSt
      have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
      have transferPrev : ∀ (tid2 : SeLe4n.ThreadId)
          (prev : SeLe4n.ThreadId) (prevTcb : TCB),
          st.objects[prev.toObjId]? = some (.tcb prevTcb) →
          prevTcb.queueNext = some tid2 →
          ∃ prevTcb', pair.2.objects[prev.toObjId]? = some (.tcb prevTcb') ∧
            prevTcb'.queueNext = some tid2 := by
        intro tid2 prev prevTcb hPrev hNext
        by_cases hPrevEq : prev.toObjId = tid.toObjId
        · rw [hPrevEq] at hPrev; rw [hTcbObj] at hPrev; cases hPrev
          exact ⟨{ tcb with ipcState := ipcState, pendingMessage := msg },
            by rw [hPrevEq]; exact hEqAt, hNext⟩
        · exact ⟨prevTcb, by rw [hFrame _ hPrevEq]; exact hPrev, hNext⟩
      intro tid2 tcb2 hTcb2
      by_cases hEq : tid2.toObjId = tid.toObjId
      · -- tid2 is the stored TCB: new ipcState is trivially V3-J
        rw [hEq, hEqAt] at hTcb2
        simp only [Option.some.injEq, KernelObject.tcb.injEq] at hTcb2; subst hTcb2
        match ipcState with
        | .ready => trivial
        | .blockedOnReply _ _ => trivial
        | .blockedOnNotification _ => trivial
        | .blockedOnSend epId => exact absurd rfl (hNotSend epId)
        | .blockedOnReceive epId => exact absurd rfl (hNotRecv epId)
        | .blockedOnCall epId => exact absurd rfl (hNotCall epId)
      · -- tid2 ≠ tid: transfer pre-state V3-J evidence
        rw [hFrame tid2.toObjId hEq] at hTcb2
        have hPre := hInv tid2 tcb2 hTcb2
        match hIpc : tcb2.ipcState with
        | .blockedOnSend epId =>
          simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach⟩ := hPre
          have hNeEp : epId ≠ tid.toObjId := by
            intro h; subst h; rw [hTcbObj] at hEp; cases hEp
          exact ⟨ep, by rw [hFrame epId hNeEp]; exact hEp,
            hReach.elim Or.inl fun ⟨prev, prevTcb, hP, hN⟩ =>
              let ⟨pt, hPt, hNt⟩ := transferPrev tid2 prev prevTcb hP hN
              Or.inr ⟨prev, pt, hPt, hNt⟩⟩
        | .blockedOnReceive epId =>
          simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach⟩ := hPre
          have hNeEp : epId ≠ tid.toObjId := by
            intro h; subst h; rw [hTcbObj] at hEp; cases hEp
          exact ⟨ep, by rw [hFrame epId hNeEp]; exact hEp,
            hReach.elim Or.inl fun ⟨prev, prevTcb, hP, hN⟩ =>
              let ⟨pt, hPt, hNt⟩ := transferPrev tid2 prev prevTcb hP hN
              Or.inr ⟨prev, pt, hPt, hNt⟩⟩
        | .blockedOnCall epId =>
          simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach⟩ := hPre
          have hNeEp : epId ≠ tid.toObjId := by
            intro h; subst h; rw [hTcbObj] at hEp; cases hEp
          exact ⟨ep, by rw [hFrame epId hNeEp]; exact hEp,
            hReach.elim Or.inl fun ⟨prev, prevTcb, hP, hN⟩ =>
              let ⟨pt, hPt, hNt⟩ := transferPrev tid2 prev prevTcb hP hN
              Or.inr ⟨prev, pt, hPt, hNt⟩⟩
        | .ready => trivial
        | .blockedOnReply _ _ => trivial
        | .blockedOnNotification _ => trivial

/-- storeTcbIpcStateAndMessage_fromTcb preserves ipcStateQueueMembershipConsistent. -/
theorem storeTcbIpcStateAndMessage_fromTcb_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (ipcState : ThreadIpcState) (msg : Option IpcMessage)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hObjInv : st.objects.invExt)
    (hLookup : lookupTcb st tid = some tcb)
    (hNotSend : ∀ epId, ipcState ≠ .blockedOnSend epId)
    (hNotRecv : ∀ epId, ipcState ≠ .blockedOnReceive epId)
    (hNotCall : ∀ epId, ipcState ≠ .blockedOnCall epId)
    (hStore : storeTcbIpcStateAndMessage_fromTcb st tid tcb ipcState msg = .ok st') :
    ipcStateQueueMembershipConsistent st' :=
  storeTcbIpcStateAndMessage_preserves_ipcStateQueueMembershipConsistent
    st st' tid ipcState msg hInv hObjInv hNotSend hNotRecv hNotCall
    (by rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLookup]; exact hStore)

/-- storeTcbIpcState preserves ipcStateQueueMembershipConsistent for non-blocking states. -/
theorem storeTcbIpcState_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipcState : ThreadIpcState)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hObjInv : st.objects.invExt)
    (hNotSend : ∀ epId, ipcState ≠ .blockedOnSend epId)
    (hNotRecv : ∀ epId, ipcState ≠ .blockedOnReceive epId)
    (hNotCall : ∀ epId, ipcState ≠ .blockedOnCall epId)
    (hStore : storeTcbIpcState st tid ipcState = .ok st') :
    ipcStateQueueMembershipConsistent st' := by
  unfold storeTcbIpcState at hStore
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStore
  | some tcb =>
    simp only [hLookup] at hStore
    cases hSt : storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState }) st with
    | error e => simp [hSt] at hStore
    | ok pair =>
      simp only [hSt, Except.ok.injEq] at hStore; subst hStore
      have hFrame : ∀ x, x ≠ tid.toObjId → pair.2.objects[x]? = st.objects[x]? :=
        fun x hNe => storeObject_objects_ne st pair.2 tid.toObjId x _ hNe hObjInv hSt
      have hEqAt := storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hSt
      have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
      have transferPrev : ∀ (tid2 prev : SeLe4n.ThreadId) (prevTcb : TCB),
          st.objects[prev.toObjId]? = some (.tcb prevTcb) →
          prevTcb.queueNext = some tid2 →
          ∃ prevTcb', pair.2.objects[prev.toObjId]? = some (.tcb prevTcb') ∧
            prevTcb'.queueNext = some tid2 := by
        intro tid2 prev prevTcb hPrev hNext
        by_cases hPrevEq : prev.toObjId = tid.toObjId
        · rw [hPrevEq] at hPrev; rw [hTcbObj] at hPrev; cases hPrev
          exact ⟨{ tcb with ipcState := ipcState },
            by rw [hPrevEq]; exact hEqAt, hNext⟩
        · exact ⟨prevTcb, by rw [hFrame _ hPrevEq]; exact hPrev, hNext⟩
      intro tid2 tcb2 hTcb2
      by_cases hEq : tid2.toObjId = tid.toObjId
      · rw [hEq, hEqAt] at hTcb2
        simp only [Option.some.injEq, KernelObject.tcb.injEq] at hTcb2; subst hTcb2
        match ipcState with
        | .ready => trivial
        | .blockedOnReply _ _ => trivial
        | .blockedOnNotification _ => trivial
        | .blockedOnSend epId => exact absurd rfl (hNotSend epId)
        | .blockedOnReceive epId => exact absurd rfl (hNotRecv epId)
        | .blockedOnCall epId => exact absurd rfl (hNotCall epId)
      · rw [hFrame tid2.toObjId hEq] at hTcb2
        have hPre := hInv tid2 tcb2 hTcb2
        match hIpc : tcb2.ipcState with
        | .blockedOnSend epId =>
          simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach⟩ := hPre
          have hNeEp : epId ≠ tid.toObjId := by
            intro h; subst h; rw [hTcbObj] at hEp; cases hEp
          exact ⟨ep, by rw [hFrame epId hNeEp]; exact hEp,
            hReach.elim Or.inl fun ⟨prev, prevTcb, hP, hN⟩ =>
              let ⟨pt, hPt, hNt⟩ := transferPrev tid2 prev prevTcb hP hN
              Or.inr ⟨prev, pt, hPt, hNt⟩⟩
        | .blockedOnReceive epId =>
          simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach⟩ := hPre
          have hNeEp : epId ≠ tid.toObjId := by
            intro h; subst h; rw [hTcbObj] at hEp; cases hEp
          exact ⟨ep, by rw [hFrame epId hNeEp]; exact hEp,
            hReach.elim Or.inl fun ⟨prev, prevTcb, hP, hN⟩ =>
              let ⟨pt, hPt, hNt⟩ := transferPrev tid2 prev prevTcb hP hN
              Or.inr ⟨prev, pt, hPt, hNt⟩⟩
        | .blockedOnCall epId =>
          simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach⟩ := hPre
          have hNeEp : epId ≠ tid.toObjId := by
            intro h; subst h; rw [hTcbObj] at hEp; cases hEp
          exact ⟨ep, by rw [hFrame epId hNeEp]; exact hEp,
            hReach.elim Or.inl fun ⟨prev, prevTcb, hP, hN⟩ =>
              let ⟨pt, hPt, hNt⟩ := transferPrev tid2 prev prevTcb hP hN
              Or.inr ⟨prev, pt, hPt, hNt⟩⟩
        | .ready => trivial
        | .blockedOnReply _ _ => trivial
        | .blockedOnNotification _ => trivial

-- ============================================================================
-- Section 4: Per-operation preservation proofs
-- ============================================================================

/-- notificationSignal preserves ipcStateQueueMembershipConsistent. -/
theorem notificationSignal_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    ipcStateQueueMembershipConsistent st' := by
  unfold notificationSignal at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hWaiters : ntfn.waitingThreads with
      | cons waiter rest =>
        simp only [hWaiters] at hStep
        generalize hStore1 : storeObject notificationId _ st = r1 at hStep
        cases r1 with
        | error e => simp at hStep
        | ok pair1 =>
          simp only [] at hStep
          have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair1 hObjInv hStore1
          have hInv1 := storeObject_non_ep_non_tcb_preserves_ipcStateQueueMembershipConsistent
            st pair1.2 notificationId _ hInv hObjInv
            (fun ep => by intro h; cases h) (fun tcb => by intro h; cases h)
            (fun ep => by rw [hObj]; intro h; cases h) (fun tcb => by rw [hObj]; intro h; cases h)
            hStore1
          generalize hMsg : storeTcbIpcStateAndMessage pair1.2 waiter .ready _ = rMsg at hStep
          cases rMsg with
          | error e => simp at hStep
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, rfl⟩ := hStep
            exact ensureRunnable_preserves_ipcStateQueueMembershipConsistent _ _ <|
              storeTcbIpcStateAndMessage_preserves_ipcStateQueueMembershipConsistent _ _ _ _ _ hInv1 hObjInv1
                (fun epId => by intro h; cases h) (fun epId => by intro h; cases h)
                (fun epId => by intro h; cases h) hMsg
      | nil =>
        simp only [hWaiters] at hStep
        exact storeObject_non_ep_non_tcb_preserves_ipcStateQueueMembershipConsistent
          st st' notificationId _ hInv hObjInv
          (fun ep => by intro h; cases h) (fun tcb => by intro h; cases h)
          (fun ep => by rw [hObj]; intro h; cases h) (fun tcb => by rw [hObj]; intro h; cases h)
          hStep

/-- notificationWait preserves ipcStateQueueMembershipConsistent. -/
theorem notificationWait_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    ipcStateQueueMembershipConsistent st' := by
  unfold notificationWait at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | some badge =>
        simp only [hBadge] at hStep
        generalize hStore1 : storeObject notificationId _ st = r1 at hStep
        cases r1 with
        | error e => simp at hStep
        | ok pair1 =>
          simp only [] at hStep
          have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair1 hObjInv hStore1
          have hInv1 := storeObject_non_ep_non_tcb_preserves_ipcStateQueueMembershipConsistent
            st pair1.2 notificationId _ hInv hObjInv
            (fun ep => by intro h; cases h) (fun tcb => by intro h; cases h)
            (fun ep => by rw [hObj]; intro h; cases h) (fun tcb => by rw [hObj]; intro h; cases h)
            hStore1
          generalize hIpc : storeTcbIpcState pair1.2 waiter .ready = rIpc at hStep
          cases rIpc with
          | error e => simp at hStep
          | ok pair2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, rfl⟩ := hStep
            exact storeTcbIpcState_preserves_ipcStateQueueMembershipConsistent _ _ _ _ hInv1 hObjInv1
              (fun epId => by intro h; cases h) (fun epId => by intro h; cases h)
              (fun epId => by intro h; cases h) hIpc
      | none =>
        simp only [hBadge] at hStep
        cases hLookup : lookupTcb st waiter with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          split at hStep
          · simp at hStep
          · generalize hStore1 : storeObject notificationId _ st = r1 at hStep
            cases r1 with
            | error e => simp at hStep
            | ok pair1 =>
              simp only [] at hStep
              have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair1 hObjInv hStore1
              have hInv1 := storeObject_non_ep_non_tcb_preserves_ipcStateQueueMembershipConsistent
                st pair1.2 notificationId _ hInv hObjInv
                (fun ep => by intro h; cases h) (fun tcb => by intro h; cases h)
                (fun ep => by rw [hObj]; intro h; cases h) (fun tcb => by rw [hObj]; intro h; cases h)
                hStore1
              generalize hIpc : storeTcbIpcState_fromTcb pair1.2 waiter _ _ = rIpc at hStep
              cases rIpc with
              | error e => simp at hStep
              | ok pair2 =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, rfl⟩ := hStep
                have hLookup1 : lookupTcb pair1.2 waiter = some tcb := by
                  have hNe : waiter.toObjId ≠ notificationId := by
                    intro h
                    have hTcbObj := lookupTcb_some_objects st waiter tcb hLookup
                    rw [h] at hTcbObj; rw [hObj] at hTcbObj; cases hTcbObj
                  unfold lookupTcb
                  rw [show waiter.isReserved = false from by
                    unfold lookupTcb at hLookup; split at hLookup <;> simp_all]
                  rw [storeObject_objects_ne st pair1.2 notificationId waiter.toObjId _ hNe hObjInv hStore1]
                  unfold lookupTcb at hLookup
                  split at hLookup <;> simp_all
                rw [storeTcbIpcState_fromTcb_eq hLookup1] at hIpc
                exact removeRunnable_preserves_ipcStateQueueMembershipConsistent _ _ <|
                  storeTcbIpcState_preserves_ipcStateQueueMembershipConsistent _ _ _ _ hInv1 hObjInv1
                    (fun epId => by intro h; cases h) (fun epId => by intro h; cases h)
                    (fun epId => by intro h; cases h) hIpc

/-- endpointReply preserves ipcStateQueueMembershipConsistent. -/
theorem endpointReply_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    ipcStateQueueMembershipConsistent st' := by
  unfold endpointReply at hStep
  split at hStep
  · simp at hStep
  · split at hStep
    · simp at hStep
    · cases hLookup : lookupTcb st target with
      | none => simp [hLookup] at hStep
      | some tcb =>
        simp only [hLookup] at hStep
        cases hIpc : tcb.ipcState with
        | blockedOnReply epId replyTarget =>
          simp only [hIpc] at hStep
          split at hStep
          · -- replyTarget = some expected
            split at hStep
            · generalize hMsg : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = rMsg at hStep
              cases rMsg with
              | error e => simp at hStep
              | ok st1 =>
                simp at hStep; obtain ⟨_, rfl⟩ := hStep
                exact ensureRunnable_preserves_ipcStateQueueMembershipConsistent _ _ <|
                  storeTcbIpcStateAndMessage_fromTcb_preserves_ipcStateQueueMembershipConsistent
                    st st1 target tcb .ready (some msg) hInv hObjInv hLookup
                    (fun epId => by intro h; cases h) (fun epId => by intro h; cases h)
                    (fun epId => by intro h; cases h) hMsg
            · simp at hStep
          · -- replyTarget = none
            generalize hMsg : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = rMsg at hStep
            cases rMsg with
            | error e => simp at hStep
            | ok st1 =>
              simp at hStep; obtain ⟨_, rfl⟩ := hStep
              exact ensureRunnable_preserves_ipcStateQueueMembershipConsistent _ _ <|
                storeTcbIpcStateAndMessage_fromTcb_preserves_ipcStateQueueMembershipConsistent
                  st st1 target tcb .ready (some msg) hInv hObjInv hLookup
                  (fun epId => by intro h; cases h) (fun epId => by intro h; cases h)
                  (fun epId => by intro h; cases h) hMsg
        | _ => simp [hIpc] at hStep

end SeLe4n.Kernel
