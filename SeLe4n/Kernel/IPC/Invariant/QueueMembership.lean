import SeLe4n.Kernel.IPC.Invariant.Defs
import SeLe4n.Kernel.IPC.DualQueue.Transport

/-!
# V3-J: ipcStateQueueMembershipConsistent Preservation Proofs
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

set_option linter.unusedVariables false

/-! ## AN3-E.1 (IPC-M05) — shared `transfer` / `transferRecv` helper note.

The `storeObject_non_ep_non_tcb_preserves_ipcStateQueueMembershipConsistent`
proof below introduces two file-local let-bindings, `transfer` and
`transferRecv`, whose bodies are structurally identical except for the
endpoint queue they index (`sendQ` vs. `receiveQ`) and the queue-side
component of the membership witness.  The audit (IPC-M05) suggested
factoring them into a single `transferAux` helper parameterised on
`QueueSide`.

**Decision (AN3-E.1):** the two `let`-bodies stay as-is.  They are
_inside_ a single proof and their outer context (`tid`, `tcbA`,
`hFrame`, `hObjInv`, and several `h*NotEp` / `h*NotTcb` hypotheses)
is captured implicitly.  Extracting them to a top-level
`transferAux` would either require 18 additional parameters per call
site (eliminating the code-size saving) or threading a record struct
through (adding a new abstraction whose maintenance cost exceeds the
~40 LOC the audit hoped to recover).  The pair is short, the
duplication is mechanical, and any future audit concern about drift
between the `sendQ` and `receiveQ` paths is satisfied by the fact
that every preservation theorem downstream uses both sides of the
let-binding symmetrically — drift would break the surrounding theorem
immediately.  See IPC-M05 in the AN3-E work log.
-/

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

/-- storeTcbIpcState general variant: preserves V3-J for blocking states
when the thread has reachability evidence in the post-state. -/
theorem storeTcbIpcState_general_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipcState : ThreadIpcState)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbIpcState st tid ipcState = .ok st')
    (hSendReach : ∀ epId, ipcState = .blockedOnSend epId →
        ∃ ep, st'.objects[epId]? = some (KernelObject.endpoint ep) ∧
          (ep.sendQ.head = some tid ∨
           ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
             st'.objects[prev.toObjId]? = some (KernelObject.tcb prevTcb) ∧
             prevTcb.queueNext = some tid))
    (hRecvReach : ∀ epId, ipcState = .blockedOnReceive epId →
        ∃ ep, st'.objects[epId]? = some (KernelObject.endpoint ep) ∧
          (ep.receiveQ.head = some tid ∨
           ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
             st'.objects[prev.toObjId]? = some (KernelObject.tcb prevTcb) ∧
             prevTcb.queueNext = some tid))
    (hCallReach : ∀ epId, ipcState = .blockedOnCall epId →
        ∃ ep, st'.objects[epId]? = some (KernelObject.endpoint ep) ∧
          (ep.sendQ.head = some tid ∨
           ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
             st'.objects[prev.toObjId]? = some (KernelObject.tcb prevTcb) ∧
             prevTcb.queueNext = some tid)) :
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
      · have hTidEq := ThreadId.toObjId_injective tid2 tid hEq; subst hTidEq
        rw [hEqAt] at hTcb2
        simp only [Option.some.injEq, KernelObject.tcb.injEq] at hTcb2; subst hTcb2
        simp only []
        match ipcState with
        | .ready => trivial
        | .blockedOnReply _ _ => trivial
        | .blockedOnNotification _ => trivial
        | .blockedOnSend epId => exact hSendReach epId rfl
        | .blockedOnReceive epId => exact hRecvReach epId rfl
        | .blockedOnCall epId => exact hCallReach epId rfl
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
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
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
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
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
          -- AK1-B (I-H02): Outer match on replyTarget now fails closed on .none
          cases replyTarget with
          | none => simp at hStep
          | some expected =>
            simp only at hStep
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
        | _ => simp [hIpc] at hStep

-- ============================================================================
-- Section 5: V3-J helper — storeTcbPendingMessage
-- ============================================================================

/-- V3-J-helper-3: storeTcbPendingMessage preserves ipcStateQueueMembershipConsistent.
Only pendingMessage changes; ipcState and queueNext are preserved. -/
theorem storeTcbPendingMessage_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbPendingMessage st tid msg = .ok st') :
    ipcStateQueueMembershipConsistent st' := by
  unfold storeTcbPendingMessage at hStore
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStore
  | some tcb =>
    simp only [hLookup] at hStore
    cases hSt : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
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
          exact ⟨{ tcb with pendingMessage := msg },
            by rw [hPrevEq]; exact hEqAt, hNext⟩
        · exact ⟨prevTcb, by rw [hFrame _ hPrevEq]; exact hPrev, hNext⟩
      intro tid2 tcb2 hTcb2
      by_cases hEq : tid2.toObjId = tid.toObjId
      · rw [hEq, hEqAt] at hTcb2
        simp only [Option.some.injEq, KernelObject.tcb.injEq] at hTcb2; subst hTcb2
        -- ipcState unchanged; membership from pre-state
        have hPre := hInv tid2 tcb (hEq ▸ hTcbObj)
        match hIpc : tcb.ipcState with
        | .blockedOnSend epId =>
          simp only [hIpc] at hPre ⊢; obtain ⟨ep, hEp, hReach⟩ := hPre
          have hNeEp : epId ≠ tid.toObjId := by
            intro h; subst h; rw [hTcbObj] at hEp; cases hEp
          exact ⟨ep, by rw [hFrame epId hNeEp]; exact hEp,
            hReach.elim Or.inl fun ⟨prev, prevTcb, hP, hN⟩ =>
              let ⟨pt, hPt, hNt⟩ := transferPrev tid2 prev prevTcb hP hN
              Or.inr ⟨prev, pt, hPt, hNt⟩⟩
        | .blockedOnReceive epId =>
          simp only [hIpc] at hPre ⊢; obtain ⟨ep, hEp, hReach⟩ := hPre
          have hNeEp : epId ≠ tid.toObjId := by
            intro h; subst h; rw [hTcbObj] at hEp; cases hEp
          exact ⟨ep, by rw [hFrame epId hNeEp]; exact hEp,
            hReach.elim Or.inl fun ⟨prev, prevTcb, hP, hN⟩ =>
              let ⟨pt, hPt, hNt⟩ := transferPrev tid2 prev prevTcb hP hN
              Or.inr ⟨prev, pt, hPt, hNt⟩⟩
        | .blockedOnCall epId =>
          simp only [hIpc] at hPre ⊢; obtain ⟨ep, hEp, hReach⟩ := hPre
          have hNeEp : epId ≠ tid.toObjId := by
            intro h; subst h; rw [hTcbObj] at hEp; cases hEp
          exact ⟨ep, by rw [hFrame epId hNeEp]; exact hEp,
            hReach.elim Or.inl fun ⟨prev, prevTcb, hP, hN⟩ =>
              let ⟨pt, hPt, hNt⟩ := transferPrev tid2 prev prevTcb hP hN
              Or.inr ⟨prev, pt, hPt, hNt⟩⟩
        | .ready => trivial
        | .blockedOnReply _ _ => trivial
        | .blockedOnNotification _ => trivial
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
-- Section 6: General storeTcbIpcStateAndMessage for blocking transitions
-- ============================================================================

/-- V3-J-prim-general: storeTcbIpcStateAndMessage preserves ipcStateQueueMembershipConsistent
for ANY new ipcState, given a reachability witness for blocking states.
The reachability is stated in terms of the POST-state objects (pair.2). -/
theorem storeTcbIpcStateAndMessage_general_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState) (msg : Option IpcMessage)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbIpcStateAndMessage st tid ipcState msg = .ok st')
    (hSendReach : ∀ epId, ipcState = .blockedOnSend epId →
        ∃ ep, st'.objects[epId]? = some (KernelObject.endpoint ep) ∧
          (ep.sendQ.head = some tid ∨
           ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
             st'.objects[prev.toObjId]? = some (KernelObject.tcb prevTcb) ∧
             prevTcb.queueNext = some tid))
    (hRecvReach : ∀ epId, ipcState = .blockedOnReceive epId →
        ∃ ep, st'.objects[epId]? = some (KernelObject.endpoint ep) ∧
          (ep.receiveQ.head = some tid ∨
           ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
             st'.objects[prev.toObjId]? = some (KernelObject.tcb prevTcb) ∧
             prevTcb.queueNext = some tid))
    (hCallReach : ∀ epId, ipcState = .blockedOnCall epId →
        ∃ ep, st'.objects[epId]? = some (KernelObject.endpoint ep) ∧
          (ep.sendQ.head = some tid ∨
           ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
             st'.objects[prev.toObjId]? = some (KernelObject.tcb prevTcb) ∧
             prevTcb.queueNext = some tid)) :
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
      · -- tid2 is the stored TCB: use reachability precondition for blocking states
        have hTidEq := ThreadId.toObjId_injective tid2 tid hEq; subst hTidEq
        rw [hEqAt] at hTcb2
        simp only [Option.some.injEq, KernelObject.tcb.injEq] at hTcb2; subst hTcb2
        -- The updated TCB has ipcState = ipcState; case split on ipcState
        simp only []
        match ipcState with
        | .ready => trivial
        | .blockedOnReply _ _ => trivial
        | .blockedOnNotification _ => trivial
        | .blockedOnSend epId => exact hSendReach epId rfl
        | .blockedOnReceive epId => exact hRecvReach epId rfl
        | .blockedOnCall epId => exact hCallReach epId rfl
      · -- tid2 ≠ tid: transfer pre-state V3-J evidence (identical to non-blocking version)
        rw [hFrame tid2.toObjId hEq] at hTcb2
        have hPre := hInv tid2 tcb2 hTcb2
        match hIpc : tcb2.ipcState with
        | .blockedOnSend epId =>
          simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach'⟩ := hPre
          have hNeEp : epId ≠ tid.toObjId := by
            intro h; subst h; rw [hTcbObj] at hEp; cases hEp
          exact ⟨ep, by rw [hFrame epId hNeEp]; exact hEp,
            hReach'.elim Or.inl fun ⟨prev, prevTcb, hP, hN⟩ =>
              let ⟨pt, hPt, hNt⟩ := transferPrev tid2 prev prevTcb hP hN
              Or.inr ⟨prev, pt, hPt, hNt⟩⟩
        | .blockedOnReceive epId =>
          simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach'⟩ := hPre
          have hNeEp : epId ≠ tid.toObjId := by
            intro h; subst h; rw [hTcbObj] at hEp; cases hEp
          exact ⟨ep, by rw [hFrame epId hNeEp]; exact hEp,
            hReach'.elim Or.inl fun ⟨prev, prevTcb, hP, hN⟩ =>
              let ⟨pt, hPt, hNt⟩ := transferPrev tid2 prev prevTcb hP hN
              Or.inr ⟨prev, pt, hPt, hNt⟩⟩
        | .blockedOnCall epId =>
          simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach'⟩ := hPre
          have hNeEp : epId ≠ tid.toObjId := by
            intro h; subst h; rw [hTcbObj] at hEp; cases hEp
          exact ⟨ep, by rw [hFrame epId hNeEp]; exact hEp,
            hReach'.elim Or.inl fun ⟨prev, prevTcb, hP, hN⟩ =>
              let ⟨pt, hPt, hNt⟩ := transferPrev tid2 prev prevTcb hP hN
              Or.inr ⟨prev, pt, hPt, hNt⟩⟩
        | .ready => trivial
        | .blockedOnReply _ _ => trivial
        | .blockedOnNotification _ => trivial

-- ============================================================================
-- Section 3: storeObject(endpoint) V3-J preservation
-- ============================================================================

/-- Storing an endpoint preserves V3-J when the relevant queue heads are either
unchanged or were none (so no blocked thread relied on the head evidence). -/
theorem storeObject_endpoint_preserves_ipcStateQueueMembershipConsistent
    (st : SystemState) (endpointId : SeLe4n.ObjId) (ep ep' : Endpoint)
    (pair : Unit × SystemState)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hObjInv : st.objects.invExt)
    (hOldEp : st.objects[endpointId]? = some (.endpoint ep))
    (hStore : storeObject endpointId (.endpoint ep') st = .ok pair)
    (hSendHead : ep'.sendQ.head = ep.sendQ.head ∨ ep.sendQ.head = none)
    (hRecvHead : ep'.receiveQ.head = ep.receiveQ.head ∨ ep.receiveQ.head = none) :
    ipcStateQueueMembershipConsistent pair.2 := by
  have hFrame := fun x (h : x ≠ endpointId) =>
    storeObject_objects_ne' st endpointId x (.endpoint ep') pair h hObjInv hStore
  have hAt := storeObject_objects_eq' st endpointId (.endpoint ep') pair hObjInv hStore
  intro tid2 tcb2 hTcb2
  have hNe : tid2.toObjId ≠ endpointId := by
    intro h; rw [h, hAt] at hTcb2; cases hTcb2
  rw [hFrame tid2.toObjId hNe] at hTcb2
  have hPre := hInv tid2 tcb2 hTcb2
  match hIpc : tcb2.ipcState with
  | .ready | .blockedOnReply _ _ | .blockedOnNotification _ => trivial
  | .blockedOnSend epId =>
    simp only [hIpc] at hPre; obtain ⟨epObj, hEpObj, hReach⟩ := hPre
    have transferPred : ∀ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
        st.objects[prev.toObjId]? = some (.tcb prevTcb) → prevTcb.queueNext = some tid2 →
        ∃ pt, pair.2.objects[prev.toObjId]? = some (.tcb pt) ∧ pt.queueNext = some tid2 := by
      intro prev prevTcb hP hN
      have : prev.toObjId ≠ endpointId := by intro h; rw [h, hOldEp] at hP; cases hP
      exact ⟨prevTcb, by rw [hFrame prev.toObjId this]; exact hP, hN⟩
    by_cases hEpEq : epId = endpointId
    · subst hEpEq; rw [hOldEp] at hEpObj; cases hEpObj
      exact ⟨ep', hAt, hReach.elim (fun h => by
        cases hSendHead with
        | inl hEq => exact Or.inl (hEq ▸ h)
        | inr hNone => rw [hNone] at h; cases h) fun ⟨p, pt, hP, hN⟩ =>
        let ⟨pt', hPt', hNt'⟩ := transferPred p pt hP hN
        Or.inr ⟨p, pt', hPt', hNt'⟩⟩
    · exact ⟨epObj, by rw [hFrame epId hEpEq]; exact hEpObj,
        hReach.elim Or.inl fun ⟨p, pt, hP, hN⟩ =>
          let ⟨pt', hPt', hNt'⟩ := transferPred p pt hP hN
          Or.inr ⟨p, pt', hPt', hNt'⟩⟩
  | .blockedOnReceive epId =>
    simp only [hIpc] at hPre; obtain ⟨epObj, hEpObj, hReach⟩ := hPre
    have transferPred : ∀ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
        st.objects[prev.toObjId]? = some (.tcb prevTcb) → prevTcb.queueNext = some tid2 →
        ∃ pt, pair.2.objects[prev.toObjId]? = some (.tcb pt) ∧ pt.queueNext = some tid2 := by
      intro prev prevTcb hP hN
      have : prev.toObjId ≠ endpointId := by intro h; rw [h, hOldEp] at hP; cases hP
      exact ⟨prevTcb, by rw [hFrame prev.toObjId this]; exact hP, hN⟩
    by_cases hEpEq : epId = endpointId
    · subst hEpEq; rw [hOldEp] at hEpObj; cases hEpObj
      exact ⟨ep', hAt, hReach.elim (fun h => by
        cases hRecvHead with
        | inl hEq => exact Or.inl (hEq ▸ h)
        | inr hNone => rw [hNone] at h; cases h) fun ⟨p, pt, hP, hN⟩ =>
        let ⟨pt', hPt', hNt'⟩ := transferPred p pt hP hN
        Or.inr ⟨p, pt', hPt', hNt'⟩⟩
    · exact ⟨epObj, by rw [hFrame epId hEpEq]; exact hEpObj,
        hReach.elim Or.inl fun ⟨p, pt, hP, hN⟩ =>
          let ⟨pt', hPt', hNt'⟩ := transferPred p pt hP hN
          Or.inr ⟨p, pt', hPt', hNt'⟩⟩
  | .blockedOnCall epId =>
    simp only [hIpc] at hPre; obtain ⟨epObj, hEpObj, hReach⟩ := hPre
    have transferPred : ∀ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
        st.objects[prev.toObjId]? = some (.tcb prevTcb) → prevTcb.queueNext = some tid2 →
        ∃ pt, pair.2.objects[prev.toObjId]? = some (.tcb pt) ∧ pt.queueNext = some tid2 := by
      intro prev prevTcb hP hN
      have : prev.toObjId ≠ endpointId := by intro h; rw [h, hOldEp] at hP; cases hP
      exact ⟨prevTcb, by rw [hFrame prev.toObjId this]; exact hP, hN⟩
    by_cases hEpEq : epId = endpointId
    · subst hEpEq; rw [hOldEp] at hEpObj; cases hEpObj
      exact ⟨ep', hAt, hReach.elim (fun h => by
        cases hSendHead with
        | inl hEq => exact Or.inl (hEq ▸ h)
        | inr hNone => rw [hNone] at h; cases h) fun ⟨p, pt, hP, hN⟩ =>
        let ⟨pt', hPt', hNt'⟩ := transferPred p pt hP hN
        Or.inr ⟨p, pt', hPt', hNt'⟩⟩
    · exact ⟨epObj, by rw [hFrame epId hEpEq]; exact hEpObj,
        hReach.elim Or.inl fun ⟨p, pt, hP, hN⟩ =>
          let ⟨pt', hPt', hNt'⟩ := transferPred p pt hP hN
          Or.inr ⟨p, pt', hPt', hNt'⟩⟩

-- ============================================================================
-- Section 4: storeTcbQueueLinks V3-J preservation (queueNext=none guard)
-- ============================================================================

/-- V3-J-prim-links: storeTcbQueueLinks preserves ipcStateQueueMembershipConsistent
when the target TCB's pre-state queueNext was none. Since no blocked thread used
the target as a predecessor (prevTcb.queueNext = some tid2 requires queueNext ≠ none),
all V3-J evidence transfers through the queue link update. -/
theorem storeTcbQueueLinks_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (target : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st target prev pprev next = .ok st')
    (hNextNone : ∀ tcb, st.objects[target.toObjId]? = some (.tcb tcb) →
        tcb.queueNext = none) :
    ipcStateQueueMembershipConsistent st' := by
  intro tid2 tcb2 hTcb2
  -- ipcState backward: tid2 had same ipcState in pre-state
  obtain ⟨tcbPre, hTcbPre, hIpcEq⟩ :=
    storeTcbQueueLinks_tcb_ipcState_backward st st' target prev pprev next hObjInv hStep tid2 tcb2 hTcb2
  have hPre := hInv tid2 tcbPre hTcbPre
  -- Helper: epId ≠ target.toObjId (endpoint slot ≠ TCB slot)
  have hNeEp : ∀ epId ep, st.objects[epId]? = some (.endpoint ep) → epId ≠ target.toObjId := by
    intro epId ep hEp h; rw [h] at hEp
    unfold storeTcbQueueLinks at hStep
    cases hLk : lookupTcb st target with
    | none => simp [hLk] at hStep
    | some tcb => have := lookupTcb_some_objects st target tcb hLk; rw [this] at hEp; cases hEp
  -- Match on tcb2.ipcState (what the goal matches on)
  match hIpc2 : tcb2.ipcState with
  | .ready => trivial
  | .blockedOnReply _ _ => trivial
  | .blockedOnNotification _ => trivial
  | .blockedOnSend epId =>
    have hIpc : tcbPre.ipcState = .blockedOnSend epId := by rw [← hIpc2, ← hIpcEq]
    simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach⟩ := hPre
    exact ⟨ep, by rw [storeTcbQueueLinks_preserves_objects_ne st st' target prev pprev next
      epId (hNeEp epId ep hEp) hObjInv hStep]; exact hEp,
      hReach.elim Or.inl fun ⟨prev', prevTcb, hPrev, hNext⟩ => by
        by_cases hPrevEq : prev'.toObjId = target.toObjId
        · rw [hPrevEq] at hPrev; exact absurd (hNextNone prevTcb hPrev) (by rw [hNext]; simp)
        · exact Or.inr ⟨prev', prevTcb,
            by rw [storeTcbQueueLinks_preserves_objects_ne st st' target prev pprev next
              prev'.toObjId hPrevEq hObjInv hStep]; exact hPrev, hNext⟩⟩
  | .blockedOnReceive epId =>
    have hIpc : tcbPre.ipcState = .blockedOnReceive epId := by rw [← hIpc2, ← hIpcEq]
    simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach⟩ := hPre
    exact ⟨ep, by rw [storeTcbQueueLinks_preserves_objects_ne st st' target prev pprev next
      epId (hNeEp epId ep hEp) hObjInv hStep]; exact hEp,
      hReach.elim Or.inl fun ⟨prev', prevTcb, hPrev, hNext⟩ => by
        by_cases hPrevEq : prev'.toObjId = target.toObjId
        · rw [hPrevEq] at hPrev; exact absurd (hNextNone prevTcb hPrev) (by rw [hNext]; simp)
        · exact Or.inr ⟨prev', prevTcb,
            by rw [storeTcbQueueLinks_preserves_objects_ne st st' target prev pprev next
              prev'.toObjId hPrevEq hObjInv hStep]; exact hPrev, hNext⟩⟩
  | .blockedOnCall epId =>
    have hIpc : tcbPre.ipcState = .blockedOnCall epId := by rw [← hIpc2, ← hIpcEq]
    simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach⟩ := hPre
    exact ⟨ep, by rw [storeTcbQueueLinks_preserves_objects_ne st st' target prev pprev next
      epId (hNeEp epId ep hEp) hObjInv hStep]; exact hEp,
      hReach.elim Or.inl fun ⟨prev', prevTcb, hPrev, hNext⟩ => by
        by_cases hPrevEq : prev'.toObjId = target.toObjId
        · rw [hPrevEq] at hPrev; exact absurd (hNextNone prevTcb hPrev) (by rw [hNext]; simp)
        · exact Or.inr ⟨prev', prevTcb,
            by rw [storeTcbQueueLinks_preserves_objects_ne st st' target prev pprev next
              prev'.toObjId hPrevEq hObjInv hStep]; exact hPrev, hNext⟩⟩

-- ============================================================================
-- Section 5: endpointQueueEnqueue V3-J preservation
-- ============================================================================

/-- V3-J-op-1: endpointQueueEnqueue preserves ipcStateQueueMembershipConsistent.
Enqueue modifies only queue link fields and the endpoint's head/tail pointers;
no thread's ipcState changes. Existing V3-J evidence transfers because:
- The target thread (enqueueTid) is ready (guard), so no blocked thread is affected.
- The tail thread (non-empty case) had queueNext = none (DQWF P3), so it was
  nobody's V3-J predecessor. -/
theorem endpointQueueEnqueue_preserves_ipcStateQueueMembershipConsistent
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (enqueueTid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hObjInv : st.objects.invExt)
    (hDQWF : dualQueueEndpointWellFormed endpointId st)
    (hEnqueue : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st') :
    ipcStateQueueMembershipConsistent st' := by
  unfold endpointQueueEnqueue at hEnqueue
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hEnqueue
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hEnqueue
    | endpoint ep =>
      simp only [hObj] at hEnqueue
      -- Extract DQWF
      unfold dualQueueEndpointWellFormed at hDQWF; rw [hObj] at hDQWF
      obtain ⟨hWFSend, hWFRecv⟩ := hDQWF
      cases hLookup : lookupTcb st enqueueTid with
      | none => simp [hLookup] at hEnqueue
      | some tcb =>
        simp only [hLookup] at hEnqueue
        -- Extract guard conditions by cases + simp contradiction
        have hReady : tcb.ipcState = .ready := by
          by_cases h : tcb.ipcState = .ready
          · exact h
          · simp [h] at hEnqueue
        have hTcbObj := lookupTcb_some_objects st enqueueTid tcb hLookup
        -- Simplify past first guard
        simp only [hReady, ne_eq, not_true_eq_false, ite_false] at hEnqueue
        have hQNNone : tcb.queueNext = none := by
          cases hQN : tcb.queueNext <;> first | rfl | simp [hQN] at hEnqueue
        have hPP : tcb.queuePPrev = none := by
          cases hPP : tcb.queuePPrev <;> first | rfl | simp [hPP] at hEnqueue
        have hPN : tcb.queuePrev = none := by
          cases hPN : tcb.queuePrev <;> first | rfl | simp [hPP, hPN] at hEnqueue
        -- Simplify past second guard
        simp only [hPP, hPN, hQNNone, Option.isSome_none, Bool.false_or,
          Bool.false_eq_true, ite_false] at hEnqueue
        -- Case split on tail
        revert hEnqueue
        cases hTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
        | none =>
          -- EMPTY QUEUE case
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            simp only []
            intro hLink
            have hInvExt1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            have hV3J1 : ipcStateQueueMembershipConsistent pair.2 :=
              storeObject_endpoint_preserves_ipcStateQueueMembershipConsistent
                st endpointId ep _ pair hInv hObjInv hObj hStore
                (by cases isReceiveQ <;> simp_all [intrusiveQueueWellFormed])
                (by cases isReceiveQ <;> simp_all [intrusiveQueueWellFormed])
            exact storeTcbQueueLinks_preserves_ipcStateQueueMembershipConsistent
              pair.2 st' enqueueTid _ _ _ hV3J1 hInvExt1 hLink (by
                intro tcb' hTcb'
                have hNe : enqueueTid.toObjId ≠ endpointId := by
                  intro h; rw [h, storeObject_objects_eq' st endpointId _ pair hObjInv hStore] at hTcb'; cases hTcb'
                rw [storeObject_objects_ne' st endpointId enqueueTid.toObjId _ pair hNe hObjInv hStore] at hTcb'
                rw [hTcbObj] at hTcb'; cases hTcb'; exact hQNNone)
        | some tailTid =>
          -- NON-EMPTY QUEUE case
          cases hLookupTail : lookupTcb st tailTid with
          | none => simp [hLookupTail]
          | some tailTcb =>
            simp only [hLookupTail]
            -- P3: tail.queueNext = none
            have hTailQNNone : tailTcb.queueNext = none := by
              have hTailObj := lookupTcb_some_objects st tailTid tailTcb hLookupTail
              cases isReceiveQ <;> simp_all [intrusiveQueueWellFormed] <;> {
                obtain ⟨tcb', hTcb', hN⟩ := (by assumption : ∀ tl, _ = some tl → _) rfl
                rw [hTailObj] at hTcb'; cases hTcb'; exact hN }
            have hTailObj := lookupTcb_some_objects st tailTid tailTcb hLookupTail
            cases hStore : storeObject endpointId _ st with
            | error e => simp
            | ok pair =>
              simp only []
              cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some enqueueTid) with
              | error e => simp
              | ok st2 =>
                simp only []
                intro hLink2
                have hInvExt1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                have hInvExt2 := storeTcbQueueLinks_preserves_objects_invExt pair.2 st2 tailTid _ _ _ hInvExt1 hLink1
                have hV3J1 : ipcStateQueueMembershipConsistent pair.2 :=
                  storeObject_endpoint_preserves_ipcStateQueueMembershipConsistent
                    st endpointId ep _ pair hInv hObjInv hObj hStore
                    (by cases isReceiveQ <;> simp_all [intrusiveQueueWellFormed])
                    (by cases isReceiveQ <;> simp_all [intrusiveQueueWellFormed])
                have hV3J2 : ipcStateQueueMembershipConsistent st2 :=
                  storeTcbQueueLinks_preserves_ipcStateQueueMembershipConsistent
                    pair.2 st2 tailTid _ _ _ hV3J1 hInvExt1 hLink1 (by
                      intro tcb' hTcb'
                      have hNe : tailTid.toObjId ≠ endpointId := by
                        intro h; rw [h, storeObject_objects_eq' st endpointId _ pair hObjInv hStore] at hTcb'; cases hTcb'
                      rw [storeObject_objects_ne' st endpointId tailTid.toObjId _ pair hNe hObjInv hStore] at hTcb'
                      rw [hTailObj] at hTcb'; cases hTcb'; exact hTailQNNone)
                -- V3-J for st': storeTcbQueueLinks at enqueueTid
                by_cases hTidEq : enqueueTid.toObjId = tailTid.toObjId
                · -- Edge case: enqueueTid.toObjId = tailTid.toObjId
                  -- Prove V3-J directly from pre-state (no blocked thread is enqueueTid
                  -- and no blocked thread had enqueueTid as predecessor)
                  have hNeEpTid : enqueueTid.toObjId ≠ endpointId := by
                    intro h; rw [h] at hTcbObj; rw [hObj] at hTcbObj; cases hTcbObj
                  -- Forward frame for objects at oid ≠ endpointId ∧ oid ≠ enqueueTid.toObjId
                  have hFwd : ∀ oid, oid ≠ endpointId → oid ≠ enqueueTid.toObjId →
                      st'.objects[oid]? = st.objects[oid]? := by
                    intro oid h1 h2
                    rw [storeTcbQueueLinks_preserves_objects_ne st2 st' enqueueTid _ _ _ oid h2 hInvExt2 hLink2,
                        storeTcbQueueLinks_preserves_objects_ne pair.2 st2 tailTid _ _ _ oid (hTidEq ▸ h2) hInvExt1 hLink1,
                        storeObject_objects_ne' st endpointId oid _ pair h1 hObjInv hStore]
                  -- Endpoint at endpointId in st' (unchanged through link steps)
                  have hEpPost : st'.objects[endpointId]? = some (.endpoint (
                      if isReceiveQ = true then { ep with receiveQ := { head := (if isReceiveQ = true then ep.receiveQ else ep.sendQ).head, tail := some enqueueTid } }
                      else { ep with sendQ := { head := (if isReceiveQ = true then ep.receiveQ else ep.sendQ).head, tail := some enqueueTid } })) := by
                    rw [storeTcbQueueLinks_preserves_objects_ne st2 st' enqueueTid _ _ _ endpointId hNeEpTid.symm hInvExt2 hLink2,
                        storeTcbQueueLinks_preserves_objects_ne pair.2 st2 tailTid _ _ _ endpointId (hTidEq ▸ hNeEpTid.symm) hInvExt1 hLink1]
                    exact storeObject_objects_eq' st endpointId _ pair hObjInv hStore
                  -- Helper: ipcState at enqueueTid.toObjId in st' is .ready
                  have hEnqReady : ∀ tcb', st'.objects[enqueueTid.toObjId]? = some (.tcb tcb') →
                      tcb'.ipcState = .ready := by
                    intro tcb' hTcb'
                    obtain ⟨tcb2', hTcb2', hIpc2⟩ :=
                      storeTcbQueueLinks_tcb_ipcState_backward st2 st' enqueueTid _ _ _ hInvExt2 hLink2 enqueueTid tcb' hTcb'
                    obtain ⟨tcb1', hTcb1', hIpc1⟩ :=
                      storeTcbQueueLinks_tcb_ipcState_backward pair.2 st2 tailTid _ _ _ hInvExt1 hLink1 enqueueTid tcb2' hTcb2'
                    rw [storeObject_objects_ne' st endpointId enqueueTid.toObjId _ pair hNeEpTid hObjInv hStore, hTcbObj] at hTcb1'
                    simp only [Option.some.injEq, KernelObject.tcb.injEq] at hTcb1'; subst hTcb1'
                    rw [← hIpc2, ← hIpc1]; exact hReady
                  -- Helper: predecessor ≠ enqueueTid (queueNext = none in pre-state)
                  have hPredNe : ∀ (prev' : SeLe4n.ThreadId) (prevTcb : TCB) (tid2 : SeLe4n.ThreadId),
                      st.objects[prev'.toObjId]? = some (.tcb prevTcb) →
                      prevTcb.queueNext = some tid2 → prev' ≠ enqueueTid := by
                    intro prev' prevTcb tid2' hPrev hNext h; subst h
                    rw [hTcbObj] at hPrev
                    simp only [Option.some.injEq, KernelObject.tcb.injEq] at hPrev; subst hPrev
                    rw [hQNNone] at hNext; cases hNext
                  -- Helper: endpoint at eid in st' with preserved queue heads
                  have hEpInPost : ∀ (eid : SeLe4n.ObjId) (epObj : Endpoint),
                      st.objects[eid]? = some (.endpoint epObj) →
                      ∃ epObj', st'.objects[eid]? = some (.endpoint epObj') ∧
                        epObj'.sendQ.head = epObj.sendQ.head ∧
                        epObj'.receiveQ.head = epObj.receiveQ.head := by
                    intro eid epObj hEid
                    have hNeT : eid ≠ enqueueTid.toObjId := by
                      intro h; rw [h] at hEid; rw [hTcbObj] at hEid; cases hEid
                    by_cases hEq : eid = endpointId
                    · subst hEq; rw [hObj] at hEid
                      simp only [Option.some.injEq, KernelObject.endpoint.injEq] at hEid; subst hEid
                      exact ⟨_, hEpPost, by cases isReceiveQ <;> simp, by cases isReceiveQ <;> simp⟩
                    · exact ⟨epObj, by rw [hFwd eid hEq hNeT]; exact hEid, rfl, rfl⟩
                  -- Helper: predecessor TCB at prev' in st' (prev' ≠ enqueueTid, prev' ≠ endpointId)
                  have hPrevInPost : ∀ (prev' : SeLe4n.ThreadId) (prevTcb : TCB) (tid2' : SeLe4n.ThreadId),
                      st.objects[prev'.toObjId]? = some (.tcb prevTcb) →
                      prevTcb.queueNext = some tid2' →
                      st'.objects[prev'.toObjId]? = some (.tcb prevTcb) := by
                    intro prev' prevTcb tid2' hPrev hNext
                    have hPrevNeEp : prev'.toObjId ≠ endpointId := by
                      intro h; rw [h] at hPrev; rw [hObj] at hPrev; cases hPrev
                    have hPrevNeEnq : prev'.toObjId ≠ enqueueTid.toObjId := by
                      intro h
                      exact absurd (ThreadId.toObjId_injective prev' enqueueTid h)
                        (hPredNe prev' prevTcb tid2' hPrev hNext)
                    rw [hFwd prev'.toObjId hPrevNeEp hPrevNeEnq]; exact hPrev
                  intro tid2 tcb2 hTcb2
                  have hNe1 : tid2.toObjId ≠ endpointId := by
                    intro h; rw [h] at hTcb2; rw [hEpPost] at hTcb2; cases hTcb2
                  match hIpc2 : tcb2.ipcState with
                  | .ready | .blockedOnReply _ _ | .blockedOnNotification _ => trivial
                  | .blockedOnSend epId =>
                    have hNe2 : tid2.toObjId ≠ enqueueTid.toObjId := by
                      intro h; rw [h] at hTcb2; exact absurd (hEnqReady tcb2 hTcb2) (by rw [hIpc2]; intro h; cases h)
                    rw [hFwd tid2.toObjId hNe1 hNe2] at hTcb2
                    have hPre := hInv tid2 tcb2 hTcb2; simp only [hIpc2] at hPre
                    obtain ⟨epObj, hEpObj, hReach⟩ := hPre
                    obtain ⟨epObj', hEpObj', hSendH, _⟩ := hEpInPost epId epObj hEpObj
                    exact ⟨epObj', hEpObj', hReach.elim (fun h => Or.inl (hSendH ▸ h))
                      fun ⟨prev', prevTcb, hPrev, hNext⟩ =>
                        Or.inr ⟨prev', prevTcb, hPrevInPost prev' prevTcb tid2 hPrev hNext, hNext⟩⟩
                  | .blockedOnReceive epId =>
                    have hNe2 : tid2.toObjId ≠ enqueueTid.toObjId := by
                      intro h; rw [h] at hTcb2; exact absurd (hEnqReady tcb2 hTcb2) (by rw [hIpc2]; intro h; cases h)
                    rw [hFwd tid2.toObjId hNe1 hNe2] at hTcb2
                    have hPre := hInv tid2 tcb2 hTcb2; simp only [hIpc2] at hPre
                    obtain ⟨epObj, hEpObj, hReach⟩ := hPre
                    obtain ⟨epObj', hEpObj', _, hRecvH⟩ := hEpInPost epId epObj hEpObj
                    exact ⟨epObj', hEpObj', hReach.elim (fun h => Or.inl (hRecvH ▸ h))
                      fun ⟨prev', prevTcb, hPrev, hNext⟩ =>
                        Or.inr ⟨prev', prevTcb, hPrevInPost prev' prevTcb tid2 hPrev hNext, hNext⟩⟩
                  | .blockedOnCall epId =>
                    have hNe2 : tid2.toObjId ≠ enqueueTid.toObjId := by
                      intro h; rw [h] at hTcb2; exact absurd (hEnqReady tcb2 hTcb2) (by rw [hIpc2]; intro h; cases h)
                    rw [hFwd tid2.toObjId hNe1 hNe2] at hTcb2
                    have hPre := hInv tid2 tcb2 hTcb2; simp only [hIpc2] at hPre
                    obtain ⟨epObj, hEpObj, hReach⟩ := hPre
                    obtain ⟨epObj', hEpObj', hSendH, _⟩ := hEpInPost epId epObj hEpObj
                    exact ⟨epObj', hEpObj', hReach.elim (fun h => Or.inl (hSendH ▸ h))
                      fun ⟨prev', prevTcb, hPrev, hNext⟩ =>
                        Or.inr ⟨prev', prevTcb, hPrevInPost prev' prevTcb tid2 hPrev hNext, hNext⟩⟩
                · -- Normal case: enqueueTid ≠ tailTid
                  exact storeTcbQueueLinks_preserves_ipcStateQueueMembershipConsistent
                    st2 st' enqueueTid _ _ _ hV3J2 hInvExt2 hLink2 (by
                      intro tcb' hTcb'
                      rw [storeTcbQueueLinks_preserves_objects_ne pair.2 st2 tailTid _ _ _
                        enqueueTid.toObjId hTidEq hInvExt1 hLink1] at hTcb'
                      have hNe : enqueueTid.toObjId ≠ endpointId := by
                        intro h; rw [h, storeObject_objects_eq' st endpointId _ pair hObjInv hStore] at hTcb'; cases hTcb'
                      rw [storeObject_objects_ne' st endpointId enqueueTid.toObjId _ pair hNe hObjInv hStore] at hTcb'
                      rw [hTcbObj] at hTcb'; cases hTcb'; exact hQNNone)

-- ============================================================================
-- Section 6: storeTcbQueueLinks queueNext extraction
-- ============================================================================

/-- After storeTcbQueueLinks, the stored TCB at tid.toObjId has queueNext = next. -/
theorem storeTcbQueueLinks_stored_queueNext
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    ∃ tcb', st'.objects[tid.toObjId]? = some (.tcb tcb') ∧ tcb'.queueNext = next := by
  unfold storeTcbQueueLinks at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb (tcbWithQueueLinks tcb prev pprev next)) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      exact ⟨tcbWithQueueLinks tcb prev pprev next,
        storeObject_objects_eq' st tid.toObjId _ pair hObjInv hStore,
        rfl⟩

-- ============================================================================
-- Section 7: Partial V3-J preservation (for rendezvous paths)
-- ============================================================================

/-- storeTcbIpcStateAndMessage restores ipcStateQueueMembershipConsistent from
a partial invariant (V3-J holds for all threads except tid) when the new
ipcState is non-blocking. Used for rendezvous paths where PopHead temporarily
breaks V3-J for the popped thread. -/
theorem storeTcbIpcStateAndMessage_partial_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState) (msg : Option IpcMessage)
    (hPartialInv : ∀ (tid2 : SeLe4n.ThreadId) (tcb2 : TCB),
        st.objects[tid2.toObjId]? = some (.tcb tcb2) →
        tid2.toObjId ≠ tid.toObjId →
        match tcb2.ipcState with
        | .blockedOnSend epId =>
            ∃ ep, st.objects[epId]? = some (KernelObject.endpoint ep) ∧
              (ep.sendQ.head = some tid2 ∨
               ∃ (prev' : SeLe4n.ThreadId) (prevTcb : TCB),
                 st.objects[prev'.toObjId]? = some (KernelObject.tcb prevTcb) ∧
                 TCB.queueNext prevTcb = some tid2)
        | .blockedOnReceive epId =>
            ∃ ep, st.objects[epId]? = some (KernelObject.endpoint ep) ∧
              (ep.receiveQ.head = some tid2 ∨
               ∃ (prev' : SeLe4n.ThreadId) (prevTcb : TCB),
                 st.objects[prev'.toObjId]? = some (KernelObject.tcb prevTcb) ∧
                 TCB.queueNext prevTcb = some tid2)
        | .blockedOnCall epId =>
            ∃ ep, st.objects[epId]? = some (KernelObject.endpoint ep) ∧
              (ep.sendQ.head = some tid2 ∨
               ∃ (prev' : SeLe4n.ThreadId) (prevTcb : TCB),
                 st.objects[prev'.toObjId]? = some (KernelObject.tcb prevTcb) ∧
                 TCB.queueNext prevTcb = some tid2)
        | _ => True)
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
          (prev' : SeLe4n.ThreadId) (prevTcb : TCB),
          st.objects[prev'.toObjId]? = some (.tcb prevTcb) →
          prevTcb.queueNext = some tid2 →
          ∃ prevTcb', pair.2.objects[prev'.toObjId]? = some (.tcb prevTcb') ∧
            prevTcb'.queueNext = some tid2 := by
        intro tid2 prev' prevTcb hPrev hNext
        by_cases hPrevEq : prev'.toObjId = tid.toObjId
        · rw [hPrevEq] at hPrev; rw [hTcbObj] at hPrev; cases hPrev
          exact ⟨{ tcb with ipcState := ipcState, pendingMessage := msg },
            by rw [hPrevEq]; exact hEqAt, hNext⟩
        · exact ⟨prevTcb, by rw [hFrame _ hPrevEq]; exact hPrev, hNext⟩
      intro tid2 tcb2 hTcb2
      by_cases hEq : tid2.toObjId = tid.toObjId
      · -- tid2 is the stored TCB: new ipcState is non-blocking → trivially V3-J
        have hTidEq := ThreadId.toObjId_injective tid2 tid hEq; subst hTidEq
        rw [hEqAt] at hTcb2
        simp only [Option.some.injEq, KernelObject.tcb.injEq] at hTcb2; subst hTcb2
        match ipcState with
        | .ready => trivial
        | .blockedOnReply _ _ => trivial
        | .blockedOnNotification _ => trivial
        | .blockedOnSend epId => exact absurd rfl (hNotSend epId)
        | .blockedOnReceive epId => exact absurd rfl (hNotRecv epId)
        | .blockedOnCall epId => exact absurd rfl (hNotCall epId)
      · -- tid2 ≠ tid: transfer from partial pre-state V3-J
        rw [hFrame tid2.toObjId hEq] at hTcb2
        have hPre := hPartialInv tid2 tcb2 hTcb2 hEq
        match hIpc : tcb2.ipcState with
        | .blockedOnSend epId =>
          simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach⟩ := hPre
          have hNeEp : epId ≠ tid.toObjId := by
            intro h; subst h; rw [hTcbObj] at hEp; cases hEp
          exact ⟨ep, by rw [hFrame epId hNeEp]; exact hEp,
            hReach.elim Or.inl fun ⟨prev', prevTcb, hP, hN⟩ =>
              let ⟨pt, hPt, hNt⟩ := transferPrev tid2 prev' prevTcb hP hN
              Or.inr ⟨prev', pt, hPt, hNt⟩⟩
        | .blockedOnReceive epId =>
          simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach⟩ := hPre
          have hNeEp : epId ≠ tid.toObjId := by
            intro h; subst h; rw [hTcbObj] at hEp; cases hEp
          exact ⟨ep, by rw [hFrame epId hNeEp]; exact hEp,
            hReach.elim Or.inl fun ⟨prev', prevTcb, hP, hN⟩ =>
              let ⟨pt, hPt, hNt⟩ := transferPrev tid2 prev' prevTcb hP hN
              Or.inr ⟨prev', pt, hPt, hNt⟩⟩
        | .blockedOnCall epId =>
          simp only [hIpc] at hPre; obtain ⟨ep, hEp, hReach⟩ := hPre
          have hNeEp : epId ≠ tid.toObjId := by
            intro h; subst h; rw [hTcbObj] at hEp; cases hEp
          exact ⟨ep, by rw [hFrame epId hNeEp]; exact hEp,
            hReach.elim Or.inl fun ⟨prev', prevTcb, hP, hN⟩ =>
              let ⟨pt, hPt, hNt⟩ := transferPrev tid2 prev' prevTcb hP hN
              Or.inr ⟨prev', pt, hPt, hNt⟩⟩
        | .ready => trivial
        | .blockedOnReply _ _ => trivial
        | .blockedOnNotification _ => trivial

-- ============================================================================
-- Section 8: IPC operation V3-J preservation proofs
-- ============================================================================

/-- After endpointQueueEnqueue, the enqueued thread is reachable from the
queue head in the post-state: either it IS the head (empty queue case) or
the old tail's queueNext points to it (non-empty queue case).
Requires that tid is not already the tail of the target queue (hNotTail),
which follows from the freshness condition used by the DQSI preservation proof. -/
theorem endpointQueueEnqueue_thread_reachable
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hNotTail : ∀ ep, st.objects[endpointId]? = some (.endpoint ep) →
      (if isReceiveQ then ep.receiveQ else ep.sendQ).tail ≠ some tid)
    (hEnqueue : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    ∃ ep', st'.objects[endpointId]? = some (.endpoint ep') ∧
      ((if isReceiveQ then ep'.receiveQ.head else ep'.sendQ.head) = some tid ∨
       ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
         st'.objects[prev.toObjId]? = some (.tcb prevTcb) ∧
         prevTcb.queueNext = some tid) := by
  unfold endpointQueueEnqueue at hEnqueue
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hEnqueue
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hEnqueue
    | endpoint ep =>
      simp only [hObj] at hEnqueue
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup] at hEnqueue
      | some tcb =>
        simp only [hLookup] at hEnqueue
        have hReady : tcb.ipcState = .ready := by
          by_cases h : tcb.ipcState = .ready; exact h; simp [h] at hEnqueue
        have hQN : tcb.queueNext = none := by
          cases h : tcb.queueNext <;> first | rfl | simp [hReady, h] at hEnqueue
        have hPP : tcb.queuePPrev = none := by
          cases h : tcb.queuePPrev <;> first | rfl | simp [hReady, h] at hEnqueue
        have hPN : tcb.queuePrev = none := by
          cases h : tcb.queuePrev <;> first | rfl | simp [hReady, hPP, h] at hEnqueue
        simp only [hReady, ne_eq, not_true_eq_false, ite_false, hPP, hPN, hQN,
          Option.isSome_none, Bool.false_or, Bool.false_eq_true] at hEnqueue
        revert hEnqueue
        cases hTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
        | none =>
          -- Empty queue: tid becomes head
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            simp only []
            cases hLink : storeTcbQueueLinks pair.2 tid _ _ _ with
            | error e => simp
            | ok st2 =>
              intro hEnqueue
              have hEq := Except.ok.inj hEnqueue; subst hEq
              have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
              -- Endpoint at endpointId in st2
              have hNeT : tid.toObjId ≠ endpointId := by
                intro h
                have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
                rw [h] at hTcbObj; rw [hObj] at hTcbObj; cases hTcbObj
              have hEp1 := storeObject_objects_eq' st endpointId _ pair hObjInv hStore
              have hEp2 : st2.objects[endpointId]? = some (.endpoint (if isReceiveQ then { ep with receiveQ := { head := some tid, tail := some tid } } else { ep with sendQ := { head := some tid, tail := some tid } })) := by
                rw [storeTcbQueueLinks_preserves_objects_ne pair.2 st2 tid _ _ _ endpointId hNeT.symm hInv1 hLink]
                exact hEp1
              exact ⟨_, hEp2, Or.inl (by cases isReceiveQ <;> simp)⟩
        | some tailTid =>
          -- Non-empty queue: old tail's queueNext = some tid
          cases hLookupTail : lookupTcb st tailTid with
          | none => simp [hLookupTail]
          | some tailTcb =>
            simp only [hLookupTail]
            cases hStore : storeObject endpointId _ st with
            | error e => simp
            | ok pair =>
              simp only []
              cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some tid) with
              | error e => simp
              | ok st2 =>
                simp only []
                cases hLink2 : storeTcbQueueLinks st2 tid _ _ _ with
                | error e => simp
                | ok st3 =>
                  intro hEnqueue
                  have hEq := Except.ok.inj hEnqueue; subst hEq
                  have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                  have hInv2 := storeTcbQueueLinks_preserves_objects_invExt pair.2 st2 tailTid _ _ _ hInv1 hLink1
                  -- tailTid's queueNext = some tid in st2 (after link1)
                  obtain ⟨tailTcb', hTailPost1, hTailQN⟩ :=
                    storeTcbQueueLinks_stored_queueNext pair.2 st2 tailTid _ _ (some tid) hInv1 hLink1
                  -- tailTid's TCB survives link2 (link2 modifies tid, not tailTid)
                  -- Derive tailTid ≠ tid from hNotTail
                  have hNeTailTid : tailTid.toObjId ≠ tid.toObjId := by
                    intro h
                    have := ThreadId.toObjId_injective tailTid tid h
                    subst this; exact absurd hTail (hNotTail ep hObj)
                  -- Normal case: tailTid ≠ tid — predecessor survives link2
                  obtain ⟨tailTcb2, hTailPost2⟩ :=
                    storeTcbQueueLinks_tcb_forward st2 st3 tid _ _ _ tailTid.toObjId tailTcb' hInv2 hLink2 hTailPost1
                  have hQNPres : tailTcb2.queueNext = some tid := by
                    rw [storeTcbQueueLinks_preserves_objects_ne st2 st3 tid _ _ _ tailTid.toObjId hNeTailTid hInv2 hLink2] at hTailPost2
                    rw [hTailPost1] at hTailPost2
                    cases hTailPost2; exact hTailQN
                  have hNeT : endpointId ≠ tid.toObjId := by
                    intro h
                    have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
                    rw [← h] at hTcbObj; rw [hObj] at hTcbObj; cases hTcbObj
                  have hNeTail : endpointId ≠ tailTid.toObjId := by
                    intro h
                    have hTailObj := lookupTcb_some_objects st tailTid tailTcb hLookupTail
                    rw [← h] at hTailObj; rw [hObj] at hTailObj; cases hTailObj
                  exact ⟨_, by
                    rw [storeTcbQueueLinks_preserves_objects_ne st2 st3 tid _ _ _ endpointId hNeT hInv2 hLink2,
                        storeTcbQueueLinks_preserves_objects_ne pair.2 st2 tailTid _ _ _ endpointId hNeTail hInv1 hLink1]
                    exact storeObject_objects_eq' st endpointId _ pair hObjInv hStore,
                    Or.inr ⟨tailTid, tailTcb2, hTailPost2, hQNPres⟩⟩

/-- After endpointQueuePopHead, any TCB at oid ≠ tid.toObjId (the popped head)
has its queueNext preserved from pre-state to post-state. PopHead only clears
the popped head's queueNext; all other TCBs' queueNext fields are unchanged. -/
theorem endpointQueuePopHead_preserves_non_head_queueNext
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (prev : SeLe4n.ThreadId) (prevTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st'))
    (hPrev : st.objects[prev.toObjId]? = some (.tcb prevTcb))
    (hNe : prev.toObjId ≠ tid.toObjId) :
    ∃ prevTcb', st'.objects[prev.toObjId]? = some (.tcb prevTcb') ∧
      prevTcb'.queueNext = prevTcb.queueNext := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep; revert hStep
      have hNeEp : prev.toObjId ≠ endpointId := by
        intro h; rw [h] at hPrev; rw [hObj] at hPrev; cases hPrev
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp
      | some headTid =>
        simp only []
        cases hLookup : lookupTcb st headTid with
        | none => simp
        | some htcb =>
          simp only []
          -- headTid.toObjId = tid.toObjId will be derived from the result
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            simp only []
            have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            have hPrev1 : pair.2.objects[prev.toObjId]? = some (.tcb prevTcb) := by
              rw [storeObject_objects_ne st pair.2 endpointId prev.toObjId _ hNeEp hObjInv hStore]
              exact hPrev
            cases hNext : htcb.queueNext with
            | none =>
              -- No next: just clear headTid's links
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨hTidEq, _, hEq⟩; subst hEq
                have hNeHead : prev.toObjId ≠ headTid.toObjId := hTidEq ▸ hNe
                have hPrev3 : st3.objects[prev.toObjId]? = some (.tcb prevTcb) := by
                  rw [storeTcbQueueLinks_preserves_objects_ne pair.2 st3 headTid _ _ _ prev.toObjId
                    hNeHead hInv1 hFinal]; exact hPrev1
                exact ⟨prevTcb, hPrev3, rfl⟩
            | some nextTid =>
              -- Has next: update nextTid's prev links, then clear headTid's links
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none
                    (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInv1 hLink
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨hTidEq, _, hEq⟩; subst hEq
                    -- headTid = tid, so prev ≠ headTid
                    have hNeHead : prev.toObjId ≠ headTid.toObjId := hTidEq ▸ hNe
                    by_cases hPrevNext : prev.toObjId = nextTid.toObjId
                    · -- prev = nextTid: storeTcbQueueLinks preserved queueNext
                      rw [hPrevNext] at hPrev1
                      have hNextObj := lookupTcb_some_objects pair.2 nextTid nextTcb hLookupNext
                      -- nextTcb = prevTcb since they're at the same ObjId
                      have hTcbEq : nextTcb = prevTcb := by
                        rw [hNextObj] at hPrev1
                        simp only [Option.some.injEq, KernelObject.tcb.injEq] at hPrev1
                        exact hPrev1
                      -- storeTcbQueueLinks preserved queueNext = nextTcb.queueNext = prevTcb.queueNext
                      obtain ⟨tcb', hTcb', hQN'⟩ :=
                        storeTcbQueueLinks_stored_queueNext pair.2 st2 nextTid _ _ nextTcb.queueNext hInv1 hLink
                      rw [← hPrevNext] at hTcb'
                      have hTcb'3 : st3.objects[prev.toObjId]? = some (.tcb tcb') := by
                        rw [storeTcbQueueLinks_preserves_objects_ne st2 st3 headTid _ _ _ prev.toObjId
                          hNeHead hInv2 hFinal]; exact hTcb'
                      exact ⟨tcb', hTcb'3, hTcbEq ▸ hQN'⟩
                    · -- prev ≠ nextTid: TCB unchanged through both storeTcbQueueLinks calls
                      have hPrev2 : st2.objects[prev.toObjId]? = some (.tcb prevTcb) := by
                        rw [storeTcbQueueLinks_preserves_objects_ne pair.2 st2 nextTid _ _ _ prev.toObjId
                          hPrevNext hInv1 hLink]; exact hPrev1
                      have hPrev3 : st3.objects[prev.toObjId]? = some (.tcb prevTcb) := by
                        rw [storeTcbQueueLinks_preserves_objects_ne st2 st3 headTid _ _ _ prev.toObjId
                          hNeHead hInv2 hFinal]; exact hPrev2
                      exact ⟨prevTcb, hPrev3, rfl⟩

-- ============================================================================
-- Section 9: PopHead post-state endpoint queue heads helper
-- ============================================================================

/-- After PopHead, the endpoint at endpointId has:
    - The popped queue's head = headTcb.queueNext
    - The other queue's head = the pre-state other queue's head -/
theorem endpointQueuePopHead_post_endpoint_queues
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (ep : Endpoint)
    (hObjInv : st.objects.invExt)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st')) :
    ∃ ep', st'.objects[endpointId]? = some (.endpoint ep') ∧
      (if isReceiveQ then ep'.receiveQ.head else ep'.sendQ.head) = headTcb.queueNext ∧
      (if isReceiveQ then ep'.sendQ.head else ep'.receiveQ.head) =
        (if isReceiveQ then ep.sendQ.head else ep.receiveQ.head) := by
  unfold endpointQueuePopHead at hStep
  rw [hObj] at hStep; simp only at hStep; revert hStep
  cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
  | none => simp
  | some headTid =>
    simp only []
    cases hLookup : lookupTcb st headTid with
    | none => simp
    | some tcb =>
      simp only []
      cases hStore : storeObject endpointId _ st with
      | error e => simp
      | ok pair =>
        simp only []
        have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
        have hEpStored := storeObject_objects_eq' st endpointId _ pair hObjInv hStore
        -- headTid.toObjId ≠ endpointId (endpoint vs TCB)
        have hNeHead : endpointId ≠ headTid.toObjId := by
          intro h
          have hTcbObj := lookupTcb_some_objects st headTid tcb hLookup
          rw [← h] at hTcbObj; rw [hObj] at hTcbObj; cases hTcbObj
        cases hNext : tcb.queueNext with
        | none =>
          simp only []
          cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
          | error e => simp
          | ok st3 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, _, hEq⟩; subst hEq
            -- Forward: pair.2 → st3 (rewrite hEpStored from pair.2 to st3)
            rw [← storeTcbQueueLinks_preserves_objects_ne pair.2 st3 headTid _ _ _
              endpointId hNeHead hInv1 hFinal] at hEpStored
            refine ⟨_, hEpStored, ?_, ?_⟩
            · simp only [hNext]; cases isReceiveQ <;> simp_all
            · cases isReceiveQ <;> simp_all
        | some nextTid =>
          simp only []
          cases hLookupNext : lookupTcb pair.2 nextTid with
          | none => simp
          | some nextTcb =>
            simp only []
            -- nextTid.toObjId ≠ endpointId (endpoint vs TCB in pair.2)
            have hNeNext : endpointId ≠ nextTid.toObjId := by
              intro h; have := lookupTcb_some_objects pair.2 nextTid nextTcb hLookupNext
              rw [← h] at this; rw [hEpStored] at this; cases this
            cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
            | error e => simp
            | ok st2 =>
              simp only []
              have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInv1 hLink
              cases hFinal : storeTcbQueueLinks st2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, hEq⟩; subst hEq
                -- Forward chain: pair.2 → st2 → st3
                rw [← storeTcbQueueLinks_preserves_objects_ne pair.2 st2 nextTid _ _ _
                  endpointId hNeNext hInv1 hLink] at hEpStored
                rw [← storeTcbQueueLinks_preserves_objects_ne st2 st3 headTid _ _ _
                  endpointId hNeHead hInv2 hFinal] at hEpStored
                refine ⟨_, hEpStored, ?_, ?_⟩
                · simp only [hNext]; cases isReceiveQ <;> simp_all
                · cases isReceiveQ <;> simp_all

-- ============================================================================
-- Section 10: PopHead except-head V3-J preservation
-- ============================================================================

/-- After PopHead, V3-J holds for all threads except the popped head.
    The popped head (tid) temporarily has blocking ipcState but is no longer
    reachable from any queue. The caller must restore V3-J for tid by setting
    its ipcState to a non-blocking state via storeTcbIpcStateAndMessage_partial.

    The `hHeadBlocked` precondition captures that the queue head is blocked on
    the correct queue (receiveQ head → blockedOnReceive, sendQ head →
    blockedOnSend/blockedOnCall). This is always satisfied in well-formed states
    but cannot be derived from V3-J alone (V3-J gives blocked→reachable, not
    reachable→blocked). All compound IPC callers satisfy this trivially. -/
theorem endpointQueuePopHead_preserves_ipcStateQueueMembershipConsistent_except_head
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (ep : Endpoint)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hObjInv : st.objects.invExt)
    (hQNBC : queueNextBlockingConsistent st)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHeadBlocked : if isReceiveQ
      then headTcb.ipcState = .blockedOnReceive endpointId
      else headTcb.ipcState = .blockedOnSend endpointId ∨
           headTcb.ipcState = .blockedOnCall endpointId)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st')) :
    ∀ (tid' : SeLe4n.ThreadId) (tcb' : TCB),
      st'.objects[tid'.toObjId]? = some (.tcb tcb') →
      tid'.toObjId ≠ tid.toObjId →
      match tcb'.ipcState with
      | .blockedOnSend epId =>
          ∃ ep', st'.objects[epId]? = some (.endpoint ep') ∧
            (ep'.sendQ.head = some tid' ∨
             ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
               st'.objects[prev.toObjId]? = some (.tcb prevTcb) ∧
               prevTcb.queueNext = some tid')
      | .blockedOnReceive epId =>
          ∃ ep', st'.objects[epId]? = some (.endpoint ep') ∧
            (ep'.receiveQ.head = some tid' ∨
             ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
               st'.objects[prev.toObjId]? = some (.tcb prevTcb) ∧
               prevTcb.queueNext = some tid')
      | .blockedOnCall epId =>
          ∃ ep', st'.objects[epId]? = some (.endpoint ep') ∧
            (ep'.sendQ.head = some tid' ∨
             ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
               st'.objects[prev.toObjId]? = some (.tcb prevTcb) ∧
               prevTcb.queueNext = some tid')
      | _ => True := by
  obtain ⟨epPost, hEpPost, hPoppedHead, hOtherHead⟩ :=
    endpointQueuePopHead_post_endpoint_queues endpointId isReceiveQ st st' tid headTcb ep hObjInv hObj hStep
  have hHeadEq := endpointQueuePopHead_returns_head endpointId isReceiveQ st ep tid st' hObj hStep
  have hHeadTcb := endpointQueuePopHead_returns_pre_tcb endpointId isReceiveQ st ep tid headTcb st' hObj hStep
  intro tid' tcb' hTcb' hNe
  obtain ⟨preTcb, hPreTcb, hIpcEq⟩ :=
    endpointQueuePopHead_tcb_ipcState_backward endpointId isReceiveQ st st' tid tid' tcb' hObjInv hStep hTcb'
  rw [← hIpcEq]
  have hVJ := hInv tid' preTcb hPreTcb
  -- Generic transfer: given pre-state V3-J witnesses for a blocking state targeting
  -- queue qIsRecv at epId, produce post-state witnesses.
  -- hSameQueueEp: when prev = tid, the blocking match forces same queue AND same endpoint.
  have transferReach : ∀ (epId : SeLe4n.ObjId) (qIsRecv : Bool),
    (∃ epPre, st.objects[epId]? = some (.endpoint epPre) ∧
      ((if qIsRecv then epPre.receiveQ.head else epPre.sendQ.head) = some tid' ∨
       ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
         st.objects[prev.toObjId]? = some (.tcb prevTcb) ∧ prevTcb.queueNext = some tid')) →
    (headTcb.queueNext = some tid' → qIsRecv = isReceiveQ ∧ epId = endpointId) →
    ∃ ep', st'.objects[epId]? = some (.endpoint ep') ∧
      ((if qIsRecv then ep'.receiveQ.head else ep'.sendQ.head) = some tid' ∨
       ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
         st'.objects[prev.toObjId]? = some (.tcb prevTcb) ∧ prevTcb.queueNext = some tid') := by
    intro epId qIsRecv ⟨epPre, hEpPre, hReach⟩ hSameQueueEp
    obtain ⟨epId', hEpId'⟩ := endpointQueuePopHead_endpoint_forward endpointId isReceiveQ st st'
      tid headTcb epId epPre hObjInv hStep hEpPre
    refine ⟨epId', hEpId', ?_⟩
    cases hReach with
    | inl hHead' =>
      by_cases hEpEq : epId = endpointId
      · subst hEpEq
        by_cases hQEq : qIsRecv = isReceiveQ
        · -- Same queue as popped: pre-state head was tid ≠ tid'
          rw [hObj] at hEpPre; cases hEpPre; rw [hQEq] at hHead'
          cases isReceiveQ <;> simp at hHeadEq hHead' <;>
            rw [hHeadEq] at hHead' <;> cases hHead' <;> exact absurd rfl hNe
        · -- Other queue: head unchanged
          rw [hObj] at hEpPre; cases hEpPre; rw [hEpPost] at hEpId'; cases hEpId'
          exact Or.inl (by cases hQr : qIsRecv <;> cases hIr : isReceiveQ <;> simp_all)
      · -- Different endpoint: unchanged
        have hEpUnch := endpointQueuePopHead_endpoint_backward_ne endpointId isReceiveQ
          st st' tid epId epId' hEpEq hObjInv hStep hEpId'
        rw [hEpPre] at hEpUnch; cases hEpUnch; exact Or.inl hHead'
    | inr hPrev =>
      obtain ⟨prev, prevTcb, hPrevTcb, hPrevNext⟩ := hPrev
      by_cases hPrevEq : prev.toObjId = tid.toObjId
      · -- prev = tid: headTcb.queueNext = some tid'
        rw [hPrevEq] at hPrevTcb; rw [hHeadTcb] at hPrevTcb; cases hPrevTcb
        obtain ⟨hQEq, hEpEq⟩ := hSameQueueEp hPrevNext
        subst hEpEq; rw [hEpPost] at hEpId'; cases hEpId'
        -- tid' becomes new head of popped queue (qIsRecv = isReceiveQ)
        exact Or.inl (by rw [hQEq]; cases isReceiveQ <;> simp_all)
      · -- prev ≠ tid: queueNext preserved
        obtain ⟨prevTcb', hPrevTcb', hQN'⟩ :=
          endpointQueuePopHead_preserves_non_head_queueNext endpointId isReceiveQ st st'
            tid headTcb prev prevTcb hObjInv hStep hPrevTcb hPrevEq
        exact Or.inr ⟨prev, prevTcb', hPrevTcb', hQN' ▸ hPrevNext⟩
  -- Dispatch each blocking case to the generic transfer
  match hIpcMatch : preTcb.ipcState with
  | .ready => trivial
  | .blockedOnNotification _ => trivial
  | .blockedOnReply _ _ => trivial
  | .blockedOnSend epId =>
    simp only [hIpcMatch] at hVJ
    exact transferReach epId false hVJ (by
      intro hQN
      have hMatch := hQNBC tid tid' headTcb preTcb hHeadTcb hPreTcb hQN
      rw [hIpcMatch] at hMatch
      cases hIsRecv : isReceiveQ with
      | false =>
        simp only [hIsRecv] at hHeadBlocked
        cases hHeadBlocked with
        | inl hS => rw [hS] at hMatch; simp [queueNextBlockingMatch] at hMatch; exact ⟨rfl, hMatch.symm⟩
        | inr hC => rw [hC] at hMatch; simp [queueNextBlockingMatch] at hMatch; exact ⟨rfl, hMatch.symm⟩
      | true =>
        simp only [hIsRecv] at hHeadBlocked
        rw [hHeadBlocked] at hMatch; exact absurd hMatch id)
  | .blockedOnReceive epId =>
    simp only [hIpcMatch] at hVJ
    exact transferReach epId true hVJ (by
      intro hQN
      have hMatch := hQNBC tid tid' headTcb preTcb hHeadTcb hPreTcb hQN
      rw [hIpcMatch] at hMatch
      cases hIsRecv : isReceiveQ with
      | true =>
        simp only [hIsRecv] at hHeadBlocked
        rw [hHeadBlocked] at hMatch; simp [queueNextBlockingMatch] at hMatch; exact ⟨rfl, hMatch.symm⟩
      | false =>
        simp only [hIsRecv] at hHeadBlocked
        cases hHeadBlocked with
        | inl hS => rw [hS] at hMatch; exact absurd hMatch id
        | inr hC => rw [hC] at hMatch; exact absurd hMatch id)
  | .blockedOnCall epId =>
    simp only [hIpcMatch] at hVJ
    exact transferReach epId false hVJ (by
      intro hQN
      have hMatch := hQNBC tid tid' headTcb preTcb hHeadTcb hPreTcb hQN
      rw [hIpcMatch] at hMatch
      cases hIsRecv : isReceiveQ with
      | false =>
        simp only [hIsRecv] at hHeadBlocked
        cases hHeadBlocked with
        | inl hS => rw [hS] at hMatch; simp [queueNextBlockingMatch] at hMatch; exact ⟨rfl, hMatch.symm⟩
        | inr hC => rw [hC] at hMatch; simp [queueNextBlockingMatch] at hMatch; exact ⟨rfl, hMatch.symm⟩
      | true =>
        simp only [hIsRecv] at hHeadBlocked
        rw [hHeadBlocked] at hMatch; exact absurd hMatch id)

end SeLe4n.Kernel
