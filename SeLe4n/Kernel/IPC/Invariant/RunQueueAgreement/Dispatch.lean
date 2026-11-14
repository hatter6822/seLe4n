/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Scheduling
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.SuspendHolders
import SeLe4n.Kernel.ReschedulePendingArms.Dispatch
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.ReplyHolderCancel

/-!
# Every kernel entry keeps the run-queue link agreement

WS-ZA ZA4.5 part 2.  The capability-only dispatch, the capability dispatch, the
checked syscall dispatch, the timer tick and the reschedule interrupt are
`RunQueueStage`s: composed from the per-arm stages, so the run queues agree with
the threads' run-queue links after every entry that started from agreement.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Model.SystemState (RunQueueStage)
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-- Between scheduling points a notification's head waiter is blocked on it,
so no core runs it. -/
theorem notificationHeadsWakeable_of {st : SystemState} (hD : st.currentDequeuedUnique)
    (hNW : notificationWaiterConsistent st) : notificationHeadsWakeable st := by
  intro nid ntfn hN w hW
  obtain ⟨tcb, hT, hB⟩ := waitHead_blocked_of_notificationWaiterConsistent hNW
    ((SystemState.getNotification?_eq_some_iff _ _ _).mp hN) hW
  have hT' : st.getTcb? w = some tcb := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hNR : tcb.ipcState ≠ .ready := by rw [hB]; exact fun h => by cases h
  exact ⟨blockedCurrentNowhere_of_currentDequeuedUnique hD w tcb hT' hNR, tcb, hT', hNR⟩

/-- A thread's two endpoint-queue link codes: the previous and the next waiter. -/
def _root_.SeLe4n.Model.TCB.queueLinks (t : TCB) : Nat × Nat := (t.queuePrevCode, t.queueNextCode)

/-- **A step that changes no thread's IPC blocking**: it keeps every object
that is no TCB, every thread's IPC state and every core's current slot, and
the object store's invariant (a register save, a ledger write).  Every thread
after it was there before with the same scheduling-context binding, too, so the
current threads' contexts stay where they were (WS-ZA ZA6.4).  Every thread's
endpoint-queue links stay as they were (WS-SX SX4: what the entry premises'
queue facts read). -/
def IpcFrame (st st' : SystemState) : Prop :=
  st.objects.invExt → st'.objects.invExt ∧
    (∀ (k : SeLe4n.ObjId) (o : KernelObject), (∀ t : TCB, o ≠ .tcb t) →
      st'.objects[k]? = some o → st.objects[k]? = some o) ∧
    (∀ (w : SeLe4n.ThreadId) (t' : TCB), st'.getTcb? w = some t' →
      ∃ t, st.getTcb? w = some t ∧ t.ipcState = t'.ipcState ∧
        t.schedContextBinding = t'.schedContextBinding) ∧
    (∀ (w : SeLe4n.ThreadId) (t : TCB), st.getTcb? w = some t →
      ∃ t', st'.getTcb? w = some t' ∧ t'.ipcState = t.ipcState) ∧
    (∀ c : Concurrency.CoreId, st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c) ∧
    (∀ w : SeLe4n.ThreadId, (st'.getTcb? w).map TCB.queueLinks = (st.getTcb? w).map TCB.queueLinks)

namespace IpcFrame

variable {st st' st'' : SystemState}

theorem refl (st : SystemState) : IpcFrame st st :=
  fun h => ⟨h, fun _ _ _ h => h, fun _ t' h => ⟨t', h, rfl, rfl⟩, fun _ t h => ⟨t, h, rfl⟩,
    fun _ => rfl, fun _ => rfl⟩

theorem trans (h1 : IpcFrame st st') (h2 : IpcFrame st' st'') : IpcFrame st st'' := fun h =>
  let ⟨h', a1, b1, c1, d1, q1⟩ := h1 h
  let ⟨h'', a2, b2, c2, d2, q2⟩ := h2 h'
  ⟨h'', fun k o ho hk => a1 k o ho (a2 k o ho hk),
    fun w t'' hw =>
      let ⟨t', ht', e2, f2⟩ := b2 w t'' hw
      let ⟨t, ht, e1, f1⟩ := b1 w t' ht'
      ⟨t, ht, e1.trans e2, f1.trans f2⟩,
    fun w t hw =>
      let ⟨t', ht', e1⟩ := c1 w t hw
      let ⟨t'', ht'', e2⟩ := c2 w t' ht'
      ⟨t'', ht'', e2.trans e1⟩,
    fun c => (d2 c).trans (d1 c), fun w => (q2 w).trans (q1 w)⟩

/-- A step that keeps the object store and every current slot. -/
theorem of_frame (hO : st'.objects = st.objects)
    (hC : ∀ c, st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c) :
    IpcFrame st st' := fun h =>
  have hT : ∀ w, st'.getTcb? w = st.getTcb? w := fun w => by
    unfold SystemState.getTcb?; rw [hO]
  ⟨by rw [hO]; exact h, fun _ _ _ hk => hO ▸ hk, fun w t' hw => ⟨t', (hT w) ▸ hw, rfl, rfl⟩,
    fun w t hw => ⟨t, (hT w).symm ▸ hw, rfl⟩, hC, fun w => by rw [hT w]⟩

/-- A write to one TCB that keeps its IPC state, its binding and its queue
links. -/
theorem updateTcb (st : SystemState) (tid : SeLe4n.ThreadId) {f : TCB → TCB}
    (hf : ∀ x, (f x).ipcState = x.ipcState)
    (hb : ∀ x, (f x).schedContextBinding = x.schedContextBinding := by intro _; rfl)
    (hq : ∀ x, (f x).queueLinks = x.queueLinks := by intro _; rfl) :
    IpcFrame st (st.updateTcb tid f) := fun h =>
  ⟨SystemState.updateTcb_preserves_objects_invExt _ _ _ h,
    fun _ _ ho hk => updateTcb_objects_back_nonTcb h ho hk,
    fun w t' hw => by
      rw [updateTcb_getTcb?_eq h] at hw
      split at hw
      · obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hw
        exact ⟨t, ht, (hf t).symm, (hb t).symm⟩
      · exact ⟨t', hw, rfl, rfl⟩,
    fun _ _ hw => updateTcb_getTcb?_fwd h hf hw,
    fun _ => by rw [SystemState.updateTcb_scheduler],
    fun w => by
      rw [updateTcb_getTcb?_eq h]
      split
      · rw [Option.map_map]; exact Option.map_congr fun x _ => hq x
      · rfl⟩

end IpcFrame

/-- Two states whose threads read the same queue links: each thread in the
first stands in the second with the same two links. -/
theorem queueLinks_carried {A B : SystemState}
    (hQL : ∀ w : SeLe4n.ThreadId, (A.getTcb? w).map TCB.queueLinks = (B.getTcb? w).map TCB.queueLinks)
    {w : SeLe4n.ThreadId} {t' : TCB} (h : A.objects[w.toObjId]? = some (.tcb t')) :
    ∃ t, B.objects[w.toObjId]? = some (.tcb t) ∧ t.queuePrev = t'.queuePrev ∧
      t.queueNext = t'.queueNext := by
  have e := hQL w
  rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr h] at e
  cases h0 : B.getTcb? w with
  | none => rw [h0] at e; cases e
  | some t =>
    rw [h0] at e
    have e' : t'.queueLinks = t.queueLinks := Option.some.inj e
    have hp : t'.queuePrevCode = t.queuePrevCode := congrArg Prod.fst e'
    have hn : t'.queueNextCode = t.queueNextCode := congrArg Prod.snd e'
    refine ⟨t, (SystemState.getTcb?_eq_some_iff _ _ _).mp h0, ?_, ?_⟩
    · show SeLe4n.ThreadId.ofOptCode _ = SeLe4n.ThreadId.ofOptCode _; rw [hp]
    · show SeLe4n.ThreadId.ofOptCode _ = SeLe4n.ThreadId.ofOptCode _; rw [hn]

/-- A `queueNext` path after a step that keeps every thread's links was there
before. -/
theorem queueNextPath_carried {A B : SystemState}
    (hQL : ∀ w : SeLe4n.ThreadId, (A.getTcb? w).map TCB.queueLinks = (B.getTcb? w).map TCB.queueLinks)
    {a b : SeLe4n.ThreadId} (h : QueueNextPath A a b) : QueueNextPath B a b := by
  induction h with
  | single a b t hO hN =>
    obtain ⟨t0, h0, -, hn⟩ := queueLinks_carried hQL hO
    exact .single a b t0 h0 (hn.trans hN)
  | cons a b c t hO hN _ ih =>
    obtain ⟨t0, h0, -, hn⟩ := queueLinks_carried hQL hO
    exact .cons a b c t0 h0 (hn.trans hN) ih

/-- **The queue facts a reply holder's cancel reads hold after a step that
changes no thread's IPC blocking**: it keeps every endpoint, every IPC state
and every queue link. -/
theorem QueueHeadCancelFacts.of_ipcFrame {st st' : SystemState} (F : QueueHeadCancelFacts st)
    (hF : IpcFrame st st') (hInv : st.objects.invExt) : QueueHeadCancelFacts st' := by
  obtain ⟨_, hNT, hTB, _, _, hQL⟩ := hF hInv
  have hEp : ∀ (eid : SeLe4n.ObjId) (ep : Endpoint), st'.objects[eid]? = some (.endpoint ep) →
      st.objects[eid]? = some (.endpoint ep) := fun _ _ hE => hNT _ _ (fun _ h => by cases h) hE
  have hTI : ∀ (y : SeLe4n.ThreadId) (t' : TCB), st'.objects[y.toObjId]? = some (.tcb t') →
      ∃ t, st.objects[y.toObjId]? = some (.tcb t) ∧ t.ipcState = t'.ipcState := fun y t' hY =>
    let ⟨t, ht, hs, _⟩ := hTB y t' ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hY)
    ⟨t, (SystemState.getTcb?_eq_some_iff _ _ _).mp ht, hs⟩
  have hQL' : ∀ w : SeLe4n.ThreadId,
      (st.getTcb? w).map TCB.queueLinks = (st'.getTcb? w).map TCB.queueLinks :=
    fun w => (hQL w).symm
  refine ⟨queueHeadBlockedConsistent_of_endpoint_tcb_backward st st' hEp hTI F.heads,
    endpointQueueTailBlockedConsistent_of_endpoint_tcb_backward st st' hEp hTI F.tails,
    ⟨fun a tA' hA b hN => ?_, fun b tB' hB a hP => ?_⟩,
    fun tid hP => F.acyclic tid (queueNextPath_carried hQL hP),
    fun a b tA' tB' hA hB hN => ?_⟩
  · obtain ⟨tA, hA0, -, hn⟩ := queueLinks_carried hQL hA
    obtain ⟨tB, hB0, hp⟩ := F.links.1 a tA hA0 b (hn.trans hN)
    obtain ⟨tB', hB', hp', -⟩ := queueLinks_carried hQL' hB0
    exact ⟨tB', hB', hp'.trans hp⟩
  · obtain ⟨tB, hB0, hp, -⟩ := queueLinks_carried hQL hB
    obtain ⟨tA, hA0, hn⟩ := F.links.2 b tB hB0 a (hp.trans hP)
    obtain ⟨tA', hA', -, hn'⟩ := queueLinks_carried hQL' hA0
    exact ⟨tA', hA', hn'.trans hn⟩
  · obtain ⟨tA, hA0, -, hn⟩ := queueLinks_carried hQL hA
    obtain ⟨tA1, hA1, hsA⟩ := hTI a tA' hA
    rw [hA0] at hA1; cases hA1
    obtain ⟨tB, hB0, hsB⟩ := hTI b tB' hB
    have hT := F.targets a b tA tB hA0 hB0 (hn.trans hN)
    rw [← hsA, ← hsB]; exact hT

/-- What a kernel entry reads off the state it starts from: the three placement
properties, the endpoint queues' heads and the notifications' head waiters
blocked, and every core's current context placeable on its core (WS-ZA ZA6.4:
what the bound yield's postpone needs), and every context a thread holds the one
its binding names (WS-ZA ZA6.33: what the resume's context settle needs). -/
structure EntryPremises (st : SystemState) : Prop where
  objInv : st.objects.invExt
  refined : st.runQueueRefined
  dequeued : st.currentDequeuedUnique
  queueHeads : queueHeadBlockedConsistent st
  ntfnHeads : notificationHeadsWakeable st
  placeable : ∀ c, st.currentContextPlaceableOnCore c
  holders : holdersNameTheirContexts st
  /-- WS-SX SX4: the endpoint queues' tails blocked, the queue links two-way
  and acyclic, and each waiter's successor blocked as it is: with the heads,
  what a busy-reply receive's cancel of the reply's holder reads. -/
  queueTails : endpointQueueTailBlockedConsistent st
  queueLinkIntegrity : tcbQueueLinkIntegrity st
  queueAcyclic : tcbQueueChainAcyclic st
  queueNextTargets : queueNextTargetBlocked st

/-- What a syscall arm reads besides: the caller is core `c`'s current thread and
no idle thread (an idle thread runs the kernel's own loop and never traps). -/
structure SyscallArmPremises (st : SystemState) (c : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) : Prop extends EntryPremises st where
  current : st.scheduler.currentOnCore c = some tid
  notIdle : isIdleThreadId tid = false

namespace EntryPremises

variable {st st' : SystemState}

/-- The premises from the state's invariants: the endpoint-queue facts are
conjuncts of `ipcInvariantFull`. -/
theorem of_invariants (hInv : st.objects.invExt) (hR : st.runQueueRefined)
    (hD : st.currentDequeuedUnique) (hIpc : ipcInvariantFull st)
    (hNW : notificationWaiterConsistent st) (hP : ∀ c, st.currentContextPlaceableOnCore c)
    (hB : schedContextBindingConsistent st) :
    EntryPremises st :=
  let F := QueueHeadCancelFacts.of_ipcInvariantFull hIpc
  ⟨hInv, hR, hD, F.heads, notificationHeadsWakeable_of hD hNW, hP,
    holdersNameTheirContexts_of_schedContextBindingConsistent hB, F.tails, F.links, F.acyclic,
    F.targets⟩

/-- The queue facts a reply holder's cancel reads. -/
theorem queueHeadCancelFacts (E : EntryPremises st) : QueueHeadCancelFacts st :=
  ⟨E.queueHeads, E.queueTails, E.queueLinkIntegrity, E.queueAcyclic, E.queueNextTargets⟩

theorem endpointHeads (E : EntryPremises st) : endpointHeadsWakeable st :=
  endpointHeadsWakeable_of E.dequeued E.queueHeads

theorem blocked (E : EntryPremises st) : blockedCurrentNowhere st :=
  blockedCurrentNowhere_of_currentDequeuedUnique E.dequeued

/-- The premises hold after a stage that changes no thread's IPC blocking. -/
theorem of_ipcFrame (E : EntryPremises st) (hS : RunQueueStage st st') (hF : IpcFrame st st') :
    EntryPremises st' :=
  let hL := hS.1 E.objInv E.refined
  let ⟨_, hNT, hTB, hTF, hC, _⟩ := hF E.objInv
  { objInv := hL.1, refined := hL.2
    dequeued := hS.2.1 none E.objInv E.refined hL.2 E.dequeued
    queueHeads := queueHeadBlockedConsistent_of_endpoint_tcb_backward st st'
      (fun _ _ hE => hNT _ _ (fun _ h => by cases h) hE)
      (fun y t' hY =>
        let ⟨t, ht, hs, _⟩ := hTB y t' ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hY)
        ⟨t, (SystemState.getTcb?_eq_some_iff _ _ _).mp ht, hs⟩) E.queueHeads
    ntfnHeads := fun nid ntfn hN w hW => by
      have hN0 : st.getNotification? nid = some ntfn :=
        (SystemState.getNotification?_eq_some_iff _ _ _).mpr (hNT _ _ (fun _ h => by cases h)
          ((SystemState.getNotification?_eq_some_iff _ _ _).mp hN))
      obtain ⟨hCN, t, ht, hb⟩ := E.ntfnHeads nid ntfn hN0 w hW
      obtain ⟨t', ht', hs⟩ := hTF w t ht
      exact ⟨fun c => by rw [hC c]; exact hCN c, t', ht', by rw [hs]; exact hb⟩
    placeable := fun c tid tcb' scId sc hCur hT hb hS => by
      rw [hC c] at hCur
      obtain ⟨t, ht, -, hbd⟩ := hTB tid tcb' hT
      have hS0 : st.getSchedContext? scId = some sc :=
        (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr (hNT _ _ (fun _ h => by cases h)
          ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hS))
      obtain ⟨h1, h2⟩ := E.placeable c tid t scId sc hCur ht (by rw [hbd]; exact hb) hS0
      refine ⟨h1, ?_⟩
      unfold SystemState.releaseFreeFor SystemState.releaseCoreOf at h2 ⊢
      rw [hS]; rw [hS0] at h2; exact h2
    holders := fun s sc t hs hb x hx => by
      have hS0 : st.getSchedContext? s = some sc :=
        (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr (hNT _ _ (fun _ h => by cases h)
          ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hs))
      obtain ⟨y, hy, -, hbd⟩ := hTB t x hx
      rw [← hbd]
      exact E.holders s sc t hS0 hb y hy
    queueTails := (E.queueHeadCancelFacts.of_ipcFrame hF E.objInv).tails
    queueLinkIntegrity := (E.queueHeadCancelFacts.of_ipcFrame hF E.objInv).links
    queueAcyclic := (E.queueHeadCancelFacts.of_ipcFrame hF E.objInv).acyclic
    queueNextTargets := (E.queueHeadCancelFacts.of_ipcFrame hF E.objInv).targets }

/-- The caller's premises: core `c`'s current thread, no idle thread. -/
theorem arm (E : EntryPremises st) {c : Concurrency.CoreId} {tid : SeLe4n.ThreadId}
    (hCur : st.scheduler.currentOnCore c = some tid) (hNI : isIdleThreadId tid = false) :
    SyscallArmPremises st c tid :=
  { toEntryPremises := E, current := hCur, notIdle := hNI }

end EntryPremises

namespace SyscallArmPremises

variable {st st' : SystemState} {c : Concurrency.CoreId} {tid : SeLe4n.ThreadId}

theorem endpointHeads (P : SyscallArmPremises st c tid) : endpointHeadsWakeable st :=
  P.toEntryPremises.endpointHeads

/-- WS-ZA ZA6.33: the trapping thread is not suspended: it is core `c`'s
current thread, so runnable. -/
theorem currentActive (P : SyscallArmPremises st c tid) : st.activeAt tid :=
  (P.dequeued.runnable P.current).activeAt

theorem blocked (P : SyscallArmPremises st c tid) : blockedCurrentNowhere st :=
  P.toEntryPremises.blocked

/-- The premises hold after a stage that changes no thread's IPC blocking. -/
theorem of_ipcFrame (P : SyscallArmPremises st c tid) (hS : RunQueueStage st st')
    (hF : IpcFrame st st') : SyscallArmPremises st' c tid :=
  (P.toEntryPremises.of_ipcFrame hS hF).arm
    (by rw [(hF P.objInv).2.2.2.2.1 c]; exact P.current) P.notIdle

end SyscallArmPremises

/-- A validated thread operand is no core's idle thread. -/
theorem validateThreadIdArg_ok_val_not_idle {tid : SeLe4n.ThreadId} {vtid : SeLe4n.ValidThreadId}
    (h : validateThreadIdArg tid = .ok vtid) : isIdleThreadId vtid.val = false := by
  rw [SeLe4n.ThreadId.toValid?_some_val_eq _ _ (validateThreadIdArg_ok_toValid? _ _ h)]
  exact validateThreadIdArg_ok_not_reserved _ _ h

/-- WS-ZA ZA6.32: the interrupt acknowledge writes the line's mask and the
controller write it owes, no object and no scheduler field. -/
theorem irqHandlerAck_runQueueStage {line : Nat} {st st' : SystemState}
    (h : Architecture.irqHandlerAck line st = .ok ((), st')) : RunQueueStage st st' := by
  rw [Architecture.irqHandlerAck_ok h]
  exact RunQueueStage.of_frame rfl rfl rfl

/-- WS-ZA ZA6.32: `seL4_IRQControl_Get` keeps the run queues: the line's
state, the handler capability's insert and its derivation edge. -/
theorem irqControlGet_runQueueStage {control dst : CSpaceAddr} {line : Nat}
    {st st' : SystemState} (h : irqControlGet control dst line st = .ok ((), st')) :
    RunQueueStage st st' := by
  obtain ⟨-, stI, hI, rfl⟩ := irqControlGet_ok h
  exact ((setIrqLineSignal_runQueueStage st line true).trans
    (cspaceInsertSlot_runQueueStage hI)).trans (cdtRecord_runQueueStage stI control dst .mint)

/-- WS-ZA ZA6.32: `seL4_IRQHandler_SetNotification` keeps the run queues: the
node slot's finalising delete, then the copy. -/
theorem irqHandlerSetNotification_runQueueEntryStage {ec : Concurrency.CoreId} {line : Nat}
    {src : CSpaceAddr} {st st' : SystemState}
    (h : irqHandlerSetNotification ec line src st = .ok ((), st')) :
    SystemState.RunQueueEntryStage st st' := by
  obtain ⟨-, st1, -, -, -, hD, hC | rfl⟩ := irqHandlerSetNotification_ok_cases h
  · exact (cspaceDeleteSlotZombie_runQueueEntryStage hD).trans (cspaceCopy_runQueueStage hC).entry
  · exact (cspaceDeleteSlotZombie_runQueueEntryStage hD).trans
      (cspaceCopyPerform_runQueueStage _ _ _ _).entry

/-- The capability-only dispatch keeps the run queues in agreement with the
threads' links on every arm but the yieldTo, which links its caller
(`dispatchCapabilityOnly_runQueueEntryStageOn`). -/
theorem dispatchCapabilityOnly_runQueueEntryStage
    (decoded : SyscallDecodeResult) (cap : Capability) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (k : Kernel Unit) (st st' : SystemState)
    (hInv : st.objects.invExt) (hH : holdersNameTheirContexts st)
    (hNY : decoded.syscallId ≠ .schedContextYieldTo)
    (hArm : dispatchCapabilityOnly decoded cap tid executingCore = some k)
    (hStep : k st = .ok ((), st')) :
    SystemState.RunQueueEntryStage st st' := by
  unfold dispatchCapabilityOnly at hArm
  cases hSy : decoded.syscallId <;> simp only [hSy] at hArm <;> try cases hArm
  case schedContextYieldTo => exact absurd hSy hNY
  case irqHandlerAck =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line => exact RunQueueStage.entry (irqHandlerAck_runQueueStage hStep)
    all_goals try cases hStep
  case irqControlGet =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqControl =>
      obtain ⟨_, _, _, -, -, -, hG⟩ := irqControlGetFromCap_ok _ _ _ _ _ hStep
      exact RunQueueStage.entry (irqControlGet_runQueueStage hG)
    all_goals try cases hStep
  case irqHandlerSetNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line =>
      obtain ⟨_, _, -, hN⟩ := irqHandlerSetNotificationFromCap_ok _ _ _ _ _ _ hStep
      exact irqHandlerSetNotification_runQueueEntryStage hN
    all_goals try cases hStep
  case irqHandlerClear =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line =>
      exact cspaceDeleteSlotZombie_runQueueEntryStage (irqHandlerClear_ok hStep).2
    all_goals try cases hStep
  case cspaceDelete =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object cnodeId =>
      try dsimp only [] at hStep
      cases hDec : decodeCSpaceDeleteArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          exact cspaceDeleteSlotZombie_runQueueEntryStage hStep
    all_goals try cases hStep
  case cspaceRevoke =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object cnodeId =>
      try dsimp only [] at hStep
      cases hDec : decodeCSpaceDeleteArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          exact cspaceRevokeCdtFinalising_runQueueEntryStage hStep
    all_goals try cases hStep
  case mintReplyCap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object cnodeId =>
      try dsimp only [] at hStep
      cases hDec : decodeMintReplyCapArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          refine RunQueueStage.entry ?_
          exact mintReplyCapWithCdt_runQueueStage hStep
    all_goals try cases hStep
  case untypedRetype =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object _ =>
      refine RunQueueStage.entry ?_
      exact untypedRetypeFromCap_runQueueStage hStep
    all_goals try cases hStep
  case untypedReset =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object _ =>
      refine RunQueueStage.entry ?_
      obtain ⟨_, _, _, -, -, hS⟩ := untypedResetFromCap_ok _ _ _ _ hStep
      exact untypedResetSlot_runQueueStage hS
    all_goals try cases hStep
  case vspaceMap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodeVSpaceMapArgs decoded st.machine.maxASID with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          · refine RunQueueStage.entry ?_
            exact vspaceMapOrRemapFromFrameCap_runQueueStage hStep
    all_goals try cases hStep
  case vspaceUnmap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodeVSpaceUnmapArgs decoded st.machine.maxASID with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          · refine RunQueueStage.entry ?_
            exact vspaceUnmapPageWithShootdownAndIcacheBroadcast_runQueueStage hStep
    all_goals try cases hStep
  case vspaceUnifyInstruction =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodeVSpaceUnifyInstructionArgs decoded st.machine.maxASID with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          · refine RunQueueStage.entry ?_
            exact vspaceUnifyInstructionPage_runQueueStage hStep
    all_goals try cases hStep
  case serviceRevoke =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      obtain ⟨_, hRev⟩ := revokeServiceByRecordedRegistration_revokeService hStep
      refine RunQueueStage.entry ?_
      exact revokeService_runQueueStage hRev
    all_goals try cases hStep
  case serviceQuery =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object epId =>
      try dsimp only [] at hStep
      cases hLkS : lookupServiceByRecordedRegistration epId st with
      | error e => simp only [hLkS] at hStep; cases hStep
      | ok pair =>
          obtain ⟨reg, st1⟩ := pair
          simp only [hLkS] at hStep
          have hStEq : st1 = st := lookupServiceByRecordedRegistration_preserves_state epId st reg st1 hLkS
          subst hStEq
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
          subst hStep
          refine RunQueueStage.entry ?_
          exact writeReturnFrameToTcb_runQueueStage _ _ _
    all_goals try cases hStep
  case schedContextConfigure =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case schedControl core =>
      try dsimp only [] at hStep
      cases hDec : decodeSchedContextConfigureArgsChecked decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : resolveSchedControlConfigureTarget tid core args.scCPtr st with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              split at hStep
              · exact schedControlConfigure_runQueueEntryStage hStep
              · cases hStep
    all_goals try cases hStep
  case schedContextBind =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hRes : resolveSchedContextBindThread tid (decodeSchedContextBindArgs decoded) st with
      | error e => simp only [hRes] at hStep; cases hStep
      | ok vThreadId =>
          simp only [hRes] at hStep
          cases hVal : validateObjIdArg scId with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              refine RunQueueStage.entry ?_
              exact schedContextBind_runQueueStage hStep
    all_goals try cases hStep
  case schedContextUnbind =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hDec : decodeSchedContextUnbindArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateObjIdArg scId with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              cases hUn : SchedContextOps.schedContextUnbindOnCore vScId
                  executingCore st with
              | error e => simp only [hUn] at hStep; cases hStep
              | ok pair =>
                  obtain ⟨stU, sgiU⟩ := pair
                  simp only [hUn] at hStep
                  cases hStep
                  exact schedContextUnbindOnCore_runQueueEntryStage hUn
    all_goals try cases hStep
  case schedContextConsumed =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hVal : validateObjIdArg scId with
      | error e => simp only [hVal] at hStep; cases hStep
      | ok vScId =>
          simp only [hVal] at hStep
          cases hC : schedContextConsumedOnCore (SeLe4n.SchedContextId.ofObjId vScId.val)
              executingCore st with
          | error e => simp only [hC] at hStep; cases hStep
          | ok stC =>
              simp only [hC] at hStep
              cases hStep
              exact SystemState.schedContextConsumedOnCore_runQueueEntryStage hC
    all_goals try cases hStep
  case tcbBindNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object tcbObjId =>
      try dsimp only [] at hStep
      cases hDec : decodeTcbBindNotificationArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hCaller : st.getTcb? tid with
          | none => simp only [hCaller] at hStep; cases hStep
          | some callerTcb =>
              simp only [hCaller] at hStep
              try dsimp only [] at hStep
              simp only [syscallLookupArgumentCap] at hStep
              cases hCap2 : syscallLookupCap { callerId := tid, cspaceRootCap := callerTcb.spaceCells[0], capAddr := args.notificationCPtr, requiredRight := .write } st with
              | error e => simp only [hCap2] at hStep; cases hStep
              | ok pair =>
                  obtain ⟨ntfnCap, stL⟩ := pair
                  simp only [hCap2] at hStep
                  cases hNT : ntfnCap.target with
                  | object notifId =>
                      simp only [hNT] at hStep
                      refine RunQueueStage.entry ?_
                      exact bindNotification_runQueueStage hStep
                  | _ => simp only [hNT] at hStep; cases hStep
    all_goals try cases hStep
  case tcbUnbindNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object tcbObjId =>
      try dsimp only [] at hStep
      cases hUn : unbindNotification (SeLe4n.ThreadId.ofNat tcbObjId.toNat) st with
      | error e => simp only [hUn] at hStep; cases hStep
      | ok pair =>
          obtain ⟨u, stU⟩ := pair; cases u
          simp only [hUn] at hStep
          cases hStep
          refine RunQueueStage.entry ?_
          exact unbindNotification_runQueueStage hUn
    all_goals try cases hStep
  case tcbSuspend =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSuspendArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hSus : Lifecycle.Suspend.suspendThreadOnCore st vtid
                  executingCore with
              | error e => simp only [hSus] at hStep; cases hStep
              | ok pair =>
                  obtain ⟨stU, sgiU⟩ := pair
                  simp only [hSus] at hStep
                  cases hStep
                  exact suspendThreadOnCore_runQueueEntryStage
                    (validateThreadIdArg_ok_val_not_idle hVal) hSus
    all_goals try cases hStep
  case tcbResume =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeResumeArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
      | error e => simp only [hVal] at hStep; cases hStep
      | ok vtid =>
          simp only [hVal] at hStep
          cases hRes : Lifecycle.Suspend.restartThreadOnCore st vtid executingCore with
          | error e => simp only [hRes] at hStep; cases hStep
          | ok pair =>
              obtain ⟨stU, sgiU⟩ := pair
              simp only [hRes] at hStep
              cases hStep
              rcases Lifecycle.Suspend.restartThreadOnCore_cases hRes with
                hRes | ⟨st1, _, hSus, hRes⟩ | ⟨rfl, _⟩
              · exact (retirePendingFaultForResume_runQueueStage st vtid.val).entry.trans
                  (resumeThreadOnCore_runQueueEntryStage
                    (hH.retirePendingFaultForResume vtid.val hInv) hRes)
              · exact (suspendThreadOnCore_runQueueEntryStage
                  (validateThreadIdArg_ok_val_not_idle hVal) hSus).trans
                  ((retirePendingFaultForResume_runQueueStage st1 vtid.val).entry.trans
                    (resumeThreadOnCore_runQueueEntryStage
                      ((suspendThreadOnCore_holdersNameTheirContexts hInv hH hSus).retirePendingFaultForResume
                        vtid.val (suspendThreadOnCore_preserves_objects_invExt _ _ _ _ _ hInv hSus))
                      hRes))
              · exact ⟨SystemState.RunQueueLinkStage.refl _, fun _ _ _ d => d⟩
    all_goals try cases hStep
  case tcbSetPriority =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetPriorityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hValC : validateThreadIdArg tid with
          | error e => simp only [hValC] at hStep; cases hStep
          | ok vCallerTid =>
              simp only [hValC] at hStep
              cases hValT : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
              | error e => simp only [hValT] at hStep; cases hStep
              | ok vTargetTid =>
                  simp only [hValT] at hStep
                  cases hSet : SchedContext.PriorityManagement.setPriorityOnCore st
                      vCallerTid vTargetTid (Priority.ofNat args.newPriority)
                      executingCore with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨stU, sgiU⟩ := pair
                      simp only [hSet] at hStep
                      cases hStep
                      exact setPriorityOnCore_runQueueEntryStage hSet
    all_goals try cases hStep
  case tcbSetMCPriority =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetMCPriorityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hValC : validateThreadIdArg tid with
          | error e => simp only [hValC] at hStep; cases hStep
          | ok vCallerTid =>
              simp only [hValC] at hStep
              cases hValT : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
              | error e => simp only [hValT] at hStep; cases hStep
              | ok vTargetTid =>
                  simp only [hValT] at hStep
                  cases hSet : SchedContext.PriorityManagement.setMCPriorityOnCore st
                      vCallerTid vTargetTid (Priority.ofNat args.newMCP)
                      executingCore with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨stU, sgiU⟩ := pair
                      simp only [hSet] at hStep
                      cases hStep
                      exact setMCPriorityOnCore_runQueueEntryStage hSet
    all_goals try cases hStep
  case tcbSetIPCBuffer =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetIPCBufferArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hSet : Architecture.IpcBufferValidation.setIPCBufferOp st vtid
                  args.bufferAddr with
              | error e => simp only [hSet] at hStep; cases hStep
              | ok stU =>
                  simp only [hSet] at hStep
                  cases hStep
                  refine RunQueueStage.entry ?_
                  exact setIPCBufferOp_runQueueStage hSet
    all_goals try cases hStep
  case tcbSetAffinity =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodeSetAffinityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hAff : decodeAffinity args.affinityRaw with
              | error e => simp only [hAff] at hStep; cases hStep
              | ok affinity =>
                  simp only [hAff] at hStep
                  cases hSet : setThreadCpuAffinityOnCore st vtid affinity
                      executingCore with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨stU, sgiU⟩ := pair
                      simp only [hSet] at hStep
                      cases hStep
                      exact setThreadCpuAffinityOnCore_runQueueEntryStage hSet
    all_goals try cases hStep
  case tcbSetFaultHandler =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodeSetFaultHandlerArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hSet : setThreadFaultHandlerOp st vtid args.handlerCPtr with
              | error e => simp only [hSet] at hStep; cases hStep
              | ok stU =>
                  simp only [hSet] at hStep
                  cases hStep
                  refine RunQueueStage.entry ?_
                  exact setThreadFaultHandlerOp_runQueueStage hSet
    all_goals try cases hStep
  case tcbSetSpace =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodeSetSpaceArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hR : resolveSetSpace tid args st with
              | error e => simp only [hR] at hStep; cases hStep
              | ok p =>
                  obtain ⟨cn, vr⟩ := p
                  simp only [hR] at hStep
                  cases hSet : copyThreadSpacesZombie executingCore st vtid cn vr args.cspaceRootData with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok stU =>
                      simp only [hSet] at hStep
                      cases hStep
                      exact copyThreadSpacesZombie_runQueueEntryStage hSet
    all_goals try cases hStep
  case pageTableMap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodePageTableMapArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hR : resolveCallerCapObject tid args.vspaceRoot .write st with
          | error e => simp only [hR] at hStep; cases hStep
          | ok p =>
              obtain ⟨_, rootId⟩ := p
              simp only [hR] at hStep
              refine RunQueueStage.entry ?_
              exact pageTableMap_runQueueStage hStep
    all_goals try cases hStep
  case pageTableUnmap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      refine RunQueueStage.entry ?_
      exact pageTableUnmap_runQueueStage hStep
    all_goals try cases hStep

/-- WS-ZA ZA6.29: **the capability-only dispatch is a kernel entry that links
only the executing core's current thread**: the yieldTo arm links it
(`schedContextYieldToOnCore_runQueueEntryStage`); every other arm links no
thread. -/
theorem dispatchCapabilityOnly_runQueueEntryStageOn
    (decoded : SyscallDecodeResult) (cap : Capability) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (k : Kernel Unit) (st st' : SystemState)
    (hInv : st.objects.invExt) (hH : holdersNameTheirContexts st)
    (hArm : dispatchCapabilityOnly decoded cap tid executingCore = some k)
    (hStep : k st = .ok ((), st')) :
    SystemState.RunQueueEntryStageOn (SystemState.currentObjOn st executingCore) st st' := by
  by_cases hNY : decoded.syscallId = .schedContextYieldTo
  · unfold dispatchCapabilityOnly at hArm
    simp only [hNY] at hArm
    cases hArm
    cases hTgt : cap.target with
    | object scId =>
      simp only [hTgt] at hStep
      try dsimp only [] at hStep
      cases hVal : validateObjIdArg scId with
      | error e => simp only [hVal] at hStep; cases hStep
      | ok vScId =>
          simp only [hVal] at hStep
          cases hC : SchedContextOps.schedContextYieldToOnCore
              (SeLe4n.SchedContextId.ofObjId vScId.val) executingCore st with
          | error e => simp only [hC] at hStep; cases hStep
          | ok stC =>
              simp only [hC] at hStep
              cases hStep
              exact schedContextYieldToOnCore_runQueueEntryStage hC
    | _ => simp only [hTgt] at hStep; cases hStep
  · exact (dispatchCapabilityOnly_runQueueEntryStage decoded cap tid executingCore k st st' hInv hH
      hNY hArm hStep).toOn _

/-- The yieldTo is a capability-only arm: the capability dispatch never falls
through to the routed arms for it. -/
theorem dispatchCapabilityOnly_yieldTo_isSome {decoded : SyscallDecodeResult} {cap : Capability}
    {tid : SeLe4n.ThreadId} {executingCore : Concurrency.CoreId}
    (hNY : decoded.syscallId = .schedContextYieldTo) :
    dispatchCapabilityOnly decoded cap tid executingCore ≠ none := by
  unfold dispatchCapabilityOnly; simp [hNY]

/-! ### The wrapping steps of the capability dispatch -/

/-- Clearing a woken receiver's stash rewrites one TCB's stash field. -/
theorem clearWokenReceiverStash_runQueueStage (receiver? : Option SeLe4n.ThreadId)
    {st st' : SystemState} (h : clearWokenReceiverStash receiver? st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold clearWokenReceiverStash at h
  split at h
  · cases h; exact RunQueueStage.refl _
  · split at h
    · rename_i rTcb hT
      split at h
      · exact storeObject_tcbOver_runQueueStage hT h (fun _ => rfl)
      · cases h; exact RunQueueStage.refl _
    · cases h; exact RunQueueStage.refl _

/-- Read a pair-returning transition's stage off the equation naming its result. -/
theorem runQueueStage_of_pair_eq {α : Type} {R : SystemState → SystemState → Prop}
    {st s : SystemState} {p : SystemState × α}
    {r : α} (hS : R st p.1) (hEq : p = (s, r)) : R st s := by
  subst hEq; exact hS

/-- The tail every waking arm ends with: clear the woken receiver's stash, then
stage the delivered frames. -/
theorem clearStashStage_runQueueEntryStage {st s st' : SystemState}
    {woken? : Option SeLe4n.ThreadId} {stage : SystemState → SystemState}
    (hS : SystemState.RunQueueEntryStage st s) (hStage : ∀ x, RunQueueStage x (stage x))
    (h : (match clearWokenReceiverStash woken? s with
      | .error e => .error e
      | .ok ((), s') => .ok ((), stage s')) =
        (.ok ((), st') : Except KernelError (Unit × SystemState))) :
    SystemState.RunQueueEntryStage st st' := by
  split at h
  · cases h
  · rename_i s3 hClr
    cases h
    exact hS.trans ((clearWokenReceiverStash_runQueueStage woken? hClr).trans (hStage _)).entry

/-- The two badge stagings a signal arm ends with. -/
theorem stageWokenDeliveryTwice_runQueueStage (x : SystemState) (w p : Option SeLe4n.ThreadId) :
    RunQueueStage x (Architecture.stageWokenDelivery
      (Architecture.stageWokenDelivery x w 0) p 0) :=
  (stageWokenDelivery_runQueueStage x w 0).trans (stageWokenDelivery_runQueueStage _ p 0)

theorem endpointSendCrossCoreDispatchChecked_runQueueEntryStage (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (c : Concurrency.CoreId)
    (st : SystemState) (P : SyscallArmPremises st c sender) :
    SystemState.RunQueueEntryStage st
      (endpointSendCrossCoreDispatchChecked ctx endpointId sender payload c st).1 := by
  unfold endpointSendCrossCoreDispatchChecked
  repeat' split
  all_goals first
    | exact (RunQueueStage.refl _).entry
    | exact endpointSendDualWithCapsOnCore_runQueueEntryStage _ _ _ _ _ P.endpointHeads
        P.current P.notIdle

theorem endpointCallCrossCoreDispatchChecked_runQueueEntryStage (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (c : Concurrency.CoreId)
    (st : SystemState) (P : SyscallArmPremises st c caller) :
    SystemState.RunQueueEntryStage st
      (endpointCallCrossCoreDispatchChecked ctx endpointId caller payload c st).1 := by
  unfold endpointCallCrossCoreDispatchChecked
  split
  · exact endpointCallCrossCoreDispatch_runQueueEntryStage _ _ _ _ _ P.endpointHeads
      P.current P.notIdle P.objInv P.refined P.currentActive
  · exact (RunQueueStage.refl _).entry

theorem notificationSignalBoundCrossCoreDispatchChecked_runQueueStage (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId) (badge : SeLe4n.Badge)
    (c : Concurrency.CoreId) (st : SystemState) (hHeads : notificationHeadsWakeable st)
    (hBlk : blockedCurrentNowhere st) :
    RunQueueStage st (notificationSignalBoundCrossCoreDispatchChecked ctx notificationId
      signaler badge c st).1 := by
  unfold notificationSignalBoundCrossCoreDispatchChecked
  repeat' split
  all_goals first
    | exact RunQueueStage.refl _
    | exact notificationSignalBoundOnCore_runQueueStage _ _ _ _ hHeads hBlk

theorem notificationWaitCrossCoreDispatchChecked_runQueueEntryStage (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (c : Concurrency.CoreId)
    (st : SystemState) (P : SyscallArmPremises st c waiter) :
    SystemState.RunQueueEntryStage st
      (notificationWaitCrossCoreDispatchChecked ctx notificationId waiter c st).1 := by
  unfold notificationWaitCrossCoreDispatchChecked
  split
  · split
    · exact (RunQueueStage.refl _).entry
    · exact notificationWaitOnCore_runQueueEntryStage _ _ _ _ P.current P.notIdle
  · exact (RunQueueStage.refl _).entry

/-- The declassified signal: the bound signal, then the audit records, which
touch the trail alone. -/
theorem notificationSignalDeclassifiedOnCore_runQueueStage (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : Concurrency.CoreId) (st : SystemState)
    (hHeads : notificationHeadsWakeable st) (hBlk : blockedCurrentNowhere st) :
    RunQueueStage st
      (notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st).1 := by
  unfold notificationSignalDeclassifiedOnCore
  split
  · exact RunQueueStage.refl _
  split
  · split <;> exact RunQueueStage.refl _
  dsimp only
  split
  · exact RunQueueStage.refl _
  have hB := notificationSignalBoundOnCore_runQueueStage notificationId badge c st hHeads hBlk
  generalize notificationSignalBoundOnCore notificationId badge c st = r at hB
  obtain ⟨st1, res⟩ := r
  cases res with
  | error _ => exact RunQueueStage.refl _
  | ok sgi =>
    dsimp only at hB ⊢
    split
    · exact RunQueueStage.refl _
    · rename_i st2 hRec
      rw [recordDeclassifiedHops_frame _ _ _ _ _ hRec]
      exact hB.trans (RunQueueStage.of_frame rfl rfl rfl)

/-- **Every arm `dispatchWithCapChecked` routes but the yieldTo keeps the run
queues in agreement with the threads' links**, the capability-only arms it
delegates included. -/
theorem dispatchWithCapChecked_runQueueEntryStage (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st st' : SystemState)
    (P : SyscallArmPremises st executingCore tid)
    (hNY : decoded.syscallId ≠ .schedContextYieldTo)
    (h : dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), st')) :
    SystemState.RunQueueEntryStage st st' := by
  unfold dispatchWithCapChecked at h
  cases hC : dispatchCapabilityOnly decoded cap tid executingCore with
  | some k =>
    rw [hC] at h
    exact dispatchCapabilityOnly_runQueueEntryStage decoded cap tid executingCore k st st'
      P.objInv P.holders hNY hC (dispatchCapabilityOnlyChecked_ok hC h)
  | none =>
  rw [hC] at h
  dsimp only at h
  cases hId : decoded.syscallId <;> rw [hId] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.auditRead =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    rw [auditReadFromCore_frame _ _ _ _ _ _ _ hA]
    refine RunQueueStage.entry ?_
    exact writeReturnFrameToTcb_runQueueStage _ _ _
  case none.auditDrain =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    unfold auditDrainVisiblePrefix at hA
    split at hA
    · cases hA
      refine RunQueueStage.entry ?_
      refine RunQueueStage.trans ?_ (writeReturnFrameToTcb_runQueueStage _ _ _)
      exact RunQueueStage.of_frame rfl rfl rfl
    · cases hA
  all_goals
    cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.send.object epId =>
    split at h
    · cases h
    rename_i hSend
    exact clearStashStage_runQueueEntryStage
      ((runQueueStage_of_pair_eq
        (endpointSendCrossCoreDispatchChecked_runQueueEntryStage _ _ _ _ _ _ P) hSend))
      (fun x => stageWokenDelivery_runQueueStage x _ _) h
  case none.receive.object epId =>
    split at h
    · cases h
    unfold receiveResolvedArm at h
    -- WS-SX SX4: the busy reply's holder is cancelled first; the receive then
    -- runs from the cancelled state, which keeps every premise it reads.
    have hSC : SystemState.RunQueueEntryStage st
          (cancelRecvBusyReply ctx tid gate decoded executingCore st) ∧
        endpointHeadsWakeable (cancelRecvBusyReply ctx tid gate decoded executingCore st) ∧
        (cancelRecvBusyReply ctx tid gate decoded executingCore st).scheduler.currentOnCore
          executingCore = some tid ∧
        (cancelRecvBusyReply ctx tid gate decoded executingCore st).activeAt tid := by
      rcases cancelRecvBusyReply_cases ctx tid gate decoded executingCore st with e | ⟨hd, hne, e⟩ <;>
        rw [e]
      · exact ⟨(RunQueueStage.refl _).entry, P.endpointHeads, P.current, P.currentActive⟩
      · exact ⟨cancelReplyHolder_runQueueEntryStage st hd executingCore,
          cancelReplyHolder_endpointHeadsWakeable P.objInv P.dequeued
            P.toEntryPremises.queueHeadCancelFacts,
          by rw [cancelReplyHolder_currentOnCore]; exact P.current,
          cancelReplyHolder_activeAt P.objInv P.refined (Ne.symm hne) P.currentActive⟩
    obtain ⟨hS, hHC, hCurC, hActC⟩ := hSC
    obtain ⟨hIC, hRC⟩ := hS.1.links P.objInv P.refined
    have hDC := hS.2 P.objInv P.refined hRC P.dequeued
    generalize cancelRecvBusyReply ctx tid gate decoded executingCore st = stC
      at h hS hHC hCurC hActC hIC hRC hDC
    simp only at h
    split at h
    · cases h
    split at h
    · rename_i st1 dequeued summ sgi hRecv
      split at h
      · cases h
      rename_i stDon hHand
      cases h
      have E := runQueueStage_of_pair_eq
        (endpointReceiveDualWithCapsOnCore_runQueueEntryStage _ _ _ _ _ hHC
          hCurC P.notIdle hActC) hRecv
      obtain ⟨_, hR2⟩ := E.1.links hIC hRC
      exact runQueueEntryStage_trans_of_invExt hS fun _ _ => E.trans
        (((applyReceiveRendezvousHandoff_runQueueStage
            ((E.2 hIC hRC hR2 hDC).coherent _) hHand).trans
          (stageWokenSendCompletion_runQueueStage _ _)).trans
          (stageDeliveredMessage_runQueueStage _ _ _)).entry
    · cases h
  case none.call.object epId =>
    split at h
    · rename_i hCall
      cases h
      exact ((runQueueStage_of_pair_eq
        (endpointCallCrossCoreDispatchChecked_runQueueEntryStage _ _ _ _ _ _ P) hCall)).trans
        (stageWokenDelivery_runQueueStage _ _ _).entry
    · cases h
  case none.reply.replyCap rid =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact replyTransferOnCoreChecked_runQueueEntryStage P.objInv P.dequeued h
  case none.cspaceMint.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    all_goals
      unfold cspaceMintChecked at h
      dsimp only at h
      split at h
      · refine RunQueueStage.entry ?_
        exact cspaceMintWithCdt_runQueueStage h
      · cases h
  case none.cspaceCopy.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceCopyChecked at h
    dsimp only at h
    split at h
    · refine RunQueueStage.entry ?_
      exact cspaceCopy_runQueueStage h
    · cases h
  case none.cspaceMove.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceMoveChecked at h
    dsimp only at h
    split at h
    · refine RunQueueStage.entry ?_
      exact cspaceMove_runQueueStage h
    · cases h
  case none.serviceRegister.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold registerServiceChecked at h
    split at h
    · refine RunQueueStage.entry ?_
      exact registerService_runQueueStage h
    · cases h
  case none.notificationSignal.object notifId =>
    try dsimp only at h
    split at h
    · rename_i hSig
      exact clearStashStage_runQueueEntryStage (runQueueStage_of_pair_eq
        (notificationSignalBoundCrossCoreDispatchChecked_runQueueStage _ _ _ _ _ _ P.ntfnHeads
          P.blocked) hSig).entry
        (fun x => stageWokenDeliveryTwice_runQueueStage x _ _) h
    · cases h
  case none.notificationWait.object notifId =>
    split at h
    · rename_i hW
      cases h
      exact (runQueueStage_of_pair_eq
        (notificationWaitCrossCoreDispatchChecked_runQueueEntryStage _ _ _ _ _ P) hW).trans
        (writeReturnFrameToTcb_runQueueStage _ _ _).entry
    · rename_i hW
      cases h
      exact runQueueStage_of_pair_eq
        (notificationWaitCrossCoreDispatchChecked_runQueueEntryStage _ _ _ _ _ P) hW
    · cases h
  case none.replyRecv.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ stR hRR
    cases h
    exact (endpointReplyRecvOnCore_runQueueEntryStage P.objInv P.refined P.dequeued P.queueHeads
      P.current P.notIdle hRR).trans (stageDeliveredMessage_runQueueStage _ _ _).entry
  case none.declassify.object targetId =>
    unfold declassifyObjectFromCore at h
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rw [(authorizeDeclassificationOnCore_frame _ _ _ _ _ _ _ _ _ h).1]
    refine RunQueueStage.entry ?_
    exact RunQueueStage.of_frame rfl rfl rfl
  case none.declassifySignal.object notifId =>
    try dsimp only at h
    split at h
    · rename_i hSig
      exact clearStashStage_runQueueEntryStage (runQueueStage_of_pair_eq
        (notificationSignalDeclassifiedOnCore_runQueueStage _ _ _ _ _ _ P.ntfnHeads
          P.blocked) hSig).entry
        (fun x => stageWokenDeliveryTwice_runQueueStage x _ _) h
    · cases h

/-- WS-ZA ZA6.29: **every arm `dispatchWithCapChecked` routes links only the
executing core's current thread**: the yieldTo's capability-only arm links it,
and every other arm links no thread. -/
theorem dispatchWithCapChecked_runQueueEntryStageOn (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st st' : SystemState)
    (P : SyscallArmPremises st executingCore tid)
    (h : dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), st')) :
    SystemState.RunQueueEntryStageOn (SystemState.currentObjOn st executingCore) st st' := by
  by_cases hNY : decoded.syscallId = .schedContextYieldTo
  · unfold dispatchWithCapChecked at h
    cases hC : dispatchCapabilityOnly decoded cap tid executingCore with
    | some k =>
      rw [hC] at h
      exact dispatchCapabilityOnly_runQueueEntryStageOn decoded cap tid executingCore k st st'
        P.objInv P.holders hC (dispatchCapabilityOnlyChecked_ok hC h)
    | none => exact absurd hC (dispatchCapabilityOnly_yieldTo_isSome hNY)
  · exact (dispatchWithCapChecked_runQueueEntryStage ctx decoded tid executingCore gate cap st st'
      P hNY h).toOn _

/-- **The checked syscall dispatch keeps the run queues in agreement with the
threads' links**: the yield, the capability resolution (a read), the routed arm,
and the taint pass, which writes the taint table and the taint words alone.  The one premise is the
retype arm's detached target. -/
theorem dispatchSyscallChecked_runQueueEntryStage (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (st st' : SystemState)
    (P : SyscallArmPremises st executingCore tid)
    (h : dispatchSyscallChecked ctx decoded tid executingCore st = .ok ((), st')) :
    SystemState.RunQueueEntryStageOn (SystemState.currentObjOn st executingCore) st st' := by
  unfold dispatchSyscallChecked at h
  split at h
  · cases h
  by_cases hY : decoded.syscallId = .yield
  · simp only [hY, ↓reduceIte, dispatchYield] at h
    split at h
    · cases h
    · rename_i hYieldOk
      cases h
      exact (yieldOnCore_runQueueEntryStage hYieldOk (P.placeable executingCore)).toOn _
  simp only [hY, ↓reduceIte] at h
  split at h <;> try (cases h; done)
  split at h
  · cases h
  rename_i stPost hD
  cases h
  refine SystemState.RunQueueEntryStageOn.trans (st' := stPost) ?_ ((RunQueueStage.of_objectsAgreeOffTaint
    (applySyscallTaint_objectsAgreeOffTaint _ _ _) applySyscallTaint_invExt
    (by rw [applySyscallTaint_scheduler]) (by rw [applySyscallTaint_scheduler])
    (by rw [applySyscallTaint_scheduler]) (by rw [applySyscallTaint_scheduler])).entry.toOn _)
  obtain ⟨cap, -, -, hD⟩ := syscallInvokeTyped_ok _ _ _ st () stPost hD
  exact dispatchWithCapChecked_runQueueEntryStageOn ctx decoded tid executingCore _ cap _ stPost
    P hD

end SeLe4n.Kernel
