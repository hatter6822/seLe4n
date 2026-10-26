-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.CancelAllReachability
import SeLe4n.Kernel.IPC.Invariant.CancelAllPreservation

/-!
# The reachable state along the whole delete chain

STATUS: staged for WS-ZA ZA5.4 part 29: the reachable state (`ipcReachable`)
is carried, with the bundle the delete carries (`finalisingDeleteBundle`),
along every step of a final delete: the slot delete, the page teardown, the
finalisation, the retire, a thread slot's set, the space change, and the
revocation and zombie loops.  Staged because `ipcReachable` lives in the
staged `Reachability` module; it moves to production with it.

Beyond the IPC bundle, the store's invariant and the budgets — which the bundle
the delete carries already holds — the reachable state reads the notification
queues, the donation chains, the run-queue agreement and the reply-waiter
queues.  The slot delete, the derivation-link writes, the page teardown and a
thread slot's copy write none of what those read (`ReachLinkFrame`); the
finalisation and the retire keep them on their own
(`finaliseFinalObject_preserves_ipcReachable`,
`retireFinalObject_preserves_ipcReachable`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

-- ============================================================================
-- §1  What the reachable state reads beyond the bundle
-- ============================================================================

/-- **What the queue invariants of the reachable state read of an object**: a
thread's IPC state, notification links, reply view and run-queue entry; a
notification; a reply; a scheduling context's reply-stack head. -/
inductive ReachLinkView where
  | tcb (ipc : ThreadIpcState) (ntfnPrev ntfnNext : Option SeLe4n.ThreadId)
      (reply : ReplyView) (runCore : Nat) (runLink : RunQueueLink)
  | notification (n : Notification)
  | reply (r : Reply)
  | schedContext (head : Option SeLe4n.ReplyId)

/-- The view of one slot of the store. -/
def reachLinkViewOf : Option KernelObject → Option ReachLinkView
  | some (.tcb t) => some (.tcb t.ipcState t.ntfnPrev t.ntfnNext t.replyView t.runCoreCode
      (TCB.runLink t))
  | some (.notification n) => some (.notification n)
  | some (.reply r) => some (.reply r)
  | some (.schedContext sc) => some (.schedContext sc.scReply)
  | _ => none

/-- **A step that writes nothing the queue invariants read**: every key keeps
its view, and the scheduler is untouched. -/
structure ReachLinkFrame (st st' : SystemState) : Prop where
  view : ∀ oid : SeLe4n.ObjId, reachLinkViewOf st'.objects[oid]? = reachLinkViewOf st.objects[oid]?
  scheduler : st'.scheduler = st.scheduler

/-- **The queue invariants of the reachable state**: what it reads beyond the
IPC bundle, the store's invariant and the budgets. -/
def reachQueueInvariant (st : SystemState) : Prop :=
  notificationWaiterConsistent st ∧ donationChainWellFormed st ∧ st.runQueueRefined ∧
    st.replyWaitersConsistent

namespace ReachLinkFrame

theorem refl (st : SystemState) : ReachLinkFrame st st := ⟨fun _ => rfl, rfl⟩

theorem trans {a b c : SystemState} (h₁ : ReachLinkFrame a b) (h₂ : ReachLinkFrame b c) :
    ReachLinkFrame a c :=
  ⟨fun o => (h₂.view o).trans (h₁.view o), h₂.scheduler.trans h₁.scheduler⟩

end ReachLinkFrame

-- ============================================================================
-- §2  The frame keeps the queue invariants
-- ============================================================================

theorem reachLinkViewOf_eq_tcb {o : Option KernelObject} {a : ThreadIpcState}
    {b c : Option SeLe4n.ThreadId} {d : ReplyView} {e : Nat} {f : RunQueueLink}
    (h : reachLinkViewOf o = some (.tcb a b c d e f)) :
    ∃ t, o = some (.tcb t) ∧ t.ipcState = a ∧ t.ntfnPrev = b ∧ t.ntfnNext = c ∧
      t.replyView = d ∧ t.runCoreCode = e ∧ TCB.runLink t = f := by
  rcases o with _ | ⟨t | _ | _ | _ | _ | _ | _ | _ | _ | _⟩ <;>
    simp only [reachLinkViewOf, reduceCtorEq, Option.some.injEq, ReachLinkView.tcb.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨t, rfl, h1, h2, h3, h4, h5, h6⟩

theorem reachLinkViewOf_eq_notification {o : Option KernelObject} {n : Notification}
    (h : reachLinkViewOf o = some (.notification n)) : o = some (.notification n) := by
  rcases o with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _⟩ <;>
    simp only [reachLinkViewOf, reduceCtorEq, Option.some.injEq,
      ReachLinkView.notification.injEq] at h
  rw [h]

theorem reachLinkViewOf_eq_reply {o : Option KernelObject} {r : Reply}
    (h : reachLinkViewOf o = some (.reply r)) : o = some (.reply r) := by
  rcases o with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _⟩ <;>
    simp only [reachLinkViewOf, reduceCtorEq, Option.some.injEq, ReachLinkView.reply.injEq] at h
  rw [h]

/-- The reply-stack links of a slot, read off its view. -/
theorem replyStackLinks?_of_view (o : Option KernelObject) :
    replyStackLinks? o = (reachLinkViewOf o).bind fun
      | .reply r => some (r.prev, r.next)
      | _ => none := by
  rcases o with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _⟩ <;> rfl

/-- A scheduling context's reply-stack head, read off its view. -/
theorem schedContextStackHead?_of_view (o : Option KernelObject) :
    schedContextStackHead? o = (reachLinkViewOf o).bind fun
      | .schedContext h => some h
      | _ => none := by
  rcases o with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _⟩ <;> rfl

/-- A thread's reply view, read off its slot's view. -/
theorem objReplyView_of_view (o : Option KernelObject) :
    objReplyView o = (reachLinkViewOf o).bind fun
      | .tcb _ _ _ r _ _ => some r
      | _ => none := by
  rcases o with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _⟩ <;> rfl

namespace ReachLinkFrame

variable {st st' : SystemState}

theorem tcb_fwd (F : ReachLinkFrame st st') {k : SeLe4n.ObjId} {ty : TCB}
    (h : st.objects[k]? = some (.tcb ty)) :
    ∃ tx, st'.objects[k]? = some (.tcb tx) ∧ tx.ipcState = ty.ipcState ∧
      tx.ntfnPrev = ty.ntfnPrev ∧ tx.ntfnNext = ty.ntfnNext ∧ tx.replyView = ty.replyView ∧
      tx.runCoreCode = ty.runCoreCode ∧ TCB.runLink tx = TCB.runLink ty :=
  reachLinkViewOf_eq_tcb ((F.view k).trans (by rw [h]; rfl))

theorem tcb_bwd (F : ReachLinkFrame st st') {k : SeLe4n.ObjId} {tx : TCB}
    (h : st'.objects[k]? = some (.tcb tx)) :
    ∃ ty, st.objects[k]? = some (.tcb ty) ∧ ty.ipcState = tx.ipcState ∧
      ty.ntfnPrev = tx.ntfnPrev ∧ ty.ntfnNext = tx.ntfnNext ∧ ty.replyView = tx.replyView ∧
      ty.runCoreCode = tx.runCoreCode ∧ TCB.runLink ty = TCB.runLink tx :=
  reachLinkViewOf_eq_tcb ((F.view k).symm.trans (by rw [h]; rfl))

theorem runLinkOn (F : ReachLinkFrame st st') (c : CoreId) (t : SeLe4n.ThreadId) :
    st'.runLinkOn c t = st.runLinkOn c t := by
  unfold SystemState.runLinkOn
  cases hG : st.getTcb? t with
  | some ty =>
    obtain ⟨tx, hx, -, -, -, -, hC, hL⟩ :=
      F.tcb_fwd ((SystemState.getTcb?_eq_some_iff _ _ _).mp hG)
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hx]
    show TCB.runLinkOn tx c = TCB.runLinkOn ty c
    unfold TCB.runLinkOn; rw [hC, hL]
  | none =>
    cases hG' : st'.getTcb? t with
    | none => rfl
    | some tx =>
      obtain ⟨ty, hy, -⟩ := F.tcb_bwd ((SystemState.getTcb?_eq_some_iff _ _ _).mp hG')
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hy] at hG; cases hG

theorem replyViews (F : ReachLinkFrame st st') : st'.replyViews = st.replyViews := by
  funext k
  unfold SystemState.replyViews
  simp only [SystemState.getObject?_eq_getElem]
  rw [objReplyView_of_view, objReplyView_of_view, F.view k]

theorem donationChainFrame (F : ReachLinkFrame st st') :
    SeLe4n.Kernel.donationChainFrame st st' :=
  ⟨fun oid => by rw [replyStackLinks?_of_view, replyStackLinks?_of_view, F.view oid],
   fun oid => by rw [schedContextStackHead?_of_view, schedContextStackHead?_of_view, F.view oid],
   fun oid r' hR hC => ⟨r', reachLinkViewOf_eq_reply ((F.view oid).symm.trans (by rw [hR]; rfl)),
     hC⟩⟩

/-- **The frame keeps every queue invariant of the reachable state.** -/
theorem preserves (F : ReachLinkFrame st st') (h : reachQueueInvariant st) :
    reachQueueInvariant st' := by
  obtain ⟨hN, hD, hR, hW⟩ := h
  refine ⟨notificationWaiterConsistent_of_tcbLinkFrame hN
      (fun k n hn => reachLinkViewOf_eq_notification ((F.view k).symm.trans (by rw [hn]; rfl)))
      (fun k n hn => reachLinkViewOf_eq_notification ((F.view k).trans (by rw [hn]; rfl)))
      (fun k ty hy => let ⟨tx, hx, h1, h2, h3, _⟩ := F.tcb_fwd hy; ⟨tx, hx, h1, h2, h3⟩)
      (fun k tx hx => let ⟨ty, hy, h1, h2, h3, _⟩ := F.tcb_bwd hx;
        ⟨ty, hy, h1.symm, h2.symm, h3.symm⟩),
    donationChainWellFormed_of_frame F.donationChainFrame hD,
    SystemState.runQueueRefined_of_frame (fun c t => F.runLinkOn c t)
      (by rw [F.scheduler]) (by rw [F.scheduler]) hR,
    SystemState.replyWaitersConsistent.of_views F.replyViews hW⟩

end ReachLinkFrame

-- ============================================================================
-- §3  The steps of the delete that write nothing the queues read
-- ============================================================================

theorem reachLinkViewOf_withoutLinks (o : KernelObject) :
    reachLinkViewOf (some o.withoutLinks) = reachLinkViewOf (some o) := by
  cases o <;> rfl

namespace ReachLinkFrame

/-- A step that writes no object and leaves the scheduler untouched. -/
theorem of_objects_eq {st st' : SystemState} (hO : st'.objects = st.objects)
    (hS : st'.scheduler = st.scheduler) : ReachLinkFrame st st' :=
  ⟨fun _ => by rw [hO], hS⟩

/-- A step that writes derivation links alone. -/
theorem of_agreeOffDerivationLinks {st st' : SystemState}
    (hA : SystemState.objectsAgreeOffDerivationLinks st' st)
    (hS : st'.scheduler = st.scheduler) : ReachLinkFrame st st' :=
  ⟨fun o => proj_eq_of_map_eq _ _ reachLinkViewOf_withoutLinks (hA o).map_withoutLinks, hS⟩

/-- An insert that keeps its key's view. -/
theorem of_insert {st : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hV : reachLinkViewOf (some o) = reachLinkViewOf st.objects[k]?) :
    ReachLinkFrame st { st with objects := st.objects.insert k o } :=
  ⟨proj_insert_eq _ hInv hV, rfl⟩

/-- A store that keeps its key's view. -/
theorem storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hS : SeLe4n.Model.storeObject k o st = .ok ((), st'))
    (hV : reachLinkViewOf (some o) = reachLinkViewOf st.objects[k]?) : ReachLinkFrame st st' := by
  refine ⟨fun oid => ?_, storeObject_scheduler_eq st st' k o hS⟩
  by_cases h : oid = k
  · subst h; rw [storeObject_objects_eq st st' oid o hInv hS]; exact hV
  · rw [storeObject_objects_ne st st' k oid o h hInv hS]

/-- A thread rewritten in its slot keeping its view. -/
theorem updateTcb (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt)
    (hf : ∀ x, reachLinkViewOf (some (.tcb (f x))) = reachLinkViewOf (some (.tcb x))) :
    ReachLinkFrame st (st.updateTcb t f) := by
  cases hG : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hG]; exact .refl st
  | some x =>
    rw [SystemState.updateTcb_eq_of_some hG]
    exact of_insert hInv (by rw [(SystemState.getTcb?_eq_some_iff st t x).mp hG]; exact hf x)

/-- A run of slot-link writes. -/
theorem linkReach {st₀ st : SystemState} (h : SystemState.linkReach st₀ st)
    (hInv : st₀.objects.invExt) : ReachLinkFrame st₀ st :=
  of_agreeOffDerivationLinks (h.agree hInv) (by rw [h.fields])

/-- A derivation edge. -/
theorem cdtAddChild (st : SystemState) (p c : SlotRef) (op : DerivationOp)
    (hInv : st.objects.invExt) : ReachLinkFrame st (st.cdtAddChild p c op) :=
  (of_objects_eq (st := st) (st' := { st with cdt := st.cdt.addEdge p c op }) rfl rfl).trans
    (linkReach (SystemState.cdtAddChild_reach st p c op) hInv)

/-- The splice of a deleted slot out of the derivation tree. -/
theorem spliceDeletedCdtNode (st : SystemState) (ref : SlotRef) (hInv : st.objects.invExt) :
    ReachLinkFrame st (SeLe4n.Kernel.spliceDeletedCdtNode st ref) :=
  of_agreeOffDerivationLinks (spliceDeletedCdtNode_agree hInv ref).1
    (spliceDeletedCdtNode_scheduler st ref)

/-- `.cspaceDelete`: the core delete empties one slot of a CNode or a thread,
which keeps every view, and the splice writes links alone. -/
theorem cspaceDeleteSlot {st st' : SystemState} {addr : CSpaceAddr} (hInv : st.objects.invExt)
    (hStep : SeLe4n.Kernel.cspaceDeleteSlot addr st = .ok ((), st')) : ReachLinkFrame st st' := by
  obtain ⟨stC, hCore, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' hStep
  refine trans ?_ (spliceDeletedCdtNode stC addr (cspaceDeleteSlotCore_invExt _ _ _ hInv hCore))
  rcases cspaceDeleteSlotCore_ok_cases hCore with ⟨cn, hO, hS⟩ | ⟨t, hO, hS⟩
  · exact storeObject hInv hS (by rw [hO]; rfl)
  · exact storeObject hInv hS (by rw [hO]; rfl)

/-- The page teardown after a final delete writes VSpace roots alone. -/
theorem finaliseDestroyedCapabilities {ec : CoreId} {named : List SeLe4n.ObjId}
    {pages : List MappedPage} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.finaliseDestroyedCapabilities ec named pages st = .ok ((), st')) :
    ReachLinkFrame st st' := by
  have hF := finaliseDestroyedCapabilities_ok_frame ec named pages st st' hInv h
  refine ⟨fun oid => ?_, hF.2.2⟩
  rcases hF.2.1 oid with e | ⟨⟨r, hr⟩, ⟨r', hr'⟩⟩
  · rw [e]
  · rw [hr, hr']; rfl

/-- A thread slot's copy: the slot's delete, the insert of the copied capability
into the thread's space slot, and the derivation edge. -/
theorem threadSlotCopied {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hInv : st.objects.invExt) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    ReachLinkFrame st (SeLe4n.Kernel.threadSlotCopied st tid slot srcCNode srcSlot rights) := by
  have hD := cspaceDeleteSlot hInv (copyIntoThreadSlot_delete hT slot)
  obtain ⟨-, hI⟩ := threadSlotDeleted_tcb hInv hT slot
  rcases threadSlotCopied_cases st tid slot srcCNode srcSlot rights with ⟨-, e⟩ | ⟨cap, -, e⟩
  · rw [e]; exact hD
  · rw [e]
    have hU := SystemState.updateTcb_preserves_objects_invExt _ tid
      (·.insertSpaceCap slot (TCB.spaceCopyOf cap rights)) hI
    exact hD.trans ((updateTcb _ tid (·.insertSpaceCap slot (TCB.spaceCopyOf cap rights)) hI
      fun _ => rfl).trans (cdtAddChild _ _ _ _ hU))

end ReachLinkFrame

-- ============================================================================
-- §4  The reachable state along the delete chain
-- ============================================================================

/-- **The reachable state and the bundle the delete carries**, together: what
every step of a final delete keeps. -/
def reachableDeleteBundle (s : SystemState) : Prop :=
  ipcReachable s ∧ finalisingDeleteBundle s

/-- The reachable state, from the bundle the delete carries and the queues. -/
theorem ipcReachable_of_bundle {s : SystemState} (h : finalisingDeleteBundle s)
    (hQ : reachQueueInvariant s) : ipcReachable s :=
  ⟨h.1.1, h.1.2.1, h.2.budgets, hQ⟩

theorem ipcReachable.reachQueueInvariant {s : SystemState} (h : ipcReachable s) :
    reachQueueInvariant s := h.2.2.2

/-- **The finalisation keeps the reachable state and the bundle.** -/
theorem finaliseFinalObject_preserves_reachableDeleteBundle (target : Nat) (st : SystemState)
    (h : reachableDeleteBundle st) : reachableDeleteBundle (finaliseFinalObject target st) :=
  ⟨finaliseFinalObject_preserves_ipcReachable target h.1 h.2.1.2.2,
    finaliseFinalObject_preserves_finalisingDeleteBundle target st h.2⟩

/-- **The retire after the finalisation keeps the reachable state and the
bundle.** -/
theorem retireFinalisedObject_preserves_reachableDeleteBundle (ec : CoreId)
    (target recorder : Nat) (st : SystemState) (h : reachableDeleteBundle st) :
    reachableDeleteBundle (retireFinalisedObject ec target recorder st) :=
  ⟨retireFinalisedObject_preserves_ipcReachable ec target recorder h.1 h.2.1.2.2,
    retireFinalisedObject_preserves_finalisingDeleteBundle ec target recorder st h.2⟩

/-- **The slot delete and the page teardown keep the reachable state and the
bundle**: the bundle by its own theorem, the queues by the frame. -/
theorem cspaceDeleteSlotTeardown_preserves_reachableDeleteBundle {ec : CoreId}
    {addr : CSpaceAddr} {named : List SeLe4n.ObjId} {pages : List MappedPage}
    {st st1 st2 : SystemState} (h : reachableDeleteBundle st)
    (hD : cspaceDeleteSlot addr st = .ok ((), st1))
    (hF : finaliseDestroyedCapabilities ec named pages st1 = .ok ((), st2)) :
    reachableDeleteBundle st2 := by
  have hB := cspaceDeleteSlotTeardown_preserves_finalisingDeleteBundle h.2 hD hF
  have hI1 := cspaceDeleteSlot_preserves_objects_invExt st st1 addr h.2.1.2.1 hD
  exact ⟨ipcReachable_of_bundle hB (((ReachLinkFrame.cspaceDeleteSlot h.2.1.2.1 hD).trans
    (ReachLinkFrame.finaliseDestroyedCapabilities hI1 hF)).preserves h.1.reachQueueInvariant), hB⟩

/-- `.cspaceDelete`: **the finalising delete keeps the reachable state and the
bundle** — the slot delete's and the teardown's, then the finalisation's and
the retire's. -/
theorem cspaceDeleteSlotFinalising_preserves_reachableDeleteBundle (ec : CoreId)
    (addr : CSpaceAddr) (st st' : SystemState) (h : reachableDeleteBundle st)
    (hStep : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    reachableDeleteBundle st' := by
  obtain ⟨st1, st2, hD, hF, rfl⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' hStep
  exact retireFinalisedObject_preserves_reachableDeleteBundle ec _ _ st2
    (cspaceDeleteSlotTeardown_preserves_reachableDeleteBundle h hD hF)

/-- `.cspaceRevoke`: **the finalising revocation keeps the reachable state and
the bundle** — through every delete it runs and every finalisation. -/
theorem cspaceRevokeCdtFinalising_preserves_reachableDeleteBundle (ec : CoreId)
    (addr : CSpaceAddr) (st st' : SystemState) (h : reachableDeleteBundle st)
    (hStep : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    reachableDeleteBundle st' :=
  cspaceRevokeCdtFinalising_closed reachableDeleteBundle
    (fun c s s' hQ hD => cspaceDeleteSlotFinalising_preserves_reachableDeleteBundle ec c s s' hQ hD)
    (fun d s hQ => finaliseFinalObject_preserves_reachableDeleteBundle d s hQ)
    h hStep

/-- `.cspaceDelete`: **the zombie delete keeps the reachable state and the
bundle** — a chain of finalising deletes and finalisations. -/
theorem cspaceDeleteSlotZombie_preserves_reachableDeleteBundle (ec : CoreId)
    (addr : CSpaceAddr) (st st' : SystemState) (h : reachableDeleteBundle st)
    (hStep : cspaceDeleteSlotZombie ec addr st = .ok ((), st')) :
    reachableDeleteBundle st' :=
  cspaceDeleteSlotZombie_closed reachableDeleteBundle
    (fun c s s' hQ hD => cspaceDeleteSlotFinalising_preserves_reachableDeleteBundle ec c s s' hQ hD)
    (fun d s hQ => finaliseFinalObject_preserves_reachableDeleteBundle d s hQ)
    h hStep

-- ============================================================================
-- §5  The set-space copy
-- ============================================================================

/-- **A thread slot's copy keeps the reachable state**: the IPC bundle by its
own theorem, the budgets by the scheduling-link frame, the queues by this
module's frame. -/
theorem threadSlotCopied_preserves_ipcReachable {st : SystemState} {tid : SeLe4n.ThreadId}
    {t : TCB} (h : ipcReachable st) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    ipcReachable (threadSlotCopied st tid slot srcCNode srcSlot rights) :=
  ⟨threadSlotCopied_preserves_ipcInvariantFull h.objects_invExt h.ipcInvariantFull hT slot
      srcCNode srcSlot rights,
    (threadSlotCopied_tcb h.objects_invExt hT slot srcCNode srcSlot rights).2,
    allTimeoutBudgetsNone_of_aux (SchedLinkFrame.threadSlotCopied h.objects_invExt hT slot
      srcCNode srcSlot rights).aux h.allTimeoutBudgetsNone,
    (ReachLinkFrame.threadSlotCopied h.objects_invExt hT slot srcCNode srcSlot rights).preserves
      h.reachQueueInvariant⟩

/-- **A thread space slot's set keeps the reachable state**: the copy, then the
retire after it. -/
theorem threadSlotSet_preserves_ipcReachable (ec : CoreId) {st : SystemState}
    {tid : SeLe4n.ThreadId} {t : TCB} (h : ipcReachable st) (hT : st.getTcb? tid = some t)
    (slot : SeLe4n.Slot) (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (rights : AccessRightSet) :
    ipcReachable (threadSlotSet ec st tid slot srcCNode srcSlot rights) := by
  unfold threadSlotSet
  exact retireFinalObject_preserves_ipcReachable ec _ _
    (threadSlotCopied_preserves_ipcReachable h hT slot srcCNode srcSlot rights)

/-- **A space change keeps the reachable state** — each slot set does. -/
theorem copyThreadSpaces_preserves_ipcReachable (ec : CoreId) {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr} (h : ipcReachable st)
    (hStep : copyThreadSpaces ec st vtid cnSrc vrSrc = .ok st') : ipcReachable st' := by
  obtain ⟨tcb, hT, -, -, hCn, -, rfl⟩ := copyThreadSpaces_ok hStep
  obtain ⟨cnCap, -, hCL, -⟩ := cspaceRootSourceAdmitted_spec hCn
  obtain ⟨t1, hT1'⟩ := Option.isSome_iff_exists.mp
    (threadSlotSet_getTcb? ec h.objects_invExt hT (slot := TCB.cspaceRootSlot) (by decide)
      cnSrc.cnode cnSrc.slot TCB.cspaceRootRights hCL)
  exact threadSlotSet_preserves_ipcReachable ec
    (threadSlotSet_preserves_ipcReachable ec h hT _ _ _ _) hT1' _ _ _ _

/-- `.tcbSetSpace` through the zombie delete: **the loop's passes keep the
reachable state and the bundle, and the space change after them keeps the
reachable state and the scheduling links.** -/
theorem copyThreadSpacesZombie_preserves_ipcReachable (ec : CoreId) {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr} (h : reachableDeleteBundle st)
    (hStep : copyThreadSpacesZombie ec st vtid cnSrc vrSrc = .ok st') :
    ipcReachable st' ∧ schedContextLinkInvariant st' := by
  have hChain : ∀ n s, ZombieRun ec n st s → reachableDeleteBundle s := fun _ _ hR =>
    hR.chain.closed reachableDeleteBundle
      (fun c s s' hQ hD => cspaceDeleteSlotFinalising_preserves_reachableDeleteBundle ec c s s' hQ hD)
      (fun d s hQ => finaliseFinalObject_preserves_reachableDeleteBundle d s hQ) h
  have step : ∀ s, reachableDeleteBundle s → copyThreadSpaces ec s vtid cnSrc vrSrc = .ok st' →
      ipcReachable st' ∧ schedContextLinkInvariant st' := fun s hs hC =>
    ⟨copyThreadSpaces_preserves_ipcReachable ec hs.1 hC,
      copyThreadSpaces_preserves_schedContextLinkInvariant ec hs.1.objects_invExt hs.2.2 hC⟩
  rcases copyThreadSpacesZombie_cases hStep with h1 | ⟨n, s, hR, rfl | h2⟩
  · exact step st h h1
  · exact ⟨(hChain n _ hR).1, (hChain n _ hR).2.2⟩
  · exact step s (hChain n s hR) h2

end SeLe4n.Kernel
