-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.MappingRecordStage.Ipc
import SeLe4n.Kernel.CNodeSlotsKept

/-!
# The reply-receive's reply step keeps every CNode

The steps of a reply-receive's reply that write no CNode at all keep every
capability a CNode holds (`CNodeSlotsKept`): each is a kind-preserving write,
and a kind-preserving write rewrites no CNode (`kindPreservingWriteAt`'s
`post.objectType ≠ .cnode`).  The reply leg (`endpointReplyOnCore`) and the
caller's answer (`replyRecvAnswerCaller`) are such steps.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The reply leg keeps every CNode**: it is the state itself, or the reply's
kind-preserving write followed by scheduler links alone. -/
theorem endpointReplyOnCore_cnodeSlotsKept {replier target : SeLe4n.ThreadId} {msg : IpcMessage}
    {executingCore : Concurrency.CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    CNodeSlotsKept st (endpointReplyOnCore replier target msg executingCore st).1 := by
  rcases endpointReplyOnCore_post_agrees replier target msg executingCore st hInv
    with h | ⟨_, r1, hS, hA⟩
  · rw [h]; exact .refl _
  · exact CNodeSlotsKept.of_kindPreservingWriteAt fun oid =>
      ((endpointReply_kindPreservingWrite _ _ _ _ _ hInv hS) oid).trans
        (hA.objects.kindPreservingAt oid)

/-- The fault reply's decoded outcome keeps every CNode: a TCB write. -/
theorem faultReplyApplyOnCore_cnodeSlotsKept (st : SystemState) (faulted : SeLe4n.ThreadId)
    (outcome : Architecture.FaultReplyOutcome) (hInv : st.objects.invExt) :
    CNodeSlotsKept st (faultReplyApplyOnCore st faulted outcome) := by
  cases outcome with
  | restart frame =>
    exact CNodeSlotsKept.of_kindPreservingWrite (applyFaultRestart_kindPreservingWrite _ _ _ hInv)
  | abandon =>
    exact CNodeSlotsKept.of_kindPreservingWrite (faultAbandonOnCore_kindPreservingWrite _ _ _ hInv)

/-- **The caller's answer keeps every CNode**: its delivered message staged, or
the fault reply's outcome applied. -/
theorem replyRecvAnswerCaller_cnodeSlotsKept (answer : Option Architecture.FaultReplyOutcome)
    (st : SystemState) (prevCaller : SeLe4n.ThreadId) (capInfo : Nat)
    (hInv : st.objects.invExt) :
    CNodeSlotsKept st (replyRecvAnswerCaller answer st prevCaller capInfo) := by
  cases answer with
  | none =>
    exact CNodeSlotsKept.of_kindPreservingWrite
      (Architecture.stageDeliveredMessage_kindPreservingWrite st prevCaller capInfo hInv)
  | some o => exact faultReplyApplyOnCore_cnodeSlotsKept st prevCaller o hInv

/-! ### The capability transfer

The transfer writes CNodes by three steps: an install into a slot it found
empty (`cspaceInsertSlot`), a derivation edge (`cdtAddChild`, links alone), and
an untyped source set full (`untypedSourceSetFull`, the source slot's own
capability, which names that untyped).  None of the three rewrites a capability
naming no untyped object. -/

namespace CNodeSlotsKept

variable {st st' : SystemState}

/-- A step whose objects agree off the derivation links keeps every CNode: a
CNode that differs only in its links has the same radix and slots. -/
theorem of_agreeOffDerivationLinks (h : SystemState.objectsAgreeOffDerivationLinks st' st) :
    CNodeSlotsKept st st' := by
  refine ⟨fun id => ?_, fun id cn hC => ?_⟩
  · rcases h id with e | ⟨_, _, ha, hb, _⟩ | ⟨_, _, ha, hb, _⟩
    · rw [e]
    · rw [ha, hb]; rfl
    · rw [ha, hb]; rfl
  · rw [SystemState.getCNode?_eq_some_iff] at hC
    obtain ⟨cn', hb, hw⟩ := (h id).cnode_fwd hC
    refine ⟨cn', (SystemState.getCNode?_eq_some_iff _ _ _).mpr hb,
      CNode.proj_eq_of_withoutLinks_eq (·.radixWidth) hw, fun s c hL => ⟨c, ?_, rfl, fun _ => rfl⟩⟩
    rw [CNode.proj_eq_of_withoutLinks_eq (·.lookup s) hw]; exact hL

/-- A write of one CNode that keeps its radix and every slot it fills, with a
capability naming the same target, the very capability when it names no
untyped object, keeps every CNode. -/
theorem of_cnodeWrite {a : SeLe4n.ObjId} {cn cn' : CNode}
    (hPre : st.objects[a]? = some (.cnode cn)) (hPost : st'.objects[a]? = some (.cnode cn'))
    (hNe : ∀ oid, oid ≠ a → st'.objects[oid]? = st.objects[oid]?)
    (hR : cn'.radixWidth = cn.radixWidth)
    (hL : ∀ s c, cn.lookup s = some c → ∃ c', cn'.lookup s = some c' ∧ c'.target = c.target ∧
      (¬ capNamesUntyped st c → c' = c)) :
    CNodeSlotsKept st st' := by
  refine ⟨fun id => ?_, fun id cn0 hC => ?_⟩
  · by_cases e : id = a
    · subst e; rw [hPre, hPost]; rfl
    · rw [hNe id e]
  · rw [SystemState.getCNode?_eq_some_iff] at hC
    by_cases e : id = a
    · subst e
      rw [hPre] at hC; cases hC
      exact ⟨cn', (SystemState.getCNode?_eq_some_iff _ _ _).mpr hPost, hR, hL⟩
    · exact ⟨cn0, (SystemState.getCNode?_eq_some_iff _ _ _).mpr ((hNe id e).trans hC), rfl,
        fun _ c h => ⟨c, h, rfl, fun _ => rfl⟩⟩

end CNodeSlotsKept

/-- **An install keeps every CNode**: it fills a slot it found empty. -/
theorem cspaceInsertSlot_cnodeSlotsKept {dst : CSpaceAddr} {cap : Capability}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : cspaceInsertSlot dst cap st = .ok ((), st')) : CNodeSlotsKept st st' := by
  obtain ⟨cn, hGet, -, hEmpty, hStore⟩ := cspaceInsertSlot_ok_decompose st st' dst cap h
  have hPre := (SystemState.getCNode?_eq_some_iff st dst.cnode cn).mp hGet
  refine CNodeSlotsKept.of_cnodeWrite hPre (storeObject_objects_eq _ _ _ _ hInv hStore)
    (fun oid hne => cspaceInsertSlot_preserves_objects_ne st st' dst cap oid hne hInv h)
    (CNode.insert_radixWidth _ _ _) (fun s c hL => ⟨c, ?_, rfl, fun _ => rfl⟩)
  have hs : dst.slot ≠ s := fun e => by subst e; rw [hEmpty] at hL; cases hL
  rw [CNode.lookup_insert_ne cn dst.slot s cap hs (CNode.slotsUnique_holds _)]; exact hL

/-- A free-index write at a slot holding a capability naming an untyped object
keeps every CNode: it rewrites that capability's free index alone, so the slot
names the same target. -/
theorem setCapFreeIndex_cnodeSlotsKept {a : CSpaceAddr} {idx : Nat} {st : SystemState}
    (hInv : st.objects.invExt)
    (hU : ∀ c, SystemState.lookupSlotCap st a = some c → capNamesUntyped st c) :
    CNodeSlotsKept st (setCapFreeIndex st a idx) := by
  cases hO : st.objects[a.cnode]? with
  | none =>
    exact .of_objects_eq (by unfold setCapFreeIndex SystemState.storeCNodeWith; rw [hO])
  | some o =>
    cases o with
    | cnode cn =>
      refine CNodeSlotsKept.of_cnodeWrite hO (setCapFreeIndex_objects_self hInv hO)
        (fun oid hne => setCapFreeIndex_objects_ne hInv hne) (CNode.setFreeIndex_radixWidth _ _ _)
        (fun s c hL => ?_)
      by_cases e : a.slot = s
      · subst e
        refine ⟨c.withFreeIndex idx, ?_, Capability.withFreeIndex_target c idx, fun hNU => ?_⟩
        · rw [CNode.lookup_setFreeIndex_self, hL]; rfl
        · refine absurd (hU c ?_) hNU
          unfold SystemState.lookupSlotCap SystemState.lookupCNode
          rw [hO]; exact hL
      · exact ⟨c, by rw [CNode.lookup_setFreeIndex_ne _ _ e]; exact hL, rfl, fun _ => rfl⟩
    | _ => exact .of_objects_eq (by unfold setCapFreeIndex SystemState.storeCNodeWith; rw [hO])

/-- **Setting a derivation's source full keeps every CNode**, when the source
slot's capability names what the derived one names: it writes only when that is
an untyped object. -/
theorem untypedSourceSetFull_cnodeSlotsKept {src : CSpaceAddr} {cap : Capability}
    {st : SystemState} (hInv : st.objects.invExt)
    (hNames : ∀ c, SystemState.lookupSlotCap st src = some c → c.target = cap.target) :
    CNodeSlotsKept st (untypedSourceSetFull st src cap) := by
  unfold untypedSourceSetFull
  cases hT : cap.target with
  | object oid =>
    dsimp only
    cases hUt : st.getUntyped? oid with
    | none => exact .refl _
    | some ut =>
      dsimp only
      exact setCapFreeIndex_cnodeSlotsKept hInv fun c hc =>
        ⟨oid, (hNames c hc).trans hT, by rw [hUt]; rfl⟩
  | _ => exact .refl _

/-- **One transfer keeps every CNode**, when the capability it derives names
what its source slot holds: the install fills an empty slot, the edge writes
links alone, and the source set full rewrites only the source's own capability,
which then names an untyped object. -/
theorem ipcTransferSingleCap_cnodeSlotsKept {cap : Capability} {srcNode : SlotRef}
    {dst : CSpaceAddr} {st st' : SystemState} (hInv : st.objects.invExt)
    (hNames : ∀ c, st.slotCapAt srcNode = some c → c.target = cap.target)
    (h : ipcTransferSingleCap cap srcNode dst st = .ok ((), st')) : CNodeSlotsKept st st' := by
  obtain ⟨_, st2, -, hSrc, -, hIns, rfl⟩ := ipcTransferSingleCap_ok_cases h
  obtain ⟨c0, hL0⟩ := Option.isSome_iff_exists.mp
    (by unfold cdtNodeIsRevocable at hSrc; exact hSrc)
  have hI2 := cspaceInsertSlot_objects_invExt hInv hIns
  have hA := SystemState.cdtAddChild_agreeObjects hI2 srcNode dst .ipcTransfer
  refine ((cspaceInsertSlot_cnodeSlotsKept hInv hIns).trans
    (CNodeSlotsKept.of_agreeOffDerivationLinks hA.1)).trans
    (untypedSourceSetFull_cnodeSlotsKept hA.2 fun c hc => ?_)
  rw [hA.1.lookupSlotCap srcNode, cspaceInsertSlot_lookupSlotCap_src hInv hL0 hIns] at hc
  cases hc
  exact hNames c0 (SystemState.slotCapAt_of_lookupSlotCap hL0)

/-- What the bundle's transfer threads: each capability to transfer names what
its source slot holds. -/
def transferCapsNameSources (caps : Array TransferCap) (s : SystemState) : Prop :=
  ∀ (i : Nat) (tc : TransferCap), caps[i]? = some tc →
    ∃ c, s.slotCapAt tc.srcSlot = some c ∧ (tc.cap.target = c.target ∧
      tc.cap.cnodeGuard = c.cnodeGuard ∧ tc.cap.cnodeGuardSize = c.cnodeGuardSize)

/-- **The transfer loop keeps every CNode**, its capabilities naming their
sources: every install does (`ipcTransferSingleCap_cnodeSlotsKept`), and keeps
the sources named (`ipcTransferSingleCap_slotTarget`). -/
theorem ipcUnwrapCaps_cnodeSlotsKept {caps : Array TransferCap}
    {endpointId : Option SeLe4n.ObjId} {rtcb : TCB} {slot? : Option CSpaceAddr}
    {st st' : SystemState} {summary : CapTransferSummary} (hInv : st.objects.invExt)
    (hNames : transferCapsNameSources caps st)
    (h : ipcUnwrapCaps caps endpointId rtcb slot? st = .ok (summary, st')) :
    CNodeSlotsKept st st' := by
  have hR := ipcUnwrapCaps_rel
    (fun a b => b.objects.invExt → transferCapsNameSources caps b →
      (a.objects.invExt ∧ transferCapsNameSources caps a) ∧ CNodeSlotsKept b a)
    (fun s hI hN => ⟨⟨hI, hN⟩, .refl s⟩)
    (fun _ _ _ h1 h2 hI hN =>
      let r := h2 hI hN
      let r' := h1 r.1.1 r.1.2
      ⟨r'.1, r.2.trans r'.2⟩)
    (fun s i b hI hN => ⟨⟨by rw [recordUnwrappedBadge_objects]; exact hI,
      fun j tc hj => by rw [recordUnwrappedBadge_slotCapAt]; exact hN j tc hj⟩,
      .of_objects_eq (recordUnwrappedBadge_objects _ _ _ _)⟩)
    (fun dst s s' tc _ ⟨i, hi⟩ hT hI hN =>
      ⟨⟨ipcTransferSingleCap_preserves_objects_invExt _ _ _ _ _ hI hT,
        fun j tc' hj => by
          obtain ⟨c, hc, hTg, hGg, hSg⟩ := hN j tc' hj
          obtain ⟨c', hc', hT', hG', hS'⟩ := ipcTransferSingleCap_slotTarget hI hT _ hc
          exact ⟨c', hc', hTg.trans hT'.symm, hGg.trans hG'.symm, hSg.trans hS'.symm⟩⟩,
       ipcTransferSingleCap_cnodeSlotsKept hI (fun c hc => by
          obtain ⟨c0, hc0, hTg, -⟩ := hN i tc hi
          rw [hc0] at hc; cases hc; exact hTg.symm) hT⟩)
    h
  exact (hR hInv hNames).2

/-- **The rendezvous transfer keeps every CNode**: it is the state itself or an
unwrap of capabilities resolved from their slots on the state it starts from,
so each names its source (`resolveExtraCaps_slot`). -/
theorem receiveTransferCaps_cnodeSlotsKept {req : Option (Capability × Array SeLe4n.CPtr)}
    {endpointId : Option SeLe4n.ObjId} {target? : Option (TCB × Option CSpaceAddr)}
    {st st' : SystemState} {summary : CapTransferSummary} (hInv : st.objects.invExt)
    (h : receiveTransferCaps req endpointId target? st = .ok (summary, st')) :
    CNodeSlotsKept st st' := by
  unfold receiveTransferCaps at h
  cases req with
  | none => cases h; exact .refl _
  | some r =>
    obtain ⟨root, addrs⟩ := r
    dsimp only at h
    by_cases hE : (resolveExtraCaps root addrs true st).isEmpty = true
    · rw [if_pos hE] at h; cases h; exact .refl _
    · rw [if_neg hE] at h
      cases target? with
      | none => cases h; exact .refl _
      | some t =>
        obtain ⟨rtcb, slot?⟩ := t
        dsimp only at h
        refine ipcUnwrapCaps_cnodeSlotsKept hInv (fun i tc hi => ?_) h
        have hL := resolveExtraCaps_slot root addrs true st tc (Array.mem_of_getElem? hi)
        exact ⟨tc.cap, SystemState.slotCapAt_of_lookupSlotCap hL, rfl, rfl, rfl⟩

/-! ### The pop -/

/-- A returned context's settle writes scheduler links alone. -/
theorem settleReturnedContext_cnodeSlotsKept (st : SystemState) (c : Concurrency.CoreId)
    (s : SeLe4n.SchedContextId) :
    CNodeSlotsKept st (SchedContextOps.settleReturnedContext st c s) :=
  CNodeSlotsKept.of_kindPreservingWrite (SystemState.objectsAgreeOffSchedulerLinks.of_releaseLinks
    (SchedContextOps.settleReturnedContext_agree st c s)).kindPreserving

/-- The pop at an unheld head keeps every CNode: its stores keep every kind. -/
theorem popUnheldReplyHead_cnodeSlotsKept {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {target : SeLe4n.ThreadId} {home : Concurrency.CoreId} (hInv : st.objects.invExt)
    (h : popUnheldReplyHead st rid target home = .ok st') : CNodeSlotsKept st st' := by
  rcases popUnheldReplyHead_objects_frame h with ⟨-, rfl⟩ | ⟨_, _, st1, -, -, hP, rfl⟩ |
      ⟨_, _, -, -, hS⟩
  · exact .refl _
  · exact (CNodeSlotsKept.of_kindPreservingWrite
      (returnUnheldSchedContext_kindPreservingWrite hInv hP)).trans
      (settleReturnedContext_cnodeSlotsKept _ _ _)
  · exact CNodeSlotsKept.of_kindPreservingWrite (severUnheldSchedContext_kindPreservingWrite hInv hS)

/-- **The reply-receive's pop keeps every CNode**: a return and its settle, a
keep, or an unheld pop, each of which keeps every kind.  Read off the pop's
discriminants, not its compiled match. -/
theorem replyRecvPopDonation_cnodeSlotsKept {rid : SeLe4n.ReplyId} {target : SeLe4n.ThreadId}
    {st st' : SystemState} {r : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)}
    (hInv : st.objects.invExt) (h : replyRecvPopDonation rid target st = .ok (r, st')) :
    CNodeSlotsKept st st' := by
  unfold replyRecvPopDonation at h
  cases hH : replyFrameHeadHolder? st rid with
  | none =>
    rw [hH] at h
    dsimp only at h
    cases hP : popUnheldReplyHead st rid target (determineTargetCore st target) with
    | error e => rw [hP] at h; cases h
    | ok s1 =>
      rw [hP] at h; dsimp only at h; cases h
      exact popUnheldReplyHead_cnodeSlotsKept hInv hP
  | some p =>
    obtain ⟨oldScId, holder⟩ := p
    rw [hH] at h
    dsimp only at h
    cases hV1 : holder.toValid? with
    | none => rw [hV1] at h; dsimp only at h; cases h
    | some v1 =>
      cases hV2 : target.toValid? with
      | none => rw [hV1, hV2] at h; dsimp only at h; cases h
      | some v2 =>
        rw [hV1, hV2] at h
        dsimp only at h
        by_cases hD : donationRecipientAcceptable st target = true
        · rw [if_pos hD] at h
          cases hRet : returnDonatedSchedContextResolved st holder oldScId target with
          | error e => rw [hRet] at h; cases h
          | ok s1 =>
            rw [hRet] at h; dsimp only at h; cases h
            obtain ⟨_, -, hR⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
            exact (CNodeSlotsKept.of_kindPreservingWrite
              (returnDonatedSchedContext_kindPreservingWrite hInv hR)).trans
              (settleReturnedContext_cnodeSlotsKept _ _ _)
        · rw [if_neg hD] at h
          cases hK : keepDonatedSchedContextResolved st holder oldScId with
          | error e => rw [hK] at h; cases h
          | ok s1 =>
            rw [hK] at h; dsimp only at h; cases h
            exact CNodeSlotsKept.of_kindPreservingWrite
              (keepDonatedSchedContextResolved_kindPreservingWrite hInv hK)

/-! ### The reply step, and the receive capability it leaves -/

/-- **The reply-receive's reply step keeps every CNode**: the reply leg, the
pop, the reply's capability transfer and the caller's answer, in the order the
composite runs them (`endpointReplyRecvAnsweringBody`), each keep every
capability a CNode holds that names no untyped object. -/
theorem replyRecvReplyStep_cnodeSlotsKept {answer : Option Architecture.FaultReplyOutcome}
    {tid prevCaller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {msg : IpcMessage}
    {executingCore : Concurrency.CoreId} {req : Option (Capability × Array SeLe4n.CPtr)}
    {target : Option (TCB × Option CSpaceAddr)} {st st1 st1q st1p : SystemState}
    {sgi : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    {returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)}
    {summary : CapTransferSummary} (hInv : st.objects.invExt)
    (hLeg : endpointReplyOnCore tid prevCaller msg executingCore st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation rid prevCaller st1 = .ok (returned?, st1q))
    (hX : receiveTransferCaps req none target st1q = .ok (summary, st1p)) :
    CNodeSlotsKept st (replyRecvAnswerCaller answer st1p prevCaller summary.capInfo) := by
  have k1 := endpointReplyOnCore_cnodeSlotsKept (replier := tid) (target := prevCaller) (msg := msg)
    (executingCore := executingCore) hInv
  have hI1 := endpointReplyOnCore_preserves_objects_invExt tid prevCaller msg executingCore st hInv
  rw [hLeg] at k1 hI1
  have hIq := replyRecvPopDonation_preserves_objects_invExt _ _ _ _ _ hI1 hPop
  have hIp := receiveTransferCaps_objects_invExt hIq hX
  exact ((k1.trans (replyRecvPopDonation_cnodeSlotsKept hI1 hPop)).trans
    (receiveTransferCaps_cnodeSlotsKept hIq hX)).trans
    (replyRecvAnswerCaller_cnodeSlotsKept answer st1p prevCaller summary.capInfo hIp)

/-- **The receive capability resolves on the post-reply state as on entry**:
a capability a reply-receive accepts names an endpoint, so over a step that
keeps every CNode it resolves to the same capability, with the same type
verdict; its rights are its own. -/
theorem replyRecvReceiveCap_of_cnodeSlotsKept {st st' : SystemState} (h : CNodeSlotsKept st st')
    (gate : SyscallGate) {cap : Capability} (hR : syscallResolveCap gate st = .ok (cap, st))
    (hA : syscallTargetAccepted .replyRecv st cap = true) :
    syscallResolveCap gate st' = .ok (cap, st') ∧ syscallTargetAccepted .replyRecv st' cap = true :=
  ⟨syscallResolveCap_of_cnodeSlotsKept h gate hR (not_capNamesUntyped_of_replyRecvAccepted hA),
    (syscallTargetAccepted_of_cnodeSlotsKept h .replyRecv cap).trans hA⟩

/-! ### The `.reply` arm's transition

A reply-receive whose receive completes a bound notification answers its caller
through the `.reply` arm's transition (`replyRecvCompletesSignalArm`): the
reply leg, the donation's pop and the priority reversion, then the reply's
capability transfer and the staged message, or the fault reply's outcome. -/

theorem descheduleAtPlacement_cnodeSlotsKept (st : SystemState) (tid : SeLe4n.ThreadId) :
    CNodeSlotsKept st (descheduleAtPlacement st tid) :=
  .of_kindPreservingWrite (descheduleAtPlacement_objectsAgreeOffRunLinks st tid).kindPreserving

theorem propagatePipChainCrossCore_cnodeSlotsKept (st : SystemState) (tid : SeLe4n.ThreadId)
    (ec : Concurrency.CoreId) (fuel : Nat) (hInv : st.objects.invExt) :
    CNodeSlotsKept st (PriorityInheritance.propagatePipChainCrossCore st tid ec fuel).1 :=
  .of_kindPreservingWrite (propagatePipChainCrossCore_kindPreservingWrite st tid ec fuel hInv)

/-- The reply's donation pop keeps every CNode. -/
theorem applyReplyDonationOnCore_cnodeSlotsKept {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {targetVtid : SeLe4n.ValidThreadId} {ownerHome : Concurrency.CoreId}
    {keep : Bool} {executingCore : Concurrency.CoreId} (hInv : st.objects.invExt)
    (h : applyReplyDonationOnCore st rid targetVtid ownerHome keep executingCore = .ok st') :
    CNodeSlotsKept st st' := by
  rcases applyReplyDonationOnCore_ok_decompose _ _ _ _ _ h with
    ⟨-, hP⟩ | ⟨_, holderVtid, _, _, -, -, hR, rfl⟩ | ⟨_, _, _, -, -, -, hK⟩
  · exact popUnheldReplyHead_cnodeSlotsKept hInv hP
  · exact ((CNodeSlotsKept.of_kindPreservingWrite
      (returnDonatedSchedContext_kindPreservingWrite hInv hR)).trans
      (settleReturnedContext_cnodeSlotsKept _ _ _)).trans
      (descheduleReturnedHolder_induct (fun a b => CNodeSlotsKept a b) keep executingCore _ _
        (.refl _) (descheduleAtPlacement_cnodeSlotsKept _ holderVtid.val))
  · exact .of_kindPreservingWrite (keepDonatedSchedContext_kindPreservingWrite hInv hK)

/-- **The cross-core reply keeps every CNode**: the reply leg, the donation's
pop and the priority reversion each keep every kind.  Read off its
discriminants. -/
theorem endpointReplyCrossCoreDispatch_cnodeSlotsKept {replier target : SeLe4n.ThreadId}
    {msg : IpcMessage} {executingCore : Concurrency.CoreId} {st : SystemState}
    (hInv : st.objects.invExt) (keep : Bool := false) :
    CNodeSlotsKept st (endpointReplyCrossCoreDispatch replier target msg executingCore st keep).1 := by
  have k1 := endpointReplyOnCore_cnodeSlotsKept (replier := replier) (target := target)
    (msg := msg) (executingCore := executingCore) hInv
  have hI1 := endpointReplyOnCore_preserves_objects_invExt replier target msg executingCore st hInv
  unfold endpointReplyCrossCoreDispatch
  cases hR : endpointReplyOnCore replier target msg executingCore st with
  | mk st1 res =>
    rw [hR] at k1 hI1
    cases res with
    | error _ => exact .refl _
    | ok sgi =>
      dsimp only
      have hDon : ∀ (rid : SeLe4n.ReplyId) (tv : SeLe4n.ValidThreadId) (s2 : SystemState),
          applyReplyDonationOnCore st1 rid tv (determineTargetCore st1 target) keep executingCore
            = .ok s2 →
          CNodeSlotsKept st s2 ∧ s2.objects.invExt := fun _ _ _ hD =>
        ⟨k1.trans (applyReplyDonationOnCore_cnodeSlotsKept hI1 hD),
          applyReplyDonationOnCore_preserves_objects_invExt _ _ _ _ _ hI1 hD⟩
      cases hS : recordedReplyServer? st target with
      | some expected =>
        dsimp only
        cases hV : SeLe4n.ThreadId.toValid? expected with
        | none => exact .refl _
        | some _ =>
          dsimp only
          cases hA : answeredReplyObject? st target with
          | none => exact k1.trans (propagatePipChainCrossCore_cnodeSlotsKept _ _ _ _ hI1)
          | some rid =>
            dsimp only
            cases hT : SeLe4n.ThreadId.toValid? target with
            | none => exact .refl _
            | some tv =>
              dsimp only
              cases hD : applyReplyDonationOnCore st1 rid tv (determineTargetCore st1 target)
                  keep executingCore with
              | error _ => exact .refl _
              | ok s2 =>
                exact (hDon rid tv s2 hD).1.trans
                  (propagatePipChainCrossCore_cnodeSlotsKept _ _ _ _ (hDon rid tv s2 hD).2)
      | none =>
        dsimp only
        cases hA : answeredReplyObject? st target with
        | none => exact k1
        | some rid =>
          dsimp only
          cases hT : SeLe4n.ThreadId.toValid? target with
          | none => exact .refl _
          | some tv =>
            dsimp only
            cases hD : applyReplyDonationOnCore st1 rid tv (determineTargetCore st1 target)
                keep executingCore with
            | error _ => exact .refl _
            | ok s2 => exact (hDon rid tv s2 hD).1

/-- The fault reply keeps every CNode: the cross-core reply, then its decoded
outcome. -/
theorem faultReplyOnCore_cnodeSlotsKept {replier faulted : SeLe4n.ThreadId} {mi : MessageInfo}
    {regs : Array SeLe4n.RegValue} {executingCore : Concurrency.CoreId} {st : SystemState}
    (hInv : st.objects.invExt) (keep : Bool := false) :
    CNodeSlotsKept st (faultReplyOnCore replier faulted mi regs executingCore st keep).1 := by
  have k1 := endpointReplyCrossCoreDispatch_cnodeSlotsKept (replier := replier)
    (target := faulted) (msg := IpcMessage.empty) (executingCore := executingCore) hInv keep
  have hI1 := endpointReplyCrossCoreDispatch_preserves_objects_invExt replier faulted
    IpcMessage.empty executingCore st hInv keep
  unfold faultReplyOnCore
  cases hT : st.getTcb? faulted with
  | none => exact .refl _
  | some tcb =>
    dsimp only
    cases hF : tcb.pendingFault with
    | none => exact .refl _
    | some tf =>
      dsimp only
      cases hR : endpointReplyCrossCoreDispatch replier faulted IpcMessage.empty executingCore st
          keep with
      | mk s1 res =>
        rw [hR] at k1 hI1
        cases res with
        | error _ => exact .refl _
        | ok _ => exact k1.trans (faultReplyApplyOnCore_cnodeSlotsKept s1 faulted _ hI1)

/-- **The `.reply` arm's transition keeps every CNode**: the fault reply, or the
cross-core reply, the reply's capability transfer and the staged message. -/
theorem replyTransferOnCoreChecked_cnodeSlotsKept {ctx : LabelingContext}
    {replier callerTid : SeLe4n.ThreadId} {mi : MessageInfo} {regs : Array SeLe4n.RegValue}
    {msg : IpcMessage} {grant : Bool} {executingCore : Concurrency.CoreId} {st st' : SystemState}
    {keep : Bool} (hInv : st.objects.invExt)
    (h : replyTransferOnCoreChecked ctx replier callerTid mi regs msg grant executingCore st keep
      = .ok ((), st')) :
    CNodeSlotsKept st st' := by
  unfold replyTransferOnCoreChecked at h
  by_cases hF : threadHasPendingFault st callerTid = true
  · rw [if_pos hF] at h
    have k := faultReplyOnCore_cnodeSlotsKept (replier := replier) (faulted := callerTid)
      (mi := mi) (regs := regs) (executingCore := executingCore) hInv keep
    cases hR : faultReplyOnCore replier callerTid mi regs executingCore st keep with
    | mk s res =>
      rw [hR] at h k
      cases res with
      | error _ => cases h
      | ok _ => cases h; exact k
  · rw [if_neg hF] at h
    unfold endpointReplyCrossCoreDispatchChecked at h
    by_cases hFl : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf callerTid) = true
    · rw [if_pos hFl] at h
      have k := endpointReplyCrossCoreDispatch_cnodeSlotsKept (replier := replier)
        (target := callerTid) (msg := msg) (executingCore := executingCore) hInv keep
      have hI := endpointReplyCrossCoreDispatch_preserves_objects_invExt replier callerTid msg
        executingCore st hInv keep
      cases hR : endpointReplyCrossCoreDispatch replier callerTid msg executingCore st keep with
      | mk s res =>
        rw [hR] at h k hI
        cases res with
        | error _ => cases h
        | ok _ =>
          dsimp only at h
          cases hX : replyTransferCaps st replier callerTid grant s with
          | error _ => rw [hX] at h; cases h
          | ok p =>
            obtain ⟨summary, sX⟩ := p
            rw [hX] at h
            cases h
            exact (k.trans (receiveTransferCaps_cnodeSlotsKept hI hX)).trans
              (CNodeSlotsKept.of_kindPreservingWrite
                (Architecture.stageDeliveredMessage_kindPreservingWrite sX callerTid summary.capInfo
                  (receiveTransferCaps_objects_invExt hI hX)))
    · rw [if_neg hFl] at h; cases h

/-! ### The receive legs (WS-SX SX36.1)

A reply-receive whose receive capability looks up after its reply runs the
receive legs on the answered state; they keep every CNode too, so a lookup that
resolved before them resolves after. -/

/-- **The receive leg keeps every CNode**: the state itself, or the receive's
kind-preserving write followed by scheduler links alone. -/
theorem endpointReceiveDualOnCore_cnodeSlotsKept {endpointId : SeLe4n.ObjId}
    {receiver : SeLe4n.ThreadId} {replyId : Option SeLe4n.ReplyId}
    {executingCore : Concurrency.CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    CNodeSlotsKept st (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1 := by
  rcases endpointReceiveDualOnCore_post_agrees endpointId receiver replyId executingCore st hInv
    with h | ⟨_, r1, hS, hA⟩
  · rw [h]; exact .refl _
  · exact CNodeSlotsKept.of_kindPreservingWriteAt fun oid =>
      ((endpointReceiveDual_kindPreservingWrite _ _ _ _ _ _ hInv hS) oid).trans
        (hA.objects.kindPreservingAt oid)

/-- **The capability-carrying receive leg keeps every CNode**: the receive leg,
then the rendezvous transfer (`receiveTransferCaps_cnodeSlotsKept`). -/
theorem endpointReceiveDualWithCapsOnCore_cnodeSlotsKept {endpointId : SeLe4n.ObjId}
    {receiver : SeLe4n.ThreadId} {replyId : Option SeLe4n.ReplyId}
    {executingCore : Concurrency.CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    CNodeSlotsKept st
      (endpointReceiveDualWithCapsOnCore endpointId receiver replyId executingCore st).1 := by
  unfold endpointReceiveDualWithCapsOnCore
  have hRcv := endpointReceiveDualOnCore_cnodeSlotsKept (endpointId := endpointId)
    (receiver := receiver) (replyId := replyId) (executingCore := executingCore) hInv
  have hI1 := endpointReceiveDualOnCore_preserves_objects_invExt endpointId receiver replyId
    executingCore st hInv
  generalize endpointReceiveDualOnCore endpointId receiver replyId executingCore st = r at hRcv hI1
  obtain ⟨st1, res⟩ := r
  dsimp only at hRcv hI1 ⊢
  cases res with
  | error _ => exact hRcv
  | ok p =>
    obtain ⟨senderId, sgi⟩ := p
    dsimp only
    repeat' split
    all_goals first
      | exact hRcv
      | (rename_i hU; exact hRcv.trans (receiveTransferCaps_cnodeSlotsKept hI1 hU))

/-- **The receive's return of a bound notification's context keeps every
CNode**: it rewrites the receiver's TCB and the context alone
(`receiveReturnSchedContext_objects`), neither a CNode. -/
theorem receiveReturnSchedContext_cnodeSlotsKept (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    CNodeSlotsKept st (receiveReturnSchedContext blocks st tid) := by
  refine ⟨fun id => ?_, fun id cn hC => ⟨cn, ?_, rfl, fun _ c hL => ⟨c, hL, rfl, fun _ => rfl⟩⟩⟩
  · rcases receiveReturnSchedContext_objects blocks st tid hInv id with
      e | ⟨tcb, hp, hq⟩ | ⟨sc, sc', hp, hq⟩
    · rw [e]
    · rw [hp, hq]; rfl
    · rw [hp, hq]; rfl
  · rw [SystemState.getCNode?_eq_some_iff] at hC ⊢
    rcases receiveReturnSchedContext_objects blocks st tid hInv id with
      e | ⟨tcb, hp, -⟩ | ⟨sc, sc', hp, -⟩
    · rw [e]; exact hC
    · rw [hC] at hp; cases hp
    · rw [hC] at hp; cases hp

end SeLe4n.Kernel
