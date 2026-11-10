/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.SavedRegistersCallReply
import SeLe4n.Kernel.Architecture.TaintWordFrame

/-!
# The saved-register census over the whole syscall dispatch

WS-ZA ZA6.26.  The census from the routed arms to the ABI dispatch: no syscall
writes the saved registers of a thread another core holds current or resident
(`syscallDispatchFromAbi_savedRegsKeptOffCore`).  It is the remote stall's rule
(ZA6.11): an arm that wrote such a thread's saved context would let the stall's
save, or the other core's next restore, lose that write.

* **Every routed arm** (`dispatchWithCapChecked_savedRegsKeptOffCore`): the
  capability-only arms (`dispatchCapabilityOnly_savedRegsKeptOffCore`); the IPC
  and notification arms (`*Arm_savedRegsWrittenFree`); the CSpace mint, copy
  and move, which write CNodes, a thread's space slots and the derivation tree
  (`cspaceMintWithCdt_savedRegsKept`, `cspaceCopy_savedRegsKept`,
  `cspaceMove_savedRegsKept`); the registry, the declassification and the
  audit read and drain, which write an endpoint's service record, the audit
  trail and the caller's return frame.
* **The yield** writes the caller alone: its charge writes a time slice, a
  scheduling context, the release queue, run-queue links and flags and moves
  no current thread, so the scheduling point saves the caller
  (`yieldOnCore_savedRegsWrittenFree`).
* **The taint pass** writes taint words alone
  (`savedRegsKeptExcept.of_objectsAgreeOffTaint`).
* **The ABI dispatch** spills the arguments into the caller, then runs the
  checked entry, whose premises the register-only spill keeps, or delivers a
  capability fault to the handler endpoint's receive head, blocked at the
  entry's start, or records a refusal.

Each composition closes with the step's own coverage frames (`stepCovers`).
The census is stated over the specification functions; the compiled forms are
proven equal to them.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-! ### The CSpace arms -/

/-- **The core delete** clears a slot in a CNode or in a thread's space slots;
the thread keeps its registers. -/
theorem cspaceDeleteSlotCore_savedRegsKept {st st' : SystemState} {addr : CSpaceAddr}
    (hInv : st.objects.invExt) (h : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    savedRegsKept st st' :=
  savedRegsKept.of_objectsAt fun oid x hx => by
    by_cases hk : oid = addr.cnode
    · subst hk
      rcases cspaceDeleteSlotCore_ok_cases h with ⟨cn, hO, hS⟩ | ⟨t, hO, hS⟩
      · rw [hO] at hx; cases hx
      · rw [hO] at hx; cases hx
        exact ⟨_, storeObject_objects_eq' st _ _ _ hInv hS, rfl⟩
    · rcases cspaceDeleteSlotCore_ok_cases h with ⟨_, _, hS⟩ | ⟨_, _, hS⟩ <;>
        exact ⟨x, (storeObject_objects_ne st st' _ oid _ hk hInv hS).trans hx, rfl⟩

/-- A lookup, a capability insert into a CNode. -/
theorem cspaceMint_savedRegsKept {st st' : SystemState} {src dst : CSpaceAddr}
    {rights : AccessRightSet} {badge : Option SeLe4n.Badge} (hInv : st.objects.invExt)
    (h : cspaceMint src dst rights badge st = .ok ((), st')) :
    savedRegsKept st st' ∧ st'.objects.invExt := by
  unfold cspaceMint at h
  split at h
  · contradiction
  · rename_i parent stMid hLk
    have hMid : stMid = st := cspaceLookupSlot_state_eq st stMid src parent hLk
    subst hMid
    split at h
    · contradiction
    · split at h
      · contradiction
      · exact ⟨savedRegsKept.cspaceInsertSlot hInv h,
          cspaceInsertSlot_preserves_objects_invExt _ _ _ _ hInv h⟩

/-- The untyped source's free-index write. -/
theorem untypedSourceSetFull_savedRegsKept (st : SystemState) (src : CSpaceAddr)
    (cap : Capability) (hInv : st.objects.invExt) :
    savedRegsKept st (untypedSourceSetFull st src cap) :=
  untypedSourceSetFull_of (P := savedRegsKept st) (.refl st)
    fun idx => savedRegsKept.setCapFreeIndex st src idx hInv

/-- **The mint**: the insert, the derivation edge and the source's free index. -/
theorem cspaceMintWithCdt_savedRegsKept {st st' : SystemState} {src dst : CSpaceAddr}
    {rights : AccessRightSet} {badge : Option SeLe4n.Badge} (hInv : st.objects.invExt)
    (h : cspaceMintWithCdt src dst rights badge st = .ok ((), st')) : savedRegsKept st st' := by
  obtain ⟨_, stM, hMint, -, -, rfl⟩ := cspaceMintWithCdt_ok_decompose h
  obtain ⟨k1, i1⟩ := cspaceMint_savedRegsKept hInv hMint
  exact (k1.trans (savedRegsKept.cdtAddChild stM src dst .mint i1)).trans
    (untypedSourceSetFull_savedRegsKept _ src _ (cdtRecord_keyFrame stM src dst .mint i1).2.2)

/-- **The copy**: the insert, the derivation edge and the source's free index. -/
theorem cspaceCopy_savedRegsKept {st st' : SystemState} {src dst : CSpaceAddr}
    (hInv : st.objects.invExt) (h : cspaceCopy src dst st = .ok ((), st')) :
    savedRegsKept st st' := by
  obtain ⟨_, st2, -, -, hIns, -, rfl⟩ := cspaceCopy_ok_decompose h
  have i2 := cspaceInsertSlot_preserves_objects_invExt _ _ _ _ hInv hIns
  exact ((savedRegsKept.cspaceInsertSlot hInv hIns).trans
    (savedRegsKept.cdtAddChild st2 src dst .copy i2)).trans
    (untypedSourceSetFull_savedRegsKept _ src _ (cdtRecord_keyFrame st2 src dst .copy i2).2.2)

/-- **The move**: the insert, the core delete and the tree's move with its slot
links. -/
theorem cspaceMove_savedRegsKept {st st' : SystemState} {src dst : CSpaceAddr}
    (hInv : st.objects.invExt) (h : cspaceMove src dst st = .ok ((), st')) :
    savedRegsKept st st' := by
  unfold cspaceMove at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · rename_i cap stMid hLk
      have hMid : stMid = st := cspaceLookupSlot_state_eq st stMid src cap hLk
      subst hMid
      split at h
      · contradiction
      · split at h
        · contradiction
        · rename_i st2 hIns
          have i2 := cspaceInsertSlot_preserves_objects_invExt _ _ _ _ hInv hIns
          split at h
          · contradiction
          · rename_i st3 hDel
            cases h
            exact ((savedRegsKept.cspaceInsertSlot hInv hIns).trans
              (cspaceDeleteSlotCore_savedRegsKept i2 hDel)).trans
              (savedRegsKept.of_withCdt_linkReach (SystemState.cdtMove_reach st3 src dst)
                (cspaceDeleteSlotCore_invExt st2 st3 src i2 hDel))


/-! ### Every arm of the capability dispatch -/

/-- WS-ZA ZA6.26: **every arm `dispatchWithCapChecked` routes writes the saved
registers of no thread another core holds**: the capability-only arms by
`dispatchCapabilityOnly_savedRegsKeptOffCore`; the IPC and notification arms
write only threads blocked at the entry's start and the caller
(`*Arm_savedRegsWrittenFree`); the CSpace, registry, declassification and
audit arms write CNodes, the derivation tree, an endpoint's service record, the
audit trail, and the caller's return frame. -/
theorem dispatchWithCapChecked_savedRegsKeptOffCore {ctx : LabelingContext}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {ec : CoreId} {gate : SyscallGate}
    {cap : Capability} {st st' : SystemState} (P : SyscallArmPremises st ec tid)
    (hRT : st.residentsHaveTcbs) (hN : st.currentNotResidentElsewhere)
    (hB : finalisingDeleteBundle st) (hBNR : st.blockedNotResident) (hYA : st.yieldLinksAgree)
    (hYN : st.yieldLinkedNotResident)
    (h : dispatchWithCapChecked ctx decoded tid ec gate cap st = .ok ((), st'))
    (hCK : currentKeptOffCore ec st st') (hRK : residentKeptOffCore ec st st') :
    savedRegsKeptOffCore ec st st' := by
  unfold dispatchWithCapChecked at h
  cases hC : dispatchCapabilityOnly decoded cap tid ec with
  | some k =>
    rw [hC] at h
    exact dispatchCapabilityOnly_savedRegsKeptOffCore P hRT hN hB hBNR hYA hYN hC
      (dispatchCapabilityOnlyChecked_ok hC h) hCK hRK
  | none =>
  rw [hC] at h
  dsimp only at h
  have hInv := P.objInv
  have hU := currentsUnique_of_dequeuedUnique P.dequeued
  have hFr : offCoreFree ec st tid := offCoreFree_of_current P.current hU hN
  have hF : savedRegsKept st st' → savedRegsKeptOffCore ec st st' := fun hS =>
    savedRegsKeptOffCore_of_savedRegsKept hS P.dequeued hRT hCK hRK
  have hW : savedRegsWrittenFree ec st st st' → savedRegsKeptOffCore ec st st' := fun w =>
    w.census hCK hRK
  clear hCK hRK
  cases hId : decoded.syscallId <;> rw [hId] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.auditRead =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    rw [auditReadFromCore_frame _ _ _ _ _ _ _ hA] at hW ⊢
    exact hW (.of_kept (writeReturnFrameToTcb_savedRegsKeptExcept st tid _ hInv) fun _ e =>
      e ▸ hFr)
  case none.auditDrain =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    unfold auditDrainVisiblePrefix at hA
    split at hA
    · cases hA
      exact hW (.of_kept ((savedRegsKeptExcept.of_objects_eq rfl).trans
        (writeReturnFrameToTcb_savedRegsKeptExcept _ tid _ hInv)) fun _ e => e ▸ hFr)
    · cases hA
  all_goals
    cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.send.object epId =>
    split at h
    · cases h
    rename_i hSend
    split at h
    · cases h
    rename_i hClr
    cases h
    exact hW (sendArm_savedRegsWrittenFree _ P hRT hBNR hSend hClr)
  case none.receive.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ _ hRecv _ stDon hHand
    cases h
    exact hW (receiveArm_savedRegsWrittenFree _ P hRT hBNR hN hRecv hHand)
  case none.call.object epId =>
    split at h
    · rename_i hCall
      cases h
      exact hW (callArm_savedRegsWrittenFree _ P hRT hBNR hCall)
    · cases h
  case none.reply.replyCap rid =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact hW (replyTransferOnCoreChecked_savedRegsWrittenFree P.dequeued hRT hBNR hInv h)
  case none.cspaceMint.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    all_goals
      unfold cspaceMintChecked at h
      dsimp only at h
      split at h
      · exact hF (cspaceMintWithCdt_savedRegsKept hInv h)
      · cases h
  case none.cspaceCopy.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceCopyChecked at h
    dsimp only at h
    split at h
    · exact hF (cspaceCopy_savedRegsKept hInv h)
    · cases h
  case none.cspaceMove.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceMoveChecked at h
    dsimp only at h
    split at h
    · exact hF (cspaceMove_savedRegsKept hInv h)
    · cases h
  case none.serviceRegister.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold registerServiceChecked at h
    split at h
    · exact hF (savedRegsKept.of_serviceRecordRewrite hInv (registerService_serviceRecordRewrite h))
    · cases h
  case none.notificationSignal.object notifId =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      split at h
      · cases h
      rename_i hClr
      cases h
      exact hW (notificationSignalArm_savedRegsWrittenFree P hRT hBNR hSig hClr)
    · cases h
  case none.notificationWait.object notifId =>
    split at h
    · rename_i hWt
      cases h
      exact hW (notificationWaitArm_savedRegsWrittenFree _ P hN hWt).2
    · rename_i hWt
      cases h
      exact hW (notificationWaitArm_savedRegsWrittenFree default P hN hWt).1
    · cases h
  case none.replyRecv.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ stR hRR
    cases h
    obtain ⟨w, i⟩ := endpointReplyRecvOnCore_savedRegsWrittenFree P.dequeued P.queueHeads hRT
      hBNR hInv hRR
    exact hW (w.trans (.of_kept (stageDeliveredMessage_savedRegsKeptExcept _ tid _ i).1
      fun _ e => e ▸ hFr))
  case none.declassify.object targetId =>
    unfold declassifyObjectFromCore at h
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rw [(authorizeDeclassificationOnCore_frame _ _ _ _ _ _ _ _ _ h).1] at hF ⊢
    exact hF (savedRegsKept.of_objects_eq rfl)
  case none.declassifySignal.object notifId =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      split at h
      · cases h
      rename_i hClr
      cases h
      exact hW (declassifySignalArm_savedRegsWrittenFree P hRT hBNR hSig hClr)
    · cases h


/-! ### The yield -/

/-- **The yield's charge moves no core's current thread**: the slice reset and
the budget charge write a thread's time slice, a scheduling context, its
release queue, the run queue and the reschedule flags. -/
theorem yieldChargeOnCore_currentOnCore {st st' : SystemState} {c : CoreId}
    {tid : SeLe4n.ThreadId} (h : yieldChargeOnCore st c tid = .ok st') (d : CoreId) :
    st'.scheduler.currentOnCore d = st.scheduler.currentOnCore d := by
  unfold yieldChargeOnCore at h
  split at h
  · cases h
  · split at h
    · cases h
      simp [sliceExpireOnCore, SystemState.rewriteObject_scheduler]
    all_goals
      split at h
      · cases h
        simp [spendBudgetOnCore, replenishOnCore_currentOnCore,
          SystemState.rewriteObject_scheduler]
      · cases h

/-- The release queue's placement writes scheduling contexts' release links. -/
theorem replenishOnCore_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop} (st : SystemState)
    (c : CoreId) (scId : SeLe4n.SchedContextId) :
    savedRegsKeptExcept W st (replenishOnCore st c scId) := .of_eq fun t => by
  unfold SystemState.savedRegs
  rw [replenishOnCore_getTcb?]

/-- **The yield's charge writes no saved register**: the slice reset rewrites
the caller's TCB with its registers, the budget charge rewrites a scheduling
context, the release queue's place and the run queue write links, and the key
hook writes flags. -/
theorem yieldChargeOnCore_savedRegsUnwritten {st st' : SystemState} {c : CoreId}
    {tid : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : yieldChargeOnCore st c tid = .ok st') : savedRegsUnwritten st st' := by
  unfold yieldChargeOnCore at h
  split at h
  · cases h
  · rename_i tcb hTcb _
    split at h
    · cases h
      refine ⟨?_, sliceExpireOnCore_objects_invExt st c tid tcb hTcb hInv⟩
      unfold sliceExpireOnCore
      dsimp only
      refine savedRegsKeptExcept.trans ?_
        (.of_runLinks (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ _ _ _))
      exact savedRegsKeptExcept.rewriteObject_tcb _ hInv
        ((SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb) rfl
    all_goals
      split at h
      · rename_i sc hSc _
        cases h
        refine ⟨?_, by
          rw [markKeyChangeFor_objects]
          exact spendBudgetOnCore_objects_invExt st c tid _ sc hSc _ _ hInv⟩
        refine savedRegsKeptExcept.trans ?_
          (savedRegsKeptExcept.of_objects_eq (markKeyChangeFor_objects _ _ _))
        unfold spendBudgetOnCore
        dsimp only
        refine savedRegsKeptExcept.trans ?_
          (.of_runLinks (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ _ _ _))
        refine savedRegsKeptExcept.trans ?_ (replenishOnCore_savedRegsKeptExcept _ _ _)
        exact savedRegsKeptExcept.rewriteObject_notTcb _ hInv (fun x hx => by
          rw [(SystemState.getSchedContext?_eq_some_iff st _ sc).mp hSc] at hx; cases hx)
          (fun x hx => by cases hx)
      · cases h

/-- **The save writes the outgoing thread alone**, core `c`'s current thread. -/
theorem saveOutgoingContextOnCore_savedRegsKeptExcept (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) :
    savedRegsKeptExcept (fun t => st.scheduler.currentOnCore c = some t) st
      (saveOutgoingContextOnCore st c) := by
  unfold saveOutgoingContextOnCore
  split
  · exact .refl _
  · rename_i outTid hCur
    exact .updateTcb_written _ _ _ hInv hCur

/-- **The scheduling point writes the outgoing thread alone**: the save, then
run-queue links and the incoming core's bank. -/
theorem scheduleEffectiveOnCore_savedRegsKeptExcept {st st' : SystemState} {c : CoreId}
    (hInv : st.objects.invExt) (h : scheduleEffectiveOnCore st c = .ok st') :
    savedRegsKeptExcept (fun t => st.scheduler.currentOnCore c = some t) st st' :=
  (saveOutgoingContextOnCore_savedRegsKeptExcept st c hInv).trans
    (.of_runLinks (scheduleEffectiveOnCore_objectsAgreeOffRunLinks st c st' h))

/-- WS-ZA ZA6.26: **the yield writes the caller alone**: the charge writes no
saved register and moves no current thread, so the scheduling point's save
names the caller, the executing core's current thread, which no other core
holds. -/
theorem yieldOnCore_savedRegsWrittenFree {st st' : SystemState} {e : CoreId}
    (hInv : st.objects.invExt) (hU : currentsUnique st) (hN : st.currentNotResidentElsewhere)
    (h : yieldOnCore st e = .ok st') : savedRegsWrittenFree e st st st' := by
  unfold yieldOnCore at h
  split at h
  · cases h
  rename_i tid hCur
  split at h
  · cases h
  rename_i st1 hCharge
  have h1 := yieldChargeOnCore_savedRegsUnwritten hInv hCharge
  refine h1.writtenFree.trans (.of_kept (scheduleEffectiveOnCore_savedRegsKeptExcept h1.2 h)
    fun t ht => ?_)
  rw [yieldChargeOnCore_currentOnCore hCharge, hCur] at ht
  cases ht
  exact offCoreFree_of_current hCur hU hN


/-! ### The taint pass and the checked dispatch -/

/-- **A write of taint words alone keeps every saved context**: a thread's TCB
differs only in its taint words, and a slot that held no TCB holds none. -/
theorem savedRegsKeptExcept.of_objectsAgreeOffTaint {W : SeLe4n.ThreadId → Prop}
    {pre post : SystemState} (h : pre.objectsAgreeOffTaint post) :
    savedRegsKeptExcept W pre post :=
  savedRegsKeptExcept.of_slotsTcb fun k => by
    by_cases hT : ∃ x : TCB, pre.objects[k]? = some (.tcb x)
    · obtain ⟨x, hx⟩ := hT
      obtain ⟨w, hw⟩ := SystemState.objectsAgreeOffTaint.tcb_fwd_eq h hx
      exact .inr (.inr ⟨x, _, hx, hw, rfl⟩)
    · refine .inr (.inl ⟨fun x hx => hT ⟨x, hx⟩, fun y hy => ?_⟩)
      obtain ⟨x, -, hx, -⟩ := SystemState.objectsAgreeOffTaint.tcb_back_eq h hy
      exact hT ⟨x, hx⟩

/-- WS-ZA ZA6.26: **the checked syscall dispatch writes the saved registers of no
thread another core holds**: the yield writes the caller alone, the capability
resolution is a read, every routed arm writes no other core's thread
(`dispatchWithCapChecked_savedRegsKeptOffCore`), and the taint pass writes taint
words alone.  The coverage frames are the dispatch's own
(`dispatchSyscallChecked_stepCovers`, `dispatchWithCapChecked_stepCovers`). -/
theorem dispatchSyscallChecked_savedRegsKeptOffCore {ctx : LabelingContext}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {e : CoreId} {st st' : SystemState}
    (P : SyscallArmPremises st e tid) (hRT : st.residentsHaveTcbs)
    (hN : st.currentNotResidentElsewhere) (hB : finalisingDeleteBundle st)
    (hBNR : st.blockedNotResident) (hYA : st.yieldLinksAgree) (hYN : st.yieldLinkedNotResident)
    (hPlaced : placedThreadsHaveTcbs st)
    (hAwayCur : ∀ t, st.scheduler.currentOnCore e = some t → ∀ c, st.queuedOn c t = false)
    (h : dispatchSyscallChecked ctx decoded tid e st = .ok ((), st')) :
    savedRegsKeptOffCore e st st' := by
  have hInv := P.objInv
  have hU := currentsUnique_of_dequeuedUnique P.dequeued
  unfold dispatchSyscallChecked at h
  split at h
  · cases h
  by_cases hY : decoded.syscallId = .yield
  · simp only [hY, ↓reduceIte, dispatchYield] at h
    split at h
    · cases h
    · rename_i hYieldOk
      cases h
      have hC := (yieldOnCore_stepCovers st _ e hInv hB.bidirectional hAwayCur hYieldOk).1
      exact (yieldOnCore_savedRegsWrittenFree hInv hU hN hYieldOk).census hC.currentKept
        hC.residentKept
  simp only [hY, ↓reduceIte] at h
  split at h <;> try (cases h; done)
  split at h <;> try (cases h; done)
  split at h
  · cases h
  rename_i stPost hD
  cases h
  suffices hP : savedRegsKeptOffCore e st stPost from fun d hd t ht =>
    ((savedRegsKeptExcept.of_objectsAgreeOffTaint (W := fun _ => False)
      (applySyscallTaint_objectsAgreeOffTaint _ _ _)) t id).trans
      (hP d hd t (by rwa [applySyscallTaint_scheduler, applySyscallTaint_machine] at ht))
  obtain ⟨cap, -, -, hD⟩ := syscallInvokeTyped_ok _ _ _ st () stPost hD
  have hC := (dispatchWithCapChecked_stepCovers e hInv hB hPlaced hD).1
  exact dispatchWithCapChecked_savedRegsKeptOffCore P hRT hN hB hBNR hYA hYN hD
    hC.currentKept hC.residentKept


/-! ### The entry -/

/-- WS-ZA ZA6.26: **the checked syscall entry writes the saved registers of no
thread another core holds**: the register and decode reads write nothing, the
IPC-buffer fill writes one core's TLB, and the dispatch writes no other core's
thread (`dispatchSyscallChecked_savedRegsKeptOffCore`). -/
theorem syscallEntryChecked_savedRegsKeptOffCore {ctx : LabelingContext}
    {layout : SeLe4n.SyscallRegisterLayout} {e : CoreId} {regCount : Nat}
    {st st' : SystemState} (E : EntryPremises st)
    (hNI : ∀ tid, st.scheduler.currentOnCore e = some tid → isIdleThreadId tid = false)
    (hRT : st.residentsHaveTcbs) (hN : st.currentNotResidentElsewhere)
    (hB : finalisingDeleteBundle st) (hBNR : st.blockedNotResident) (hYA : st.yieldLinksAgree)
    (hYN : st.yieldLinkedNotResident) (hPlaced : placedThreadsHaveTcbs st)
    (hAwayCur : ∀ t, st.scheduler.currentOnCore e = some t → ∀ c, st.queuedOn c t = false)
    (h : syscallEntryChecked ctx layout e regCount st = .ok ((), st')) :
    savedRegsKeptOffCore e st st' := by
  unfold syscallEntryChecked at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i tid hCur
  split at h
  · cases h
  rename_i regs s hLk
  split at h
  · cases h
  rename_i decoded hDec
  dsimp only at h
  obtain ⟨t, ht⟩ := Architecture.tlbFillIpcBufferOnCore_eq_setPerCoreTlb st e tid
    decoded.overflowCount
  rw [ht] at h
  have hF := SystemState.RunQueueStage.of_frame (st := st)
    (st' := { st with perCoreTlb := t }) rfl rfl rfl
  exact dispatchSyscallChecked_savedRegsKeptOffCore (st := { st with perCoreTlb := t })
    ((E.of_ipcFrame hF (IpcFrame.of_frame rfl fun _ => rfl)).arm hCur (hNI tid hCur))
    hRT (CurrentNotResidentElsewhere.of_frame hN rfl rfl)
    (finalisingDeleteBundle.of_objects_scheduler_eq (s := st) rfl rfl hB) hBNR hYA hYN
    hPlaced (fun t ht c => hAwayCur t ht c) h


/-! ### What a register-only write keeps -/

section registerWrite

variable {st : SystemState} {tid : SeLe4n.ThreadId} {f : TCB → TCB}

theorem updateTcb_getTcb?_cases (hInv : st.objects.invExt) (t : SeLe4n.ThreadId) :
    (st.updateTcb tid f).getTcb? t = (st.getTcb? t).map f ∧ tid = t ∨
      (st.updateTcb tid f).getTcb? t = st.getTcb? t := by
  by_cases e : tid = t
  · subst e; exact .inl ⟨SystemState.updateTcb_getTcb?_self _ _ _ hInv, rfl⟩
  · exact .inr (SystemState.updateTcb_getTcb?_ne _ _ _ hInv t
      fun h => e (SeLe4n.ThreadId.toObjId_injective _ _ h))

theorem updateTcb_getEndpoint? (hInv : st.objects.invExt) (ep : SeLe4n.ObjId) :
    (st.updateTcb tid f).getEndpoint? ep = st.getEndpoint? ep := by
  by_cases hk : tid.toObjId = ep
  · subst hk
    cases hT : st.getTcb? tid with
    | none => rw [SystemState.updateTcb_eq_self_of_none hT]
    | some t =>
      have h2 : (st.updateTcb tid f).getTcb? tid = some (f t) := by
        rw [SystemState.updateTcb_getTcb?_self _ _ _ hInv, hT]; rfl
      unfold SystemState.getEndpoint?
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hT,
        (SystemState.getTcb?_eq_some_iff _ _ _).mp h2]
  · unfold SystemState.getEndpoint?
    rw [SystemState.updateTcb_objects_ne _ _ _ _ hk hInv]

theorem residentsHaveTcbs_updateTcb (hInv : st.objects.invExt) (h : st.residentsHaveTcbs) :
    (st.updateTcb tid f).residentsHaveTcbs := fun d t hR => by
  rw [SystemState.updateTcb_machine] at hR
  have h0 := h d t hR
  rcases updateTcb_getTcb?_cases (f := f) (tid := tid) hInv t with ⟨e, -⟩ | e <;> rw [e]
  · rw [Option.isSome_map]; exact h0
  · exact h0

theorem blockedNotResident_updateTcb (hInv : st.objects.invExt)
    (hf : ∀ x, (f x).ipcState = x.ipcState) (h : st.blockedNotResident) :
    (st.updateTcb tid f).blockedNotResident := fun d t x hR hT => by
  rw [SystemState.updateTcb_machine] at hR
  rcases updateTcb_getTcb?_cases (f := f) (tid := tid) hInv t with ⟨e, -⟩ | e <;> rw [e] at hT
  · cases hS : st.getTcb? t with
    | none => rw [hS] at hT; cases hT
    | some y =>
      rw [hS] at hT; cases hT
      rw [hf]; exact h d t y hR hS
  · exact h d t x hR hT

theorem yieldLinkedNotResident_updateTcb (hInv : st.objects.invExt)
    (hf : ∀ x, (f x).yieldToCode = x.yieldToCode) (h : st.yieldLinkedNotResident) :
    (st.updateTcb tid f).yieldLinkedNotResident := fun d t x hR hT => by
  rw [SystemState.updateTcb_machine, SystemState.updateTcb_scheduler] at hR
  rcases updateTcb_getTcb?_cases (f := f) (tid := tid) hInv t with ⟨e, -⟩ | e <;> rw [e] at hT
  · cases hS : st.getTcb? t with
    | none => rw [hS] at hT; cases hT
    | some y =>
      rw [hS] at hT; cases hT
      rw [hf]; exact h d t y hR hS
  · exact h d t x hR hT

theorem currentNotResidentElsewhere_updateTcb (h : st.currentNotResidentElsewhere) :
    (st.updateTcb tid f).currentNotResidentElsewhere :=
  CurrentNotResidentElsewhere.of_frame h (SystemState.updateTcb_scheduler _ _ _)
    (by rw [SystemState.updateTcb_machine])

end registerWrite


/-! ### The capability-fault delivery and the ABI dispatch -/

/-- The fault record writes a thread's pending fault and its fault-send bit. -/
theorem recordPendingFault_savedRegsKeptExcept (s : SystemState) (tid : SeLe4n.ThreadId)
    (tf : ThreadFault) (hInv : s.objects.invExt) :
    savedRegsKeptExcept (fun _ => False) s (recordPendingFault s tid tf) := by
  unfold recordPendingFault
  exact .updateTcb _ _ _ hInv fun _ => rfl

/-- WS-ZA ZA6.26: **the fault delivery writes only the woken handler**: the
suspend and the fault record write a thread's state and its pending fault, the
fault's call writes no saved register, and the handler's delivery names the
handler endpoint's receive head, which `hHead` gives free at `base`. -/
theorem faultDeliverOnCoreChecked_savedRegsWrittenFree {ctx : LabelingContext}
    {e c : CoreId} {base s : SystemState} {tid : SeLe4n.ThreadId} {f : Fault}
    {fctx : FaultContext} (hInv : s.objects.invExt)
    (hHead : ∀ ep t, (s.getEndpoint? ep).bind (·.receiveQ.head) = some t → offCoreFree e base t) :
    savedRegsWrittenFree e base s (faultDeliverOnCoreChecked ctx s tid f fctx c).1 := by
  have hSusp : savedRegsWrittenFree e base s
      (recordPendingFault (faultSuspendOnCore s tid c) tid { fault := f, context := fctx }) := by
    have i1 := removeRunnableOnCore_objects_invExt s tid c hInv
    have i2 : (faultSuspendOnCore s tid c).objects.invExt := by
      unfold faultSuspendOnCore; exact SystemState.updateTcb_preserves_objects_invExt _ _ _ i1
    have k1 : savedRegsKeptExcept (fun _ => False) s (faultSuspendOnCore s tid c) := by
      unfold faultSuspendOnCore
      exact (savedRegsUnwritten.of_removeRunnableOnCore s tid c hInv).kept.trans
        (.updateTcb _ _ _ i1 fun _ => rfl)
    exact .of_kept (k1.trans (recordPendingFault_savedRegsKeptExcept _ tid _ i2)) fun _ h => h.elim
  unfold faultDeliverOnCoreChecked
  split
  · exact hSusp
  rename_i tgt hRes
  split
  · unfold faultDeliverOnCore
    rw [hRes]
    dsimp only
    have h1 := endpointCallCrossCoreDispatch_savedRegsUnwritten tgt.endpoint tid
      (.fault f fctx tgt.cap.badge) c hInv
    revert h1
    generalize endpointCallCrossCoreDispatch tgt.endpoint tid (.fault f fctx tgt.cap.badge)
      c s = r
    obtain ⟨s1, res⟩ := r
    cases res with
    | error _ => intro _; exact hSusp
    | ok x =>
      intro h1
      obtain ⟨w, i⟩ := stageWokenDelivery_savedRegsWrittenFree (e := e) (base := base)
        x.1.capInfo h1.2 (hHead _)
      exact (h1.writtenFree.trans w).trans (.of_kept
        (recordPendingFault_savedRegsKeptExcept _ tid _ i) fun _ h => h.elim)
  · exact hSusp


/-- WS-ZA ZA6.26: **the ABI syscall dispatch writes the saved registers of no
thread another core holds.**  The argument spill writes the caller, the
executing core's current thread, which no other core holds; then the checked
entry (`syscallEntryChecked_savedRegsKeptOffCore`, its premises carried across
the spill, which writes registers alone), or on a refused capability the fault
window's spill into the caller and the fault delivery, which writes only the
handler endpoint's receive head, blocked at the entry's start
(`faultDeliverOnCoreChecked_savedRegsWrittenFree`), or a refusal record, which
writes no object.  The coverage frames are the dispatch's own
(`syscallDispatchFromAbi_stepCovers`, `syscallEntryChecked_stepCovers`).  An arm
that wrote the saved registers of a thread current or resident on another core
would break the remote stall's rule; none does. -/
theorem syscallDispatchFromAbi_savedRegsKeptOffCore {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64}
    {st st' : SystemState} {outcome : Architecture.SyscallOutcome}
    (E : EntryPremises st) (hRT : st.residentsHaveTcbs) (hN : st.currentNotResidentElsewhere)
    (hB : finalisingDeleteBundle st) (hBNR : st.blockedNotResident) (hYA : st.yieldLinksAgree)
    (hYN : st.yieldLinkedNotResident) (hPlaced : placedThreadsHaveTcbs st)
    (hAwayCur : ∀ t, st.scheduler.currentOnCore e = some t → ∀ c, st.queuedOn c t = false)
    (h : Platform.FFI.syscallDispatchFromAbi ctx e syscallId x0 x1 x2 x3 x4 x5
      ipcBufferAddr elr spsr spEl0 x30 st = .ok (outcome, st')) :
    savedRegsKeptOffCore e st st' := by
  have hInv := E.objInv
  have hU := currentsUnique_of_dequeuedUnique E.dequeued
  have hC := (syscallDispatchFromAbi_stepCovers hInv hB hPlaced hAwayCur h).1
  unfold Platform.FFI.syscallDispatchFromAbi at h
  split at h
  · cases h; exact savedRegsKeptOffCore_refl e st
  rename_i tid hCur
  split at h
  · cases h; exact savedRegsKeptOffCore_refl e st
  rename_i hIdle
  have hNI : isIdleThreadId tid = false := by simpa using hIdle
  have hFr : offCoreFree e st tid := offCoreFree_of_current hCur hU hN
  have hEq := Platform.FFI.writeFfiRegistersToTcb_eq_updateTcb st tid syscallId x0 x1 x2 x3 x4 x5
  have iW : (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5).objects.invExt
    := by rw [hEq]; exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv
  have hW1 : savedRegsKeptExcept (· = tid) st
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) := by
    rw [hEq]; exact .updateTcb_written _ _ _ hInv rfl
  dsimp only at h
  split at h
  · split at h
    · cases h
      refine savedRegsWrittenFree.census (base := st) ?_ hC.currentKept hC.residentKept
      unfold Platform.FFI.deliverSyscallCapFault
      dsimp only
      have hW2 : savedRegsKeptExcept (· = tid)
          (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5)
          (writeFaultRegistersToTcb
            (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) tid
            (Platform.FFI.syscallWindow syscallId x0 x1 x2 x3 x4 x5 ipcBufferAddr spEl0 x30)) := by
        unfold writeFaultRegistersToTcb; exact .updateTcb_written _ _ _ iW rfl
      have iW2 : (writeFaultRegistersToTcb
          (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) tid
          (Platform.FFI.syscallWindow syscallId x0 x1 x2 x3 x4 x5 ipcBufferAddr spEl0 x30)
          ).objects.invExt := by
        unfold writeFaultRegistersToTcb; exact SystemState.updateTcb_preserves_objects_invExt _ _ _ iW
      refine ((savedRegsWrittenFree.of_kept hW1 fun _ e => e ▸ hFr).trans
        (.of_kept hW2 fun _ e => e ▸ hFr)).trans
        (faultDeliverOnCoreChecked_savedRegsWrittenFree iW2 fun ep t ht => ?_)
      unfold writeFaultRegistersToTcb at ht
      rw [updateTcb_getEndpoint? iW, hEq, updateTcb_getEndpoint? hInv] at ht
      exact offCoreFree_of_receiveHead E.dequeued E.queueHeads hRT hBNR ht
    · cases h
      exact savedRegsWrittenFree.census (base := st) ((savedRegsWrittenFree.of_kept hW1
        fun _ e => e ▸ hFr).trans (.of_kept (W := fun _ => False)
          (.of_objects_eq (Platform.FFI.recordSyscallRefusal_objects_eq _ _ _ _ _ _ _))
          fun _ h => h.elim)) hC.currentKept hC.residentKept
  · rename_i hE
    cases h
    have hB' := finalisingDeleteBundle_writeFfiRegistersToTcb tid syscallId x0 x1 x2 x3 x4 x5 hB
    have hPl : placedThreadsHaveTcbs
        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) := by
      rw [hEq]; exact placedThreadsHaveTcbs_updateTcb hInv hPlaced
    have hAwayW : ∀ t, (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5
        ).scheduler.currentOnCore e = some t → ∀ c,
        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5).queuedOn c t =
          false := by
      intro t ht c
      rw [Platform.FFI.writeFfiRegistersToTcb_scheduler] at ht
      rw [hEq, (SystemState.RunCoresAgree.updateTcb
        (f := Platform.FFI.ffiRegisterSpill syscallId x0 x1 x2 x3 x4 x5) hInv fun _ => rfl).queuedOn c t]
      exact hAwayCur t ht c
    have hS : SystemState.RunQueueStage st
        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) := by
      rw [hEq]; exact SystemState.RunQueueStage.updateTcb _ _ (fun _ _ => rfl)
    have E1 := E.of_ipcFrame hS (by rw [hEq]; exact IpcFrame.updateTcb _ _ fun _ => rfl)
    have hC2 := (syscallEntryChecked_stepCovers iW hB' hPl hAwayW hE).1
    refine savedRegsKeptOffCore_trans_stepCovers
      (writeFfiRegistersToTcb_savedRegsKeptOffCore syscallId x0 x1 x2 x3 x4 x5 hInv hCur hU hN)
      (syscallEntryChecked_savedRegsKeptOffCore E1 (fun t ht => ?_) ?_ ?_ hB' ?_ ?_ ?_ hPl hAwayW
        hE) hC2
    · rw [Platform.FFI.writeFfiRegistersToTcb_scheduler, hCur] at ht
      cases ht; exact hNI
    · rw [hEq]; exact residentsHaveTcbs_updateTcb hInv hRT
    · rw [hEq]; exact currentNotResidentElsewhere_updateTcb hN
    · rw [hEq]; exact blockedNotResident_updateTcb hInv (fun _ => rfl) hBNR
    · rw [hEq]
      exact SystemState.yieldLinksAgree_of_kept (YieldLinksKept.updateTcb _ _ _ hInv fun _ => rfl)
        hYA
    · rw [hEq]; exact yieldLinkedNotResident_updateTcb hInv (fun _ => rfl) hYN

end SeLe4n.Kernel
