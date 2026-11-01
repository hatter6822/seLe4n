-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ReschedulePendingArms.Ipc
import SeLe4n.Kernel.API
import SeLe4n.Kernel.Lifecycle.Invariant.CleanupReservation
import SeLe4n.Kernel.SlotConfinement.MemoryArms

/-!
# The checked dispatcher's own arms cover

The KSC-1 / HAL-3 row of `docs/REGISTERED_DEBT.md`, PR B2.  Each arm
`dispatchWithCapChecked` routes itself (the IPC, notification, CSpace, service,
declassification and audit arms) is one of the transitions the sibling modules
prove covering, wrapped in steps that move no key input: extra-capability
resolution (CDT nodes only), the woken receiver's stash clear, the return-frame
staging, the service registry and the audit trail.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-! ### The wrapping steps -/

theorem clearWokenReceiverStash_keyFrame (receiver? : Option SeLe4n.ThreadId) {st : SystemState}
    {pair : Unit × SystemState} (hInv : st.objects.invExt)
    (h : clearWokenReceiverStash receiver? st = .ok pair) : capabilityKeyFrame st pair.2 := by
  unfold clearWokenReceiverStash at h
  split at h
  · cases h; exact capabilityKeyFrame_refl hInv
  · split at h
    · rename_i rTcb hT
      split at h
      · exact keyFrame_storeObject_tcbKeeping_after
          ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) (by rfl) (capabilityKeyFrame_refl hInv) h
      · cases h; exact capabilityKeyFrame_refl hInv
    · cases h; exact capabilityKeyFrame_refl hInv

/-- The registry's one object write — an endpoint's `serviceRegistered` — feeds no
key: an endpoint holds no key input. -/
theorem serviceRecordRewrite_keyFrame {st st' : SystemState} (hInv : st.objects.invExt)
    (hW : ServiceRecordRewrite st.objects st'.objects) (hS : st'.scheduler = st.scheduler) :
    capabilityKeyFrame st st' :=
  ⟨fun oid => by
    rcases hW.lookup hInv oid with h | ⟨_, _, h0, h1⟩
    · rw [h]
    · rw [h0, h1]; rfl, hS, hW.invExt hInv⟩

theorem registerService_keyFrame {reg : ServiceRegistration} {st st' : SystemState}
    (hInv : st.objects.invExt) (h : registerService reg st = .ok ((), st')) :
    capabilityKeyFrame st st' :=
  serviceRecordRewrite_keyFrame hInv (registerService_serviceRecordRewrite h)
    (registerService_preserves_scheduler _ _ _ h)

theorem revokeService_keyFrame {sid : ServiceId} {st st' : SystemState}
    (hInv : st.objects.invExt) (h : revokeService sid st = .ok ((), st')) :
    capabilityKeyFrame st st' :=
  serviceRecordRewrite_keyFrame hInv (revokeService_serviceRecordRewrite h)
    (revokeService_preserves_scheduler _ _ _ h)

/-- WS-ZA ZA5.5: the release of a final endpoint's registration feeds no key: it
is a revocation or nothing. -/
theorem releaseFinalRegistration_keyFrame (target : Nat) (st : SystemState)
    (hInv : st.objects.invExt) : capabilityKeyFrame st (releaseFinalRegistration target st) := by
  rcases releaseFinalRegistration_cases target st with hE | ⟨_, _, _, _, hR⟩
  · rw [hE]; exact capabilityKeyFrame_refl hInv
  · exact revokeService_keyFrame hInv hR

/-- ...and so is the revoke the kernel runs, through the invoked endpoint. -/
theorem revokeServiceByRecordedRegistration_keyFrame {epId : SeLe4n.ObjId} {st st' : SystemState}
    (hInv : st.objects.invExt) (h : revokeServiceByRecordedRegistration epId st = .ok ((), st')) :
    capabilityKeyFrame st st' := by
  obtain ⟨_, h⟩ := revokeServiceByRecordedRegistration_revokeService h
  exact revokeService_keyFrame hInv h

/-! ### The dispatch's writes keep the machine

What `resident_frame` reads through the dispatch arms' writes
(`machine_chain`): each keeps the machine, so no core's residency record moves. -/

theorem storeTcbWith_machine (st : SystemState) (id : SeLe4n.ObjId) (f : TCB → TCB) :
    (st.storeTcbWith id f).machine = st.machine := by
  unfold SystemState.storeTcbWith
  split
  · split
    · rfl
    · split
      · rename_i h; exact storeObject_machine_eq _ _ _ _ h
      · rfl
  · rfl

theorem threadSlotCopied_machine (st : SystemState) (tid : SeLe4n.ThreadId) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    (threadSlotCopied st tid slot srcCNode srcSlot rights).machine = st.machine := by
  rcases threadSlotCopied_cases st tid slot srcCNode srcSlot rights with ⟨-, e⟩ | ⟨cap, -, e⟩ <;>
    rw [e] <;>
    simp [threadSlotCleared, storeTcbWith_machine, SystemState.updateTcb_machine]

theorem setThreadFaultHandlerOp_machine_eq {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {cptr : SeLe4n.CPtr} (hStep : setThreadFaultHandlerOp st vtid cptr = .ok st') :
    st'.machine = st.machine := by
  cases hT : st.getTcb? vtid.val with
  | none => simp [setThreadFaultHandlerOp, SystemState.getTcbWitnessed?_eq_none hT] at hStep
  | some tcb =>
      cases hR : resolveFaultHandlerCPtr st tcb cptr with
      | error e =>
          simp [setThreadFaultHandlerOp, SystemState.getTcbWitnessed?_eq_some hT, hR] at hStep
      | ok tgt =>
          rw [setThreadFaultHandlerOp_ok_eq st vtid cptr tcb tgt hT hR] at hStep
          cases hStep
          rfl

theorem setConsumed_machine (st : SystemState) (s : SeLe4n.SchedContextId) (t : SeLe4n.ThreadId) :
    (setConsumed st s t).machine = st.machine := by
  unfold setConsumed
  split <;> simp [SystemState.updateTcb_machine, SystemState.updateSchedContext_machine]

theorem cancelYieldFrom_machine (st : SystemState) (s : SeLe4n.SchedContextId) :
    (cancelYieldFrom st s).machine = st.machine := by
  unfold cancelYieldFrom
  repeat' split
  all_goals simp [SystemState.updateTcb_machine, SystemState.updateSchedContext_machine]

theorem completeYieldFrom_machine (st : SystemState) (s : SeLe4n.SchedContextId) :
    (completeYieldFrom st s).machine = st.machine := by
  unfold completeYieldFrom
  repeat' split
  all_goals first | rfl | rw [cancelYieldFrom_machine, setConsumed_machine]

theorem storeUnbindNotification_machine (st : SystemState) (t : SeLe4n.ThreadId)
    (n : SeLe4n.ObjId) : (storeUnbindNotification st t n).machine = st.machine := by
  simp [storeUnbindNotification, SystemState.modifyObject, SystemState.updateTcb_machine]

theorem bindNotification_machine_eq {st st' : SystemState} {nid : SeLe4n.ObjId}
    {tcbId : SeLe4n.ThreadId} (hStep : bindNotification nid tcbId st = .ok ((), st')) :
    st'.machine = st.machine := by
  unfold bindNotification at hStep
  split at hStep
  · split at hStep
    · contradiction
    · split at hStep
      · contradiction
      · split at hStep
        · contradiction
        · rename_i hStore1
          split at hStep
          · contradiction
          · rename_i hStore2
            cases hStep
            rw [storeObject_machine_eq _ _ _ _ hStore2, storeObject_machine_eq _ _ _ _ hStore1]
  · split at hStep <;> contradiction

theorem unbindNotification_machine_eq {st st' : SystemState} {tcbId : SeLe4n.ThreadId}
    (hStep : unbindNotification tcbId st = .ok ((), st')) : st'.machine = st.machine := by
  unfold unbindNotification at hStep
  split at hStep
  · contradiction
  · split at hStep
    · contradiction
    · split at hStep
      · contradiction
      · rename_i hStore1
        split at hStep
        · split at hStep
          · contradiction
          · rename_i hStore2
            cases hStep
            rw [storeObject_machine_eq _ _ _ _ hStore2, storeObject_machine_eq _ _ _ _ hStore1]
        · cases hStep
          exact storeObject_machine_eq _ _ _ _ hStore1

theorem pageTableMap_machine_eq {tableId rootId : SeLe4n.ObjId} {vaddr : SeLe4n.VAddr}
    {st st' : SystemState} (hStep : Architecture.pageTableMap tableId rootId vaddr st = .ok ((), st')) :
    st'.machine = st.machine := by
  obtain ⟨_, _, _, _, -, -, -, -, -, -, hS1, hS2⟩ :=
    Architecture.pageTableMap_ok tableId rootId vaddr st st' hStep
  rw [storeObject_machine_eq _ _ _ _ hS2, Architecture.recordPhysicalWrites_machine,
    storeObject_machine_eq _ _ _ _ hS1]

theorem pageTableUnmap_machine_eq {tableId : SeLe4n.ObjId} {st st' : SystemState}
    (hStep : Architecture.pageTableUnmap tableId st = .ok ((), st')) :
    st'.machine = st.machine := by
  unfold Architecture.pageTableUnmap at hStep
  cases hT : st.getPageTable? tableId with
  | none => rw [hT] at hStep; cases hStep
  | some table =>
    rw [hT] at hStep
    simp only at hStep
    cases hI : table.installedIn with
    | none => rw [hI] at hStep; cases hStep; rfl
    | some inst =>
      rw [hI] at hStep
      simp only at hStep
      cases hR : st.getVSpaceRoot? inst.root with
      | none => rw [hR] at hStep; exact storeObject_machine_eq _ _ _ _ hStep
      | some root =>
        rw [hR] at hStep
        simp only at hStep
        split at hStep
        · split at hStep
          · cases hStep
          · cases hS1 : storeObject tableId _ st with
            | error e => rw [hS1] at hStep; cases hStep
            | ok p =>
              obtain ⟨⟨⟩, st1⟩ := p
              rw [hS1] at hStep
              rw [storeObject_machine_eq _ _ _ _ hStep, Architecture.recordPhysicalWrites_machine,
                storeObject_machine_eq _ _ _ _ hS1]
        · exact storeObject_machine_eq _ _ _ _ hStep

theorem revokeServiceByRecordedRegistration_machine_eq {epId : SeLe4n.ObjId} {st st' : SystemState}
    (h : revokeServiceByRecordedRegistration epId st = .ok ((), st')) :
    st'.machine = st.machine := by
  obtain ⟨_, h⟩ := revokeServiceByRecordedRegistration_revokeService h
  exact revokeService_preserves_machine _ _ _ h

theorem mintReplyCapWithCdt_machine_eq {st st' : SystemState} {src dst : CSpaceAddr}
    (hStep : mintReplyCapWithCdt src dst st = .ok ((), st')) : st'.machine = st.machine := by
  unfold mintReplyCapWithCdt at hStep
  split at hStep
  · contradiction
  · rename_i stM hMint
    cases hStep
    rw [SystemState.cdtAddChild_machine]
    unfold mintReplyCap at hMint
    split at hMint
    · contradiction
    · rename_i parent stMid hLk
      have hMid : stMid = st := cspaceLookupSlot_state_eq st stMid src parent hLk
      subst hMid
      split at hMint
      · dsimp only [] at hMint
        split at hMint
        · exact cspaceInsertSlot_preserves_machine _ _ _ _ hMint
        · contradiction
      · contradiction

theorem untypedResetFromCap_machine_eq {tid : SeLe4n.ThreadId} {srcAddr : SeLe4n.CPtr}
    {st st' : SystemState} (hStep : untypedResetFromCap tid srcAddr st = .ok ((), st')) :
    st'.machine = st.machine := by
  obtain ⟨_, _, _, -, -, hS⟩ := untypedResetFromCap_ok _ _ st st' hStep
  rw [untypedResetSlot_ok_frame hS, setCapFreeIndex_machine]

theorem releaseFinalRegistration_machine (target : Nat) (st : SystemState) :
    (releaseFinalRegistration target st).machine = st.machine := by
  unfold releaseFinalRegistration
  repeat' split
  all_goals first | rfl | (rename_i h; exact revokeService_preserves_machine _ _ _ h)

theorem cspaceMint_machine_eq {st st' : SystemState} {src dst : CSpaceAddr}
    {rights : AccessRightSet} {badge : Option SeLe4n.Badge}
    (hStep : cspaceMint src dst rights badge st = .ok ((), st')) : st'.machine = st.machine := by
  unfold cspaceMint at hStep
  split at hStep
  · contradiction
  · rename_i parent stMid hLk
    have hMid : stMid = st := cspaceLookupSlot_state_eq st stMid src parent hLk
    subst hMid
    split at hStep
    · contradiction
    · split at hStep
      · contradiction
      · exact cspaceInsertSlot_preserves_machine _ _ _ _ hStep

theorem cspaceMintWithCdt_machine_eq {st st' : SystemState} {src dst : CSpaceAddr}
    {rights : AccessRightSet} {badge : Option SeLe4n.Badge}
    (hStep : cspaceMintWithCdt src dst rights badge st = .ok ((), st')) :
    st'.machine = st.machine := by
  obtain ⟨_, stM, hMint, -, -, rfl⟩ := cspaceMintWithCdt_ok_decompose hStep
  rw [untypedSourceSetFull_machine, SystemState.cdtAddChild_machine, cspaceMint_machine_eq hMint]

theorem cspaceCopy_machine_eq {st st' : SystemState} {src dst : CSpaceAddr}
    (hStep : cspaceCopy src dst st = .ok ((), st')) : st'.machine = st.machine := by
  obtain ⟨_, st2, -, -, hIns, -, rfl⟩ := cspaceCopy_ok_decompose hStep
  rw [untypedSourceSetFull_machine, SystemState.cdtAddChild_machine,
    cspaceInsertSlot_preserves_machine _ _ _ _ hIns]

theorem cspaceMove_machine_eq {st st' : SystemState} {src dst : CSpaceAddr}
    (hStep : cspaceMove src dst st = .ok ((), st')) : st'.machine = st.machine := by
  unfold cspaceMove at hStep
  split at hStep
  · contradiction
  · split at hStep
    · contradiction
    · rename_i cap stMid hLk
      have hMid : stMid = st := cspaceLookupSlot_state_eq st stMid src cap hLk
      subst hMid
      split at hStep
      · contradiction
      · split at hStep
        · contradiction
        · rename_i st2 hIns
          split at hStep
          · contradiction
          · rename_i st3 hDel
            cases hStep
            rw [SystemState.cdtMove_machine,
              (cspaceDeleteSlotCore_scheduler_machine src st2 st3 hDel).2,
              cspaceInsertSlot_preserves_machine _ _ _ _ hIns]

theorem retirePendingFaultForResume_machine (st : SystemState) (tid : SeLe4n.ThreadId) :
    (retirePendingFaultForResume st tid).machine = st.machine := by
  unfold retirePendingFaultForResume
  repeat' split
  all_goals simp [applyFaultRestart_machine_eq, discardPendingFault_machine_eq]

theorem vspaceMapFromFrameCap_machine_eq {tid : SeLe4n.ThreadId} {ec : CoreId}
    {args : Architecture.SyscallArgDecode.VSpaceMapArgs} {st st' : SystemState}
    (h : vspaceMapFromFrameCap tid ec args st = .ok ((), st')) : st'.machine = st.machine := by
  obtain ⟨_, _, _, st1, _, _, _, _, _, hMap, epoch, st2, hT, hRec⟩ :=
    vspaceMapFromFrameCap_ok tid ec args st st' h
  obtain ⟨_, _, _, _, hStore⟩ := cspaceRecordFrameMapping_ok_decompose _ _ st2 st' hRec
  exact (storeObject_machine_eq _ _ _ _ hStore).trans
    ((tagFrameMapping_scheduler_machine _ _ _ st1 st2 epoch hT).2.trans
      (vspaceMapPageCheckedWithShootdownFromStatePerCore_framed _ _ _ _ _ st st1 hMap).2)

theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_machine_eq {ec : CoreId}
    {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr} {st st' : SystemState}
    (h : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast ec asid vaddr st
      = .ok ((), st')) : st'.machine = st.machine :=
  (vspaceUnmapPageWithShootdownAndIcacheBroadcast_framed ec asid vaddr st st' h).2

macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (completeYieldFrom_machine _ _).trans ?_; machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (storeUnbindNotification_machine _ _ _).trans ?_; machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (Architecture.writeReturnFrameToTcb_machine_eq _ _ _).trans ?_;
   machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (bindNotification_machine_eq (by assumption)).trans ?_; machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (unbindNotification_machine_eq (by assumption)).trans ?_; machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (pageTableMap_machine_eq (by assumption)).trans ?_; machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (pageTableUnmap_machine_eq (by assumption)).trans ?_; machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (revokeServiceByRecordedRegistration_machine_eq (by assumption)).trans ?_;
   machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (vspaceMapFromFrameCap_machine_eq (by assumption)).trans ?_;
   machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine
    (vspaceUnmapPageWithShootdownAndIcacheBroadcast_machine_eq (by assumption)).trans ?_;
   machine_chain))

macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (threadSlotCopied_machine _ _ _ _ _ _).trans ?_; machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (setThreadFaultHandlerOp_machine_eq (by assumption)).trans ?_;
   machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (setIPCBufferOp_machine_eq _ _ _ _ (by assumption)).trans ?_;
   machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (setConsumed_machine _ _ _).trans ?_; machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (SystemState.cancelYieldTo_machine _ _).trans ?_; machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (clearWokenReceiverStash_machine_eq _ _ _ (by assumption)).trans ?_;
   machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (storeTcbWith_machine _ _ _).trans ?_; machine_chain))

/-- The declassified signal covers: the bound signal, then the audit records,
which touch the trail alone. -/
theorem notificationSignalDeclassifiedOnCore_stepCovers (e : CoreId)
    {ctx : GenericLabelingContext} {declPolicy : DeclassificationPolicy}
    {notificationId : SeLe4n.ObjId} {badge : SeLe4n.Badge} {c : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) :
    stepCovers e st (notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge
      c st).1 ∧
    (notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge
      c st).1.objects.invExt := by
  have hRefl : stepCovers e st st ∧ st.objects.invExt := ⟨stepCovers_refl e st, hInv⟩
  unfold notificationSignalDeclassifiedOnCore
  split
  · exact hRefl
  split
  · split <;> exact hRefl
  dsimp only
  split
  · exact hRefl
  have hB := notificationSignalBoundOnCore_stepCovers e (notificationId := notificationId)
    (badge := badge) (executingCore := c) hInv
  generalize notificationSignalBoundOnCore notificationId badge c st = r at hB
  obtain ⟨st1, res⟩ := r
  obtain ⟨hB, hBInv⟩ := hB
  cases res with
  | error _ => exact hRefl
  | ok sgi =>
    dsimp only at hB ⊢
    split
    · exact hRefl
    · rename_i st2 hRec
      rw [recordDeclassifiedHops_frame _ _ _ _ _ hRec]
      exact ⟨stepCovers_trans hB (stepCovers_of_scheduler_eq (keyInputsEq_of_objects_eq rfl) rfl),
        hBInv⟩

/-- A key frame covers and keeps the store invariant. -/
theorem capabilityKeyFrame.stepCoversInv {e : CoreId} {st st' : SystemState}
    (h : capabilityKeyFrame st st')
    (hRes : st'.machine.residentCode = st.machine.residentCode := by resident_frame)
    (hBank : banksKeptOffCore e st st' := by bank_kept) :
    SeLe4n.Kernel.stepCovers e st st' ∧ st'.objects.invExt :=
  ⟨h.stepCovers hRes hBank, h.2.2⟩

/-- Coverage composes, the invariant read off the second leg. -/
theorem stepCoversInv_trans {e : CoreId} {a b d : SystemState} (h₁ : stepCovers e a b)
    (h₂ : stepCovers e b d ∧ d.objects.invExt) : stepCovers e a d ∧ d.objects.invExt :=
  ⟨stepCovers_trans h₁ h₂.1, h₂.2⟩

/-! ### The final-delete retire -/

/-- A binding that names a scheduling context carries its code. -/
theorem SchedContextBinding.scCode_of_scId? {b : SchedContextBinding} {sc : SeLe4n.SchedContextId}
    (h : b.scId? = some sc) : b.scCode = sc.val + 1 := by
  cases b with
  | unbound => cases h
  | bound s => cases h; rfl
  | donated s o => cases h; rfl

/-- **The retire keeps the key of every thread it keeps**: the thread's own
fields are untouched, and the scheduling context its binding names is named by
it, so — the binding pair, the loan record and the budgets holding — the retire
guard refuses that context (`schedContextRetirable_false_of_tcbNamed`) and it
stays. -/
theorem retireFinalObject_getSchedContext?_named (ec : CoreId) (target recorder : Nat)
    (st : SystemState)
    (hObjInv : st.objects.invExt) (hI : ipcInvariantFull st) (hL : schedContextLinkInvariant st)
    {t : SeLe4n.ThreadId} {x : TCB}
    (hx : (retireFinalObject ec target recorder st).getTcb? t = some x)
    (sc : SeLe4n.SchedContextId) (hsc : x.schedContextBinding.scId? = some sc) :
    (retireFinalObject ec target recorder st).getSchedContext? sc = st.getSchedContext? sc := by
  have hp := (SystemState.getTcb?_eq_some_iff _ t x).mp hx
  have hk := retireFinalObject_tcb_back ec target recorder st hObjInv hp
  unfold SystemState.getSchedContext?
  cases hS : st.objects[sc.toObjId]? with
  | some o =>
    cases o with
    | schedContext s =>
      have hN : objectNamesSchedContext (.tcb x) (sc.toObjId.val + 1) = true := by
        have hc := SchedContextBinding.scCode_of_scId? hsc
        rw [SeLe4n.Kernel.SchedContextBinding.scCode_ofCodes] at hc
        simp only [objectNamesSchedContext, Bool.or_eq_true, beq_iff_eq]
        exact .inl hc
      rw [retireFinalObject_schedContext ec target recorder st hObjInv hS
        (schedContextRetirable_false_of_tcbNamed hL.binding hI.donationOwnerValid hL.budgets
          hk hN)]
    | _ =>
      cases hP : (retireFinalObject ec target recorder st).objects[sc.toObjId]? with
      | none => rfl
      | some o' =>
        cases o' with
        | schedContext s' =>
          rw [retireFinalObject_back ec target recorder st hObjInv hP (fun _ e => by cases e)] at hS
          cases hS
        | _ => rfl
  | none =>
    cases hP : (retireFinalObject ec target recorder st).objects[sc.toObjId]? with
    | none => rfl
    | some o' =>
      cases o' with
      | schedContext s' =>
        rw [retireFinalObject_back ec target recorder st hObjInv hP (fun _ e => by cases e)] at hS
        cases hS
      | _ => rfl

/-- **The retire keeps the key of every thread it keeps**: the thread's own
fields are untouched and the context its binding names stays
(`retireFinalObject_getSchedContext?_named`). -/
theorem retireFinalObject_schedKeyView (ec : CoreId) (target recorder : Nat) (st : SystemState)
    (hObjInv : st.objects.invExt) (hI : ipcInvariantFull st) (hL : schedContextLinkInvariant st)
    {t : SeLe4n.ThreadId} {x : TCB}
    (hx : (retireFinalObject ec target recorder st).getTcb? t = some x) :
    schedKeyView (retireFinalObject ec target recorder st) t = schedKeyView st t := by
  have hp := (SystemState.getTcb?_eq_some_iff _ t x).mp hx
  have hk := retireFinalObject_tcb_back ec target recorder st hObjInv hp
  have hpre : st.getTcb? t = some x := (SystemState.getTcb?_eq_some_iff st t x).mpr hk
  unfold schedKeyView
  rw [hx, hpre]
  simp only [Option.map_some, Option.some.injEq]
  rw [effectiveSchedParams_congr_binding (st := st) (st' := retireFinalObject ec target recorder st)
    (a := x) (b := x) rfl (fun sc hsc => by
    rw [retireFinalObject_getSchedContext?_named ec target recorder st hObjInv hI hL hx sc hsc])]

/-- **The retire keeps the budget eligibility of every thread it keeps**, by the
same context-stays argument. -/
theorem retireFinalObject_budgetEligibleView (ec : CoreId) (target recorder : Nat)
    (st : SystemState)
    (hObjInv : st.objects.invExt) (hI : ipcInvariantFull st) (hL : schedContextLinkInvariant st)
    {t : SeLe4n.ThreadId} {x : TCB}
    (hx : (retireFinalObject ec target recorder st).getTcb? t = some x) :
    budgetEligibleView (retireFinalObject ec target recorder st) t = budgetEligibleView st t := by
  have hp := (SystemState.getTcb?_eq_some_iff _ t x).mp hx
  have hk := retireFinalObject_tcb_back ec target recorder st hObjInv hp
  have hpre : st.getTcb? t = some x := (SystemState.getTcb?_eq_some_iff st t x).mpr hk
  unfold budgetEligibleView
  rw [hx, hpre]
  simp only [Option.map_some, Option.some.injEq]
  rw [hasSufficientBudget_congr_binding (st := st) (st' := retireFinalObject ec target recorder st)
    (a := x) (b := x) rfl (fun sc hsc => by
    rw [retireFinalObject_getSchedContext?_named ec target recorder st hObjInv hI hL hx sc hsc])]

/-- **The retire keeps every resident's TCB**: a thread it erases is held on
no core (`threadRetirable`), so no core's resident is a thread it erases. -/
theorem retireFinalObject_residentTcbKept (e ec : CoreId) (target recorder : Nat)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    residentTcbKeptOffCore e st (retireFinalObject ec target recorder st) := by
  intro c _ r hR hT
  rw [(retireFinalObject_fields ec target recorder st).2.2] at hR
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hT
  have hk := (SystemState.getTcb?_eq_some_iff st r x).mp hx
  rcases retireFinalObject_tcb_kept_or_quiescent ec target recorder st hObjInv hk with
    hE | ⟨-, hId, -, -, hH⟩
  · rw [(SystemState.getTcb?_eq_some_iff _ r x).mpr (hE.trans hk)]; rfl
  · have hEq : x.tid = r :=
      SeLe4n.ThreadId.toObjId_injective _ _ (congrArg SeLe4n.ObjId.ofNat hId)
    have hNo : st.machine.residentOnSomeCore x.tid = false := by
      unfold threadHeldOnSomeCore at hH
      simp only [Bool.or_eq_false_iff] at hH
      exact hH.2
    rw [hEq] at hNo
    exact absurd hR ((MachineState.residentOnSomeCore_eq_false_iff _ _).mp hNo c)

/-- **The final-delete retire covers**: it frames the scheduler and every
thread's run-queue links, so no core's queue gains a thread and no current slot
moves, and every thread it keeps keeps its key
(`retireFinalObject_schedKeyView`); the thread it erases is queued nowhere and
claims nothing afterwards. -/
theorem retireFinalObject_stepCovers (e ec : CoreId) (target recorder : Nat) (st : SystemState)
    (hObjInv : st.objects.invExt) (hI : ipcInvariantFull st) (hL : schedContextLinkInvariant st) :
    stepCovers e st (retireFinalObject ec target recorder st) ∧
      (retireFinalObject ec target recorder st).objects.invExt := by
  have hS := (retireFinalObject_fields ec target recorder st).2.1
  have hQ : ∀ c t, (retireFinalObject ec target recorder st).queuedOn c t = st.queuedOn c t :=
    fun c t => by
      rw [SystemState.queuedOn_eq_runLinkOn, SystemState.queuedOn_eq_runLinkOn,
        retireFinalObject_runLinkOn ec target recorder hObjInv]
  have hView : ∀ t kq, schedKeyView (retireFinalObject ec target recorder st) t = some kq →
      schedKeyView (retireFinalObject ec target recorder st) t = schedKeyView st t := by
    intro t kq hq
    unfold schedKeyView at hq
    cases hx : (retireFinalObject ec target recorder st).getTcb? t with
    | none => rw [hx] at hq; cases hq
    | some x => exact retireFinalObject_schedKeyView ec target recorder st hObjInv hI hL hx
  refine ⟨⟨fun c _ => .inr ⟨fun t ht => ⟨(hQ c t) ▸ ht, ?_⟩, by rw [hS],
      fun t _ kq hq => ⟨kq, ((hView t kq hq).symm.trans hq), Nat.le_refl _, Nat.le_refl _, rfl⟩⟩,
    reschedulePendingMonotone_of_scheduler_eq hS,
    currentKeptOffCore_of_eq fun c _ => by rw [hS],
    residentKeptOffCore_of_eq (by rw [(retireFinalObject_fields ec target recorder st).2.2]), banksKeptOffCore_of_eq (by rw [(retireFinalObject_fields ec target recorder st).2.2]),
    retireFinalObject_residentTcbKept e ec target recorder st hObjInv⟩,
    (retireFinalObject_frame ec target recorder st hObjInv).1⟩
  unfold SystemState.queuedOn at ht
  cases hx : (retireFinalObject ec target recorder st).getTcb? t with
  | none => rw [hx] at ht; cases ht
  | some x =>
    exact ⟨(retireFinalObject_schedKeyView ec target recorder st hObjInv hI hL hx).symm,
      candidacyNotGained_of_eq
        (retireFinalObject_budgetEligibleView ec target recorder st hObjInv hI hL hx).symm⟩

/-- A thread space slot's set covers: the copy moves no key input, and the
retire of what the old capability took with it covers
(`retireFinalObject_stepCovers`). -/
theorem threadSlotSet_stepCovers (e ec : CoreId) {st : SystemState} {tid : SeLe4n.ThreadId}
    {t : TCB} (hObjInv : st.objects.invExt) (hI : ipcInvariantFull st)
    (hL : schedContextLinkInvariant st) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    stepCovers e st (threadSlotSet ec st tid slot srcCNode srcSlot rights) ∧
      (threadSlotSet ec st tid slot srcCNode srcSlot rights).objects.invExt := by
  unfold threadSlotSet
  exact stepCoversInv_trans
    (threadSlotCopied_keyFrame hObjInv hT slot srcCNode srcSlot rights).stepCovers
    (retireFinalObject_stepCovers e ec _ _ _
      (threadSlotCopied_tcb hObjInv hT slot srcCNode srcSlot rights).2
      (threadSlotCopied_preserves_ipcInvariantFull hObjInv hI hT slot srcCNode srcSlot rights)
      ((SchedLinkFrame.threadSlotCopied hObjInv hT slot srcCNode srcSlot rights).preserves hL))

theorem copyThreadSpaces_stepCovers (e ec : CoreId) (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (cnSrc vrSrc : CSpaceAddr) (hObjInv : st.objects.invExt)
    (hI : ipcInvariantFull st) (hL : schedContextLinkInvariant st)
    (hStep : copyThreadSpaces ec st vtid cnSrc vrSrc = .ok st') :
    stepCovers e st st' ∧ st'.objects.invExt := by
  obtain ⟨tcb, hT, -, -, hCn, -, rfl⟩ := copyThreadSpaces_ok hStep
  obtain ⟨cnCap, -, hCL, -⟩ := cspaceRootSourceAdmitted_spec hCn
  obtain ⟨t1, hT1'⟩ := Option.isSome_iff_exists.mp
    (threadSlotSet_getTcb? ec hObjInv hT (slot := TCB.cspaceRootSlot) (by decide)
      cnSrc.cnode cnSrc.slot
      TCB.cspaceRootRights hCL)
  have hI1 : (threadSlotSet ec st vtid.val TCB.cspaceRootSlot cnSrc.cnode cnSrc.slot
      TCB.cspaceRootRights).objects.invExt := by
    unfold threadSlotSet
    exact (retireFinalObject_frame ec _ _ _ (threadSlotCopied_tcb hObjInv hT TCB.cspaceRootSlot
      cnSrc.cnode cnSrc.slot TCB.cspaceRootRights).2).1
  exact stepCoversInv_trans (threadSlotSet_stepCovers e ec hObjInv hI hL hT _ _ _ _).1
    (threadSlotSet_stepCovers e ec hI1
      (threadSlotSet_preserves_ipcInvariantFull ec hObjInv hI hL.budgets hT _ _ _ _).1
      (threadSlotSet_preserves_schedContextLinkInvariant ec hObjInv hL hT _ _ _ _) hT1' _ _ _ _)

/-! ### Retype -/

/-- Every thread queued or current on a core has a TCB. -/
def placedThreadsHaveTcbs (st : SystemState) : Prop :=
  ∀ c t, (t ∈ st.scheduler.runQueueOnCore c ∨ st.scheduler.currentOnCore c = some t) →
    (st.getTcb? t).isSome

/-- A write that moves only slot `X` keeps the key of every thread that neither
lives at `X` nor names `X` as its scheduling context. -/
theorem schedKeyView_eq_of_slotUnread {pre post : SystemState} {X : SeLe4n.ObjId}
    (hFrame : ∀ oid, oid ≠ X → keyInputsOf post.objects[oid]? = keyInputsOf pre.objects[oid]?)
    {t : SeLe4n.ThreadId} (ht : t.toObjId ≠ X)
    (hNo : ∀ tcb, pre.getTcb? t = some tcb → ∀ sc, tcb.schedContextBinding.scId? = some sc →
      sc.toObjId ≠ X) :
    schedKeyView post t = schedKeyView pre t := by
  have hT := getTcb?_keyFields_of_keyInputsOf (hFrame _ ht)
  unfold schedKeyView
  cases hq : post.getTcb? t <;> cases hp : pre.getTcb? t <;> simp only [hq, hp] at hT ⊢
  · rfl
  · simp at hT
  · simp at hT
  · rename_i b a
    simp only [Option.map_some, Option.some.injEq] at hT ⊢
    rw [effectiveSchedParams_congr_binding hT (fun sc hsc =>
      getSchedContext?_deadline_of_keyInputsOf (hFrame _ (hNo a hp sc hsc)))]

/-- The budget-eligibility twin of `schedKeyView_eq_of_slotUnread`: a step that
moves no key input off slot `X` keeps the eligibility of every thread neither
living at `X` nor bound to a context stored there. -/
theorem budgetEligibleView_eq_of_slotUnread {pre post : SystemState} {X : SeLe4n.ObjId}
    (hFrame : ∀ oid, oid ≠ X → keyInputsOf post.objects[oid]? = keyInputsOf pre.objects[oid]?)
    {t : SeLe4n.ThreadId} (ht : t.toObjId ≠ X)
    (hNo : ∀ tcb, pre.getTcb? t = some tcb → ∀ sc, tcb.schedContextBinding.scId? = some sc →
      sc.toObjId ≠ X) :
    budgetEligibleView post t = budgetEligibleView pre t := by
  have hT := getTcb?_keyFields_of_keyInputsOf (hFrame _ ht)
  unfold budgetEligibleView
  cases hq : post.getTcb? t <;> cases hp : pre.getTcb? t <;> simp only [hq, hp] at hT ⊢
  · rfl
  · simp at hT
  · simp at hT
  · rename_i b a
    simp only [Option.map_some, Option.some.injEq, tcbKeyFields, Prod.mk.injEq] at hT ⊢
    rw [hasSufficientBudget_congr_binding hT.2.2.1 (fun sc hsc =>
      getSchedContext?_budget_of_keyInputsOf (hFrame _ (hNo a hp sc hsc)))]

/-- One slot's key inputs fix whether the thread living there is queued on a core. -/
theorem queuedOn_of_keyInputsOf {pre post : SystemState} {t : SeLe4n.ThreadId}
    (hk : keyInputsOf post.objects[t.toObjId]? = keyInputsOf pre.objects[t.toObjId]?)
    (c : CoreId) : post.queuedOn c t = pre.queuedOn c t := by
  unfold SystemState.queuedOn SystemState.getTcb?
  revert hk
  generalize post.objects[t.toObjId]? = a
  generalize pre.objects[t.toObjId]? = b
  intro hk
  cases a with
  | none => cases b with
    | none => rfl
    | some o => cases o <;> simp_all [keyInputsOf]
  | some o => cases b with
    | none => cases o <;> simp_all [keyInputsOf]
    | some o' => cases o <;> cases o' <;> simp_all [keyInputsOf]

/-- **A step that fills one empty slot with an object queued nowhere covers**:
no thread placed before it lives at the slot (each has a TCB) or reads its
deadline there (the binding reciprocity names a scheduling context stored
elsewhere), so every key a remote decision read is unchanged, and the new
object joins no run queue. -/
theorem stepCovers_of_freshSlot (e : CoreId) {pre post : SystemState} {X : SeLe4n.ObjId}
    (hFrame : ∀ oid, oid ≠ X → keyInputsOf post.objects[oid]? = keyInputsOf pre.objects[oid]?)
    (hAbs : pre.objects[X]? = none)
    (hUnq : ∀ c (t : SeLe4n.ThreadId), t.toObjId = X → post.queuedOn c t = false)
    (hSched : post.scheduler = pre.scheduler)
    (hBi : schedContextBindingBidirectional pre) (hPlaced : placedThreadsHaveTcbs pre)
    (hRes : post.machine.residentCode = pre.machine.residentCode)
    (hBk : post.machine.coreRegs = pre.machine.coreRegs) :
    stepCovers e pre post := by
  have hKeyNe : ∀ t, t.toObjId ≠ X → schedKeyView post t = schedKeyView pre t := by
    intro t ht
    refine schedKeyView_eq_of_slotUnread hFrame ht ?_
    intro tcb hT sc hsc hEq
    obtain ⟨sco, hSo, _⟩ := hBi t tcb sc ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hsc
    rw [hEq, hAbs] at hSo; cases hSo
  refine ⟨fun c _ => Or.inr ⟨fun t ht => ?_, by rw [hSched], fun t ht => ?_⟩,
    fun c _ hc => by rw [hSched]; exact hc, currentKeptOffCore_of_eq fun c _ => by rw [hSched],
    residentKeptOffCore_of_eq hRes, banksKeptOffCore_of_eq hBk,
    tcbsKept.residentTcbKept fun t hT => tcbsKept.of_view (hKeyNe t fun hEq => by
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hT
      have := (SystemState.getTcb?_eq_some_iff _ _ _).mp hx
      rw [hEq, hAbs] at this; cases this) hT⟩
  · have hne : t.toObjId ≠ X := fun hEq => by rw [hUnq c t hEq] at ht; cases ht
    refine ⟨(queuedOn_of_keyInputsOf (hFrame _ hne) c) ▸ ht, (hKeyNe t hne).symm,
      candidacyNotGained_of_eq (budgetEligibleView_eq_of_slotUnread hFrame hne ?_).symm⟩
    intro tcb hT sc hsc hEq
    obtain ⟨sco, hSo, _⟩ := hBi t tcb sc ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hsc
    rw [hEq, hAbs] at hSo; cases hSo
  · rw [hSched] at ht
    refine schedKeyNotWeakened_of_eq (hKeyNe t (fun hEq => ?_)).symm
    obtain ⟨tcb, hT⟩ := Option.isSome_iff_exists.mp (hPlaced c t (Or.inr ht))
    have hTo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
    rw [hEq, hAbs] at hTo; cases hTo

/-- The carve writes objects, the CDT and frame memory, no residency record. -/
theorem untypedRetypeObject_residentCode {src dst : CSpaceAddr} {childId : SeLe4n.ObjId}
    {req : CarveRequest} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : untypedRetypeObject src childId dst req st = .ok ((), st')) :
    st'.machine.residentCode = st.machine.residentCode := by
  obtain ⟨utCap, untypedId, ut, st1, st2, _, _, _, hRt, hIns, rfl⟩ :=
    untypedRetypeObject_ok_decompose src dst childId req st st' hInv h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hStUt, hStCh, _, hStIdx⟩ :=
    retypeFromUntyped_ok_stores st st1 src untypedId childId _ _ hInv hRt
  rw [SystemState.cdtAddChild_machine, cspaceInsertSlot_preserves_machine _ _ _ _ hIns,
    CarveRequest.scrub_residentCode, storeObject_machine_eq _ _ _ _ hStIdx,
    storeObject_machine_eq _ _ _ _ hStCh, storeObject_machine_eq _ _ _ _ hStUt]

/-- The scrub writes memory alone, no core's bank. -/
theorem CarveRequest.scrub_coreRegs (st : SystemState) (ut : UntypedObject) (idx : Nat)
    (req : CarveRequest) :
    (req.scrub st ut idx).machine.coreRegs = st.machine.coreRegs := by
  cases req <;> simp only [CarveRequest.scrub, carveZeroFrame] <;> (try split) <;> rfl

/-- ...and the carve writes no core's bank. -/
theorem untypedRetypeObject_coreRegs {src dst : CSpaceAddr} {childId : SeLe4n.ObjId}
    {req : CarveRequest} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : untypedRetypeObject src childId dst req st = .ok ((), st')) :
    st'.machine.coreRegs = st.machine.coreRegs := by
  obtain ⟨utCap, untypedId, ut, st1, st2, _, _, _, hRt, hIns, rfl⟩ :=
    untypedRetypeObject_ok_decompose src dst childId req st st' hInv h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hStUt, hStCh, _, hStIdx⟩ :=
    retypeFromUntyped_ok_stores st st1 src untypedId childId _ _ hInv hRt
  rw [SystemState.cdtAddChild_machine, cspaceInsertSlot_preserves_machine _ _ _ _ hIns,
    CarveRequest.scrub_coreRegs, storeObject_machine_eq _ _ _ _ hStIdx,
    storeObject_machine_eq _ _ _ _ hStCh, storeObject_machine_eq _ _ _ _ hStUt]

/-- A thread's final-delete core release writes the FP/SIMD owners and the
residency records, no core's bank. -/
theorem finaliseThreadReleaseCores_coreRegs (st : SystemState) (tid : SeLe4n.ThreadId) :
    (finaliseThreadReleaseCores st tid).machine.coreRegs = st.machine.coreRegs := by
  rw [finaliseThreadReleaseCores_machine, MachineState.releaseThread,
    MachineState.releaseThreadOnCores_fields]

/-- **The carve covers** (WS-ZA ZA5.4 part 14), for every kind it makes: the
child's slot was empty and the object stored there is queued nowhere — a carved
TCB is inactive with empty links — and no other key input moved. -/
theorem untypedRetypeObject_stepCovers (e : CoreId) {src dst : CSpaceAddr}
    {childId : SeLe4n.ObjId} {req : CarveRequest} {st st' : SystemState}
    (hInv : st.objects.invExt) (hBi : schedContextBindingBidirectional st)
    (hPlaced : placedThreadsHaveTcbs st)
    (h : untypedRetypeObject src childId dst req st = .ok ((), st')) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  obtain ⟨hFrame, hAbs, hUnq, hSched, hInv'⟩ :=
    untypedRetypeObject_keyFrameOffChild src dst childId req st st' hInv h
  exact ⟨stepCovers_of_freshSlot e hFrame hAbs hUnq hSched hBi hPlaced
    (untypedRetypeObject_residentCode hInv h) (untypedRetypeObject_coreRegs hInv h), hInv'⟩

/-! ### The finalising destroyers -/

/-- WS-ZA ZA5.4 part 23: **an endpoint waiter's cancel covers**: the head pop
(`endpointQueuePopHead_keyFrame`, through `popHead_inPlace`) and the waiter's
rewrite move no key input and no scheduler field, and the wake raises the flag
of the core it queues on (`enqueueRunnableOnCore_covers`). -/
theorem storeEndpointWaiterCancelled_stepCovers (e : CoreId) (st : SystemState)
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (ep : Endpoint) (t : SeLe4n.ThreadId)
    (tcb : TCB) (hInv : st.objects.invExt) (hE : st.getEndpoint? endpointId = some ep)
    (hH : (endpointWaitQueue ep isReceiveQ).head = some t) (hT : st.getTcb? t = some tcb)
    (hC : endpointWaiterCancellable st endpointId t tcb = true) :
    stepCovers e st (storeEndpointWaiterCancelled st endpointId isReceiveQ t tcb.queueNext) := by
  obtain ⟨-, -, hG⟩ := endpointWaiterCancellable_parts hC
  have hEo := (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hE
  have hTo := (SystemState.getTcb?_eq_some_iff st t tcb).mp hT
  have hH' : (if isReceiveQ then ep.receiveQ else ep.sendQ).head = some t := hH
  obtain ⟨hPop, -⟩ := popHead_inPlace st endpointId isReceiveQ ep t tcb hEo hH' hTo hG
  have hF1 := endpointQueuePopHead_keyFrame hInv hPop
  unfold storeEndpointWaiterCancelled wakeCancelledWaiter
  generalize storePopHead st endpointId isReceiveQ t tcb.queueNext = s1 at hPop hF1 ⊢
  have hI2 := SystemState.updateTcb_preserves_objects_invExt s1 t cancelledEndpointWaiterTcb hF1.2.2
  have hK : keyInputsEq s1 (s1.updateTcb t cancelledEndpointWaiterTcb) :=
    keyInputsEq_updateTcb hF1.2.2 (fun _ => rfl)
  have hS : (s1.updateTcb t cancelledEndpointWaiterTcb).scheduler = st.scheduler := by
    rw [SystemState.updateTcb_scheduler, hF1.2.1]
  have h1 : stepCovers e st (s1.updateTcb t cancelledEndpointWaiterTcb) :=
    stepCovers_of_keys_sched (keyInputsEq_trans hF1.1 hK) hS
  exact stepCovers_trans h1
    ⟨enqueueRunnableOnCore_covers e (determineTargetCore (s1.updateTcb t cancelledEndpointWaiterTcb) t)
      _ t hI2, enqueueRunnableOnCore_monotone e _ _ t, enqueueRunnableOnCore_currentKept e _ _ _,
      residentKeptOffCore_of_eq (by rw [enqueueRunnableOnCore_machineEq]), banksKeptOffCore_of_eq (by rw [enqueueRunnableOnCore_machineEq]),
      (tcbsKept_enqueueRunnableOnCore _ _ _ hI2).residentTcbKept⟩

/-- WS-ZA ZA5.4 part 24: **a thread's endpoint cancel covers**: the removal
(`endpointQueueRemoveDual_keyFrame`, through `queueRemove_inPlace`) and the
thread's rewrite move no key input and no scheduler field. -/
theorem storeEndpointBlockedCancelled_stepCovers (e : CoreId) (st : SystemState)
    (en : SeLe4n.ObjId) (q : Bool) (t : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB)
    (hInv : st.objects.invExt) (hT : st.getTcb? t = some tcb) (hE : st.getEndpoint? en = some ep)
    (hC : endpointBlockedCancellable st en q t ep tcb = true) :
    stepCovers e st (storeEndpointBlockedCancelled st en q t ep tcb) ∧
      (storeEndpointBlockedCancelled st en q t ep tcb).objects.invExt := by
  obtain ⟨-, -, hG, -⟩ := endpointBlockedCancellable_parts hC
  obtain ⟨hRem, -⟩ := queueRemove_inPlace st en q t ep tcb
    ((SystemState.getEndpoint?_eq_some_iff st en ep).mp hE)
    ((SystemState.getTcb?_eq_some_iff st t tcb).mp hT) hG
  have hF1 := endpointQueueRemoveDual_keyFrame hInv hRem
  unfold storeEndpointBlockedCancelled
  exact (hF1.trans (updateTcb_keyFrame _ t (f := cancelledEndpointWaiterTcb) (fun _ => rfl)
    hF1.2.2)).stepCoversInv

/-- WS-ZA ZA5.4 part 23: **a notification waiter's cancel covers**: the
cancellation (`cancelIpcBlocking_stepCovers`), then the wake. -/
theorem notificationWaiterCancel_stepCovers (e : CoreId) (st : SystemState)
    (t : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt) :
    stepCovers e st (wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking st t tcb) t) :=
  stepCovers_trans (cancelIpcBlocking_stepCovers e st t tcb hInv)
    ⟨enqueueRunnableOnCore_covers e _ _ t
      (Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt st t tcb hInv),
     enqueueRunnableOnCore_monotone e _ _ t, enqueueRunnableOnCore_currentKept e _ _ _,
     residentKeptOffCore_of_eq (by
       unfold wakeCancelledWaiter; rw [enqueueRunnableOnCore_machineEq]), banksKeptOffCore_of_eq (by
       unfold wakeCancelledWaiter; rw [enqueueRunnableOnCore_machineEq]),
     (tcbsKept_enqueueRunnableOnCore _ _ _
       (Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt st t tcb hInv)).residentTcbKept⟩

/-- WS-ZA ZA5.4 parts 23–24: **the finalisation covers**, every step of it
(`finaliseFinalObject_closed`): each cancel's, the notification unbind's
(`unbindNotification_keyFrame`, through `unbindNotification_of_inPlace`), a
context's dequeue of its holder (`descheduleAtPlacement_stepCovers`), the
reservation unbind's (`cancelBoundDonationOnCore_stepCovers`), the suspend — the
deschedule wherever the thread is placed (`descheduleAtPlacement_stepCovers`),
then a mark that writes no key field (`updateTcb_keyFrame`) — the release of the
cores' holds on the thread, which writes no object and no scheduler field, a
context's reply-stack unlink (a reply and a context's head, neither a key
input), a reply's caller cancel — a head reply's with its loan returned and its
holder descheduled (`cancelIpcBlockingReclaimed_stepCovers`) — with its boost
reverted (`propagatePipChainCrossCore_stepCovers`), and a stashed reply's unlink, a stash
that is no key input (`updateTcb_keyFrame`). -/
theorem finaliseFinalObject_stepCovers (e : CoreId) (target : Nat) (st : SystemState)
    (hInv : st.objects.invExt) :
    stepCovers e st (finaliseFinalObject target st) ∧ (finaliseFinalObject target st).objects.invExt :=
  finaliseFinalObject_closed (fun s => stepCovers e st s ∧ s.objects.invExt)
    (fun en q s ep t tcb h hE hH hT hC =>
      ⟨stepCovers_trans h.1 (storeEndpointWaiterCancelled_stepCovers e s en q ep t tcb h.2 hE hH hT hC),
        (FinaliseFrame.storeEndpointWaiterCancelled s en q t _ h.2).invExt⟩)
    (fun n s _ t tcb h _ _ _ hC =>
      ⟨stepCovers_trans h.1 (notificationWaiterCancel_stepCovers e s t tcb h.2),
        ((FinaliseFrame.notificationCancel s t tcb n h.2
          (notificationWaiterCancellable_blocked hC)).trans
          (FinaliseFrame.wakeCancelledWaiter _ t
            (FinaliseFrame.notificationCancel s t tcb n h.2
              (notificationWaiterCancellable_blocked hC)).invExt)).invExt⟩)
    (fun n s _ t h _ _ hCode hIn => by
      have hSpec := unbindNotification_of_inPlace s t hIn
      rw [hCode, Nat.add_sub_cancel] at hSpec
      exact stepCoversInv_trans h.1 (unbindNotification_keyFrame _ _ _ h.2 hSpec).stepCoversInv)
    (fun s t _ h _ _ _ _ =>
      have d := descheduleAtPlacement_stepCovers e s t h.2
      ⟨stepCovers_trans h.1 d.1, d.2⟩)
    (fun _ _ _ _ _ _ h _ _ _ _ hOk =>
      stepCoversInv_trans h.1 (cancelBoundDonationOnCore_stepCovers e h.2 hOk))
    (fun s _ t tcb _ h _ _ _ _ =>
      ⟨stepCovers_trans h.1 (cancelIpcBlocking_stepCovers e s t tcb h.2),
        Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt s t tcb h.2⟩)
    (fun s en q t ep tcb h hT hE hC =>
      stepCoversInv_trans h.1 (storeEndpointBlockedCancelled_stepCovers e s en q t ep tcb h.2 hT hE hC))
    (fun s t _ h _ _ _ _ _ =>
      have d := descheduleAtPlacement_stepCovers e s t h.2
      stepCoversInv_trans (stepCovers_trans h.1 d.1) (updateTcb_keyFrame _ t
        (f := finalisedSuspendMark) (fun _ => rfl) d.2).stepCoversInv)
    (fun s t h => by
      have hO := finaliseThreadReleaseCores_objects s t
      refine ⟨stepCovers_trans h.1 (stepCovers_of_scheduler_eq_residentKept
        (keyInputsEq_of_objects_eq hO) (finaliseThreadReleaseCores_scheduler s t)
        (fun c _ u hU => by
          rw [finaliseThreadReleaseCores_machine] at hU
          unfold MachineState.releaseThread at hU
          rw [MachineState.releaseThreadOnCores_residentOnCore] at hU
          split at hU
          · cases hU
          · exact hU)
        (banksKeptOffCore_of_eq (finaliseThreadReleaseCores_coreRegs s t))), ?_⟩
      rw [hO]; exact h.2)
    (fun s s1 x _ _ r h _ _ hR _ hS _ _ _ _ => by
      have hI1 := storeObject_preserves_objects_invExt s s1 _ _ h.2 hS
      have hK1 : keyInputsEq s s1 := keyInputsEq_storeObject h.2 hS (by
        rw [(SystemState.getReply?_eq_some_iff _ _ _).mp hR]; rfl)
      have hK2 : keyInputsEq s1 (s1.updateSchedContext ⟨x.val⟩ fun sc => { sc with scReply := none }) :=
        keyInputsEq_updateSchedContext hI1 (fun _ => rfl)
      have hSch : (s1.updateSchedContext ⟨x.val⟩ fun sc => { sc with scReply := none }).scheduler =
          s.scheduler := by
        rw [SystemState.updateSchedContext_scheduler, storeObject_scheduler_eq s s1 _ _ hS]
      exact ⟨stepCovers_trans h.1 (stepCovers_of_keys_sched (keyInputsEq_trans hK1 hK2) hSch),
        SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hI1⟩)
    (fun s _ _ c t h _ _ _ _ => by
      have h1 := stepCovers_trans h.1 (cancelIpcBlockingReclaimed_stepCovers e s c t h.2)
      have hI1 := cancelIpcBlockingReclaimed_objects_invExt c t s
        (Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt s c t h.2)
      unfold finaliseReplyRevert
      cases t.blockingServer? with
      | none => exact ⟨h1, hI1⟩
      | some sv =>
        exact ⟨stepCovers_trans h1 (propagatePipChainCrossCore_stepCovers e _ _ _ sv hI1).1,
          (propagatePipChainCrossCore_stepCovers e _ _ _ sv hI1).2⟩)
    (fun s _ _ tid _ h _ _ e => e ▸
      stepCoversInv_trans h.1 ((updateTcb_keyFrame s tid (f := TCB.stashCleared) (fun _ => rfl)
        h.2).stepCoversInv (hRes := by rw [SystemState.updateTcb_machine]) (hBank := banksKeptOffCore_of_eq (by rw [SystemState.updateTcb_machine]))))
    ⟨fun s t h => ⟨stepCovers_trans h.1 (stepCovers_of_keys_sched
        (keyInputsEq_of_objectsAgreeOffYield (SystemState.cancelYieldTo_objectsAgreeOffYield s t h.2))
        (SystemState.cancelYieldTo_scheduler s t)
        (hRes := by rw [SystemState.cancelYieldTo_machine]) (hBank := banksKeptOffCore_of_eq (by rw [SystemState.cancelYieldTo_machine]))),
        SystemState.cancelYieldTo_preserves_objects_invExt _ _ h.2⟩,
     fun s c h => ⟨stepCovers_trans h.1 (stepCovers_of_keys_sched
        (keyInputsEq_of_objectsAgreeOffYield
          (SystemState.completeYieldFrom_objectsAgreeOffYield s c h.2))
        (SystemState.completeYieldFrom_scheduler s c)
        (hRes := by rw [completeYieldFrom_machine]) (hBank := banksKeptOffCore_of_eq (by rw [completeYieldFrom_machine]))),
        SystemState.completeYieldFrom_preserves_objects_invExt _ _ h.2⟩⟩
    target st ⟨stepCovers_refl e st, hInv⟩

/-- WS-ZA ZA5.4 part 23: **the finalising delete covers**: the delete and the
page teardown move no key input and no scheduler field, the finalisation covers
(`finaliseFinalObject_stepCovers`), and so does the retire. -/
theorem cspaceDeleteSlotFinalising_stepCovers (e ec : CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (hB : finalisingDeleteBundle st)
    (hStep : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  obtain ⟨st1, st2, hD, hF, rfl⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' hStep
  have h1 : capabilityKeyFrame st st1 := cspaceDeleteSlot_keyInputsEq st st1 addr hB.1.2.1 hD
  have h2 := (h1.trans (finaliseDestroyedCapabilities_keyFrame ec _ _ st1 st2 h1.2.2 hF)).trans
    (releaseFinalRegistration_keyFrame (slotRetireTarget st addr.cnode addr.slot) st2
      (h1.trans (finaliseDestroyedCapabilities_keyFrame ec _ _ st1 st2 h1.2.2 hF)).2.2)
  have h3 := finaliseFinalObject_stepCovers e (slotRetireTarget st addr.cnode addr.slot)
    (releaseFinalRegistration (slotRetireTarget st addr.cnode addr.slot) st2) h2.2.2
  have hB3 := finaliseFinalObject_preserves_finalisingDeleteBundle
    (slotRetireTarget st addr.cnode addr.slot)
    (releaseFinalRegistration (slotRetireTarget st addr.cnode addr.slot) st2)
    (releaseFinalRegistration_closed finalisingDeleteBundle
      (fun _ _ _ hs hR => revokeService_preserves_finalisingDeleteBundle hs hR)
      (slotRetireTarget st addr.cnode addr.slot) st2
      (cspaceDeleteSlotTeardown_preserves_finalisingDeleteBundle hB hD hF))
  have hM2 : (releaseFinalRegistration (slotRetireTarget st addr.cnode addr.slot) st2).machine =
      st.machine := by
    rw [releaseFinalRegistration_machine,
      (finaliseDestroyedCapabilities_framed ec _ _ st1 st2 hF).2,
      (cspaceDeleteSlot_scheduler_machine addr st st1 hD).2]
  exact stepCoversInv_trans (stepCovers_trans (h2.stepCovers (hRes := by rw [hM2]) (hBank := banksKeptOffCore_of_eq (by rw [hM2]))) h3.1)
    (retireFinalObject_stepCovers e ec _ _ _ h3.2 hB3.1.1 hB3.2)

/-- What the delete loops carry: coverage from the start state, and the bundle
the delete carries. -/
def coversWithDeleteBundle (e : CoreId) (st s : SystemState) : Prop :=
  stepCovers e st s ∧ finalisingDeleteBundle s

/-- A finalising delete inside a loop extends the coverage and keeps the bundle. -/
theorem coversWithDeleteBundle.delete {e ec : CoreId} {st s s' : SystemState} {c : CSpaceAddr}
    (hQ : coversWithDeleteBundle e st s) (hD : cspaceDeleteSlotFinalising ec c s = .ok ((), s')) :
    coversWithDeleteBundle e st s' :=
  ⟨stepCovers_trans hQ.1 (cspaceDeleteSlotFinalising_stepCovers e ec c s s' hQ.2 hD).1,
    cspaceDeleteSlotFinalising_preserves_finalisingDeleteBundle ec c s s' hQ.2 hD⟩

/-- A finalisation inside a loop extends the coverage and keeps the bundle. -/
theorem coversWithDeleteBundle.finalise {e : CoreId} {st s : SystemState} (d : Nat)
    (hQ : coversWithDeleteBundle e st s) : coversWithDeleteBundle e st (finaliseFinalObject d s) :=
  ⟨stepCovers_trans hQ.1 (finaliseFinalObject_stepCovers e d s hQ.2.1.2.1).1,
    finaliseFinalObject_preserves_finalisingDeleteBundle d s hQ.2⟩

/-- WS-ZA ZA5.4 part 23: **the finalising revocation covers**, one finalising
delete at a time. -/
theorem cspaceRevokeCdtFinalising_stepCovers (e ec : CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (hB : finalisingDeleteBundle st)
    (hStep : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    stepCovers e st st' ∧ st'.objects.invExt :=
  have h := cspaceRevokeCdtFinalising_closed (coversWithDeleteBundle e st)
    (fun _ _ _ hQ hD => hQ.delete hD) (fun d _ hQ => hQ.finalise d)
    ⟨stepCovers_refl e st, hB⟩ hStep
  ⟨h.1, h.2.1.2.1⟩

/-- WS-ZA ZA5.4 part 26: **the zombie delete covers**, one finalising delete or
finalisation at a time. -/
theorem cspaceDeleteSlotZombie_stepCovers (e ec : CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (hB : finalisingDeleteBundle st)
    (hStep : cspaceDeleteSlotZombie ec addr st = .ok ((), st')) :
    stepCovers e st st' ∧ st'.objects.invExt :=
  have h := cspaceDeleteSlotZombie_closed (coversWithDeleteBundle e st)
    (fun _ _ _ hQ hD => hQ.delete hD) (fun d _ hQ => hQ.finalise d)
    ⟨stepCovers_refl e st, hB⟩ hStep
  ⟨h.1, h.2.1.2.1⟩

/-- WS-ZA ZA5.4 part 26: **the space change through the zombie delete covers**,
one finalising delete or finalisation at a time, then the plain space change
(`copyThreadSpaces_stepCovers`). -/
theorem copyThreadSpacesZombie_stepCovers (e ec : CoreId) (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (cnSrc vrSrc : CSpaceAddr) (hB : finalisingDeleteBundle st)
    (hStep : copyThreadSpacesZombie ec st vtid cnSrc vrSrc = .ok st') :
    stepCovers e st st' ∧ st'.objects.invExt := by
  rcases copyThreadSpacesZombie_cases hStep with h1 | ⟨n, s, hR, rfl | h2⟩
  · exact copyThreadSpaces_stepCovers e ec st st' vtid cnSrc vrSrc hB.1.2.1 hB.1.1 hB.2 h1
  · have h := hR.chain.closed (coversWithDeleteBundle e st)
      (fun _ _ _ hQ hD => hQ.delete hD) (fun d _ hQ => hQ.finalise d) ⟨stepCovers_refl e st, hB⟩
    exact ⟨h.1, h.2.1.2.1⟩
  · have h := hR.chain.closed (coversWithDeleteBundle e st)
      (fun _ _ _ hQ hD => hQ.delete hD) (fun d _ hQ => hQ.finalise d) ⟨stepCovers_refl e st, hB⟩
    exact stepCoversInv_trans h.1
      (copyThreadSpaces_stepCovers e ec s st' vtid cnSrc vrSrc h.2.1.2.1 h.2.1.1 h.2.2 h2)

/-- WS-ZA ZA6.9: **the Consumed invocation covers**: `setConsumed` moves no key
input and no scheduler field. -/
theorem schedContextConsumedOnCore_stepCovers (e : CoreId) {s : SeLe4n.SchedContextId}
    {c : CoreId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : schedContextConsumedOnCore s c st = .ok st') :
    stepCovers e st st' ∧ st'.objects.invExt := by
  obtain ⟨caller, -, rfl⟩ := schedContextConsumedOnCore_ok h
  exact ⟨stepCovers_of_keys_sched
      (keyInputsEq_of_objectsAgreeOffYield (SystemState.setConsumed_objectsAgreeOffYield st s caller hInv))
      (SystemState.setConsumed_scheduler st s caller),
    SystemState.setConsumed_preserves_objects_invExt _ _ _ hInv⟩

/-! ### The capability-only arms -/

/-- **Every arm `dispatchCapabilityOnly` routes covers**, on the executing core,
under the bundle the finalising delete carries (`finalisingDeleteBundle`, from
which the binding reciprocity follows) and the placement facts — pre-state facts
the dispatch's invariant payoff consumes. -/
theorem dispatchCapabilityOnly_stepCovers {decoded : SyscallDecodeResult} {cap : Capability}
    {tid : SeLe4n.ThreadId} {ec : CoreId} {k : Kernel Unit} {st st' : SystemState}
    (hInv : st.objects.invExt) (hB : finalisingDeleteBundle st)
    (hPlaced : placedThreadsHaveTcbs st)
    (hK : dispatchCapabilityOnly decoded cap tid ec = some k)
    (h : k st = .ok ((), st')) : stepCovers ec st st' ∧ st'.objects.invExt := by
  have hBi := hB.bidirectional
  unfold dispatchCapabilityOnly at hK
  cases hId : decoded.syscallId <;> rw [hId] at hK <;> simp only [Option.some.injEq,
    reduceCtorEq] at hK
  all_goals subst hK
  all_goals cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  all_goals (repeat' split at h)
  all_goals first | (cases h; done) | skip
  all_goals try first
    | exact cspaceDeleteSlotZombie_stepCovers _ _ _ _ _ hB h
    | exact cspaceRevokeCdtFinalising_stepCovers _ _ _ _ _ hB h
    | exact (mintReplyCapWithCdt_keyFrame _ _ _ _ hInv h).stepCoversInv
        (hRes := by rw [mintReplyCapWithCdt_machine_eq h]) (hBank := banksKeptOffCore_of_eq (by rw [mintReplyCapWithCdt_machine_eq h]))
    | exact (untypedResetFromCap_keyFrame _ _ _ _ hInv h).stepCoversInv
        (hRes := by rw [untypedResetFromCap_machine_eq h]) (hBank := banksKeptOffCore_of_eq (by rw [untypedResetFromCap_machine_eq h]))
    | exact (vspaceMapFromFrameCap_keyFrame _ _ _ _ _ hInv h).stepCoversInv
    | exact (vspaceRootOnlyWrite_keyFrame
        (vspaceUnmapPageWithShootdownAndIcacheBroadcast_ok_frame _ _ _ _ _ hInv h)).stepCoversInv
    | exact (capabilityKeyFrame_of_objects_scheduler_eq hInv
        (Architecture.vspaceUnifyInstructionPage_frame h).1
        (Architecture.vspaceUnifyInstructionPage_frame h).2.2.1).stepCoversInv
        (hRes := by rw [(Architecture.vspaceUnifyInstructionPage_frame h).2.2.2.1]) (hBank := banksKeptOffCore_of_eq (by rw [(Architecture.vspaceUnifyInstructionPage_frame h).2.2.2.1]))
    | exact (revokeServiceByRecordedRegistration_keyFrame hInv h).stepCoversInv
    | exact (schedControlConfigure_stepCovers _ _ _ _ _ _ _ _ _ _ hInv hBi h)
    | exact (schedContextBind_stepCovers _ _ _ _ _ hInv hBi h)
    | exact (bindNotification_keyFrame _ _ _ _ hInv h).stepCoversInv
    | exact (pageTableMap_keyFrame _ _ _ _ _ hInv h).stepCoversInv
    | exact (pageTableUnmap_keyFrame _ _ _ hInv h).stepCoversInv
    | (cases h; rename_i hU
       first
        | (rw [lookupServiceByRecordedRegistration_preserves_state _ _ _ _ hU]
           exact (writeReturnFrameToTcb_keyFrame _ _ _ hInv).stepCoversInv
             (hRes := by rw [Architecture.writeReturnFrameToTcb_machine_eq]) (hBank := banksKeptOffCore_of_eq (by rw [Architecture.writeReturnFrameToTcb_machine_eq])))
        | exact (schedContextUnbindOnCore_stepCovers _ _ _ _ _ hInv hU)
        | exact (schedContextConsumedOnCore_stepCovers _ hInv hU)
        | exact (unbindNotification_keyFrame _ _ _ hInv hU).stepCoversInv
            (hRes := by rw [unbindNotification_machine_eq hU]) (hBank := banksKeptOffCore_of_eq (by rw [unbindNotification_machine_eq hU]))
        | exact (suspendThreadOnCore_stepCovers _ _ _ _ _ hInv hU)
        | exact stepCoversInv_trans ((retirePendingFaultForResume_keyFrame _ _ hInv).stepCovers
              (hRes := by rw [retirePendingFaultForResume_machine]) (hBank := banksKeptOffCore_of_eq (by rw [retirePendingFaultForResume_machine])))
            (resumeThreadOnCore_stepCovers _ _ _ _ _
              (retirePendingFaultForResume_keyFrame _ _ hInv).2.2 hU)
        | exact (setPriorityOnCore_stepCovers _ _ _ _ _ _ _ hInv hU)
        | exact (setMCPriorityOnCore_stepCovers _ _ _ _ _ _ _ hInv hU)
        | exact (setThreadCpuAffinityOnCore_stepCovers _ _ _ _ _ _ hInv hU)
        | exact (setIPCBufferOp_keyFrame _ _ _ _ hInv hU).stepCoversInv
            (hRes := by rw [Architecture.IpcBufferValidation.setIPCBufferOp_machine_eq _ _ _ _ hU]) (hBank := banksKeptOffCore_of_eq (by rw [Architecture.IpcBufferValidation.setIPCBufferOp_machine_eq _ _ _ _ hU]))
        | exact (setThreadFaultHandlerOp_keyFrame _ _ _ _ hInv hU).stepCoversInv
            (hRes := by rw [setThreadFaultHandlerOp_machine_eq hU]) (hBank := banksKeptOffCore_of_eq (by rw [setThreadFaultHandlerOp_machine_eq hU]))
        | exact copyThreadSpacesZombie_stepCovers _ _ _ _ _ _ _ hB hU)
  all_goals
    obtain ⟨_, _, _, _, _, _, _, _, _, hU⟩ := untypedRetypeFromCap_ok _ _ _ _ _ _ h
    exact untypedRetypeObject_stepCovers ec hInv hBi hPlaced hU

/-! ### The checked dispatcher -/

/-- Read a pair-returning transition's coverage off the equation that named its
result. -/
theorem stepCovers_of_pair_eq {α : Type} {e : CoreId} {st s : SystemState}
    {p : SystemState × α} {r : α}
    (hCov : stepCovers e st p.1 ∧ p.1.objects.invExt) (hEq : p = (s, r)) :
    stepCovers e st s ∧ s.objects.invExt := by
  subst hEq; exact hCov

/-- The tail every waking arm ends with: clear the woken receiver's stash, then
stage the delivered frames. -/
theorem stepCovers_clearStash_stage {e : CoreId} {st s st' : SystemState}
    {woken? : Option SeLe4n.ThreadId} {stage : SystemState → SystemState}
    (hS : stepCovers e st s) (hInv : s.objects.invExt)
    (hStage : ∀ x, x.objects.invExt → capabilityKeyFrame x (stage x))
    (h : (match clearWokenReceiverStash woken? s with
      | .error e => .error e
      | .ok ((), s') => .ok ((), stage s')) = (.ok ((), st') : Except KernelError (Unit × SystemState)))
    (hStageM : ∀ x, (stage x).machine.residentCode = x.machine.residentCode := by
      intro x; resident_frame)
    (hStageB : ∀ x, (stage x).machine.coreRegs = x.machine.coreRegs := by
      intro x; bank_frame) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  split at h
  · cases h
  · rename_i s3 hClr
    cases h
    have hF := clearWokenReceiverStash_keyFrame woken? hInv hClr
    exact stepCoversInv_trans (stepCovers_trans hS hF.stepCovers)
      ((hStage _ hF.2.2).stepCoversInv (hRes := hStageM _)
        (hBank := banksKeptOffCore_of_eq (hStageB _)))

/-- The two badge stagings a signal arm ends with. -/
theorem keyFrame_trans_stage {x : SystemState} {w p : Option SeLe4n.ThreadId}
    (hx : x.objects.invExt) :
    capabilityKeyFrame x (Architecture.stageWokenDelivery
      (Architecture.stageWokenDelivery x w 0) p 0) := by
  have h1 := stageWokenDelivery_keyFrame x w 0 hx
  exact h1.trans (stageWokenDelivery_keyFrame _ p 0 h1.2.2)

/-- **Every arm `dispatchWithCapChecked` routes covers** on the executing core,
the capability-only arms it delegates included. -/
theorem dispatchWithCapChecked_stepCovers (e : CoreId) {ctx : LabelingContext}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId}
    {gate : SyscallGate} {cap : Capability} {st st' : SystemState} (hInv : st.objects.invExt)
    (hB : finalisingDeleteBundle st)
    (hPlaced : placedThreadsHaveTcbs st)
    (h : dispatchWithCapChecked ctx decoded tid e gate cap st = .ok ((), st')) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold dispatchWithCapChecked at h
  cases hC : dispatchCapabilityOnly decoded cap tid e with
  | some k =>
    rw [hC] at h
    exact dispatchCapabilityOnly_stepCovers hInv hB hPlaced hC (dispatchCapabilityOnlyChecked_ok hC h)
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
    exact (writeReturnFrameToTcb_keyFrame _ _ _ hInv).stepCoversInv
  case none.auditDrain =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    unfold auditDrainVisiblePrefix at hA
    split at hA
    · cases hA
      refine stepCoversInv_trans (stepCovers_of_scheduler_eq (keyInputsEq_of_objects_eq rfl) rfl) ?_
      apply capabilityKeyFrame.stepCoversInv
      all_goals first
        | exact writeReturnFrameToTcb_keyFrame _ _ _ (by exact hInv)
        | rw [Architecture.writeReturnFrameToTcb_machine_eq]
        | exact banksKeptOffCore_of_eq (by rw [Architecture.writeReturnFrameToTcb_machine_eq])
    · cases hA
  all_goals
    cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.send.object epId =>
    split at h
    · cases h
    rename_i hSend
    obtain ⟨hS, hSInv⟩ := stepCovers_of_pair_eq
      (endpointSendCrossCoreDispatchChecked_stepCovers e hInv) hSend
    exact stepCovers_clearStash_stage hS hSInv
      (fun x hx => stageWokenDelivery_keyFrame x _ _ hx) h
  case none.receive.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ _ hRecv _ stDon hHand
    cases h
    obtain ⟨hV, hVInv⟩ := stepCovers_of_pair_eq
      (endpointReceiveDualWithCapsOnCore_stepCovers e hInv) hRecv
    obtain ⟨hD, hDInv⟩ := applyReceiveRendezvousHandoff_stepCovers e hVInv hHand
    have hS1 := stageWokenSendCompletion_keyFrame stDon
      ((st.getEndpoint? epId).bind (·.sendQ.head)) hDInv
    have hS2 := stageDeliveredMessage_keyFrame _ tid summ.installedCount hS1.2.2
    exact stepCoversInv_trans (stepCovers_trans (stepCovers_trans hV hD) hS1.stepCovers)
      hS2.stepCoversInv
  case none.call.object epId =>
    split at h
    · rename_i hCall
      cases h
      obtain ⟨hS, hSInv⟩ := stepCovers_of_pair_eq
        (endpointCallCrossCoreDispatchChecked_stepCovers e hInv) hCall
      exact stepCoversInv_trans hS (stageWokenDelivery_keyFrame _ _ _ hSInv).stepCoversInv
    · cases h
  case none.reply.replyCap rid =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact replyTransferOnCoreChecked_stepCovers e hInv h
  case none.cspaceMint.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    all_goals
      unfold cspaceMintChecked at h
      dsimp only at h
      split at h
      · exact (cspaceMintWithCdt_keyFrame _ _ _ _ _ _ hInv h).stepCoversInv
          (hRes := by rw [cspaceMintWithCdt_machine_eq h]) (hBank := banksKeptOffCore_of_eq (by rw [cspaceMintWithCdt_machine_eq h]))
      · cases h
  case none.cspaceCopy.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceCopyChecked at h
    dsimp only at h
    split at h
    · exact (cspaceCopy_keyFrame _ _ _ _ hInv h).stepCoversInv
        (hRes := by rw [cspaceCopy_machine_eq h]) (hBank := banksKeptOffCore_of_eq (by rw [cspaceCopy_machine_eq h]))
    · cases h
  case none.cspaceMove.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceMoveChecked at h
    dsimp only at h
    split at h
    · exact (cspaceMove_keyFrame _ _ _ _ hInv h).stepCoversInv
        (hRes := by rw [cspaceMove_machine_eq h]) (hBank := banksKeptOffCore_of_eq (by rw [cspaceMove_machine_eq h]))
    · cases h
  case none.serviceRegister.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold registerServiceChecked at h
    split at h
    · exact (registerService_keyFrame hInv h).stepCoversInv
        (hRes := by rw [registerService_preserves_machine _ _ _ h]) (hBank := banksKeptOffCore_of_eq (by rw [registerService_preserves_machine _ _ _ h]))
    · cases h
  case none.notificationSignal.object notifId =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      obtain ⟨hS, hSInv⟩ := stepCovers_of_pair_eq
        (notificationSignalBoundCrossCoreDispatchChecked_stepCovers e hInv) hSig
      exact stepCovers_clearStash_stage hS hSInv
        (fun x hx => keyFrame_trans_stage hx) h
    · cases h
  case none.notificationWait.object notifId =>
    split at h
    · rename_i hW
      cases h
      obtain ⟨hS, hSInv⟩ := stepCovers_of_pair_eq
        (notificationWaitCrossCoreDispatchChecked_stepCovers e hInv) hW
      exact stepCoversInv_trans hS (writeReturnFrameToTcb_keyFrame _ _ _ hSInv).stepCoversInv
    · rename_i hW
      cases h
      exact stepCovers_of_pair_eq
        (notificationWaitCrossCoreDispatchChecked_stepCovers e hInv) hW
    · cases h
  case none.replyRecv.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ stR hRR
    cases h
    obtain ⟨hS, hSInv⟩ := endpointReplyRecvOnCore_stepCovers e hInv hRR
    exact stepCoversInv_trans hS (stageDeliveredMessage_keyFrame _ tid _ hSInv).stepCoversInv
  case none.declassify.object targetId =>
    unfold declassifyObjectFromCore at h
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rw [(authorizeDeclassificationOnCore_frame _ _ _ _ _ _ _ _ _ h).1]
    exact ⟨stepCovers_of_scheduler_eq (keyInputsEq_of_objects_eq rfl) rfl, hInv⟩
  case none.declassifySignal.object notifId =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      obtain ⟨hS, hSInv⟩ := stepCovers_of_pair_eq
        (notificationSignalDeclassifiedOnCore_stepCovers e hInv) hSig
      exact stepCovers_clearStash_stage hS hSInv
        (fun x hx => keyFrame_trans_stage hx) h
    · cases h

/-! ### The checked syscall dispatch -/

theorem syscallResolveCap_state {gate : SyscallGate} {st st' : SystemState} {cap : Capability}
    (h : syscallResolveCap gate st = .ok (cap, st')) : st' = st := by
  unfold syscallResolveCap at h
  repeat' split at h
  all_goals first | (cases h; done) | (cases h; rfl)

/-- **The checked dispatch covers** on the executing core: the capability
resolution reads, the routed arm covers, and the taint pass writes the taint
ledger alone.  The yield's charge may release a ready refill (WS-ZA ZA6.4), so it
reads that the executing core's current thread is on no queue (`hAwayCur`,
which `currentDequeuedUnique` gives between scheduling points). -/
theorem dispatchSyscallChecked_stepCovers {ctx : LabelingContext}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {e : CoreId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (hB : finalisingDeleteBundle st)
    (hPlaced : placedThreadsHaveTcbs st)
    (hAwayCur : ∀ t, st.scheduler.currentOnCore e = some t → ∀ c, st.queuedOn c t = false)
    (h : dispatchSyscallChecked ctx decoded tid e st = .ok ((), st')) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold dispatchSyscallChecked at h
  split at h
  · cases h
  -- WS-ZA ZA4.3: the capability-free yield runs before any lookup.
  by_cases hY : decoded.syscallId = .yield
  · simp only [hY, ↓reduceIte, dispatchYield] at h
    split at h
    · cases h
    · rename_i hYieldOk
      cases h
      exact yieldOnCore_stepCovers st _ e hInv hB.bidirectional hAwayCur hYieldOk
  simp only [hY, ↓reduceIte] at h
  split at h <;> try (cases h; done)
  split at h <;> try (cases h; done)
  cases hTF : syscallChecksTargetFirst decoded.syscallId <;>
    simp only [hTF, Bool.false_eq_true, ↓reduceIte] at h
  all_goals
    split at h
    · cases h
    rename_i stPost hD
    cases h
    suffices hP : stepCovers e st stPost ∧ stPost.objects.invExt from
      ⟨stepCovers_trans hP.1 (stepCovers_of_scheduler_eq
          (keyInputsEq_of_objectsAgreeOffTaint (applySyscallTaint_objectsAgreeOffTaint _ _ _))
          (applySyscallTaint_scheduler _ _ _)),
        applySyscallTaint_invExt hP.2⟩
  · unfold syscallInvoke at hD
    split at hD
    · cases hD
    · rename_i cap s1 hR
      cases syscallLookupCap_preserves_state _ _ _ _ hR
      exact dispatchWithCapChecked_stepCovers e hInv hB hPlaced hD
  · unfold syscallInvokeResolved at hD
    split at hD
    · cases hD
    · rename_i cap s1 hR
      cases syscallResolveCap_state hR
      exact dispatchWithCapChecked_stepCovers e hInv hB hPlaced hD

/-- **The checked syscall entry covers** on the executing core: the register
read and the decode read, and the IPC-buffer fill writes one core's TLB. -/
theorem syscallEntryChecked_stepCovers {ctx : LabelingContext}
    {layout : SeLe4n.SyscallRegisterLayout} {e : CoreId} {regCount : Nat}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (hB : finalisingDeleteBundle st) (hPlaced : placedThreadsHaveTcbs st)
    (hAwayCur : ∀ t, st.scheduler.currentOnCore e = some t → ∀ c, st.queuedOn c t = false)
    (h : syscallEntryChecked ctx layout e regCount st = .ok ((), st')) :
    stepCovers e st st' ∧ st'.objects.invExt := by
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
  have hD := dispatchSyscallChecked_stepCovers (st := { st with perCoreTlb := t }) hInv
    (finalisingDeleteBundle.of_objects_scheduler_eq (s := st) rfl rfl hB) hPlaced
    (fun t ht c => hAwayCur t ht c)
    h
  exact ⟨⟨hD.1.1, hD.1.2, hD.1.3, hD.1.4, hD.1.5, hD.1.6⟩, hD.2⟩

end SeLe4n.Kernel
