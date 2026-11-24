-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.EndpointWaiters.Timer
import SeLe4n.Kernel.KernelRecords.Dispatch

/-! # The capability-only arms keep the endpoint waiters

WS-SX SX11.2 (D38).  The arms the capability table routes write capabilities,
address spaces, contexts and thread records, and none of them blocks a thread
on an endpoint.  Most are records' frames (`EndpointWaitersFrame.of_frame`);
the rest write objects that are no thread (a VSpace root, a page table, an
untyped, a CNode), store a fresh thread `.ready` in IPC (the carve), or retire
objects (the delete chain), and every thread after each of them was the same
thread before it (`EndpointWaitersShrink.of_tcb_back`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace EndpointWaitersShrink

/-- **A step after which every thread is one it was before.** -/
theorem of_tcb_back {st st' : SystemState}
    (h : ∀ (k : SeLe4n.ObjId) (t : TCB), st'.objects[k]? = some (.tcb t) →
      st.objects[k]? = some (.tcb t)) : EndpointWaitersShrink st st' := fun _ t' _ hT hW =>
  ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr
    (h _ _ ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT)), hW⟩

/-- A write of VSpace roots alone. -/
theorem of_vspaceRootOnlyWrite {st st' : SystemState} (h : vspaceRootOnlyWrite st st') :
    EndpointWaitersShrink st st' :=
  of_tcb_back fun k t hT => by
    rcases h k with e | ⟨-, r', hr'⟩
    · rw [← e]; exact hT
    · rw [hr'] at hT; cases hT

end EndpointWaitersShrink

namespace EndpointWaitersFrame

theorem of_tcb_back {st st' : SystemState}
    (h : ∀ (k : SeLe4n.ObjId) (t : TCB), st'.objects[k]? = some (.tcb t) →
      st.objects[k]? = some (.tcb t)) (hI : st'.objects.invExt) : EndpointWaitersFrame st st' :=
  ⟨.of_tcb_back h, hI⟩

theorem of_vspaceRootOnlyWrite {st st' : SystemState} (h : vspaceRootOnlyWrite st st')
    (hI : st'.objects.invExt) : EndpointWaitersFrame st st' :=
  ⟨.of_vspaceRootOnlyWrite h, hI⟩

theorem of_objects_eq {st st' : SystemState} (hInv : st.objects.invExt)
    (h : st'.objects = st.objects) : EndpointWaitersFrame st st' :=
  ⟨.of_objects_eq h, h ▸ hInv⟩

/-- **A store of an object that waits on no endpoint**: no thread, or a thread
blocked on none. -/
theorem storeObject_noWait {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (h : storeObject k o st = .ok ((), st'))
    (hO : ∀ t, o = .tcb t → ∀ e, ¬ ipcWaitsOnEndpoint t.ipcState e) : EndpointWaitersFrame st st' := by
  refine ⟨fun u t' e hT hW => ?_, storeObject_preserves_objects_invExt _ _ _ _ hInv h⟩
  have hO' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
  by_cases hk : u.toObjId = k
  · rw [hk, storeObject_objects_eq st st' _ _ hInv h] at hO'
    exact absurd hW (hO t' (Option.some.inj hO') e)
  · rw [storeObject_objects_ne st st' _ _ _ hk hInv h] at hO'
    exact ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO', hW⟩

/-- A store of an object that is no thread. -/
theorem storeObject_other {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (h : storeObject k o st = .ok ((), st'))
    (hO : ∀ t, o ≠ .tcb t) : EndpointWaitersFrame st st' :=
  storeObject_noWait hInv h fun t e => absurd e (hO t)

/-- The final retire keeps or erases each object, so every thread after it was
there before it. -/
theorem retireFinalObject (ec : CoreId) (target recorder : Nat) (st : SystemState)
    (hInv : st.objects.invExt) :
    EndpointWaitersFrame st (_root_.SeLe4n.Kernel.retireFinalObject ec target recorder st) :=
  of_tcb_back (fun _ _ hT => retireFinalObject_tcb_back ec target recorder st hInv hT)
    (retireFinalObject_frame ec target recorder st hInv).1

end EndpointWaitersFrame

/-! ### The address-space arms -/

namespace EndpointWaitersFrame

theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast {ec : CoreId}
    {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast ec asid vaddr st
      = .ok ((), st')) : EndpointWaitersFrame st st' :=
  have hF := vspaceUnmapPageWithShootdownAndIcacheBroadcast_ok_frame ec asid vaddr st st' hInv h
  of_vspaceRootOnlyWrite hF.2.1 hF.1

theorem vspaceMapFromFrameCap {tid : SeLe4n.ThreadId} {ec : CoreId}
    {args : Architecture.SyscallArgDecode.VSpaceMapArgs} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.vspaceMapFromFrameCap tid ec args st = .ok ((), st')) :
    EndpointWaitersFrame st st' := by
  obtain ⟨_, _, _, st1, _, _, _, _, _, hMap, epoch, st2, hT, hRec⟩ :=
    vspaceMapFromFrameCap_ok tid ec args st st' h
  obtain ⟨cn, _, -, -, hS⟩ := cspaceRecordFrameMapping_ok_decompose _ _ st2 st' hRec
  have hF := vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_frame ec _ _ _ _ st st1 hInv hMap
  have F1 := of_vspaceRootOnlyWrite hF.2.1 hF.1
  obtain ⟨f, rootId, root, stR, -, -, -, h1, h2⟩ := tagFrameMapping_ok _ _ _ st1 st2 epoch hT
  have F2 := F1.andThen fun hI => storeObject_other hI h1 (fun _ e => by cases e)
  have F3 := F2.andThen fun hI => storeObject_other hI h2 (fun _ e => by cases e)
  exact F3.andThen fun hI => storeObject_other hI hS (fun _ e => by cases e)

theorem vspaceMapOrRemapFromFrameCap {tid : SeLe4n.ThreadId} {ec : CoreId}
    {args : Architecture.SyscallArgDecode.VSpaceMapArgs} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.vspaceMapOrRemapFromFrameCap tid ec args st = .ok ((), st')) :
    EndpointWaitersFrame st st' :=
  vspaceMapOrRemapFromFrameCap_closed (fun a b => a.objects.invExt → EndpointWaitersFrame a b)
    (fun _ _ h hI => vspaceMapFromFrameCap hI h)
    (fun _ _ h hI => vspaceUnmapPageWithShootdownAndIcacheBroadcast hI h)
    (fun _ _ _ h₁ h₂ hI => (h₁ hI).andThen h₂) h hInv

theorem vspaceUnmapFrameCap {ec : CoreId} {addr : CSpaceAddr} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.vspaceUnmapFrameCap ec addr st = .ok ((), st')) :
    EndpointWaitersFrame st st' := by
  obtain ⟨st1, hU, hC⟩ := vspaceUnmapFrameCap_cases h
  obtain ⟨cn, _, -, -, hS⟩ := cspaceClearFrameMapping_ok_decompose _ st1 st' hC
  obtain ⟨hI1, hV, -⟩ := unmapLivePages_ok_frame ec _ st st1 hInv hU
  exact (of_vspaceRootOnlyWrite hV hI1).andThen fun hI =>
    storeObject_other hI hS (fun _ e => by cases e)

theorem pageTableMap {tableId rootId : SeLe4n.ObjId} {vaddr : SeLe4n.VAddr} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : Architecture.pageTableMap tableId rootId vaddr st = .ok ((), st')) :
    EndpointWaitersFrame st st' := by
  obtain ⟨table, root, level, st1, -, -, -, -, -, -, hS1, hS2⟩ :=
    Architecture.pageTableMap_ok tableId rootId vaddr st st' h
  have F1 := storeObject_other hInv hS1 (fun _ e => by cases e)
  have F2 : ∀ ws, EndpointWaitersFrame st1 (Architecture.recordPhysicalWrites st1 ws) := fun _ =>
    of_objects_eq F1.invExt rfl
  exact (F1.andThen fun _ => F2 _).andThen fun hI =>
    storeObject_other hI hS2 (fun _ e => by cases e)

theorem pageTableUnmap {tableId : SeLe4n.ObjId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : Architecture.pageTableUnmap tableId st = .ok ((), st')) : EndpointWaitersFrame st st' := by
  unfold Architecture.pageTableUnmap at h
  cases hT : st.getPageTable? tableId with
  | none => rw [hT] at h; cases h
  | some table =>
    have Ft : ∀ {s : SystemState}, storeObject tableId (.pageTable table.uninstalled) st =
        .ok ((), s) → EndpointWaitersFrame st s :=
      fun hS => storeObject_other hInv hS (fun _ e => by cases e)
    rw [hT] at h
    simp only at h
    split at h
    · cases h; exact refl hInv
    · split at h
      · exact Ft h
      · split at h
        · split at h
          · cases h
          · cases hS1 : storeObject tableId (.pageTable table.uninstalled) st with
            | error e => rw [hS1] at h; cases h
            | ok p =>
              obtain ⟨⟨⟩, st1⟩ := p
              rw [hS1] at h
              simp only at h
              have F1 := Ft hS1
              have F2 : ∀ ws, EndpointWaitersFrame st1 (Architecture.recordPhysicalWrites st1 ws) :=
                fun _ => of_objects_eq F1.invExt rfl
              exact (F1.andThen fun _ => F2 _).andThen fun hI =>
                storeObject_other hI h (fun _ e => by cases e)
        · exact Ft h

end EndpointWaitersFrame

/-! ### The carve, the delete chain, the space set and the handler arms -/

/-- A carved thread is born `.ready` in IPC. -/
theorem carvedTcb_ipcState (childId : SeLe4n.ObjId) (d : SeLe4n.DomainId) (c : CoreId) :
    (carvedTcb childId d c).ipcState = .ready := rfl

namespace EndpointWaitersFrame

/-- **The carve**: the watermark, the fresh child (a thread is born `.ready` in
IPC, seL4's zeroed TCB), the free index, the scrub, the capability insert and
the derivation edge. -/
theorem untypedRetypeObject {src dst : CSpaceAddr} {childId : SeLe4n.ObjId}
    {req : CarveRequest} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.untypedRetypeObject src childId dst req st = .ok ((), st')) :
    EndpointWaitersFrame st st' := by
  obtain ⟨utCap, untypedId, ut, st1, st2, _, _, _, hRt, hIns, rfl⟩ :=
    untypedRetypeObject_ok_decompose src dst childId req st st' hInv h
  obtain ⟨ut₀, ut', cap, stUt, _, stCh, cn, hUt, _, _, _, _, _, _, hLk, _, _, hStUt, hStCh, hOCh,
    hStIdx⟩ := retypeFromUntyped_ok_stores st st1 src untypedId childId _ _ hInv hRt
  have F1 := storeObject_other hInv hStUt (fun _ e => by cases e)
  have F2 := F1.andThen fun hI => storeObject_noWait hI hStCh fun t ht e => by
    cases req <;> simp only [CarveRequest.object, KernelObject.tcb.injEq, reduceCtorEq] at ht
    subst ht; simp [carvedTcb_ipcState]
  have F3 := F2.andThen fun hI => storeObject_other hI hStIdx (fun _ e => by cases e)
  have F4 := F3.trans (of_objects_eq F3.invExt (CarveRequest.scrub_objects st1 ut
    (req.carveIndex ut (retypeFreeIndex st src utCap)) req))
  have F5 := F4.trans (of_frame (RecordsFrame.cspaceInsertSlot F4.invExt hIns))
  exact F5.trans (of_frame (RecordsFrame.cdtAddChild st2 _ _ _ F5.invExt))

/-- The live `.untypedRetype` arm: the carve chain. -/
theorem untypedRetypeFromCap {tid : SeLe4n.ThreadId} {ec : CoreId}
    {srcAddr : SeLe4n.CPtr} {root? : Option SeLe4n.CPtr}
    {args? : Except KernelError SeLe4n.Kernel.Architecture.SyscallArgDecode.UntypedRetypeArgs}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.untypedRetypeFromCap tid ec srcAddr root? args? st = .ok ((), st')) :
    EndpointWaitersFrame st st' :=
  (untypedRetypeFromCap_chain h).rel (P := fun s => s.objects.invExt)
    (R := fun a b => a.objects.invExt → EndpointWaitersFrame a b) (fun _ => refl)
    (fun h1 h2 hI => (h1 hI).andThen h2)
    (fun hP hC => untypedRetypeObject_preserves_objects_invExt hP hC)
    (fun hP hC _ => untypedRetypeObject hP hC) hInv hInv

/-- **The retire of what a final delete destroyed**: a node's line, or the
registration's release, the finalisation and the object's retire. -/
theorem retireFinalisedObject (ec : CoreId) (target recorder : Nat) (st : SystemState)
    (hInv : st.objects.invExt) :
    EndpointWaitersFrame st (_root_.SeLe4n.Kernel.retireFinalisedObject ec target recorder st) := by
  rcases retireFinalisedObject_cases ec target recorder st with ⟨-, hE⟩ | ⟨-, hE⟩ <;> rw [hE]
  · exact of_objects_eq hInv (retireIrqNode_objects _ _)
  · have F1 : EndpointWaitersFrame st (releaseFinalRegistration target st) :=
      releaseFinalRegistration_closed (EndpointWaitersFrame st)
        (fun _ _ _ F hR => F.andThen fun hI => of_frame (RecordsFrame.revokeService hI hR))
        target st (refl hInv)
    exact (F1.andThen fun hI => finaliseFinalObject target _ hI).andThen fun hI =>
      retireFinalObject ec target recorder _ hI

/-- **The finalising delete**: the slot's delete, the destroyed capabilities'
finalisation (VSpace roots alone), then the retire. -/
theorem cspaceDeleteSlotFinalising {ec : CoreId} {addr : CSpaceAddr} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    EndpointWaitersFrame st st' := by
  obtain ⟨st1, st2, hD, hF, rfl⟩ := cspaceDeleteSlotFinalising_ok ec addr st _ h
  have F1 := of_frame (RecordsFrame.cspaceDeleteSlot hInv hD)
  obtain ⟨hI2, hW2, -⟩ := finaliseDestroyedCapabilities_ok_frame ec _ _ st1 st2 F1.invExt hF
  exact (F1.andThen fun _ => of_vspaceRootOnlyWrite hW2 hI2).andThen fun hI =>
    retireFinalisedObject ec _ _ st2 hI

theorem cspaceDeleteSlotZombie {ec : CoreId} {addr : CSpaceAddr} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.cspaceDeleteSlotZombie ec addr st = .ok ((), st')) :
    EndpointWaitersFrame st st' :=
  cspaceDeleteSlotZombie_closed (EndpointWaitersFrame st)
    (fun _ _ _ F hD => F.andThen fun hI => cspaceDeleteSlotFinalising hI hD)
    (fun d _ F => F.andThen fun hI => finaliseFinalObject d _ hI) (refl hInv) h

theorem cspaceRevokeCdtFinalising {ec : CoreId} {addr : CSpaceAddr} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    EndpointWaitersFrame st st' :=
  cspaceRevokeCdtFinalising_closed (EndpointWaitersFrame st)
    (fun _ _ _ F hD => F.andThen fun hI => cspaceDeleteSlotFinalising hI hD)
    (fun d _ F => F.andThen fun hI => finaliseFinalObject d _ hI) (refl hInv) h

theorem threadSlotSet (ec : CoreId) {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hInv : st.objects.invExt) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) (data : UInt64) :
    EndpointWaitersFrame st
      (_root_.SeLe4n.Kernel.threadSlotSet ec st tid slot srcCNode srcSlot rights data) := by
  have F := RecordsFrame.threadSlotCopied hInv hT slot srcCNode srcSlot rights data
  unfold _root_.SeLe4n.Kernel.threadSlotSet
  exact (of_frame F).andThen fun hI => retireFinalObject ec _ _ _ hI

theorem copyThreadSpaces (ec : CoreId) {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {cnSrc vrSrc : CSpaceAddr} {cnData : UInt64} {fhSrc : CSpaceAddr} (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.copyThreadSpaces ec st vtid cnSrc vrSrc cnData fhSrc = .ok st') :
    EndpointWaitersFrame st st' := by
  obtain ⟨tcb, t1, t2, hT, -, -, -, hT1, hI1, hT2, hI2, rfl⟩ := copyThreadSpaces_ok_steps hInv hStep
  exact ((threadSlotSet ec hInv hT _ _ _ _ _).andThen fun _ => threadSlotSet ec hI1 hT1 _ _ _ _ _).andThen
    fun _ => threadSlotSet ec hI2 hT2 _ _ _ _ _

theorem copyThreadSpacesZombie (ec : CoreId) {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {cnSrc vrSrc : CSpaceAddr} {cnData : UInt64} {fhSrc : CSpaceAddr} (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.copyThreadSpacesZombie ec st vtid cnSrc vrSrc cnData fhSrc = .ok st') :
    EndpointWaitersFrame st st' := by
  have hChain : ∀ n s, ZombieRun ec n st s → EndpointWaitersFrame st s := fun _ _ hR =>
    hR.chain.closed (EndpointWaitersFrame st)
      (fun _ _ _ F hD => F.andThen fun hI => cspaceDeleteSlotFinalising hI hD)
      (fun d _ F => F.andThen fun hI => finaliseFinalObject d _ hI) (refl hInv)
  rcases copyThreadSpacesZombie_cases hStep with h1 | ⟨n, s, hR, rfl | h2⟩
  · exact copyThreadSpaces ec hInv h1
  · exact hChain n _ hR
  · exact (hChain n s hR).andThen fun hI => copyThreadSpaces ec hI h2

theorem setIPCBufferOp (ec : CoreId) {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {callerTid : SeLe4n.ThreadId} {bufferCap? : Option SeLe4n.CPtr} {addr : SeLe4n.VAddr}
    (hInv : st.objects.invExt)
    (hStep : Architecture.IpcBufferValidation.setIPCBufferOp ec st vtid callerTid bufferCap? addr
      = .ok st') : EndpointWaitersFrame st st' := by
  obtain ⟨c, s, t, hT, -, rfl⟩ := Architecture.IpcBufferValidation.setIPCBufferOp_ok_perform hStep
  unfold Architecture.IpcBufferValidation.setIPCBufferPerform
  exact (threadSlotSet ec hInv hT _ _ _ _ _).andThen fun hI =>
    updateTcb _ vtid.val (f := fun t => { t with ipcBuffer := addr }) hI fun _ => TcbWaitsKept.of_ipc rfl

theorem irqHandlerSetNotification {ec : CoreId} {line : Nat} {src : CSpaceAddr}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.irqHandlerSetNotification ec line src st = .ok ((), st')) :
    EndpointWaitersFrame st st' := by
  obtain ⟨-, st1, -, -, -, hZ, hC⟩ := irqHandlerSetNotification_ok hInv hStep
  exact (cspaceDeleteSlotZombie hInv hZ).andThen fun hI => of_frame (RecordsFrame.cspaceCopy hI hC)

theorem irqHandlerClear {ec : CoreId} {line : Nat} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.irqHandlerClear ec line st = .ok ((), st')) :
    EndpointWaitersFrame st st' := by
  unfold _root_.SeLe4n.Kernel.irqHandlerClear at hStep
  split at hStep
  · cases hStep
  exact cspaceDeleteSlotZombie hInv hStep

/-- **The thread restart** (seL4 `restart`): a resume, or a suspend then a
resume, each after the fault retire; or nothing. -/
theorem restartThreadOnCore {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {executingCore : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : Lifecycle.Suspend.restartThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    EndpointWaitersFrame st st' := by
  rcases Lifecycle.Suspend.restartThreadOnCore_cases h with hRes | ⟨st1, _, hSus, hRes⟩ | ⟨rfl, _⟩
  · exact (retirePendingFaultForResume st vtid.val hInv).andThen fun h' => resumeThreadOnCore h' hRes
  · exact ((suspendThreadOnCore hInv hSus).andThen fun h' =>
      retirePendingFaultForResume st1 vtid.val h').andThen fun h' => resumeThreadOnCore h' hRes
  · exact refl hInv

end EndpointWaitersFrame

open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-- **Every capability-only arm is a waiters' frame**: none blocks a thread on an
endpoint. -/
theorem dispatchCapabilityOnly_endpointWaitersFrame
    (decoded : SyscallDecodeResult) (cap : Capability) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) (k : Kernel Unit) (st st' : SystemState)
    (hArm : dispatchCapabilityOnly decoded cap tid executingCore = some k)
    (hInv : st.objects.invExt) (hStep : k st = .ok ((), st')) :
    EndpointWaitersFrame st st' := by
  unfold dispatchCapabilityOnly at hArm
  cases hSy : decoded.syscallId <;> simp only [hSy] at hArm <;> try cases hArm
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
          exact EndpointWaitersFrame.cspaceDeleteSlotZombie hInv hStep
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
          exact EndpointWaitersFrame.cspaceRevokeCdtFinalising hInv hStep
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
          exact EndpointWaitersFrame.of_frame (RecordsFrame.mintReplyCapWithCdt hInv hStep)
    all_goals try cases hStep
  case untypedRetype =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object _ =>
      exact EndpointWaitersFrame.untypedRetypeFromCap hInv hStep
    all_goals try cases hStep
  case vspaceMap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodePageMapArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok words =>
          simp only [hDec] at hStep
          cases hX : callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 with
          | none => simp only [hX] at hStep; cases hStep
          | some rootCPtr =>
            simp only [hX] at hStep
            cases hOps : resolvePageMapOperands tid decoded.capAddr rootCPtr words st with
            | error e => simp only [hOps] at hStep; cases hStep
            | ok p =>
              obtain ⟨_, args⟩ := p
              simp only [hOps] at hStep
              exact EndpointWaitersFrame.vspaceMapOrRemapFromFrameCap hInv hStep
    all_goals try cases hStep
  case vspaceUnmap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hR : resolveCallerCapSlot tid decoded.capAddr (syscallRequiredRight .vspaceUnmap) st with
      | error e => simp only [hR] at hStep; cases hStep
      | ok r =>
          obtain ⟨slot, _, _⟩ := r
          simp only [hR] at hStep
          exact EndpointWaitersFrame.vspaceUnmapFrameCap hInv hStep
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
          · exact EndpointWaitersFrame.of_frame (RecordsFrame.vspaceUnifyInstructionPage hInv hStep)
    all_goals try cases hStep
  case serviceRevoke =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case serviceRegistry _ =>
      replace hStep := serviceEndpointArm_ok hStep
      obtain ⟨_, oid, -, hStep⟩ := hStep
      try dsimp only [] at hStep
      obtain ⟨_, hRev⟩ := revokeServiceByRecordedRegistration_revokeService hStep
      exact EndpointWaitersFrame.of_frame (RecordsFrame.revokeService hInv hRev)
    all_goals try cases hStep
  case serviceQuery =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case serviceRegistry _ =>
      replace hStep := serviceEndpointArm_ok hStep
      obtain ⟨_, epId, -, hStep⟩ := hStep
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
          exact EndpointWaitersFrame.of_frame (RecordsFrame.writeCallReturnWord _ _ _ hInv)
    all_goals try cases hStep
  case schedContextConfigure =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case schedControl core =>
      try dsimp only [] at hStep
      rcases hXc : callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 with _ | scCPtr
      · simp only [hXc] at hStep; cases hStep
      simp only [hXc] at hStep
      cases hVal : resolveSchedControlConfigureTarget tid core scCPtr decoded.msgInfo.length st with
      | error e => simp only [hVal] at hStep; cases hStep
      | ok vScId =>
          simp only [hVal] at hStep
          cases hDec : decodeSchedContextConfigureArgsChecked decoded with
          | error e => simp only [hDec] at hStep; cases hStep
          | ok args =>
              simp only [hDec] at hStep
              split at hStep
              · exact EndpointWaitersFrame.of_frame (RecordsFrame.schedControlConfigure hInv hStep)
              · cases hStep
    all_goals try cases hStep
  case schedContextBind =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hN : resolveSchedContextBindNotificationCode tid
          (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
      | succ k =>
          simp only [hN] at hStep
          cases hVal : validateObjIdArg scId with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              exact EndpointWaitersFrame.of_frame (RecordsFrame.schedContextBindNotification hInv hStep)
      | zero =>
          simp only [hN] at hStep
          cases hRes : resolveSchedContextBindThread tid (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
          | error e => simp only [hRes] at hStep; cases hStep
          | ok vThreadId =>
              simp only [hRes] at hStep
              cases hVal : validateObjIdArg scId with
              | error e => simp only [hVal] at hStep; cases hStep
              | ok vScId =>
                  simp only [hVal] at hStep
                  exact EndpointWaitersFrame.of_frame (RecordsFrame.schedContextBind hInv hStep)
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
              cases hUn : SchedContextOps.schedContextUnbindAllOnCore vScId
                  executingCore st with
              | error e => simp only [hUn] at hStep; cases hStep
              | ok pair =>
                  obtain ⟨stU, sgiU⟩ := pair
                  simp only [hUn] at hStep
                  cases hStep
                  exact EndpointWaitersFrame.of_frame (RecordsFrame.schedContextUnbindAllOnCore hInv hUn)
    all_goals try cases hStep
  case schedContextUnbindObject =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hN : resolveSchedContextBindNotificationCode tid
          (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
      | succ k =>
          simp only [hN] at hStep
          cases hVal : validateObjIdArg scId with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              exact EndpointWaitersFrame.of_frame (RecordsFrame.schedContextUnbindNotificationObject hInv hStep)
      | zero =>
          simp only [hN] at hStep
          cases hRes : resolveSchedContextBindThread tid (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
          | error e => simp only [hRes] at hStep; cases hStep
          | ok vThreadId =>
              simp only [hRes] at hStep
              cases hVal : validateObjIdArg scId with
              | error e => simp only [hVal] at hStep; cases hStep
              | ok vScId =>
                  simp only [hVal] at hStep
                  cases hUn : SchedContextOps.schedContextUnbindThreadObjectOnCore vScId
                      vThreadId.val executingCore st with
                  | error e => simp only [hUn] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨stU, sgiU⟩ := pair
                      simp only [hUn] at hStep
                      cases hStep
                      exact EndpointWaitersFrame.of_frame (RecordsFrame.schedContextUnbindThreadObjectOnCore hInv hUn)
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
              exact EndpointWaitersFrame.of_frame (RecordsFrame.schedContextConsumedOnCore hInv hC)
    all_goals try cases hStep
  case schedContextYieldTo =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
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
              exact EndpointWaitersFrame.of_frame (RecordsFrame.schedContextYieldToOnCore hInv hC)
    all_goals try cases hStep
  case irqHandlerAck =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line =>
      rw [Architecture.irqHandlerAck_ok hStep]
      have hO := Architecture.setInterruptLineMask_objects st line false
      exact EndpointWaitersFrame.of_objects_eq hInv hO
    all_goals try cases hStep
  case irqControlGet =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqControl => exact EndpointWaitersFrame.of_frame (RecordsFrame.irqControlGetFromCap hInv hStep)
    all_goals try cases hStep
  case irqHandlerSetNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line =>
      obtain ⟨_, _, _, hS⟩ := irqHandlerSetNotificationFromCap_ok tid executingCore line _ st st' hStep
      exact EndpointWaitersFrame.irqHandlerSetNotification hInv hS
    all_goals try cases hStep
  case irqHandlerClear =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line => exact EndpointWaitersFrame.irqHandlerClear hInv hStep
    all_goals try cases hStep
  case tcbBindNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object tcbObjId =>
      simp only [tcbBindNotificationArm] at hStep
      try dsimp only [] at hStep
      cases hDec : tcbBindNotificationArgsOf st tid decoded.msgInfo.extraCaps with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hCaller : st.getTcb? tid with
          | none => simp only [hCaller] at hStep; cases hStep
          | some callerTcb =>
              simp only [hCaller] at hStep
              try dsimp only [] at hStep
              cases hCap2 : resolveBindNotificationCap { callerId := tid, cspaceRootCap := callerTcb.spaceCells[0], capAddr := args.notificationCPtr, requiredRight := .read } st with
              | error e => simp only [hCap2] at hStep; cases hStep
              | ok notifId =>
                  simp only [hCap2] at hStep
                  exact EndpointWaitersFrame.of_frame (RecordsFrame.bindNotification hInv hStep)
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
          exact EndpointWaitersFrame.of_frame (RecordsFrame.unbindNotification hInv hUn)
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
                  exact EndpointWaitersFrame.suspendThreadOnCore hInv hSus
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
              exact EndpointWaitersFrame.restartThreadOnCore hInv hRes
    all_goals try cases hStep
  case tcbSetPriority =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetPriorityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hValC : resolvePriorityAuthority st tid
              (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) with
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
                      exact EndpointWaitersFrame.of_frame (RecordsFrame.setPriorityOnCore hInv hSet)
    all_goals try cases hStep
  case tcbSetMCPriority =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetMCPriorityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hValC : resolvePriorityAuthority st tid
              (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) with
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
                      exact EndpointWaitersFrame.of_frame (RecordsFrame.setMCPriorityOnCore hInv hSet)
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
              cases hSet : Architecture.IpcBufferValidation.setIPCBufferOp executingCore st
                  vtid tid (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0)
                  args.bufferAddr with
              | error e => simp only [hSet] at hStep; cases hStep
              | ok stU =>
                  simp only [hSet] at hStep
                  cases hStep
                  exact EndpointWaitersFrame.setIPCBufferOp executingCore hInv hSet
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
                      exact EndpointWaitersFrame.of_frame (RecordsFrame.setThreadCpuAffinityOnCore hInv hSet)
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
              cases hR : resolveSetSpace tid decoded.msgInfo.extraCaps args st with
              | error e => simp only [hR] at hStep; cases hStep
              | ok p =>
                  obtain ⟨cn, vr, fh⟩ := p
                  simp only [hR] at hStep
                  cases hSet : copyThreadSpacesZombie executingCore st vtid cn vr args.cspaceRootData fh with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok stU =>
                      simp only [hSet] at hStep
                      cases hStep
                      exact EndpointWaitersFrame.copyThreadSpacesZombie executingCore hInv hSet
    all_goals try cases hStep
  case pageTableMap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodePageTableMapArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hX : callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 with
          | none => simp only [hX] at hStep; cases hStep
          | some rootCPtr =>
            simp only [hX] at hStep
            cases hR : resolveCallerCapObject tid rootCPtr .write st with
            | error e => simp only [hR] at hStep; cases hStep
            | ok p =>
                obtain ⟨_, rootId⟩ := p
                simp only [hR] at hStep
                exact EndpointWaitersFrame.pageTableMap hInv hStep
    all_goals try cases hStep
  case pageTableUnmap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      exact EndpointWaitersFrame.pageTableUnmap hInv hStep
    all_goals try cases hStep

end SeLe4n.Kernel
