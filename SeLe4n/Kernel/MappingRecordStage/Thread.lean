-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.MappingRecordStage.Ipc

/-! # The thread, notification-binding and service arms keep the mappings recorded

The thread-control arms (the IPC buffer, the fault handler, the resume's fault
retirement), the notification bind and unbind and the service registry write
TCBs, notifications and endpoints in place: each keeps its object's kind, its
thread slots and its mapping facts (none of the three holds a mapping fact), so
each is a `MappingStage` by `MappingStage.storeObject`, `MappingStage.rewriteObject`
or `MappingStage.insert`.  The bind and unbind move the binding codes, which
the mapping records do not read (`SystemState.mappingFactsKept`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState (MappingStage)

theorem setIPCBufferOp_mappingStage {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {addr : SeLe4n.VAddr}
    (h : Architecture.IpcBufferValidation.setIPCBufferOp st vtid addr = .ok st') :
    MappingStage st st' := by
  unfold Architecture.IpcBufferValidation.setIPCBufferOp at h
  split at h
  · cases h
  · split at h
    · rename_i tcb hTcb
      dsimp only at h
      split at h
      · rename_i hStore
        cases h
        exact MappingStage.storeObject hStore
          ((SystemState.getTcb?_eq_some_iff st vtid.val tcb).mp hTcb) rfl
          (by simp [KernelObject.objectType])
      · cases h
    · cases h

theorem setThreadFaultHandlerOp_mappingStage {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {cptr : SeLe4n.CPtr}
    (h : setThreadFaultHandlerOp st vtid cptr = .ok st') : MappingStage st st' := by
  cases hT : st.getTcb? vtid.val with
  | none => simp [setThreadFaultHandlerOp, SystemState.getTcbWitnessed?_eq_none hT] at h
  | some tcb =>
    cases hR : resolveFaultHandlerCPtr st tcb cptr with
    | error e => simp [setThreadFaultHandlerOp, SystemState.getTcbWitnessed?_eq_some hT, hR] at h
    | ok tgt =>
      rw [setThreadFaultHandlerOp_ok_eq st vtid cptr tcb tgt hT hR] at h
      cases h
      exact MappingStage.rewriteObject_tcb hT _

theorem bindNotification_mappingStage {st st' : SystemState} {nid : SeLe4n.ObjId}
    {tcbId : SeLe4n.ThreadId} (h : bindNotification nid tcbId st = .ok ((), st')) :
    MappingStage st st' := by
  unfold bindNotification at h
  split at h
  · rename_i ntfn hN
    split at h
    · cases h
    · rename_i tcb hT
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i st1 hStore1
          split at h
          · cases h
          · rename_i st2 hStore2
            cases h
            have hNraw := (SystemState.getNotification?_eq_some_iff st nid ntfn).mp hN
            have hTraw := lookupTcb_some_objects st tcbId tcb hT
            have hNeIds : tcbId.toObjId ≠ nid := by
              intro hEq
              rw [hEq, hNraw] at hTraw
              exact absurd (Option.some.inj hTraw) (fun hx => KernelObject.noConfusion hx)
            refine MappingStage.of_invExt fun hI => ?_
            have hPre1 : st1.objects[tcbId.toObjId]? = some (.tcb tcb) := by
              rw [storeObject_objects_ne st _ nid tcbId.toObjId _ hNeIds hI hStore1]
              exact hTraw
            exact (MappingStage.storeObject hStore1 hNraw rfl
              (by simp [KernelObject.objectType])).trans
              (MappingStage.storeObject hStore2 hPre1 rfl (by simp [KernelObject.objectType]))
  · split at h <;> cases h

theorem unbindNotification_mappingStage {st st' : SystemState} {tcbId : SeLe4n.ThreadId}
    (h : unbindNotification tcbId st = .ok ((), st')) : MappingStage st st' := by
  unfold unbindNotification at h
  split at h
  · cases h
  · rename_i tcb hT
    split at h
    · cases h
    · rename_i nid hBound
      split at h
      · cases h
      · rename_i st1 hStore1
        have s1 : MappingStage st st1 := MappingStage.storeObject hStore1
          (lookupTcb_some_objects st tcbId tcb hT) rfl (by simp [KernelObject.objectType])
        split at h
        · rename_i ntfn hN1
          split at h
          · cases h
          · rename_i st2 hStore2
            cases h
            exact s1.trans (MappingStage.storeObject hStore2
              ((SystemState.getNotification?_eq_some_iff _ nid ntfn).mp hN1) rfl
              (by simp [KernelObject.objectType]))
        · cases h; exact s1

theorem retirePendingFaultForResume_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId) :
    MappingStage st (retirePendingFaultForResume st tid) := by
  unfold retirePendingFaultForResume
  split
  · split
    · split
      · unfold discardPendingFault; exact updateTcb_mappingStage _ _ _
      · unfold applyFaultRestart; exact updateTcb_mappingStage _ _ _
    · exact MappingStage.refl _
  · exact MappingStage.refl _

/-! ### The service registry -/

/-- The registry's one object write — an endpoint's `serviceRegistered` — keeps the
endpoint's kind and mapping facts. -/
theorem serviceRecordRewrite_mappingStage {st st' : SystemState}
    (hW : ServiceRecordRewrite st.objects st'.objects) : MappingStage st st' :=
  MappingStage.of_mappingFactsKept (fun h => hW.invExt h) fun h oid => by
    rcases hW.lookup h oid with e | ⟨ep, c, h0, h1⟩
    · exact .inl e
    · exact .inr ⟨_, _, h0, h1, rfl, by simp [KernelObject.objectType], rfl, rfl⟩

theorem registerService_mappingStage {reg : ServiceRegistration} {st st' : SystemState}
    (h : registerService reg st = .ok ((), st')) : MappingStage st st' :=
  serviceRecordRewrite_mappingStage (registerService_serviceRecordRewrite h)

theorem revokeService_mappingStage {sid : ServiceId} {st st' : SystemState}
    (h : revokeService sid st = .ok ((), st')) : MappingStage st st' :=
  serviceRecordRewrite_mappingStage (revokeService_serviceRecordRewrite h)

theorem revokeServiceByRecordedRegistration_mappingStage {epId : SeLe4n.ObjId} {st st' : SystemState}
    (h : revokeServiceByRecordedRegistration epId st = .ok ((), st')) : MappingStage st st' := by
  obtain ⟨_, h⟩ := revokeServiceByRecordedRegistration_revokeService h
  exact revokeService_mappingStage h

end SeLe4n.Kernel
