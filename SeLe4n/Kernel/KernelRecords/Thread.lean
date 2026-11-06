-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.ThreadLifecycle

/-!
# The thread-configuration and service arms keep the records

WS-ZA ZA6.37.  The IPC-buffer set, the fault-handler set, the notification bind
and unbind and the service registry rewrite a thread's configuration words, a
notification or an endpoint: none of them a record view reads, so each is a
`RecordsFrame`.  The resume's fault retire clears the thread's fault record.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

namespace RecordsFrame

/-- A TCB stored over a TCB keeping its record view. -/
theorem storeObject_tcbView {st st' : SystemState} {k : SeLe4n.ObjId} {x y : TCB}
    (hInv : st.objects.invExt) (hOld : st.objects[k]? = some (.tcb x))
    (h : SeLe4n.Model.storeObject k (.tcb y) st = .ok ((), st')) (hv : y.recordView = x.recordView) :
    RecordsFrame st st' :=
  storeObject hInv h (by rw [hOld]; simp [hv]) (fun _ h => by cases h)

theorem setIPCBufferOp {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {addr : SeLe4n.VAddr} (hInv : st.objects.invExt)
    (h : Architecture.IpcBufferValidation.setIPCBufferOp st vtid addr = .ok st') :
    RecordsFrame st st' := by
  unfold Architecture.IpcBufferValidation.setIPCBufferOp at h
  split at h
  · cases h
  · split at h
    · rename_i tcb hTcb
      dsimp only at h
      split at h
      · rename_i hStore
        cases h
        exact storeObject_tcbView hInv ((SystemState.getTcb?_eq_some_iff st vtid.val tcb).mp hTcb)
          hStore rfl
      · cases h
    · cases h

theorem setThreadFaultHandlerOp {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {cptr : SeLe4n.CPtr} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.setThreadFaultHandlerOp st vtid cptr = .ok st') :
    RecordsFrame st st' := by
  cases hT : st.getTcb? vtid.val with
  | none =>
    simp [_root_.SeLe4n.Kernel.setThreadFaultHandlerOp, SystemState.getTcbWitnessed?_eq_none hT] at h
  | some tcb =>
    cases hR : resolveFaultHandlerCPtr st tcb cptr with
    | error e =>
      simp [_root_.SeLe4n.Kernel.setThreadFaultHandlerOp, SystemState.getTcbWitnessed?_eq_some hT,
        hR] at h
    | ok tgt =>
      rw [setThreadFaultHandlerOp_ok_eq st vtid cptr tcb tgt hT hR] at h
      cases h
      exact rewriteObject _ hInv (by rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hT]; rfl)

theorem bindNotification {st st' : SystemState} {nid : SeLe4n.ObjId} {tcbId : SeLe4n.ThreadId}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.bindNotification nid tcbId st = .ok ((), st')) :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.bindNotification at h
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
            have F1 := storeNotification hInv hNraw hStore1
            have hPre1 : st1.objects[tcbId.toObjId]? = some (.tcb tcb) := by
              rw [storeObject_objects_ne st _ nid tcbId.toObjId _ hNeIds hInv hStore1]
              exact hTraw
            exact F1.trans (storeObject_tcbView F1.invExt hPre1 hStore2 rfl)
  · split at h <;> cases h

theorem unbindNotification {st st' : SystemState} {tcbId : SeLe4n.ThreadId}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.unbindNotification tcbId st = .ok ((), st')) :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.unbindNotification at h
  split at h
  · cases h
  · rename_i tcb hT
    split at h
    · cases h
    · rename_i nid hBound
      split at h
      · cases h
      · rename_i st1 hStore1
        have F1 := storeObject_tcbView hInv (lookupTcb_some_objects st tcbId tcb hT) hStore1 rfl
        split at h
        · rename_i ntfn hN1
          split at h
          · cases h
          · rename_i st2 hStore2
            cases h
            exact F1.trans (storeNotification F1.invExt
              ((SystemState.getNotification?_eq_some_iff _ nid ntfn).mp hN1) hStore2)
        · cases h; exact F1

/-- The service registration writes an endpoint's record. -/
theorem registerService {reg : ServiceRegistration} {st st' : SystemState}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.registerService reg st = .ok ((), st')) :
    RecordsFrame st st' := by
  obtain ⟨e, ep, -, hE, -, -, rfl⟩ := registerService_ok h
  exact insert hInv (by rw [hE]; rfl)

theorem revokeService {sid : ServiceId} {st st' : SystemState}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.revokeService sid st = .ok ((), st')) :
    RecordsFrame st st' := by
  obtain ⟨ep, hE, -, rfl⟩ := revokeService_ok h
  exact insert hInv (by rw [hE]; rfl)

theorem revokeServiceByRecordedRegistration {epId : SeLe4n.ObjId} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.revokeServiceByRecordedRegistration epId st = .ok ((), st')) :
    RecordsFrame st st' := by
  obtain ⟨_, h⟩ := revokeServiceByRecordedRegistration_revokeService h
  exact revokeService hInv h

end RecordsFrame

namespace RecordsStep

/-- **The resume's fault retire clears the thread's fault record.** -/
theorem retirePendingFaultForResume (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    RecordsStep st (_root_.SeLe4n.Kernel.retirePendingFaultForResume st t) := by
  unfold _root_.SeLe4n.Kernel.retirePendingFaultForResume
  split
  · split
    · split
      · unfold discardPendingFault
        exact updateTcb st t hInv fun _ _ =>
          TcbStaysParked.of_noFault (TCB.pendingFault_setPendingFault _ _)
      · unfold applyFaultRestart
        exact updateTcb st t hInv fun _ _ =>
          TcbStaysParked.of_noFault (TCB.pendingFault_setPendingFault _ _)
    · exact refl hInv
  · exact refl hInv

end RecordsStep

end SeLe4n.Kernel
