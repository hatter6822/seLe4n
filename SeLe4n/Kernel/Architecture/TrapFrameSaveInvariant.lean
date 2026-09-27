-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.TrapFrameSave
import SeLe4n.Kernel.IPC.Invariant.DispatchArmPreservation
import SeLe4n.Kernel.Scheduler.Invariant.PerCore

/-!
# WS-BP BP7.3 — what saving the trap frame preserves and establishes

`saveTrapFrameOnCore` rewrites one TCB's `registerContext` — a field no
conjunct of `ipcInvariantFull` reads — and one core's register bank, and
touches nothing the scheduler reads.  So the IPC bundle transports; and the
executing core's `contextMatchesCurrentOnCore` is not merely preserved but
**established** (the bank and the thread's saved context are one value), while
every other core's match is framed as long as it runs a different thread.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency (CoreId)

/-- The typed rewrite at the saved thread's key, read back. -/
private theorem saveUpdate_at (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (rf : SeLe4n.RegisterFile) (hTcb : st.getTcb? tid = some tcb) (hInv : st.objects.invExt) :
    (st.updateTcb tid fun t => { t with registerContext := rf }).objects[tid.toObjId]? =
      some (.tcb { tcb with registerContext := rf }) := by
  rw [SystemState.updateTcb_eq_of_some hTcb]
  exact RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv

/-- **The save preserves the IPC bundle**: it rewrites a field no conjunct
reads, on one TCB, and a register bank. -/
theorem saveTrapFrameOnCore_preserves_ipcInvariantFull (st : SystemState) (c : CoreId)
    (rf : SeLe4n.RegisterFile) (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (saveTrapFrameOnCore st c rf) := by
  rcases saveTrapFrameOnCore_frame st c rf with h | ⟨tid, tcb, _, _, hTcb, h⟩
  · rw [h]; exact hInv
  · rw [h]
    have hPre : st.objects[tid.toObjId]? = some (.tcb tcb) :=
      (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
    have hAt := saveUpdate_at st tid tcb rf hTcb hObjInv
    have hFrame : ∀ oid : SeLe4n.ObjId, oid ≠ tid.toObjId →
        (st.updateTcb tid fun t => { t with registerContext := rf }).objects[oid]? =
          st.objects[oid]? :=
      fun oid hNe => SystemState.updateTcb_objects_ne st tid _ oid (Ne.symm hNe) hObjInv
    have hSched := SystemState.updateTcb_scheduler st tid fun t => { t with registerContext := rf }
    have h1 : ipcInvariantFull (st.updateTcb tid fun t => { t with registerContext := rf }) :=
      ipcInvariantFull_of_tcbFieldUpdate st _ tid.toObjId tcb { tcb with registerContext := rf }
        hInv hPre hAt hFrame rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (passiveServerIdleFrame_of_tcbFieldUpdate tid.toObjId tcb { tcb with registerContext := rf }
          hPre hAt hFrame rfl rfl hSched)
    exact ipcInvariantFull_of_objects_scheduler_eq
      (st := st.updateTcb tid fun t => { t with registerContext := rf }) rfl rfl h1

/-- **The save establishes the executing core's match**: after it, core `c`'s
bank is the frame the current thread's saved context also holds — or, when the
save wrote nothing, the match is the one that held before. -/
theorem saveTrapFrameOnCore_contextMatchesCurrentOnCore (st : SystemState) (c : CoreId)
    (rf : SeLe4n.RegisterFile) (hObjInv : st.objects.invExt)
    (hMatch : contextMatchesCurrentOnCore st c) :
    contextMatchesCurrentOnCore (saveTrapFrameOnCore st c rf) c := by
  rcases saveTrapFrameOnCore_frame st c rf with h | ⟨tid, tcb, hEl0, hCur, hTcb, _⟩
  · rw [h]; exact hMatch
  · obtain ⟨hBank, hSaved⟩ := saveTrapFrameOnCore_saves st c rf tid tcb hEl0 hCur hTcb hObjInv
    unfold contextMatchesCurrentOnCore
    simp only [saveTrapFrameOnCore_scheduler, hCur, hSaved, hBank]
    exact SeLe4n.RegisterFile.beq_self rf

/-- **Every other core's match is framed** when it runs a different thread: the
save writes only the executing core's bank and the executing core's thread. -/
theorem saveTrapFrameOnCore_contextMatchesCurrentOnCore_other (st : SystemState)
    (c c' : CoreId) (rf : SeLe4n.RegisterFile) (hObjInv : st.objects.invExt) (hNe : c' ≠ c)
    (hDistinct : ∀ tid tid', st.scheduler.currentOnCore c = some tid →
      st.scheduler.currentOnCore c' = some tid' → tid.toObjId ≠ tid'.toObjId)
    (hMatch : contextMatchesCurrentOnCore st c') :
    contextMatchesCurrentOnCore (saveTrapFrameOnCore st c rf) c' := by
  rcases saveTrapFrameOnCore_frame st c rf with h | ⟨tid, tcb, _, hCur, _, h⟩
  · rw [h]; exact hMatch
  · unfold contextMatchesCurrentOnCore at hMatch ⊢
    rw [saveTrapFrameOnCore_scheduler]
    cases hCur' : st.scheduler.currentOnCore c' with
    | none => trivial
    | some tid' =>
      rw [hCur'] at hMatch
      have hKey := hDistinct tid tid' hCur hCur'
      have hG : (saveTrapFrameOnCore st c rf).getTcb? tid' = st.getTcb? tid' := by
        rw [h]; exact SystemState.updateTcb_getTcb?_ne st tid _ hObjInv tid' hKey
      have hB : (saveTrapFrameOnCore st c rf).machine.regsOnCore c' = st.machine.regsOnCore c' := by
        rw [h]; exact SeLe4n.MachineState.regsOnCore_setRegsOnCore_ne _ c c' rf (Ne.symm hNe)
      simp only [hG, hB]
      exact hMatch

end SeLe4n.Kernel.Architecture
