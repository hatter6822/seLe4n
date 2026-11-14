/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Scheduling
import SeLe4n.Kernel.IPC.Invariant.ReplyHolderCancelHeads

/-!
# A reply holder's cancel keeps the run-queue placement

WS-SX SX4.  A receive that names a busy reply object first cancels the reply's
holder as seL4-MCS `cancelIPC` and the suspend do (`cancelReplyHolder`): the IPC
teardown and boost revert, which are run-queue stages, then the `Inactive`
write.  The holder is blocked, so no core runs it and no run queue holds it;
the write touches no placement.  The endpoint heads stay wakeable after it, and
every other thread stays active.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Model.SystemState (RunQueueStage)

/-- The cancel's IPC teardown and boost revert are a run-queue stage. -/
theorem suspendCancelRevert_runQueueStage (st : SystemState) (v : SeLe4n.ThreadId) (tcb : TCB)
    (ec : Concurrency.CoreId) :
    RunQueueStage st (Lifecycle.Suspend.suspendCancelRevert st v tcb ec) := by
  unfold Lifecycle.Suspend.suspendCancelRevert; dsimp only; split
  · exact (cancelIpcKeepingContexts_runQueueStage st v tcb).trans
      (PriorityInheritance.propagatePipChainCrossCore_runQueueStage _ _ _ _)
  · exact cancelIpcKeepingContexts_runQueueStage st v tcb

/-- ...and place every thread where it was. -/
theorem suspendCancelRevert_placedCoreOf? (st : SystemState) (v : SeLe4n.ThreadId) (tcb : TCB)
    (ec : Concurrency.CoreId) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    placedCoreOf? (Lifecycle.Suspend.suspendCancelRevert st v tcb ec) x = placedCoreOf? st x := by
  have hI1 := Lifecycle.Suspend.cancelIpcKeepingContexts_preserves_objects_invExt st v tcb hInv
  unfold Lifecycle.Suspend.suspendCancelRevert; dsimp only; split
  · exact (placedCoreOf?_congr_of_bits _ fun c =>
        ⟨PriorityInheritance.propagatePipChainCrossCore_queuedOn _ _ _ _ _ _ hI1,
          by rw [PriorityInheritance.propagatePipChainCrossCore_currentOnCore]⟩).trans
      (cancelIpcKeepingContexts_placedCoreOf? st v tcb hInv x)
  · exact cancelIpcKeepingContexts_placedCoreOf? st v tcb hInv x

/-- ...and leave the holder `.ready` in IPC. -/
theorem suspendCancelRevert_holder_ready (st : SystemState) (v : SeLe4n.ThreadId) (tcb : TCB)
    (ec : Concurrency.CoreId) (hInv : st.objects.invExt) (hL : lookupTcb st v = some tcb) :
    ∀ t', (Lifecycle.Suspend.suspendCancelRevert st v tcb ec).getTcb? v = some t' →
      t'.ipcState = .ready := by
  have hI1 := Lifecycle.Suspend.cutCancelledCallerHead_preserves_objects_invExt st tcb hInv
  have hIK := Lifecycle.Suspend.cancelIpcKeepingContexts_preserves_objects_invExt st v tcb hInv
  have hT : st.getTcb? v = some tcb :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr (lookupTcb_some_objects st v tcb hL)
  have hIp := cutCancelledCallerHead_getTcb?_map st tcb TCB.ipcState (fun _ => rfl) hInv v
  rw [hT] at hIp
  obtain ⟨x, hx, hxI⟩ := Option.map_eq_some_iff.mp hIp
  have hR0 : ∀ t', (Lifecycle.Suspend.cancelIpcKeepingContexts st v tcb).objects[v.toObjId]? =
      some (.tcb t') → t'.ipcState = .ready :=
    cancelIpcBlocking_victim_ready_of_ipcState _ v tcb x hI1
      ((SystemState.getTcb?_eq_some_iff _ _ _).mp hx) (lookupTcb_some_not_reserved st v tcb hL) hxI
  intro t' h
  have h' := (SystemState.getTcb?_eq_some_iff _ _ _).mp h
  unfold Lifecycle.Suspend.suspendCancelRevert at h'; dsimp only at h'; split at h'
  · obtain ⟨t0, h0, e⟩ := propagatePipChainCrossCore_ipcStateFrame _ _ ec _ hIK v t' h'
    rw [← e]; exact hR0 t0 h0
  · exact hR0 t' h'

/-- **A reply holder's cancel is a kernel-entry run-queue stage** (WS-SX SX4):
the teardown and revert are a stage, and the `Inactive` write lands on a
thread the pre-state ran nowhere and queued nowhere (it was blocked), which
the teardown placed nowhere either, and which is `.ready` in IPC, so stays
coherent suspended. -/
theorem cancelReplyHolder_runQueueEntryStage (st : SystemState) (holder : SeLe4n.ThreadId)
    (ec : Concurrency.CoreId) :
    SystemState.RunQueueEntryStage st (cancelReplyHolder st holder ec) := by
  rcases cancelReplyHolder_cases st holder ec with e | ⟨tcb, hL, hB, e⟩
  · rw [e]; exact (RunQueueStage.refl st).entry
  rw [e]
  have hS := suspendCancelRevert_runQueueStage st holder tcb ec
  have hT : st.getTcb? holder = some tcb :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr (lookupTcb_some_objects st holder tcb hL)
  refine ⟨hS.1.trans (SystemState.RunQueueLinkStage.updateTcb _ holder
    (f := fun t => { t with threadState := .Inactive }) (fun _ _ => rfl)), fun hI hR _ hD => ?_⟩
  obtain ⟨hIM, hRM⟩ := hS.1.links hI hR
  have hDM := hS.2.1 none hI hR hRM hD
  have hP0 : placedCoreOf? st holder = none := by
    refine (placedCoreOf?_none_iff st holder).mpr fun c => ⟨?_, ?_⟩
    · cases hq : st.queuedOn c holder
      · rfl
      · obtain ⟨y, hy, hr⟩ := hD.queuedRunnable c holder hq
        rw [hT] at hy; cases hy; exact absurd hr.1 hB
    · exact currentNowhere_of_blockedIfTcb hD (fun y hy => by rw [hT] at hy; cases hy; exact hB) c
  have hPM := ((suspendCancelRevert_placedCoreOf? st holder tcb ec hI holder).trans hP0)
  have hNP := (placedCoreOf?_none_iff _ holder).mp hPM
  exact SystemState.currentDequeuedUniqueExcept_updateTcb_offWrite hIM hDM
    (fun c => (hNP c).2) (fun c => (hNP c).1) (notIdle_of_blocked hD hT hB) (fun _ _ => rfl)
    (fun x hx => Or.inl (suspendCancelRevert_holder_ready st holder tcb ec hI hL x hx))

/-- **A reply holder's cancel keeps every endpoint head wakeable**: each head
after it is blocked (`cancelReplyHolder_queueHeadBlockedConsistent`), and was
blocked before it — the holder itself was, and every other thread keeps its IPC
state — so no core ran it, and the cancel writes no current slot. -/
theorem cancelReplyHolder_endpointHeadsWakeable {st : SystemState} {holder : SeLe4n.ThreadId}
    {ec : Concurrency.CoreId} (hInv : st.objects.invExt) (hD : st.currentDequeuedUnique)
    (F : QueueHeadCancelFacts st) : endpointHeadsWakeable (cancelReplyHolder st holder ec) := by
  have hQ := cancelReplyHolder_queueHeadBlockedConsistent st holder ec hInv F
  have hK := cancelReplyHolder_ipcStateKeptExcept st holder ec hInv
  intro epId ep hE r hr
  have hB : blockedIfTcb (cancelReplyHolder st holder ec) r := fun tcb hT => by
    have hEo := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE
    have hTo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
    rcases hr with hr | hr
    · rw [(hQ epId ep r tcb hEo hTo).1 hr]; exact fun h => by cases h
    · rcases (hQ epId ep r tcb hEo hTo).2 hr with h | h <;> rw [h] <;> exact fun h => by cases h
  refine ⟨fun c hc => ?_, hB⟩
  rw [cancelReplyHolder_currentOnCore] at hc
  have hB0 : blockedIfTcb st r := by
    intro t ht
    by_cases hrv : r = holder
    · rcases cancelReplyHolder_cases st holder ec with e | ⟨tcb, hL, hNR, -⟩
      · rw [e] at hB; exact hB t ht
      · rw [hrv] at ht
        rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr (lookupTcb_some_objects st holder tcb hL)]
          at ht
        cases ht; exact hNR
    · have e := hK r hrv
      rw [ht] at e
      cases h' : (cancelReplyHolder st holder ec).getTcb? r with
      | none => rw [h'] at e; cases e
      | some t' =>
        rw [h'] at e
        have e' : t'.ipcState = t.ipcState := Option.some.inj e
        rw [← e']; exact hB t' h'
  exact currentNowhere_of_blockedIfTcb hD hB0 c hc

/-- **A reply holder's cancel keeps every other thread active**: the teardown
and revert suspend no thread, and the `Inactive` write is the holder's. -/
theorem cancelReplyHolder_activeAt {st : SystemState} {holder t : SeLe4n.ThreadId}
    {ec : Concurrency.CoreId} (hInv : st.objects.invExt) (hR : st.runQueueRefined)
    (hNe : t ≠ holder) (h : st.activeAt t) : (cancelReplyHolder st holder ec).activeAt t := by
  rcases cancelReplyHolder_cases st holder ec with e | ⟨tcb, -, -, e⟩
  · rw [e]; exact h
  rw [e]
  have hS := suspendCancelRevert_runQueueStage st holder tcb ec
  obtain ⟨x, hx, hA⟩ := ((hS.2.2 hInv hR) t).2.2.1 h
  refine ⟨x, ?_, hA⟩
  rw [SystemState.updateTcb_getTcb?_ne _ _ _ (hS.1.links hInv hR).1 t
    (fun h' => hNe (SeLe4n.ThreadId.toObjId_injective _ _ h').symm)]
  exact hx

end SeLe4n.Kernel
