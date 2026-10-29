-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.MappingRecordStage.Thread

/-! # The run-queue writes and the scheduling point keep the mappings recorded

A run-queue write rewrites the threads' run-queue links alone
(`objectsAgreeOffRunLinks`), a context save or restore rewrites one thread's
register file or the machine, and a flag or current-slot write touches the
scheduler alone, so each is a `MappingStage`; so is the scheduling point a
reschedule runs (`handleRescheduleSgiOnCore`), built of them.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState (MappingStage)
open SeLe4n.Kernel.Concurrency (CoreId)

theorem runEnqueueOnCore_mappingStage (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : MappingStage st (st.runEnqueueOnCore c t p) :=
  MappingStage.of_objectsAgreeOffRunLinks (SystemState.runEnqueueOnCore_objects_invExt st c t p)
    (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks st c t p)

theorem runEnqueueAdmitted_mappingStage (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : MappingStage st (st.runEnqueueAdmitted c t p) :=
  MappingStage.of_objectsAgreeOffRunLinks (SystemState.runEnqueueAdmitted_objects_invExt st c t p)
    (SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks st c t p)

theorem runRemoveOnCore_mappingStage (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    MappingStage st (st.runRemoveOnCore c t) :=
  MappingStage.of_objectsAgreeOffRunLinks (SystemState.runRemoveOnCore_objects_invExt st c t)
    (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks st c t)

theorem runDescheduleOnCore_mappingStage (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    MappingStage st (st.runDescheduleOnCore c t) :=
  MappingStage.of_objectsAgreeOffRunLinks (SystemState.runDescheduleOnCore_objects_invExt st c t)
    (SystemState.runDescheduleOnCore_objectsAgreeOffRunLinks st c t)

theorem runRequeueOnCore_mappingStage (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : MappingStage st (st.runRequeueOnCore c t p) :=
  MappingStage.of_objectsAgreeOffRunLinks (SystemState.runRequeueOnCore_objects_invExt st c t p)
    (SystemState.runRequeueOnCore_objectsAgreeOffRunLinks st c t p)

theorem removeRunnableOnCore_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    MappingStage st (removeRunnableOnCore st tid c) :=
  MappingStage.of_objectsAgreeOffRunLinks (removeRunnableOnCore_objects_invExt st tid c)
    (removeRunnableOnCore_objectsAgreeOffRunLinks st tid c)

theorem enqueueRunnableOnCore_mappingStage (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) :
    MappingStage st (enqueueRunnableOnCore st c tid) :=
  MappingStage.of_kindPreservingWrite (enqueueRunnableOnCore_preserves_objects_invExt st c tid)
    (enqueueRunnableOnCore_kindPreservingWrite st c tid)

theorem markKeyChangeFor_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    MappingStage st (markKeyChangeFor st tid k) :=
  MappingStage.of_objects_eq (markKeyChangeFor_objects st tid k)

/-- The candidacy hook writes reschedule flags only. -/
theorem markCandidacyGainFor_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    MappingStage st (markCandidacyGainFor st tid b) :=
  MappingStage.of_objects_eq (markCandidacyGainFor_objects st tid b)

theorem markKeyChangeFrom_mappingStage (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    MappingStage st (markKeyChangeFrom pre st tid) :=
  MappingStage.of_objects_eq (markKeyChangeFrom_objects pre st tid)

theorem saveOutgoingContextOnCore_mappingStage (st : SystemState) (c : CoreId) :
    MappingStage st (saveOutgoingContextOnCore st c) := by
  unfold saveOutgoingContextOnCore
  split
  · exact MappingStage.refl _
  · exact updateTcb_mappingStage _ _ _

theorem restoreIncomingContextOnCore_mappingStage (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : MappingStage st (restoreIncomingContextOnCore st c tid) :=
  MappingStage.of_objects_eq (restoreIncomingContextOnCore_objects st c tid)

theorem preemptCurrentOnCore_mappingStage (st : SystemState) (c : CoreId)
    (incoming : SeLe4n.ThreadId) : MappingStage st (preemptCurrentOnCore st c incoming) := by
  unfold preemptCurrentOnCore
  split
  · exact MappingStage.refl _
  · split
    · exact MappingStage.refl _
    · split
      · rename_i prevTcb h _
        exact (MappingStage.rewriteObject_tcb h _).trans (runEnqueueOnCore_mappingStage _ _ _ _)
      · exact MappingStage.refl _

theorem switchToThreadOnCore_mappingStage {st st' : SystemState} {c : CoreId}
    {tid : SeLe4n.ThreadId} (h : switchToThreadOnCore st c tid = .ok st') : MappingStage st st' :=
  (preemptCurrentOnCore_mappingStage st c tid).trans
    (MappingStage.of_objectsAgreeOffRunLinks
      (fun hI => by
        have := switchToThreadOnCore_ok_objects st st' c tid h
        rw [this]; exact SystemState.runRemoveOnCore_objects_invExt _ _ _ hI)
      (switchToThreadOnCore_objectsAgreeOffRunLinks_preempt st c tid st' h))

theorem dropCurrentOnCore_mappingStage (st : SystemState) (c : CoreId) :
    MappingStage st (dropCurrentOnCore st c) :=
  (preemptCurrentOnCore_mappingStage st c (idleThreadId c)).trans
    (MappingStage.of_objects_eq (dropCurrentOnCore_objects st c))

theorem clearReschedulePendingOnCore_mappingStage (st : SystemState) (c : CoreId) :
    MappingStage st (st.clearReschedulePendingOnCore c) :=
  MappingStage.of_objects_eq (SystemState.clearReschedulePendingOnCore_objects st c)

/-- **The scheduling point keeps the mappings recorded**: the switch, the drop
of an out-of-domain incumbent, and the flag clear. -/
theorem handleRescheduleSgiOnCore_mappingStage {st st' : SystemState} {c : CoreId}
    (h : handleRescheduleSgiOnCore st c = .ok st') : MappingStage st st' := by
  unfold handleRescheduleSgiOnCore at h
  split at h
  · cases h
  · split at h <;> cases h
    · exact (dropCurrentOnCore_mappingStage st c).trans (clearReschedulePendingOnCore_mappingStage _ c)
    · exact clearReschedulePendingOnCore_mappingStage st c
  · split at h
    · split at h
      · rename_i st1 hS
        cases h
        exact (switchToThreadOnCore_mappingStage hS).trans (clearReschedulePendingOnCore_mappingStage _ c)
      · split at h <;> cases h
        · exact (dropCurrentOnCore_mappingStage st c).trans
            (clearReschedulePendingOnCore_mappingStage _ c)
        · exact clearReschedulePendingOnCore_mappingStage st c
    · cases h; exact clearReschedulePendingOnCore_mappingStage st c

end SeLe4n.Kernel
