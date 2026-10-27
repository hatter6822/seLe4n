-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.MappingRecordStage.Ipc

/-! # The audit and declassification arms keep the mappings recorded

The audit read writes nothing, the audit drain and the declassification write
the audit trail alone, and the declassified signal is the bound signal followed
by the trail's records; the stash clear a waking arm ends with rewrites one
thread's stash code.  Each is a `MappingStage`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState (MappingStage)
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **The audit read keeps the mappings recorded**: it writes nothing. -/
theorem auditReadFromCore_mappingStage {ctx : GenericLabelingContext}
    {monitorClearance : Option SecurityDomain} {c : CoreId} {op : AuditReadOp}
    {st st' : SystemState} {w : Nat}
    (h : auditReadFromCore ctx monitorClearance c op st = .ok (w, st')) : MappingStage st st' :=
  MappingStage.of_eq (auditReadFromCore_frame _ _ _ _ _ _ _ h)

/-- **The audit drain keeps the mappings recorded**: it writes the trail alone. -/
theorem auditDrainVisiblePrefix_mappingStage {ctx : GenericLabelingContext}
    {monitorClearance : Option SecurityDomain} {c : CoreId} {count n : Nat}
    {st st' : SystemState}
    (h : auditDrainVisiblePrefix ctx monitorClearance c count st = .ok (n, st')) :
    MappingStage st st' := by
  unfold auditDrainVisiblePrefix at h
  split at h
  · cases h; exact MappingStage.of_objects_eq rfl
  · cases h

/-- **The declassification keeps the mappings recorded**: it writes the trail
alone. -/
theorem declassifyObjectFromCore_mappingStage {ctx : GenericLabelingContext}
    {declPolicy : DeclassificationPolicy} {c : CoreId} {targetId : SeLe4n.ObjId}
    {st st' : SystemState}
    (h : declassifyObjectFromCore ctx declPolicy c targetId st = .ok ((), st')) :
    MappingStage st st' := by
  unfold declassifyObjectFromCore at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  rw [(authorizeDeclassificationOnCore_frame _ _ _ _ _ _ _ _ _ h).1]
  exact MappingStage.of_objects_eq rfl

/-- **The declassified signal keeps the mappings recorded**: the bound signal,
then the trail's records. -/
theorem notificationSignalDeclassifiedOnCore_mappingStage (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState) :
    MappingStage st
      (notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st).1 := by
  unfold notificationSignalDeclassifiedOnCore
  split
  · exact MappingStage.refl _
  split
  · split <;> exact MappingStage.refl _
  dsimp only
  split
  · exact MappingStage.refl _
  have hB : MappingStage st (notificationSignalBoundOnCore notificationId badge c st).1 :=
    notificationSignalBoundOnCore_mappingStage
  generalize notificationSignalBoundOnCore notificationId badge c st = r at hB
  obtain ⟨st1, res⟩ := r
  cases res with
  | error _ => exact MappingStage.refl _
  | ok sgi =>
    dsimp only at hB ⊢
    split
    · exact MappingStage.refl _
    · rename_i st2 hRec
      rw [recordDeclassifiedHops_frame _ _ _ _ _ hRec]
      exact hB.trans (MappingStage.of_objects_eq rfl)

/-- **Clearing a woken receiver's stash keeps the mappings recorded**: it
rewrites one thread's stash code. -/
theorem clearWokenReceiverStash_mappingStage (receiver? : Option SeLe4n.ThreadId)
    {st st' : SystemState} (h : clearWokenReceiverStash receiver? st = .ok ((), st')) :
    MappingStage st st' := by
  unfold clearWokenReceiverStash at h
  split at h
  · cases h; exact MappingStage.refl _
  · split at h
    · rename_i rTcb hT
      split at h
      · exact MappingStage.storeObject h ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) rfl
          (by simp [KernelObject.objectType])
      · cases h; exact MappingStage.refl _
    · cases h; exact MappingStage.refl _

end SeLe4n.Kernel
