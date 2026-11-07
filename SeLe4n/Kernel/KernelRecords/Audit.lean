-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.Timer

/-!
# The audit, declassification and interrupt-issue arms keep the records' reads

WS-ZA ZA6.37.  The audit read writes nothing, the drain and the declassification
write their trails, the stash clear rewrites one thread's stash code (which no
record view reads), and the handler issue writes the line's state, a capability
slot and a derivation edge: each is a `RecordsFrame`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace RecordsFrame

theorem auditReadFromCore {ctx : GenericLabelingContext} {monitorClearance : Option SecurityDomain}
    {c : CoreId} {op : AuditReadOp} {st st' : SystemState} {w : Nat} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.auditReadFromCore ctx monitorClearance c op st = .ok (w, st')) :
    RecordsFrame st st' :=
  of_eq hInv (auditReadFromCore_frame _ _ _ _ _ _ _ h)

theorem auditDrainVisiblePrefix {ctx : GenericLabelingContext}
    {monitorClearance : Option SecurityDomain} {c : CoreId} {count n : Nat} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.auditDrainVisiblePrefix ctx monitorClearance c count st = .ok (n, st')) :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.auditDrainVisiblePrefix at h
  split at h
  · cases h; exact of_objects_eq hInv rfl rfl
  · cases h

theorem declassifyObjectFromCore {ctx : GenericLabelingContext}
    {declPolicy : DeclassificationPolicy} {c : CoreId} {targetId : SeLe4n.ObjId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.declassifyObjectFromCore ctx declPolicy c targetId st = .ok ((), st')) :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.declassifyObjectFromCore at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  rw [(authorizeDeclassificationOnCore_frame _ _ _ _ _ _ _ _ _ h).1]
  exact of_objects_eq hInv rfl rfl

/-- Clearing a woken receiver's stash rewrites one thread's stash code. -/
theorem clearWokenReceiverStash (receiver? : Option SeLe4n.ThreadId) {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.clearWokenReceiverStash receiver? st = .ok ((), st')) :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.clearWokenReceiverStash at h
  split at h
  · cases h; exact refl hInv
  · split at h
    · rename_i rTcb hT
      split at h
      · exact storeObject hInv h (by rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hT]; rfl)
          (fun _ h => by cases h)
      · cases h; exact refl hInv
    · cases h; exact refl hInv

/-- The handler issue: the line's state, the handler capability's slot and its
derivation edge. -/
theorem irqControlGet {control dst : CSpaceAddr} {line : Nat} {st st' : SystemState}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.irqControlGet control dst line st = .ok ((), st')) :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.irqControlGet at h
  cases hR : irqControlLineRefusal st line with
  | some e => rw [hR] at h; cases h
  | none =>
    rw [hR] at h
    simp only at h
    cases hI : _root_.SeLe4n.Kernel.cspaceInsertSlot dst (Capability.irqHandlerOf line)
        (Architecture.setIrqLineSignal st line true) with
    | error e => rw [hI] at h; cases h
    | ok pr =>
      obtain ⟨⟨⟩, st1⟩ := pr
      rw [hI] at h
      injection h with h
      injection h with hu h
      subst h
      have F0 := of_objects_eq hInv (Architecture.setIrqLineSignal_objects st line true)
        (Architecture.setIrqLineSignal_asidTable st line true)
      have F1 := F0.trans (cspaceInsertSlot F0.invExt hI)
      exact F1.trans (cdtAddChild st1 control dst .mint F1.invExt)

theorem irqControlGetFromCap {tid : SeLe4n.ThreadId} {srcAddr : SeLe4n.CPtr}
    {args? : Except KernelError Architecture.SyscallArgDecode.IrqControlGetArgs} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.irqControlGetFromCap tid srcAddr args? st = .ok ((), st')) :
    RecordsFrame st st' := by
  obtain ⟨_, _, _, _, _, _, hG⟩ := irqControlGetFromCap_ok tid srcAddr args? st st' h
  exact irqControlGet hInv hG

end RecordsFrame

end SeLe4n.Kernel
