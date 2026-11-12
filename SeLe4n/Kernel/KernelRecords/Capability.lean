-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.Thread

/-!
# The slot-writing capability arms keep the records

WS-ZA ZA6.37.  The mint, copy, move, reply-capability mint and untyped reset
write CNode slots, a thread's space slots, the derivation tree and slot links:
none of them a record view reads, so each is a `RecordsFrame`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

namespace RecordsFrame

theorem cspaceMint {src dst : CSpaceAddr} {rights : AccessRightSet} {badge : Option SeLe4n.Badge}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.cspaceMint src dst rights badge st = .ok ((), st')) :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.cspaceMint at hStep
  split at hStep
  · contradiction
  · rename_i parent stMid hLk
    have hMid : stMid = st := cspaceLookupSlot_state_eq st stMid src parent hLk
    subst hMid
    split at hStep
    · contradiction
    · split at hStep
      · contradiction
      · exact cspaceInsertSlot hInv hStep

theorem cspaceMintWithCdt {src dst : CSpaceAddr} {rights : AccessRightSet}
    {badge : Option SeLe4n.Badge} {st st' : SystemState} (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.cspaceMintWithCdt src dst rights badge st = .ok ((), st')) :
    RecordsFrame st st' := by
  obtain ⟨_, stM, hMint, -, -, rfl⟩ := cspaceMintWithCdt_ok_decompose hStep
  have F := cspaceMint hInv hMint
  have F2 := F.trans (cdtAddChild stM src dst .mint F.invExt)
  exact F2.trans (untypedSourceSetFull _ src _ F2.invExt)

theorem cspaceCopy {src dst : CSpaceAddr} {mask : AccessRightSet} {st st' : SystemState} (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.cspaceCopy src dst mask st = .ok ((), st')) : RecordsFrame st st' := by
  obtain ⟨_, st2, -, -, hIns, -, rfl⟩ := cspaceCopy_ok_decompose hStep
  have F := cspaceInsertSlot hInv hIns
  have F2 := F.trans (cdtAddChild st2 src dst .copy F.invExt)
  exact F2.trans (untypedSourceSetFull _ src _ F2.invExt)

/-- A slot cleared in a CNode or a thread's space slots. -/
theorem cspaceDeleteSlotCore {addr : CSpaceAddr} {st st' : SystemState} (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.cspaceDeleteSlotCore addr st = .ok ((), st')) :
    RecordsFrame st st' := by
  obtain ⟨o, hO, hH, hS⟩ := cspaceDeleteSlotCore_ok hStep
  refine storeObject hInv hS (by rw [hO]; cases o <;> rfl) (fun r h => ?_)
  cases o <;> simp_all [KernelObject.removeSlotCap, KernelObject.holdsSlots]

theorem cspaceMove {src dst : CSpaceAddr} {st st' : SystemState} (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.cspaceMove src dst st = .ok ((), st')) : RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.cspaceMove at hStep
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
          have F := cspaceInsertSlot hInv hIns
          split at hStep
          · contradiction
          · rename_i st3 hDel
            have F3 := F.trans (cspaceDeleteSlotCore F.invExt hDel)
            cases hStep
            exact F3.trans ((withCdt st3 _ F3.invExt).trans
              (of_linkReach (SystemState.cdtMove_reach st3 src dst) F3.invExt))

theorem mintReplyCapWithCdt {src dst : CSpaceAddr} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.mintReplyCapWithCdt src dst st = .ok ((), st')) :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.mintReplyCapWithCdt at hStep
  split at hStep
  · contradiction
  · rename_i stM hMint
    cases hStep
    have F : RecordsFrame st stM := by
      unfold mintReplyCap at hMint
      split at hMint
      · contradiction
      · rename_i parent stMid hLk
        have hMid : stMid = st := cspaceLookupSlot_state_eq st stMid src parent hLk
        subst hMid
        split at hMint
        · dsimp only [] at hMint
          split at hMint
          · exact cspaceInsertSlot hInv hMint
          · contradiction
        · contradiction
    exact F.trans (cdtAddChild stM src dst .mint F.invExt)

theorem untypedResetFromCap {tid : SeLe4n.ThreadId} {srcAddr : SeLe4n.CPtr} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.untypedResetFromCap tid srcAddr st = .ok ((), st')) :
    RecordsFrame st st' := by
  obtain ⟨_, _, _, -, -, hS⟩ := untypedResetFromCap_ok _ _ st st' hStep
  rw [untypedResetSlot_ok_frame hS]
  exact setCapFreeIndex _ _ _ hInv

end RecordsFrame

end SeLe4n.Kernel
