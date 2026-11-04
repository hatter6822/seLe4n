-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.FrameFinalise
import SeLe4n.Kernel.Architecture.InterruptMask

/-!
# WS-ZA ZA6.32 — the interrupt-control and interrupt-handler invocations

seL4's interrupt interface, over the interrupt nodes the boot installs (one
CNode of one slot per line, `SeLe4n.Model.irqNodeId`):

* `irqControlGet` — `seL4_IRQControl_Get`: a line the board has
  (`Arch_checkIRQ`) and that no handler holds (`isIRQActive`) is put at
  `IRQSignal` and its handler capability is issued into an empty slot, as a
  derivation child of the interrupt-control capability (`cteInsert`), so a
  revocation of that capability reaches every handler it issued.
* `irqHandlerSetNotification` — `seL4_IRQHandler_SetNotification`: the line's
  node slot emptied (`cteDeleteOne`) and a copy of a notification capability
  with the send right inserted there, as a derivation child of the capability
  it copies (`cteInsert`).
* `irqHandlerClear` — `seL4_IRQHandler_Clear`: the node slot emptied.

The handler's last capability's delete ends the line (`retireIrqNode`,
`finaliseCap`'s `deletingIRQHandler` and `deletedIRQHandler`): a handler
capability names its line's node (`Capability.namedObject`), so the final
delete empties the node's slot first and then retires the node, which puts the
line at `IRQInactive`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The line checks of `seL4_IRQControl_Get`**, read before any write:
`.invalidIrq` for a line that is no device line of the board (`Arch_checkIRQ`)
or that has no interrupt node, and `.revocationRequired` for a line a handler
already holds (`isIRQActive`, seL4's `RevokeFirst`). -/
@[inline] def irqControlLineRefusal (st : SystemState) (line : Nat) : Option KernelError :=
  if !Architecture.deviceInterruptLine st line then some .invalidIrq
  else if (st.getCNode? (irqNodeId line)).isNone then some .invalidIrq
  else if st.irqSignalLines.mem line then some .revocationRequired
  else none

/-- **`seL4_IRQControl_Get`'s checks**, read before any write: the line
checks (`irqControlLineRefusal`) and the destination's (`cspaceDstAdmitted`, an
addressable empty slot of a CNode, seL4's `ensureEmptySlot`). -/
@[inline] def irqControlGetAdmitted (st : SystemState) (dst : CSpaceAddr) (line : Nat) : Bool :=
  (irqControlLineRefusal st line).isNone && cspaceDstAdmitted dst st

/-- **`seL4_IRQControl_Get`'s writes**, in place: the line put at `IRQSignal`
(`setIRQState`), then the handler capability installed at `dst` as a derivation
child of the interrupt-control capability's slot `control` (`cteInsert`). -/
def irqControlGetPerform (control dst : CSpaceAddr) (line : Nat) (st : SystemState) :
    SystemState :=
  cspaceInstallPerform control dst (Capability.irqHandlerOf line) .mint
    (Architecture.setIrqLineSignal st line true)

/-- `irqControlGetPerform` as compiled: the handler capability written over the
destination slot's own record and its target (`CNode.insertIrqHandlerCap`), so
the issue builds neither a capability nor its target. -/
@[inline] def irqControlGetPerformImpl (control dst : CSpaceAddr) (line : Nat)
    (st : SystemState) : SystemState :=
  ((Architecture.setIrqLineSignal st line true).storeCNodeWith dst.cnode
    (·.insertIrqHandlerCap dst.slot line (AccessRightSet.ofList [.write]))).cdtAddChild
    control dst .mint

@[csimp] theorem irqControlGetPerform_eq_impl :
    @irqControlGetPerform = @irqControlGetPerformImpl := by
  funext control dst line st
  unfold irqControlGetPerform irqControlGetPerformImpl cspaceInstallPerform
  simp only [CNode.insertIrqHandlerCap_eq_insert]; rfl

/-- `irqControlGetAdmitted` on the slots' words, so the live arm builds no
address record. -/
def irqControlGetAdmittedAt (dstCnode : SeLe4n.ObjId) (dstSlot : SeLe4n.Slot) (line : Nat)
    (st : SystemState) : Bool :=
  irqControlGetAdmitted st ⟨dstCnode, dstSlot⟩ line

/-- `irqControlGetPerform` on the slots' words, so the live arm builds no
address record. -/
def irqControlGetPerformAt (srcCnode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (dstCnode : SeLe4n.ObjId) (dstSlot : SeLe4n.Slot) (line : Nat) (st : SystemState) :
    SystemState :=
  irqControlGetPerform ⟨srcCnode, srcSlot⟩ ⟨dstCnode, dstSlot⟩ line st

/-- **`seL4_IRQControl_Get`**: the checks, then the line put at `IRQSignal`,
the handler capability inserted at `dst`, and the derivation edge from the
interrupt-control capability's slot `control` recorded (`cteInsert`), so a
revocation of that capability reaches every handler it issued. -/
def irqControlGet (control dst : CSpaceAddr) (line : Nat) : Kernel Unit :=
  fun st =>
    match irqControlLineRefusal st line with
    | some e => .error e
    | none =>
      match cspaceInsertSlot dst (Capability.irqHandlerOf line)
          (Architecture.setIrqLineSignal st line true) with
      | .error e => .error e
      | .ok ((), st') => .ok ((), st'.cdtAddChild control dst .mint)

/-- An admitted issue is its in-place writes. -/
theorem irqControlGet_of_admitted {control dst : CSpaceAddr} {line : Nat} {st : SystemState}
    (h : irqControlGetAdmitted st dst line = true) :
    irqControlGet control dst line st = .ok ((), irqControlGetPerform control dst line st) := by
  unfold irqControlGetAdmitted at h
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨hR, hD⟩ := h
  have hD' : cspaceDstAdmitted dst (Architecture.setIrqLineSignal st line true) = true := by
    unfold cspaceDstAdmitted at hD ⊢
    simpa [SystemState.getCNode?, SystemState.getObject?] using hD
  simp only [irqControlGet, hR, cspaceInsertSlot_of_admitted hD', irqControlGetPerform,
    cspaceInstallPerform]

/-- **Whether a capability may be bound to an interrupt line**: a notification
capability carrying the send right (seL4's `isNotificationCap` and
`capNtfnCanSend` in `decodeIRQHandlerInvocation`). -/
@[inline] def irqNotificationCapAdmitted (st : SystemState) (cap : Capability) : Bool :=
  match cap.target with
  | .object n => cap.hasRight .write && (st.getNotification? n).isSome
  | _ => false

/-- **When the bind is written in place**: the capability is not null, its slot
is not in the line's node, the node's slot is addressable, and the node slot's
delete is the plain one (`cspaceDeleteAdmitted`: an empty slot, or a capability
that finalises and retires nothing, the first case of `zombieDeleteAt`).  Then
the delete is the slot emptied, after which the copy's checks hold
(`irqHandlerSetNotification_inPlace_copy`), so the bind is its writes. -/
@[inline] def irqHandlerSetNotificationInPlace (st : SystemState) (line : Nat)
    (srcCnode : SeLe4n.ObjId) (cap : Capability) : Bool :=
  cap.isNotNull && srcCnode != irqNodeId line &&
    cspaceDeleteAdmitted (irqNodeAddr line) st &&
    (match st.getCNode? (irqNodeId line) with
     | some cn => cn.slotAddressable irqNodeSlot
     | none => false)

/-- **`seL4_IRQHandler_SetNotification`'s checks**, read before any write: the
capability the caller named is a notification capability with the send right
(`irqNotificationCapAdmitted`), the line has its node (`cnodeInvoked`), and the
bind is written in place (`irqHandlerSetNotificationInPlace`). -/
@[inline] def irqHandlerSetNotificationAdmitted (st : SystemState) (line : Nat)
    (srcCnode : SeLe4n.ObjId) (cap : Capability) : Bool :=
  irqNotificationCapAdmitted st cap && cnodeInvoked (irqNodeId line) st &&
    irqHandlerSetNotificationInPlace st line srcCnode cap

/-- **`seL4_IRQHandler_SetNotification`'s writes**, in place: the node slot
emptied by the plain delete (`cspaceDeletePerform`, seL4's `cteDeleteOne` of a
capability that finalises nothing), then the copy of `src` into it
(`cspaceCopyPerform`, `cteInsert`). -/
def irqHandlerSetNotificationPerform (line : Nat) (src : CSpaceAddr) (st : SystemState) :
    SystemState :=
  cspaceCopyPerform src (irqNodeAddr line) (cspaceDeletePerform (irqNodeAddr line) st)

/-- `irqHandlerSetNotificationPerform` on the source slot's words, so the live
arm builds no address record. -/
def irqHandlerSetNotificationPerformAt (line : Nat) (srcCnode : SeLe4n.ObjId)
    (srcSlot : SeLe4n.Slot) (st : SystemState) : SystemState :=
  irqHandlerSetNotificationPerform line ⟨srcCnode, srcSlot⟩ st

/-- **`seL4_IRQHandler_SetNotification`**: the capability in `src` (the
notification capability the caller named) bound to line `line`: refused unless it
is a notification capability with the send right and the line has its node;
then the node slot emptied by the finalising delete every slot delete is
(`cspaceDeleteSlotZombie`, seL4's `cteDeleteOne`) and `src` copied into it as a
derivation child (`cspaceCopy`, `cteInsert`).  Every refusal of the capability
precedes the delete, as in seL4's `decodeIRQHandlerInvocation`.  When the delete
is the plain one the two steps are written in place
(`irqHandlerSetNotificationPerform`), which is the same delete and copy on every
state whose object table is well formed (`irqHandlerSetNotification_inPlace_copy`). -/
def irqHandlerSetNotification (executingCore : Concurrency.CoreId) (line : Nat)
    (src : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match st.lookupSlotCap src with
    | none => .error .invalidCapability
    | some cap =>
      if !irqNotificationCapAdmitted st cap then .error .invalidCapability
      else if !cnodeInvoked (irqNodeId line) st then .error .objectNotFound
      else if irqHandlerSetNotificationInPlace st line src.cnode cap then
        .ok ((), irqHandlerSetNotificationPerform line src st)
      else
        match cspaceDeleteSlotZombie executingCore (irqNodeAddr line) st with
        | .error e => .error e
        | .ok ((), st1) => cspaceCopy src (irqNodeAddr line) st1

/-- An admitted bind is its in-place writes. -/
theorem irqHandlerSetNotification_of_admitted {ec : Concurrency.CoreId} {line : Nat}
    {src : CSpaceAddr} {cap : Capability} {st : SystemState}
    (hL : st.lookupSlotCap src = some cap)
    (h : irqHandlerSetNotificationAdmitted st line src.cnode cap = true) :
    irqHandlerSetNotification ec line src st =
      .ok ((), irqHandlerSetNotificationPerform line src st) := by
  unfold irqHandlerSetNotificationAdmitted at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hA, hC⟩, hP⟩ := h
  simp only [irqHandlerSetNotification, hL, hA, hC, hP, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]

/-- **The in-place bind's delete is the node slot's delete**: on a plain delete
the zombie delete empties the slot (`zombieDeleteAt`'s first case). -/
theorem irqHandlerSetNotification_inPlace_delete {ec : Concurrency.CoreId} {line : Nat}
    {srcCnode : SeLe4n.ObjId} {cap : Capability} {st : SystemState}
    (hC : cnodeInvoked (irqNodeId line) st = true)
    (hP : irqHandlerSetNotificationInPlace st line srcCnode cap = true) :
    cspaceDeleteSlotZombie ec (irqNodeAddr line) st =
      .ok ((), cspaceDeletePerform (irqNodeAddr line) st) := by
  unfold irqHandlerSetNotificationInPlace at hP
  simp only [Bool.and_eq_true] at hP
  obtain ⟨⟨_, hD⟩, _⟩ := hP
  rw [cspaceDeleteSlotZombie_of_admitted (cspaceDeleteFinalisingAdmitted_of_cnodeInvoked hC)]
  unfold zombieDeleteAt
  rw [if_pos hD]
  rfl

/-- **The in-place bind's copy is the copy**: after the plain delete of the node
slot the copy's checks hold (`cspaceCopyAdmitted`): the source slot is in
another object, so it still holds the notification capability, which names no
untyped, and the node slot is addressable and empty.  So on a well-formed object
table the delete-and-copy of `irqHandlerSetNotification` is its in-place
writes. -/
theorem irqHandlerSetNotification_inPlace_copy {line : Nat} {src : CSpaceAddr}
    {cap : Capability} {st : SystemState} (hInv : st.objects.invExt)
    (hL : st.lookupSlotCap src = some cap) (hA : irqNotificationCapAdmitted st cap = true)
    (hP : irqHandlerSetNotificationInPlace st line src.cnode cap = true) :
    cspaceCopy src (irqNodeAddr line) (cspaceDeletePerform (irqNodeAddr line) st) =
      .ok ((), irqHandlerSetNotificationPerform line src st) := by
  unfold irqHandlerSetNotificationInPlace at hP
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hP
  obtain ⟨⟨⟨hNN, hS⟩, _⟩, hSA⟩ := hP
  cases hG : st.getCNode? (irqNodeId line) with
  | none => rw [hG] at hSA; cases hSA
  | some cn =>
    rw [hG] at hSA
    have hObj := (SystemState.getCNode?_eq_some_iff st _ cn).mp hG
    have hStore := SystemState.storeObject_cnode_eq_storeCNodeWith hObj (·.remove irqNodeSlot)
    have hInvC := storeObject_preserves_objects_invExt st _ _ _ hInv hStore
    have hAg := (spliceDeletedCdtNode_agree hInvC (irqNodeAddr line)).1
    have hDel : cspaceDeletePerform (irqNodeAddr line) st =
        spliceDeletedCdtNode (st.storeCNodeWith (irqNodeId line) (·.remove irqNodeSlot))
          (irqNodeAddr line) := by
      unfold cspaceDeletePerform slotCleared
      rw [show (irqNodeAddr line).cnode = irqNodeId line from rfl, hG]
      rfl
    have hNe : ∀ x, x ≠ irqNodeId line →
        (st.storeCNodeWith (irqNodeId line) (·.remove irqNodeSlot)).objects[x]? =
          st.objects[x]? :=
      fun x hx => storeObject_objects_ne st _ _ x _ hx hInv hStore
    have hAt := storeObject_objects_eq st _ _ _ hInv hStore
    unfold irqHandlerSetNotificationPerform
    rw [← hDel] at hAg
    apply cspaceCopy_of_admitted
    unfold cspaceCopyAdmitted
    have hLD : (cspaceDeletePerform (irqNodeAddr line) st).lookupSlotCap src = some cap := by
      rw [hAg.lookupSlotCap src, ← hL]
      unfold SystemState.lookupSlotCap SystemState.lookupCNode
      rw [hNe _ hS]
    rw [hLD]
    unfold irqNotificationCapAdmitted at hA
    have hU : untypedDeriveRefused (cspaceDeletePerform (irqNodeAddr line) st) src cap = false := by
      unfold untypedDeriveRefused
      cases hT : cap.target with
      | object n =>
        rw [hT] at hA
        simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hA
        obtain ⟨_, ntf, hN⟩ := hA
        have hON : st.objects[n]? = some (.notification ntf) := by
          unfold SystemState.getNotification? at hN
          split at hN
          · next h => cases hN; exact h
          · cases hN
        have hn : n ≠ irqNodeId line := by
          rintro rfl; rw [hObj] at hON; cases hON
        rw [hAg.getUntyped?]
        simp [SystemState.getUntyped?, hNe _ hn, hON]
      | _ => rfl
    obtain ⟨cn', hD', hW⟩ := (hAg (irqNodeId line)).cnode_fwd hAt
    have hG' := (SystemState.getCNode?_eq_some_iff _ _ cn').mpr hD'
    have hLk : cn'.lookup irqNodeSlot = none := by
      rw [CNode.proj_eq_of_withoutLinks_eq (·.lookup irqNodeSlot) hW, CNode.lookup_eq_lookupCells]
      unfold CNode.lookupCells CNode.remove
      simp [slotArrayGet_setIfInBounds]
    have hAd : cn'.slotAddressable irqNodeSlot = true := by
      rw [CNode.proj_eq_of_withoutLinks_eq (·.slotAddressable irqNodeSlot) hW]
      exact hSA
    simp only [cspaceDstAdmitted, show (irqNodeAddr line).cnode = irqNodeId line from rfl,
      show (irqNodeAddr line).slot = irqNodeSlot from rfl, hG', hLk, hAd, hU, hNN,
      Bool.not_false, Bool.and_true, Option.isNone_none]

/-- **What a successful `seL4_IRQHandler_SetNotification` is**, on any state:
the source admitted, the node slot's delete, then the copy into it, or, on the
in-place branch, the plain delete and the copy's writes. -/
theorem irqHandlerSetNotification_ok_cases {ec : Concurrency.CoreId} {line : Nat}
    {src : CSpaceAddr} {st st' : SystemState}
    (h : irqHandlerSetNotification ec line src st = .ok ((), st')) :
    ∃ cap st1, st.lookupSlotCap src = some cap ∧ irqNotificationCapAdmitted st cap = true ∧
      cnodeInvoked (irqNodeId line) st = true ∧
      cspaceDeleteSlotZombie ec (irqNodeAddr line) st = .ok ((), st1) ∧
      (cspaceCopy src (irqNodeAddr line) st1 = .ok ((), st') ∨
        (irqHandlerSetNotificationInPlace st line src.cnode cap = true ∧
          st1 = cspaceDeletePerform (irqNodeAddr line) st ∧
          st' = cspaceCopyPerform src (irqNodeAddr line) st1)) := by
  unfold irqHandlerSetNotification at h
  cases hL : st.lookupSlotCap src with
  | none => rw [hL] at h; cases h
  | some cap =>
    rw [hL] at h
    simp only at h
    by_cases hA : irqNotificationCapAdmitted st cap = true
    · by_cases hC : cnodeInvoked (irqNodeId line) st = true
      · simp only [hA, hC, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hP : irqHandlerSetNotificationInPlace st line src.cnode cap = true
        · simp only [hP, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq, true_and] at h
          subst h
          exact ⟨cap, _, rfl, hA, hC, irqHandlerSetNotification_inPlace_delete hC hP,
            .inr ⟨hP, rfl, rfl⟩⟩
        · simp only [hP, Bool.false_eq_true, ↓reduceIte] at h
          cases hD : cspaceDeleteSlotZombie ec (irqNodeAddr line) st with
          | error e => rw [hD] at h; cases h
          | ok r =>
            obtain ⟨⟨⟩, st1⟩ := r
            rw [hD] at h
            exact ⟨cap, st1, rfl, hA, hC, rfl, .inl h⟩
      · simp only [Bool.not_eq_true] at hC
        simp [hA, hC] at h
    · simp only [Bool.not_eq_true] at hA
      simp [hA] at h

/-- **What a successful `seL4_IRQHandler_SetNotification` is**, on a
well-formed object table: the source admitted, the node slot's delete, then the
copy into it, the in-place branch being that delete and copy
(`irqHandlerSetNotification_inPlace_copy`). -/
theorem irqHandlerSetNotification_ok {ec : Concurrency.CoreId} {line : Nat}
    {src : CSpaceAddr} {st st' : SystemState} (hObjInv : st.objects.invExt)
    (h : irqHandlerSetNotification ec line src st = .ok ((), st')) :
    ∃ cap st1, st.lookupSlotCap src = some cap ∧ irqNotificationCapAdmitted st cap = true ∧
      cnodeInvoked (irqNodeId line) st = true ∧
      cspaceDeleteSlotZombie ec (irqNodeAddr line) st = .ok ((), st1) ∧
      cspaceCopy src (irqNodeAddr line) st1 = .ok ((), st') := by
  obtain ⟨cap, st1, hL, hA, hC, hD, hK | ⟨hP, rfl, rfl⟩⟩ := irqHandlerSetNotification_ok_cases h
  · exact ⟨cap, st1, hL, hA, hC, hD, hK⟩
  · exact ⟨cap, _, hL, hA, hC, hD, irqHandlerSetNotification_inPlace_copy hObjInv hL hA hP⟩

/-- **`seL4_IRQHandler_Clear`**: the line's node slot emptied by the finalising
delete (`cspaceDeleteSlotZombie`, seL4's `cteDeleteOne`), so the line signals
nothing until a notification is set again. -/
def irqHandlerClear (executingCore : Concurrency.CoreId) (line : Nat) : Kernel Unit :=
  fun st =>
    if !cnodeInvoked (irqNodeId line) st then .error .objectNotFound
    else cspaceDeleteSlotZombie executingCore (irqNodeAddr line) st

end SeLe4n.Kernel
