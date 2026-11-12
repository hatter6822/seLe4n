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

/-- **Whether the line's node slot holds a notification capability**: its
capability names a notification object.  Its delete then finalises at most that
notification, which holds no capability, so the zombie loop has no pass to run
(`zombieSlotClass` is `0`) and the delete's teardown has no page or table to
take out. -/
@[inline] def irqNodeHoldsNotificationCap (st : SystemState) (line : Nat) : Bool :=
  match st.slotCapAt ⟨irqNodeId line, irqNodeSlot⟩ with
  | some c =>
    match c.target with
    | .object n => (st.getNotification? n).isSome
    | _ => false
  | none => false

/-- **When the bind over the node slot's notification capability is written in
place**: the capability is not null, its slot is not in the line's node, the
node's slot is addressable, and the node slot holds a notification capability
(`irqNodeHoldsNotificationCap`), whose final delete retires that notification
(seL4's `cteDeleteOne`, which `invokeIRQHandler`'s `SetIRQHandler` runs before
`cteInsert`).  The delete then leaves the copy's checks holding
(`irqHandlerSetNotification_overFinal_copy`), so the bind is its writes. -/
@[inline] def irqHandlerSetNotificationOverFinal (st : SystemState) (line : Nat)
    (srcCnode : SeLe4n.ObjId) (cap : Capability) : Bool :=
  cap.isNotNull && srcCnode != irqNodeId line && irqNodeHoldsNotificationCap st line &&
    (match st.getCNode? (irqNodeId line) with
     | some cn => cn.slotAddressable irqNodeSlot
     | none => false)

/-- **`seL4_IRQHandler_SetNotification`'s checks**, read before any write: the
capability the caller named is a notification capability with the send right
(`irqNotificationCapAdmitted`), the line has its node (`cnodeInvoked`), and the
bind is written in place, over a plain delete (`irqHandlerSetNotificationInPlace`)
or over the final delete of a notification capability
(`irqHandlerSetNotificationOverFinal`). -/
@[inline] def irqHandlerSetNotificationAdmitted (st : SystemState) (line : Nat)
    (srcCnode : SeLe4n.ObjId) (cap : Capability) : Bool :=
  irqNotificationCapAdmitted st cap && cnodeInvoked (irqNodeId line) st &&
    (irqHandlerSetNotificationInPlace st line srcCnode cap ||
      irqHandlerSetNotificationOverFinal st line srcCnode cap)

/-- **`seL4_IRQHandler_SetNotification`'s writes**, in place: the node slot
emptied by the plain delete (`cspaceDeletePerform`, seL4's `cteDeleteOne` of a
capability that finalises nothing), then the copy of `src` into it
(`cspaceCopyPerform`, `cteInsert`). -/
@[inline] def irqHandlerSetNotificationPerform (line : Nat) (src : CSpaceAddr)
    (st : SystemState) :
    SystemState :=
  cspaceCopyPerform src (irqNodeAddr line) .full (cspaceDeletePerform (irqNodeAddr line) st)

/-- **The bind's writes over the node slot's notification capability**: the
node slot emptied by the zombie delete every slot delete is (`zombieDeleteAt`,
here one finalising delete), then the copy of `src` into it
(`cspaceCopyPerform`). -/
@[inline] def irqHandlerSetNotificationOverFinalPerform (executingCore : Concurrency.CoreId)
    (line : Nat) (src : CSpaceAddr) (st : SystemState) : SystemState :=
  cspaceCopyPerform src (irqNodeAddr line) .full
    (zombieDeleteAt executingCore (irqNodeAddr line).cnode (irqNodeAddr line).slot st)

/-- **The bind's writes**, whichever delete the node slot takes: the plain one
(`irqHandlerSetNotificationPerform`) or the finalising one over a notification
capability (`irqHandlerSetNotificationOverFinalPerform`), on the source slot's
words, so the live arm builds no address record (each perform is inlined, so
every read of the source is a read of its words). -/
def irqHandlerSetNotificationBindAt (executingCore : Concurrency.CoreId) (line : Nat)
    (srcCnode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (cap : Capability) (st : SystemState) :
    SystemState :=
  if irqHandlerSetNotificationInPlace st line srcCnode cap then
    irqHandlerSetNotificationPerform line ⟨srcCnode, srcSlot⟩ st
  else irqHandlerSetNotificationOverFinalPerform executingCore line ⟨srcCnode, srcSlot⟩ st

/-- **`seL4_IRQHandler_SetNotification`**: the capability in `src` (the
notification capability the caller named) bound to line `line`: refused unless it
is a notification capability with the send right and the line has its node;
then the node slot emptied by the finalising delete every slot delete is
(`cspaceDeleteSlotZombie`, seL4's `cteDeleteOne`) and `src` copied into it as a
derivation child (`cspaceCopy`, `cteInsert`).  Every refusal of the capability
precedes the delete, as in seL4's `decodeIRQHandlerInvocation`.  When the delete
is the plain one the two steps are written in place
(`irqHandlerSetNotificationPerform`), and so are they when the node slot holds a
notification capability (`irqHandlerSetNotificationOverFinalPerform`); each is
the same delete and copy on every state whose object table is well formed
(`irqHandlerSetNotification_inPlace_copy`, `irqHandlerSetNotification_overFinal_copy`). -/
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
      else if irqHandlerSetNotificationOverFinal st line src.cnode cap then
        .ok ((), irqHandlerSetNotificationOverFinalPerform executingCore line src st)
      else
        match cspaceDeleteSlotZombie executingCore (irqNodeAddr line) st with
        | .error e => .error e
        | .ok ((), st1) => cspaceCopy src (irqNodeAddr line) .full st1

/-- An admitted bind is its in-place writes. -/
theorem irqHandlerSetNotification_of_admitted {ec : Concurrency.CoreId} {line : Nat}
    {src : CSpaceAddr} {cap : Capability} {st : SystemState}
    (hL : st.lookupSlotCap src = some cap)
    (h : irqHandlerSetNotificationAdmitted st line src.cnode cap = true) :
    irqHandlerSetNotification ec line src st =
      .ok ((), irqHandlerSetNotificationBindAt ec line src.cnode src.slot cap st) := by
  unfold irqHandlerSetNotificationAdmitted at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨hA, hC⟩, hP⟩ := h
  unfold irqHandlerSetNotificationBindAt
  by_cases hI : irqHandlerSetNotificationInPlace st line src.cnode cap = true
  · simp only [irqHandlerSetNotification, hL, hA, hC, hI, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte]
  · have hO : irqHandlerSetNotificationOverFinal st line src.cnode cap = true := by
      rcases hP with h | h
      · exact absurd h hI
      · exact h
    simp only [irqHandlerSetNotification, hL, hA, hC, hI, hO, Bool.not_true, Bool.false_eq_true,
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

/-- **After the plain delete of the node slot the copy's checks hold**
(`cspaceCopyAdmitted`): the source slot is in another object, so it still holds
the notification capability, which names no untyped, and the node slot is
addressable and empty; the object table stays well formed. -/
theorem irqHandlerSetNotification_deleteCopyAdmitted {line : Nat} {src : CSpaceAddr}
    {cap : Capability} {st : SystemState} (hInv : st.objects.invExt)
    (hL : st.lookupSlotCap src = some cap) (hA : irqNotificationCapAdmitted st cap = true)
    (hNN : cap.isNotNull = true) (hS : src.cnode ≠ irqNodeId line)
    (hSA : (match st.getCNode? (irqNodeId line) with
      | some cn => cn.slotAddressable irqNodeSlot
      | none => false) = true) :
    (cspaceDeletePerform (irqNodeAddr line) st).lookupSlotCap src = some cap ∧
      (∀ n, cap.target = .object n →
        (cspaceDeletePerform (irqNodeAddr line) st).getUntyped? n = none) ∧
      cspaceDstAdmitted (irqNodeAddr line) (cspaceDeletePerform (irqNodeAddr line) st) = true ∧
      (cspaceDeletePerform (irqNodeAddr line) st).objects.invExt := by
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
    rw [← hDel] at hAg
    have hLD : (cspaceDeletePerform (irqNodeAddr line) st).lookupSlotCap src = some cap := by
      rw [hAg.lookupSlotCap src, ← hL]
      unfold SystemState.lookupSlotCap SystemState.lookupCNode
      rw [hNe _ hS]
    unfold irqNotificationCapAdmitted at hA
    have hU : ∀ n, cap.target = .object n →
        (cspaceDeletePerform (irqNodeAddr line) st).getUntyped? n = none := by
      intro n hT
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
    obtain ⟨cn', hD', hW⟩ := (hAg (irqNodeId line)).cnode_fwd hAt
    have hG' := (SystemState.getCNode?_eq_some_iff _ _ cn').mpr hD'
    have hLk : cn'.lookup irqNodeSlot = none := by
      rw [CNode.proj_eq_of_withoutLinks_eq (·.lookup irqNodeSlot) hW, CNode.lookup_eq_lookupCells]
      unfold CNode.lookupCells CNode.remove
      simp [slotArrayGet_setIfInBounds]
    have hAd : cn'.slotAddressable irqNodeSlot = true := by
      rw [CNode.proj_eq_of_withoutLinks_eq (·.slotAddressable irqNodeSlot) hW]
      exact hSA
    refine ⟨hLD, hU, ?_, by rw [hDel]; exact (spliceDeletedCdtNode_agree hInvC (irqNodeAddr line)).2⟩
    simp only [cspaceDstAdmitted, show (irqNodeAddr line).cnode = irqNodeId line from rfl,
      show (irqNodeAddr line).slot = irqNodeSlot from rfl, hG', hLk, hAd,
      Bool.and_true, Option.isNone_none]

/-- **The copy's checks, from their parts**: the source holds a capability that
is not null and names no untyped, and the destination is admitted. -/
theorem cspaceCopyAdmitted_of_parts {src dst : CSpaceAddr} {cap : Capability} {st : SystemState}
    (hL : st.lookupSlotCap src = some cap) (hNN : cap.isNotNull = true)
    (hU : ∀ n, cap.target = .object n → st.getUntyped? n = none)
    (hD : cspaceDstAdmitted dst st = true) : cspaceCopyAdmitted src dst .full st = true := by
  unfold cspaceCopyAdmitted
  have hR : untypedDeriveRefused st src cap = false := by
    unfold untypedDeriveRefused
    cases hT : cap.target with
    | object n => simp [hU n hT]
    | _ => rfl
  simp [hL, hNN, hR, hD, Capability.maskRights_full]


/-- **The in-place bind's copy is the copy**: after the plain delete of the node
slot the copy's checks hold (`irqHandlerSetNotification_deleteCopyAdmitted`).  So
on a well-formed object table the delete-and-copy of `irqHandlerSetNotification`
is its in-place writes. -/
theorem irqHandlerSetNotification_inPlace_copy {line : Nat} {src : CSpaceAddr}
    {cap : Capability} {st : SystemState} (hInv : st.objects.invExt)
    (hL : st.lookupSlotCap src = some cap) (hA : irqNotificationCapAdmitted st cap = true)
    (hP : irqHandlerSetNotificationInPlace st line src.cnode cap = true) :
    cspaceCopy src (irqNodeAddr line) .full (cspaceDeletePerform (irqNodeAddr line) st) =
      .ok ((), irqHandlerSetNotificationPerform line src st) := by
  unfold irqHandlerSetNotificationInPlace at hP
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hP
  obtain ⟨⟨⟨hNN, hS⟩, _⟩, hSA⟩ := hP
  obtain ⟨hL', hU, hD, -⟩ := irqHandlerSetNotification_deleteCopyAdmitted hInv hL hA hNN hS hSA
  exact cspaceCopy_of_admitted (cspaceCopyAdmitted_of_parts hL' hNN hU hD)

/-- The line signal's write keeps the object table. -/
theorem setIrqLineSignal_objects (st : SystemState) (line : Nat) (signal : Bool) :
    (Architecture.setIrqLineSignal st line signal).objects = st.objects := by
  simp [Architecture.setIrqLineSignal, Architecture.setInterruptLineMask]

/-- **The retire after a final delete keeps the copy's parts**: the source's
capability, that it names no untyped, and the destination's admission, when the
retired object is not the destination's CNode.  The node line's retire writes no
object; the finalisation writes no CNode and makes no untyped
(`FinaliseFrameAny`); the retire keeps every CNode slot lookup, makes no untyped,
and erases only the retired object (`finalRetireWrite`). -/
theorem retireFinalisedObject_copyParts (ec : Concurrency.CoreId) (T R : Nat)
    {src dst : CSpaceAddr} {cap : Capability} {st : SystemState} (hInv : st.objects.invExt)
    (hX : T = 0 ∨ SeLe4n.ObjId.ofNat (T - 1) ≠ dst.cnode)
    (hL : st.lookupSlotCap src = some cap)
    (hU : ∀ n, cap.target = .object n → st.getUntyped? n = none)
    (hD : cspaceDstAdmitted dst st = true) :
    (retireFinalisedObject ec T R st).lookupSlotCap src = some cap ∧
      (∀ n, cap.target = .object n → (retireFinalisedObject ec T R st).getUntyped? n = none) ∧
      cspaceDstAdmitted dst (retireFinalisedObject ec T R st) = true := by
  rcases retireFinalisedObject_cases ec T R st with ⟨-, hR⟩ | ⟨-, hR⟩
  · rw [hR]
    have hO := setIrqLineSignal_objects st ((SeLe4n.ObjId.ofNat (T - 1)).toNat - irqNodeIdBase) false
    unfold retireIrqNode
    refine ⟨?_, fun n hn => ?_, ?_⟩
    · unfold SystemState.lookupSlotCap SystemState.lookupCNode at hL ⊢; rw [hO]; exact hL
    · rw [SystemState.getUntyped?_eq_bind, hO, ← SystemState.getUntyped?_eq_bind]; exact hU n hn
    · unfold cspaceDstAdmitted SystemState.getCNode? at hD ⊢; rw [hO]; exact hD
  · rw [hR]
    have hF := finaliseReleased_frame T st hInv
    generalize finaliseFinalObject T (releaseFinalRegistration T st) = s1 at hF
    -- the finalisation writes no CNode
    have hCN : ∀ (k : SeLe4n.ObjId) cn, st.objects[k]? = some (KernelObject.cnode cn) →
        s1.objects[k]? = some (KernelObject.cnode cn) := by
      intro k cn hk
      rcases hF.write k with e | ⟨pre, post, hp, hq, ht, -, hw⟩
      · rw [e, hk]
      · rw [hk] at hp; cases hp
        exact absurd rfl hw.not_cnode
    have hL1 : s1.lookupSlotCap src = some cap := by
      unfold SystemState.lookupSlotCap SystemState.lookupCNode at hL ⊢
      cases hk : st.objects[src.cnode]? with
      | none => rw [hk] at hL; cases hL
      | some o =>
        rw [hk] at hL
        cases o with
        | cnode cn => rw [hCN _ _ hk]; exact hL
        | _ => cases hL
    have hU1 : ∀ n, cap.target = .object n → s1.getUntyped? n = none := by
      intro n hn; rw [hF.getUntyped?]; exact hU n hn
    have hD1 : cspaceDstAdmitted dst s1 = true := by
      unfold cspaceDstAdmitted SystemState.getCNode? at hD ⊢
      cases hk : st.objects[dst.cnode]? with
      | none => rw [hk] at hD; cases hD
      | some o =>
        rw [hk] at hD
        cases o with
        | cnode cn => rw [hCN _ _ hk]; exact hD
        | _ => cases hD
    have hInv1 := hF.invExt
    refine ⟨by rw [retireFinalObject_lookupSlotCap ec T R s1 hInv1 src]; exact hL1,
      fun n hn => retireFinalObject_getUntyped?_none ec T R s1 hInv1 (hU1 n hn), ?_⟩
    have hW := (retireFinalObject_frame ec T R s1 hInv1).2.2.2.2
    unfold cspaceDstAdmitted SystemState.getCNode? at hD1 ⊢
    rcases hW dst.cnode with e | ⟨hx, -, -⟩ | ⟨U, U', -, hU0, -, -⟩
    · rw [e]; exact hD1
    · rcases hX with h0 | hne
      · subst h0; unfold retireFinalObject; simp only [↓reduceIte]; exact hD1
      · exact absurd hx.symm hne
    · rw [hU0] at hD1; cases hD1

/-- **The node slot's notification capability, read**: the capability and the
notification it names. -/
theorem irqNodeHoldsNotificationCap_parts {st : SystemState} {line : Nat}
    (h : irqNodeHoldsNotificationCap st line = true) :
    ∃ c n ntf, st.slotCapAt ⟨irqNodeId line, irqNodeSlot⟩ = some c ∧ c.target = .object n ∧
      st.getNotification? n = some ntf := by
  unfold irqNodeHoldsNotificationCap at h
  cases hc : st.slotCapAt ⟨irqNodeId line, irqNodeSlot⟩ with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    dsimp only at h
    cases ht : c.target with
    | object n =>
      rw [ht] at h
      obtain ⟨ntf, hN⟩ := Option.isSome_iff_exists.mp h
      exact ⟨c, n, ntf, rfl, ht, hN⟩
    | _ => rw [ht] at h; cases h

/-- **The zombie delete of a slot holding a notification capability is one
finalising delete**: a notification holds no capability, so the loop runs no
pass (`zombieSlotClass` is `0`), and the capability names no page or table, so
the delete's teardown has nothing to take out. -/
theorem zombieDeleteAt_of_notificationCap (ec : Concurrency.CoreId) {st : SystemState}
    {line : Nat} (hC : cnodeInvoked (irqNodeId line) st = true)
    (h : irqNodeHoldsNotificationCap st line = true) :
    zombieDeleteAt ec (irqNodeAddr line).cnode (irqNodeAddr line).slot st =
      if cspaceDeleteAdmitted (irqNodeAddr line) st then cspaceDeletePerform (irqNodeAddr line) st
      else retireFinalisedObject ec (slotRetireTarget st (irqNodeId line) irqNodeSlot)
        (recorderFor st (slotRetireTarget st (irqNodeId line) irqNodeSlot) (irqNodeId line)
          irqNodeSlot)
        (cspaceDeletePerform (irqNodeAddr line) st) := by
  obtain ⟨c, n, ntf, hc, ht, hN⟩ := irqNodeHoldsNotificationCap_parts h
  have hON : st.objects[n]? = some (.notification ntf) :=
    (SystemState.getNotification?_eq_some_iff st n ntf).mp hN
  unfold zombieDeleteAt
  split
  · rfl
  · next hD =>
    have hCls : zombieSlotClass st (irqNodeId line) irqNodeSlot (irqNodeId line) irqNodeSlot = 0 := by
      have hn' : SeLe4n.ObjId.ofNat n.val = n := rfl
      unfold zombieSlotClass slotRetireTarget
      rw [hc]
      simp only [ht]
      split
      · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hn',
          SystemState.getObject?, hON]
        rfl
      · simp
    have hP : zombiePasses ec (irqNodeId line) irqNodeSlot (zombieFuel st) st = st := by
      show zombiePasses ec (irqNodeId line) irqNodeSlot (st.objects.size + 1) st = st
      unfold zombiePasses
      simp only [hCls, ↓reduceIte]
    rw [show (irqNodeAddr line).cnode = irqNodeId line from rfl,
      show (irqNodeAddr line).slot = irqNodeSlot from rfl, hP]
    unfold zombieDeleteSlot
    rw [if_pos (cspaceDeleteFinalisingAdmitted_of_cnodeInvoked
      (addr := ⟨irqNodeId line, irqNodeSlot⟩) hC)]
    unfold cspaceDeleteFinalisingPerformAt
    rw [if_neg (show ¬ cspaceDeleteAdmitted ⟨irqNodeId line, irqNodeSlot⟩ st = true from hD)]
    unfold cspaceDeleteTeardownAt
    dsimp only
    have hNoPT : st.getPageTable? n = none := by
      unfold SystemState.getPageTable?; rw [hON]
    have hNoF : st.getFrame? n = none := by
      unfold SystemState.getFrame?; rw [hON]
    have hT : slotPageTables st ⟨irqNodeId line, irqNodeSlot⟩ = [] := by
      simp [slotPageTables, hc, capabilityPageTable, ht, hNoPT]
    have hM : slotMappedPages st ⟨irqNodeId line, irqNodeSlot⟩ = [] := by
      cases hm : c.mapping <;> simp [slotMappedPages, hc, capabilityMappedPage, ht, hNoF, hm]
    rw [hT, hM, finaliseDestroyedCapabilitiesState_nil]
    rfl

/-- **The bind's copy over the node slot's notification capability is the
copy**: after the node slot's delete — the plain one, or the final delete that
retires the notification it named — the copy's checks hold, the retired
notification being no CNode.  So on a well-formed object table the
delete-and-copy of `irqHandlerSetNotification` is its writes. -/
theorem irqHandlerSetNotification_overFinal_copy (ec : Concurrency.CoreId) {line : Nat}
    {src : CSpaceAddr} {cap : Capability} {st : SystemState} (hInv : st.objects.invExt)
    (hL : st.lookupSlotCap src = some cap) (hA : irqNotificationCapAdmitted st cap = true)
    (hC : cnodeInvoked (irqNodeId line) st = true)
    (hO : irqHandlerSetNotificationOverFinal st line src.cnode cap = true) :
    cspaceCopy src (irqNodeAddr line) .full
        (zombieDeleteAt ec (irqNodeAddr line).cnode (irqNodeAddr line).slot st) =
      .ok ((), irqHandlerSetNotificationOverFinalPerform ec line src st) := by
  unfold irqHandlerSetNotificationOverFinal at hO
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hO
  obtain ⟨⟨⟨hNN, hS⟩, hN⟩, hSA⟩ := hO
  obtain ⟨hL0, hU0, hD0, hI0⟩ := irqHandlerSetNotification_deleteCopyAdmitted hInv hL hA hNN hS hSA
  unfold irqHandlerSetNotificationOverFinalPerform
  apply cspaceCopy_of_admitted
  rw [zombieDeleteAt_of_notificationCap ec hC hN]
  split
  · exact cspaceCopyAdmitted_of_parts hL0 hNN hU0 hD0
  · obtain ⟨c, n, ntf, hc, ht, hNt⟩ := irqNodeHoldsNotificationCap_parts hN
    have hX : slotRetireTarget st (irqNodeId line) irqNodeSlot = 0 ∨
        SeLe4n.ObjId.ofNat (slotRetireTarget st (irqNodeId line) irqNodeSlot - 1) ≠
          (irqNodeAddr line).cnode := by
      unfold slotRetireTarget
      rw [hc]
      simp only [ht]
      split
      · right
        rw [Nat.add_sub_cancel, show SeLe4n.ObjId.ofNat n.val = n from rfl,
          show (irqNodeAddr line).cnode = irqNodeId line from rfl]
        rintro rfl
        have hON := (SystemState.getNotification?_eq_some_iff st _ ntf).mp hNt
        unfold cnodeInvoked SystemState.getCNode? at hC
        rw [hON] at hC; cases hC
      · left; rfl
    obtain ⟨hL1, hU1, hD1⟩ := retireFinalisedObject_copyParts ec _ _ hI0 hX hL0 hU0 hD0
    exact cspaceCopyAdmitted_of_parts hL1 hNN hU1 hD1

/-- **What a successful `seL4_IRQHandler_SetNotification` is**, on any state:
the source admitted, the node slot's delete, then the copy into it, or, on the
in-place branch, the plain delete and the copy's writes. -/
theorem irqHandlerSetNotification_ok_cases {ec : Concurrency.CoreId} {line : Nat}
    {src : CSpaceAddr} {st st' : SystemState}
    (h : irqHandlerSetNotification ec line src st = .ok ((), st')) :
    ∃ cap st1, st.lookupSlotCap src = some cap ∧ irqNotificationCapAdmitted st cap = true ∧
      cnodeInvoked (irqNodeId line) st = true ∧
      cspaceDeleteSlotZombie ec (irqNodeAddr line) st = .ok ((), st1) ∧
      (cspaceCopy src (irqNodeAddr line) .full st1 = .ok ((), st') ∨
        st' = cspaceCopyPerform src (irqNodeAddr line) .full st1) := by
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
          exact ⟨cap, _, rfl, hA, hC, irqHandlerSetNotification_inPlace_delete hC hP, .inr rfl⟩
        · simp only [hP, Bool.false_eq_true, ↓reduceIte] at h
          by_cases hO : irqHandlerSetNotificationOverFinal st line src.cnode cap = true
          · simp only [hO, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq, true_and] at h
            subst h
            exact ⟨cap, _, rfl, hA, hC, cspaceDeleteSlotZombie_of_admitted
              (cspaceDeleteFinalisingAdmitted_of_cnodeInvoked hC), .inr rfl⟩
          simp only [hO, Bool.false_eq_true, ↓reduceIte] at h
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
      cspaceCopy src (irqNodeAddr line) .full st1 = .ok ((), st') := by
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
            irqHandlerSetNotification_inPlace_copy hObjInv hL hA hP⟩
        · simp only [hP, Bool.false_eq_true, ↓reduceIte] at h
          by_cases hO : irqHandlerSetNotificationOverFinal st line src.cnode cap = true
          · simp only [hO, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq, true_and] at h
            subst h
            exact ⟨cap, _, rfl, hA, hC, cspaceDeleteSlotZombie_of_admitted
              (cspaceDeleteFinalisingAdmitted_of_cnodeInvoked hC),
              irqHandlerSetNotification_overFinal_copy ec hObjInv hL hA hC hO⟩
          simp only [hO, Bool.false_eq_true, ↓reduceIte] at h
          cases hD : cspaceDeleteSlotZombie ec (irqNodeAddr line) st with
          | error e => rw [hD] at h; cases h
          | ok r =>
            obtain ⟨⟨⟩, st1⟩ := r
            rw [hD] at h
            exact ⟨cap, st1, rfl, hA, hC, rfl, h⟩
      · simp only [Bool.not_eq_true] at hC
        simp [hA, hC] at h
    · simp only [Bool.not_eq_true] at hA
      simp [hA] at h

/-- **`seL4_IRQHandler_Clear`**: the line's node slot emptied by the finalising
delete (`cspaceDeleteSlotZombie`, seL4's `cteDeleteOne`), so the line signals
nothing until a notification is set again. -/
def irqHandlerClear (executingCore : Concurrency.CoreId) (line : Nat) : Kernel Unit :=
  fun st =>
    if !cnodeInvoked (irqNodeId line) st then .error .objectNotFound
    else cspaceDeleteSlotZombie executingCore (irqNodeAddr line) st

end SeLe4n.Kernel
