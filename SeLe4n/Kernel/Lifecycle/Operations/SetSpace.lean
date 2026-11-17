-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.Core
import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.Capability.FinalRetire

/-!
# Setting a thread's spaces — seL4's `TCB_SetSpace`

A thread holds its CSpace and VSpace roots and its fault handler as
capabilities in three slots of its own (`TCB.spaceCells`, seL4-MCS's
`tcbCTable`, `tcbVTable` and `tcbFaultHandler`), and those slots are derivation
nodes like a CNode's.  The fault endpoint, the CSpace root and the VSpace root
are the invocation's extra capabilities 0, 1 and 2, as seL4-MCS's
`decodeSetSpace` reads them; a null fault capability empties the fault slot.  `copyThreadSpaces` sets them as seL4's
`invokeTCB_ThreadControl` does, slot by slot (`threadSlotCopied`):

1. the slot's old content is **deleted** through the same delete a CNode slot
   takes (`cspaceDeleteSlot`): the capability goes and the slot's node is spliced
   out of the derivation tree, its children re-derived from its parent
   (seL4's `cteDelete`);
2. the capability in the **source slot** is then read again and a copy of it
   (`TCB.spaceCopyOf`: its target, its rights masked by the slot's) is
   **inserted** with the derivation edge from the source slot (`.copy`, seL4's
   `checkCapAt` and `cteInsert`).

So a revoke of the source capability, or of any ancestor of it, reaches the
thread's slot and empties it, and a thread's root keeps a capability derived from
the one it was given.

Every refusal comes before any write.  The target must be a **suspended** TCB:
its stored flag is `.Inactive` *and* the state classifies it so
(`inferThreadState`: placed on no core, blocked on nothing).  seL4 accepts
`TCB_SetSpace` on a running thread; this kernel asks the caller to suspend first,
which keeps every invariant stated over a thread's roots from reasoning about a
thread mid-flight.  Each root source slot must hold a capability naming an
object of its kind, a **CNode** for the CSpace root and a **VSpace root** for the
VSpace root (seL4's `IllegalOperation` otherwise), and the fault source must be
empty or hold an endpoint capability with the fault-handler rights
(`faultHandlerSourceAdmitted`, seL4's `validFaultHandler`, `InvalidCapability 1`
otherwise), decided here against the store, not trusted of the resolver.  seL4
installs the fault handler first; this kernel sets it last, after the two roots,
which no check reads, so the order is visible to nothing but the derivation
links' order of insertion.

Two cases seL4 names are decided by the model:

* **The source is the thread's own slot.**  It cannot be: the source slots are
  resolved through the caller's CSpace (`resolveSetSpace`), and a CSpace
  resolves to CNode slots alone, while the destination is a slot of a TCB.
  The delete writes no CNode slot, so the source still holds its capability
  when it is read again (seL4's `checkCapAt` asks this, since its `cteDelete`
  may finalise the source's object).
* **The slot held the last capability to its object.**  seL4's `cteDelete`
  finalises it, and so does this one (WS-ZA ZA5.4 part 22): the object the old capability
  takes with it and its recorder are read before the delete
  (`slotRetireTarget`, `recorderFor`), and the object is retired
  (`retireFinalObject`) once the slot is set (`threadSlotSet`) — a VSpace
  root with its ASID's acknowledged round, a CNode while it is quiescent and
  unreferenced.  The retire runs after the insert and not between the delete
  and it: the inserted copy names the source's object, which is not the
  retired one (the old capability was its object's last), and the retire
  writes no slot and no thread, so the order changes nothing the insert reads
  or writes.  A thread slot holds only a CNode, a VSpace root or an endpoint
  capability, so the delete has no page or page table to tear down.
* **The slot was empty.**  An empty slot is outside the derivation tree
  (`cdtCompleteness`), so its delete changes no edge, and the insert adds the
  slot as a fresh node, as seL4's `cteInsert` into a null slot does.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **A thread's space slot set from a source slot** — seL4's `cteDelete` of the
slot then `checkCapAt` and `cteInsert`, on the words of the two slots.  The
slot's old content is deleted as the delete deletes a slot (`cspaceDeleteSlot`:
the core delete's clear, `threadSlotCleared`, then the splice out of the
derivation tree, `copyIntoThreadSlot_delete`), and the capability the source slot
then holds is copied in (`TCB.spaceCopyOf`, masked by `rights`) with the
derivation edge from the source.  A source that no longer holds a capability
inserts nothing, as `checkCapAt` does.  Out of line, on words, so a caller builds
no slot record; compiled as `threadSlotCopiedImpl`. -/
@[noinline] def threadSlotCopied (st : SystemState) (tid : SeLe4n.ThreadId) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) (data : UInt64) : SystemState :=
  let stD := spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
    { cnode := tid.toObjId, slot := slot }
  match SystemState.lookupSlotCap stD { cnode := srcCNode, slot := srcSlot } with
  | none => stD
  | some cap =>
    (stD.updateTcb tid (·.insertSpaceCap slot (TCB.spaceCopyOf cap rights data))).cdtAddChild
      { cnode := srcCNode, slot := srcSlot } { cnode := tid.toObjId, slot := slot } .copy

/-- **The delete `threadSlotCopied` begins with is the slot delete**: on a stored
thread, `cspaceDeleteSlot` of its slot is the core delete's clear and the splice. -/
theorem copyIntoThreadSlot_delete {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot) :
    cspaceDeleteSlot { cnode := tid.toObjId, slot := slot } st =
      .ok ((), spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
        { cnode := tid.toObjId, slot := slot }) := by
  have hO : st.objects[tid.toObjId]? = some (.tcb t) := (SystemState.getTcb?_eq_some_iff st tid t).mp hT
  unfold cspaceDeleteSlot
  rw [cspaceDeleteSlotCore_eq_slotCleared hO rfl]
  simp only [slotCleared, SystemState.getCNode?, hO]

/-- The core delete's clear of a thread slot is the store of the thread with the
slot emptied. -/
theorem threadSlotCleared_store {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot) :
    storeObject tid.toObjId (.tcb (t.removeSpaceCap slot)) st =
      .ok ((), threadSlotCleared tid.toObjId slot st) := by
  unfold threadSlotCleared
  exact SystemState.storeObject_tcb_eq_storeTcbWith (f := (·.removeSpaceCap slot))
    ((SystemState.getTcb?_eq_some_iff st tid t).mp hT)

/-- **After its slot's delete the thread is stored**, with the slot empty (up to
the links the splice rewrites), and the object table is well formed. -/
theorem threadSlotDeleted_tcb {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hObjInv : st.objects.invExt) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot) :
    (∃ t', (spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
        { cnode := tid.toObjId, slot := slot }).getTcb? tid = some t' ∧
      t'.withoutLinks = (t.removeSpaceCap slot).withoutLinks) ∧
    (spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
        { cnode := tid.toObjId, slot := slot }).objects.invExt := by
  have hS := threadSlotCleared_store hT slot
  have hC := storeObject_objects_eq _ _ _ _ hObjInv hS
  have hInvC := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hS
  obtain ⟨hA, hI⟩ := spliceDeletedCdtNode_agree hInvC { cnode := tid.toObjId, slot := slot }
  obtain ⟨t', h1, h2⟩ := hA.tcb_fwd hC
  exact ⟨⟨t', (SystemState.getTcb?_eq_some_iff _ tid t').mpr h1, h2⟩, hI⟩

/-- **What a slot copy is**, by whether the source still holds a capability. -/
theorem threadSlotCopied_cases (st : SystemState) (tid : SeLe4n.ThreadId) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) (data : UInt64) :
    (SystemState.lookupSlotCap (spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
        { cnode := tid.toObjId, slot := slot }) { cnode := srcCNode, slot := srcSlot } = none ∧
      threadSlotCopied st tid slot srcCNode srcSlot rights data =
        spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
          { cnode := tid.toObjId, slot := slot }) ∨
    ∃ cap, SystemState.lookupSlotCap (spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
        { cnode := tid.toObjId, slot := slot }) { cnode := srcCNode, slot := srcSlot } = some cap ∧
      threadSlotCopied st tid slot srcCNode srcSlot rights data =
        ((spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
          { cnode := tid.toObjId, slot := slot }).updateTcb tid
            (·.insertSpaceCap slot (TCB.spaceCopyOf cap rights data))).cdtAddChild
          { cnode := srcCNode, slot := srcSlot } { cnode := tid.toObjId, slot := slot } .copy := by
  unfold threadSlotCopied
  dsimp only
  split
  · next h => exact .inl ⟨h, rfl⟩
  · next cap h => exact .inr ⟨cap, h, rfl⟩

/-- **A slot copy keeps the thread stored** and the object table well formed. -/
theorem threadSlotCopied_tcb {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hObjInv : st.objects.invExt) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) (data : UInt64) :
    ((threadSlotCopied st tid slot srcCNode srcSlot rights data).getTcb? tid).isSome ∧
      (threadSlotCopied st tid slot srcCNode srcSlot rights data).objects.invExt := by
  obtain ⟨⟨t', hT', -⟩, hI⟩ := threadSlotDeleted_tcb hObjInv hT slot
  rcases threadSlotCopied_cases st tid slot srcCNode srcSlot rights data with ⟨-, e⟩ | ⟨cap, -, e⟩
  · rw [e, hT']; exact ⟨rfl, hI⟩
  · rw [e]
    have hU := SystemState.updateTcb_preserves_objects_invExt _ tid
      (·.insertSpaceCap slot (TCB.spaceCopyOf cap rights data)) hI
    have hR := SystemState.cdtAddChild_reach
      ((spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
        { cnode := tid.toObjId, slot := slot }).updateTcb tid
          (·.insertSpaceCap slot (TCB.spaceCopyOf cap rights data)))
      { cnode := srcCNode, slot := srcSlot } { cnode := tid.toObjId, slot := slot } .copy
    refine ⟨?_, hR.invExt hU⟩
    rw [(hR.agree hU).getTcb?_isSome tid]
    show ((SystemState.updateTcb _ tid _).getTcb? tid).isSome = true
    rw [SystemState.updateTcb_getTcb?_self _ _ _ hI, hT']
    rfl

/-- The spare record `a` keeps for slot `i`, if any.  Out of line, so reading
it is no branch of its caller (`TCB.spaceCellFilledWith`). -/
@[noinline] def spareRecordAt (a : Array (Option Capability)) (i : Nat) : Option Capability :=
  a[i]?.join

/-- The `some` cell of the capability of `target` and `rights` alone, written
over the record `o` when there is one, built when there is none.  An object
target is written over the record's own target cell too
(`Capability.overwriteObject`), so the thread's capability shares no cell with
its source's: the source slot's record, once that slot is cleared, is still its
own to be written over in place.  Out of line, so its matches are no branch of
its caller. -/
@[noinline] def capabilityCellOver (o : Option Capability) (target : CapTarget)
    (rights : AccessRightSet) (badgeWord : SeLe4n.Badge) (badged : Bool) (guard : UInt64)
    (guardSize : UInt8) : Option Capability :=
  match target, o with
  | .object id, some r => some (r.overwriteObject id rights badgeWord badged guard guardSize)
  | .object id, none => some (Capability.ofObject id rights badgeWord badged guard guardSize)
  | _, some r => some (r.overwrite target rights badgeWord badged default default 0 false 0
      guard guardSize)
  | _, none => some (Capability.ofFields target rights badgeWord badged default default 0 false 0
      guard guardSize)

theorem capabilityCellOver_eq (o : Option Capability) (target : CapTarget)
    (rights : AccessRightSet) (badgeWord : SeLe4n.Badge) (badged : Bool) (guard : UInt64)
    (guardSize : UInt8) :
    capabilityCellOver o target rights badgeWord badged guard guardSize =
      some ⟨target, rights, badgeWord, badged, default, default, 0, false, 0, guard, guardSize⟩ := by
  unfold capabilityCellOver
  split
  · rw [Capability.overwriteObject_eq]
  · rfl
  · rw [Capability.overwrite_eq]
  · rw [Capability.ofFields_eq]

/-- **Slot `s` of `t` written with the capability of `target` and `rights`
alone, over the spare record `a` keeps for it** (`TCB.spaceSpare`): the record
is read (`spareRecordAt`) and then taken out of the spares, so nothing else
holds it when the capability is written over it (`capabilityCellOver`).  The
thread is rebuilt once, after those calls, so an unshared thread is rebuilt in
its own cell.  Equal to the insert (`TCB.spaceCellFilledWith_eq`). -/
@[inline] def _root_.SeLe4n.Model.TCB.spaceCellFilledWith (t : TCB) (s : SeLe4n.Slot)
    (target : CapTarget) (rights : AccessRightSet) (badgeWord : SeLe4n.Badge) (badged : Bool)
    (guard : UInt64) (guardSize : UInt8) (a : Array (Option Capability)) : TCB :=
  let i := s.toNat
  let o := spareRecordAt a i
  let a' := a.setIfInBounds i none
  let c := capabilityCellOver o target rights badgeWord badged guard guardSize
  { t with spaceCells := t.spaceCells.setIfInBounds i c, spaceSpare := Squash.mk a' }

theorem _root_.SeLe4n.Model.TCB.spaceCellFilledWith_eq (t : TCB) (s : SeLe4n.Slot)
    (target : CapTarget) (rights : AccessRightSet) (badgeWord : SeLe4n.Badge) (badged : Bool)
    (guard : UInt64) (guardSize : UInt8) (a : Array (Option Capability)) :
    t.spaceCellFilledWith s target rights badgeWord badged guard guardSize a =
      t.insertSpaceCap s
        ⟨target, rights, badgeWord, badged, default, default, 0, false, 0, guard, guardSize⟩ := by
  unfold TCB.spaceCellFilledWith TCB.insertSpaceCap
  dsimp only
  rw [capabilityCellOver_eq]
  congr 1
  exact Subsingleton.elim _ _

/-- **Slot `s` of `t` written with the capability of `target` and `rights`
alone**, over the slot's spare record (`TCB.spaceCellFilledWith`); the insert
(`TCB.spaceCellFilled_eq`). -/
@[inline] def _root_.SeLe4n.Model.TCB.spaceCellFilled (t : TCB) (s : SeLe4n.Slot)
    (target : CapTarget) (rights : AccessRightSet) (badgeWord : SeLe4n.Badge) (badged : Bool)
    (guard : UInt64) (guardSize : UInt8) : TCB :=
  Quot.lift (fun a => t.spaceCellFilledWith s target rights badgeWord badged guard guardSize a)
    (fun a b _ => (TCB.spaceCellFilledWith_eq t s target rights badgeWord badged guard guardSize a).trans
      (TCB.spaceCellFilledWith_eq t s target rights badgeWord badged guard guardSize b).symm)
    t.spaceSpare

theorem _root_.SeLe4n.Model.TCB.spaceCellFilled_eq (t : TCB) (s : SeLe4n.Slot)
    (target : CapTarget) (rights : AccessRightSet) (badgeWord : SeLe4n.Badge) (badged : Bool)
    (guard : UInt64) (guardSize : UInt8) :
    t.spaceCellFilled s target rights badgeWord badged guard guardSize =
      t.insertSpaceCap s
        ⟨target, rights, badgeWord, badged, default, default, 0, false, 0, guard, guardSize⟩ := by
  unfold TCB.spaceCellFilled
  induction t.spaceSpare using Quot.ind with
  | mk a => exact TCB.spaceCellFilledWith_eq t s target rights badgeWord badged guard guardSize a

/-- The thread's space slot `slot` written with the capability of `target` and
`rights` alone, over the slot's spare record (`TCB.spaceCellFilled`).  Out of
line, on words, so the update is compiled into it. -/
@[noinline] def threadSpaceCellWritten (st : SystemState) (tid : SeLe4n.ThreadId)
    (slot : SeLe4n.Slot) (target : CapTarget) (rights : AccessRightSet)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (guard : UInt64) (guardSize : UInt8) : SystemState :=
  st.updateTcb tid fun t => t.spaceCellFilled slot target rights badgeWord badged guard guardSize

/-- The insert and edge of `threadSlotCopied`, on the deleted state `stD`. -/
@[noinline] def threadSlotRefilled (stD : SystemState)
    (tid : SeLe4n.ThreadId) (slot : SeLe4n.Slot) (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (rights : AccessRightSet) (data : UInt64) : SystemState :=
  match SystemState.lookupSlotCap stD { cnode := srcCNode, slot := srcSlot } with
  | none => stD
  | some cap =>
    (threadSpaceCellWritten stD tid slot cap.target (cap.rights.inter rights) cap.badgeWord
      cap.badged (TCB.spaceCopyGuard cap data) (TCB.spaceCopyGuardSize cap data)).cdtAddChild
      { cnode := srcCNode, slot := srcSlot } { cnode := tid.toObjId, slot := slot } .copy

/-- `threadSlotCopied` as compiled: the delete keeps the slot's cell as its
spare record (`TCB.removeSpaceCapImpl`), and the copy is written over that
record (`TCB.spaceCellFilled`), or over the one the carve made for a slot
never filled: setting a thread's space builds no capability. -/
@[noinline] def threadSlotCopiedImpl (st : SystemState) (tid : SeLe4n.ThreadId)
    (slot : SeLe4n.Slot) (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (rights : AccessRightSet) (data : UInt64) : SystemState :=
  threadSlotRefilled
    (spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st) { cnode := tid.toObjId, slot := slot })
    tid slot srcCNode srcSlot rights data

@[csimp] theorem threadSlotCopied_eq_impl : @threadSlotCopied = @threadSlotCopiedImpl := by
  funext st tid slot srcCNode srcSlot rights data
  unfold threadSlotCopied threadSlotCopiedImpl threadSlotRefilled threadSpaceCellWritten
  simp only [TCB.spaceCellFilled_eq]
  split <;> rfl

/-- **A thread's space slot set, finalising what it held**: the slot set from
its source (`threadSlotCopied`), then the object its old capability was the
last capability to retired (`retireFinalObject`), its target and recorder read
before the delete, as the finalising delete reads them
(`cspaceDeleteSlotFinalising`).  Nothing is retired when the old capability was
not final or named nothing retirable. -/
@[inline] def threadSlotSet (executingCore : Concurrency.CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) (slot : SeLe4n.Slot) (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (rights : AccessRightSet) (data : UInt64) : SystemState :=
  let target := slotRetireTarget st tid.toObjId slot
  retireFinalObject executingCore target (recorderFor st target tid.toObjId slot)
    (threadSlotCopied st tid slot srcCNode srcSlot rights data)

/-- The fault endpoint a `.tcbSetSpace` names as extra capability 0, numbered
`1` as seL4-MCS's `decodeSetSpace` numbers it (`invalidCapNumber = 1` when the
capability is no valid fault handler). -/
def setSpaceFaultHandlerCapNumber : UInt64 := 1

/-- **The CSpace root data word a `.tcbSetSpace` names at MR0 is refused for the
CNode `id`** — seL4's `decodeSetSpace`: a nonzero word goes through
`updateCapData`, whose CNode case answers a null capability when the guard size
it gives and the CNode's radix exceed the word (`capDataRefused`), and the null
capability is then refused as no CNode (`seL4_IllegalOperation`).  A zero word
is not passed through `updateCapData` and is never refused. -/
@[inline] def cspaceRootDataRefused (st : SystemState) (id : SeLe4n.ObjId) (data : UInt64) :
    Bool :=
  match st.getCNode? id with
  | some cn => data != 0 && decide (64 < (capDataGuardSize data).toNat + cn.radixWidth)
  | none => false

/-- The CSpace-root source check: the slot holds a capability naming a CNode,
and the root data word `data` is not refused for it (`cspaceRootDataRefused`). -/
@[inline] def cspaceRootSourceAdmitted (st : SystemState) (src : CSpaceAddr) (data : UInt64) :
    Bool :=
  match SystemState.lookupSlotCap st src with
  | some cap =>
    match cap.target with
    | .object id => (st.getCNode? id).isSome && !cspaceRootDataRefused st id data
    | _ => false
  | none => false

/-- The VSpace-root source check: the slot holds a capability naming a VSpace
root. -/
@[inline] def vspaceRootSourceAdmitted (st : SystemState) (src : CSpaceAddr) : Bool :=
  match SystemState.lookupSlotCap st src with
  | some cap =>
    match cap.target with
    | .object id => (st.getVSpaceRoot? id).isSome
    | _ => false
  | none => false

/-- **The fault-handler source check** — seL4-MCS's `validFaultHandler`: the
slot is empty (seL4's null capability, which leaves the thread with no fault
handler) or holds a capability to an endpoint with send and a grant right
(`faultHandlerCapAuthorized`).  Any other capability is refused
`invalidCapability 1` (`setSpaceFaultHandlerCapNumber`). -/
@[inline] def faultHandlerSourceAdmitted (st : SystemState) (src : CSpaceAddr) : Bool :=
  match SystemState.lookupSlotCap st src with
  | none => true
  | some cap =>
    faultHandlerCapAuthorized cap &&
      match cap.target with
      | .object id => (st.getEndpoint? id).isSome
      | _ => false

/-- **The writes of a space change**, on the source slots' words: the CSpace
root slot set from its source under the root data word `cnData`, then the VSpace
root slot from its, then the fault-handler slot from the fault endpoint's
(an empty source empties it), each finalising what it held (`threadSlotSet`).
seL4-MCS's `invokeTCB_ThreadControlCaps` installs the fault handler before the
roots; the slots are disjoint and each set reads only its own source, which
the sets before it keep (`threadSlotCopied_lookupSlotCap`,
`retireFinalObject_lookupSlotCap`), so the order writes the same slots. -/
@[inline] def copyThreadSpacesPerform (executingCore : Concurrency.CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) (cnCNode : SeLe4n.ObjId) (cnSlot : SeLe4n.Slot) (vrCNode : SeLe4n.ObjId)
    (vrSlot : SeLe4n.Slot) (cnData : UInt64) (fhCNode : SeLe4n.ObjId) (fhSlot : SeLe4n.Slot) :
    SystemState :=
  threadSlotSet executingCore
    (threadSlotSet executingCore
      (threadSlotSet executingCore st tid TCB.cspaceRootSlot cnCNode cnSlot TCB.cspaceRootRights
        cnData)
      tid TCB.vspaceRootSlot vrCNode vrSlot TCB.vspaceRootRights 0)
    tid TCB.faultHandlerSlot fhCNode fhSlot TCB.faultHandlerRights 0

/-- **Set a suspended thread's CSpace root, VSpace root and fault-handler slots
from three source slots** — seL4-MCS's `TCB_SetSpace`.  Refused, committing
nothing, when the thread is not a stored TCB (`.objectNotFound`), is not
suspended (`.illegalState`), a root source does not hold a capability naming an
object of its kind or the CSpace root data word `cnData` is refused for its
CNode (`.illegalState`, seL4's `seL4_IllegalOperation`), or the fault-handler
source is no valid handler (`faultHandlerSourceAdmitted`, `invalidCapability
1`).  Then each slot is set from its source (`copyThreadSpacesPerform`), the
CSpace root's guard from `cnData` when that is nonzero (`TCB.spaceCopyOf`). -/
def copyThreadSpaces (executingCore : Concurrency.CoreId) (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (cnSrc vrSrc : CSpaceAddr) (cnData : UInt64)
    (fhSrc : CSpaceAddr) : Except KernelError SystemState :=
  match st.getTcb? vtid.val with
  | none => .error .objectNotFound
  | some tcb =>
    if tcb.threadState != .Inactive || inferThreadState st vtid.val tcb != .Inactive then
      .error .illegalState
    else if !cspaceRootSourceAdmitted st cnSrc cnData then .error .illegalState
    else if !vspaceRootSourceAdmitted st vrSrc then .error .illegalState
    else if !faultHandlerSourceAdmitted st fhSrc then
      .error (.invalidCapability setSpaceFaultHandlerCapNumber)
    else .ok (copyThreadSpacesPerform executingCore st vtid.val cnSrc.cnode cnSrc.slot vrSrc.cnode
      vrSrc.slot cnData fhSrc.cnode fhSrc.slot)

/-- **`copyThreadSpaces`'s checks**, read before anything is written: the thread
is a suspended TCB, each root source names an object of its kind and the fault
source is a valid handler.  When they pass the operation is its writes
(`copyThreadSpaces_of_admitted`). -/
@[inline] def copyThreadSpacesAdmitted (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (cnSrc vrSrc : CSpaceAddr) (cnData : UInt64) (fhSrc : CSpaceAddr) : Bool :=
  match st.getTcb? vtid.val with
  | none => false
  | some tcb =>
    !(tcb.threadState != .Inactive || inferThreadState st vtid.val tcb != .Inactive) &&
      cspaceRootSourceAdmitted st cnSrc cnData && vspaceRootSourceAdmitted st vrSrc &&
      faultHandlerSourceAdmitted st fhSrc

theorem copyThreadSpaces_of_admitted {ec : Concurrency.CoreId} {st : SystemState}
    {vtid : SeLe4n.ValidThreadId}
    {cnSrc vrSrc : CSpaceAddr} {cnData : UInt64} {fhSrc : CSpaceAddr}
    (h : copyThreadSpacesAdmitted st vtid cnSrc vrSrc cnData fhSrc = true) :
    copyThreadSpaces ec st vtid cnSrc vrSrc cnData fhSrc =
      .ok (copyThreadSpacesPerform ec st vtid.val cnSrc.cnode cnSrc.slot vrSrc.cnode vrSrc.slot
        cnData fhSrc.cnode fhSrc.slot) := by
  unfold copyThreadSpacesAdmitted at h
  unfold copyThreadSpaces
  cases hT : st.getTcb? vtid.val with
  | none => rw [hT] at h; cases h
  | some tcb =>
    rw [hT] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hS, hC⟩, hV⟩, hF⟩ := h
    simp only [hS, hC, hV, hF, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- **What a successful space change consists of**: the thread was a suspended
TCB, each root source held a capability naming an object of its kind, the fault
source was a valid handler, and the state is the three slot copies. -/
theorem copyThreadSpaces_ok {ec : Concurrency.CoreId} {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId}
    {cnSrc vrSrc : CSpaceAddr} {cnData : UInt64} {fhSrc : CSpaceAddr}
    (h : copyThreadSpaces ec st vtid cnSrc vrSrc cnData fhSrc = .ok st') :
    ∃ tcb, st.getTcb? vtid.val = some tcb ∧ tcb.threadState = .Inactive ∧
      inferThreadState st vtid.val tcb = .Inactive ∧
      cspaceRootSourceAdmitted st cnSrc cnData = true ∧ vspaceRootSourceAdmitted st vrSrc = true ∧
      faultHandlerSourceAdmitted st fhSrc = true ∧
      st' = copyThreadSpacesPerform ec st vtid.val cnSrc.cnode cnSrc.slot vrSrc.cnode vrSrc.slot
        cnData fhSrc.cnode fhSrc.slot := by
  unfold copyThreadSpaces at h
  cases hT : st.getTcb? vtid.val with
  | none => rw [hT] at h; cases h
  | some tcb =>
    rw [hT] at h
    simp only at h
    by_cases hS : tcb.threadState = .Inactive ∧ inferThreadState st vtid.val tcb = .Inactive
    · have hB : (tcb.threadState != .Inactive || inferThreadState st vtid.val tcb != .Inactive)
          = false := by simp [hS.1, hS.2]
      rw [hB] at h
      cases hC : cspaceRootSourceAdmitted st cnSrc cnData with
      | false => simp [hC] at h
      | true =>
        cases hV : vspaceRootSourceAdmitted st vrSrc with
        | false => simp [hC, hV] at h
        | true =>
          cases hF : faultHandlerSourceAdmitted st fhSrc with
          | false => simp [hC, hV, hF] at h
          | true =>
            simp only [hC, hV, hF, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              Except.ok.injEq] at h
            exact ⟨tcb, rfl, hS.1, hS.2, rfl, rfl, rfl, h.symm⟩
    · have : (tcb.threadState != .Inactive || inferThreadState st vtid.val tcb != .Inactive)
          = true := by
        by_cases h1 : tcb.threadState = .Inactive
        · have h2 : inferThreadState st vtid.val tcb ≠ .Inactive := fun h2 => hS ⟨h1, h2⟩
          simp [h2]
        · simp [h1]
      rw [this] at h; cases h

/-- A refused space change is refused for a stated reason: the thread must be
suspended.  A thread the state places on a core, or blocks, is refused
whatever its stored flag says — a running, ready or blocked thread's spaces are
in use. -/
theorem copyThreadSpaces_refuses_active (ec : Concurrency.CoreId) (st : SystemState)
    (vtid : SeLe4n.ValidThreadId)
    (cnSrc vrSrc : CSpaceAddr) (cnData : UInt64) (fhSrc : CSpaceAddr) (tcb : TCB)
    (hT : st.getTcb? vtid.val = some tcb)
    (hS : inferThreadState st vtid.val tcb ≠ .Inactive) :
    copyThreadSpaces ec st vtid cnSrc vrSrc cnData fhSrc = .error .illegalState := by
  have : (tcb.threadState != .Inactive || inferThreadState st vtid.val tcb != .Inactive)
      = true := by simp [hS]
  simp [copyThreadSpaces, hT, this]

/-- **A thread slot's delete keeps every slot lookup**: it writes the thread,
which holds no CNode slot, and links, which a lookup does not read. -/
theorem threadSlotDeleted_lookupSlotCap {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hObjInv : st.objects.invExt) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (r : SlotRef) :
    SystemState.lookupSlotCap (spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
      { cnode := tid.toObjId, slot := slot }) r = SystemState.lookupSlotCap st r := by
  have hPre : st.objects[tid.toObjId]? = some (.tcb t) :=
    (SystemState.getTcb?_eq_some_iff st tid t).mp hT
  have hS := threadSlotCleared_store hT slot
  have hC := storeObject_objects_eq _ _ _ _ hObjInv hS
  have hInvC := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hS
  obtain ⟨hA, -⟩ := spliceDeletedCdtNode_agree hInvC { cnode := tid.toObjId, slot := slot }
  rw [hA.lookupSlotCap r]
  unfold SystemState.lookupSlotCap SystemState.lookupCNode
  by_cases h : r.cnode = tid.toObjId
  · rw [h, hC, hPre]
  · rw [storeObject_objects_ne _ _ _ _ _ h hObjInv hS]

/-- **What a slot copy leaves**: every object but the thread's is the
pre-state's up to derivation links, and the thread is the pre-state's with the
slot emptied and, when the source held a capability, its copy put in, up to
links.  A slot lookup reads no link and no thread, so the source is read as in
the pre-state. -/
theorem threadSlotCopied_frame {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hObjInv : st.objects.invExt) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) (data : UInt64) :
    (∀ k, k ≠ tid.toObjId → SystemState.objectAgreesOffDerivationLinksAt
        (threadSlotCopied st tid slot srcCNode srcSlot rights data) st k) ∧
    ∃ t', (threadSlotCopied st tid slot srcCNode srcSlot rights data).getTcb? tid = some t' ∧
      t'.withoutLinks =
        (match SystemState.lookupSlotCap st { cnode := srcCNode, slot := srcSlot } with
          | none => t.removeSpaceCap slot
          | some cap => (t.removeSpaceCap slot).insertSpaceCap slot (TCB.spaceCopyOf cap rights data)
          ).withoutLinks := by
  have hPre : st.objects[tid.toObjId]? = some (.tcb t) :=
    (SystemState.getTcb?_eq_some_iff st tid t).mp hT
  have hS := threadSlotCleared_store hT slot
  have hC := storeObject_objects_eq _ _ _ _ hObjInv hS
  have hCne : ∀ k, k ≠ tid.toObjId →
      (threadSlotCleared tid.toObjId slot st).objects[k]? = st.objects[k]? :=
    fun k h => storeObject_objects_ne _ _ _ k _ h hObjInv hS
  have hInvC := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hS
  obtain ⟨hA, hI⟩ := spliceDeletedCdtNode_agree hInvC { cnode := tid.toObjId, slot := slot }
  have hLk := threadSlotDeleted_lookupSlotCap hObjInv hT slot
  have hFar : ∀ k, k ≠ tid.toObjId → SystemState.objectAgreesOffDerivationLinksAt
      (spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
        { cnode := tid.toObjId, slot := slot }) st k :=
    fun k h => (hA k).trans (.of_eq (hCne k h))
  obtain ⟨t', hT', hW⟩ := hA.tcb_fwd hC
  rcases threadSlotCopied_cases st tid slot srcCNode srcSlot rights data with ⟨hN, e⟩ | ⟨cap, hCap, e⟩
  · rw [e, ← hLk, hN]
    exact ⟨hFar, t', (SystemState.getTcb?_eq_some_iff _ tid t').mpr hT', hW⟩
  · rw [e, ← hLk, hCap]
    have hT'' := (SystemState.getTcb?_eq_some_iff _ tid t').mpr hT'
    have hU := SystemState.updateTcb_preserves_objects_invExt _ tid
      (·.insertSpaceCap slot (TCB.spaceCopyOf cap rights data)) hI
    have hAdd := (SystemState.cdtAddChild_agreeObjects hU { cnode := srcCNode, slot := srcSlot }
      { cnode := tid.toObjId, slot := slot } .copy).1
    have hAtU := SystemState.updateTcb_getTcb?_self _ tid
      (·.insertSpaceCap slot (TCB.spaceCopyOf cap rights data)) hI
    rw [hT''] at hAtU
    obtain ⟨t'', hT3, hW3⟩ := hAdd.tcb_fwd ((SystemState.getTcb?_eq_some_iff _ tid _).mp hAtU)
    refine ⟨fun k h => (hAdd k).trans ((SystemState.objectAgreesOffDerivationLinksAt.of_eq
      (SystemState.updateTcb_objects_ne _ tid _ k (Ne.symm h) hI)).trans (hFar k h)),
      t'', (SystemState.getTcb?_eq_some_iff _ tid t'').mpr hT3, ?_⟩
    rw [hW3]
    show (t'.withoutLinks).insertSpaceCap slot _ = ((t.removeSpaceCap slot).withoutLinks).insertSpaceCap slot _
    rw [hW]

/-- **A slot copy from a filled source fills the thread's slot.** -/
theorem threadSlotCopied_slotFilled {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hObjInv : st.objects.invExt) (hT : st.getTcb? tid = some t) {slot : SeLe4n.Slot}
    (hs : slot.toNat < 4) {srcCNode : SeLe4n.ObjId} {srcSlot : SeLe4n.Slot}
    (rights : AccessRightSet) (data : UInt64) {cap : Capability}
    (hL : SystemState.lookupSlotCap st { cnode := srcCNode, slot := srcSlot } = some cap) :
    ∃ t', (threadSlotCopied st tid slot srcCNode srcSlot rights data).getTcb? tid = some t' ∧
      (t'.spaceSlotCap slot).isSome = true := by
  obtain ⟨-, t', hT', hW⟩ := threadSlotCopied_frame hObjInv hT slot srcCNode srcSlot rights data
  refine ⟨t', hT', ?_⟩
  rw [← TCB.spaceSlotCap_withoutLinks, hW, hL]
  dsimp only
  rw [TCB.spaceSlotCap_withoutLinks, TCB.spaceSlotCap_insertSpaceCap _ hs, if_pos rfl]
  rfl

/-- **The slots after a slot copy**: the thread's slot holds the copy of what
the source held in the pre-state, or nothing; every other slot holds what it
held. -/
theorem threadSlotCopied_slotCapAt {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hObjInv : st.objects.invExt) (hT : st.getTcb? tid = some t) {slot : SeLe4n.Slot}
    (hs : slot.toNat < 4) (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (rights : AccessRightSet) (data : UInt64) (r : SlotRef) :
    (threadSlotCopied st tid slot srcCNode srcSlot rights data).slotCapAt r =
      if r.cnode = tid.toObjId ∧ r.slot = slot then
        (SystemState.lookupSlotCap st { cnode := srcCNode, slot := srcSlot }).map
          (TCB.spaceCopyOf · rights data)
      else st.slotCapAt r := by
  obtain ⟨hFar, t', hT', hW⟩ := threadSlotCopied_frame hObjInv hT slot srcCNode srcSlot rights data
  have hPost := (SystemState.getTcb?_eq_some_iff _ tid t').mp hT'
  have hPre := (SystemState.getTcb?_eq_some_iff st tid t).mp hT
  by_cases hk : r.cnode = tid.toObjId
  · rw [SystemState.slotCapAt_of_object (by rw [hk]; exact hPost),
      SystemState.slotCapAt_of_object (by rw [hk]; exact hPre)]
    show t'.spaceSlotCap r.slot = _
    rw [← TCB.spaceSlotCap_withoutLinks, hW, TCB.spaceSlotCap_withoutLinks]
    by_cases he : r.slot = slot
    · rw [if_pos ⟨hk, he⟩, he]
      cases SystemState.lookupSlotCap st { cnode := srcCNode, slot := srcSlot } with
      | none => simp [TCB.spaceSlotCap_removeSpaceCap]
      | some cap => simp [TCB.spaceSlotCap_insertSpaceCap _ hs]
    · rw [if_neg (fun h => he h.2)]
      show _ = t.spaceSlotCap r.slot
      cases SystemState.lookupSlotCap st { cnode := srcCNode, slot := srcSlot } with
      | none => simp [TCB.spaceSlotCap_removeSpaceCap, he]
      | some cap => simp [TCB.spaceSlotCap_insertSpaceCap _ hs, TCB.spaceSlotCap_removeSpaceCap, he]
  · rw [if_neg (fun h => hk h.1)]
    unfold SystemState.slotCapAt SystemState.getObject?
    rcases hFar r.cnode hk with e | ⟨cn, cn', ha, hb, hw⟩ | ⟨u, u', ha, hb, hw⟩
    · rw [e]
    · rw [ha, hb]; exact CNode.proj_eq_of_withoutLinks_eq (·.lookup r.slot) hw
    · rw [ha, hb]; exact TCB.proj_eq_of_withoutLinks_eq (fun x : TCB => x.spaceSlotCap r.slot) hw

/-- A slot lookup reads only the CNode at the slot's key, and no link. -/
theorem lookupSlotCap_of_agreeAt {st st' : SystemState} {r : SlotRef}
    (h : SystemState.objectAgreesOffDerivationLinksAt st' st r.cnode) :
    SystemState.lookupSlotCap st' r = SystemState.lookupSlotCap st r := by
  unfold SystemState.lookupSlotCap SystemState.lookupCNode
  rcases h with e | ⟨cn, cn', ha, hb, hw⟩ | ⟨t, t', ha, hb, _⟩
  · rw [e]
  · rw [ha, hb]; exact CNode.proj_eq_of_withoutLinks_eq (·.lookup r.slot) hw
  · rw [ha, hb]

/-- **A slot copy keeps every slot lookup**: it writes the thread, which holds no
CNode slot, and links. -/
theorem threadSlotCopied_lookupSlotCap {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hObjInv : st.objects.invExt) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) (data : UInt64) (r : SlotRef) :
    SystemState.lookupSlotCap (threadSlotCopied st tid slot srcCNode srcSlot rights data) r =
      SystemState.lookupSlotCap st r := by
  obtain ⟨hFar, t', hT', -⟩ := threadSlotCopied_frame hObjInv hT slot srcCNode srcSlot rights data
  by_cases h : r.cnode = tid.toObjId
  · unfold SystemState.lookupSlotCap SystemState.lookupCNode
    rw [h, (SystemState.getTcb?_eq_some_iff _ tid t').mp hT',
      (SystemState.getTcb?_eq_some_iff st tid t).mp hT]
  · exact lookupSlotCap_of_agreeAt (hFar _ h)

/-- A thread's CSpace root is the object its CSpace root slot names. -/
theorem cspaceRoot_eq_slotCap (t : TCB) :
    t.cspaceRoot = TCB.spaceCellObject (t.spaceSlotCap TCB.cspaceRootSlot) := rfl

/-- A thread's VSpace root is the object its VSpace root slot names. -/
theorem vspaceRoot_eq_slotCap (t : TCB) :
    t.vspaceRoot = TCB.spaceCellObject (t.spaceSlotCap TCB.vspaceRootSlot) := rfl

theorem cspaceRootSourceAdmitted_spec {st : SystemState} {src : CSpaceAddr} {data : UInt64}
    (h : cspaceRootSourceAdmitted st src data = true) :
    ∃ cap id, SystemState.lookupSlotCap st src = some cap ∧ cap.target = .object id ∧
      (st.getCNode? id).isSome := by
  unfold cspaceRootSourceAdmitted at h
  split at h
  · next cap hL =>
    split at h
    · next id hTg => exact ⟨cap, id, hL, hTg, (Bool.and_eq_true _ _).mp h |>.1⟩
    · cases h
  · cases h

/-- **An admitted CSpace root's data word fits beside its CNode's radix**: a
nonzero word's guard size and the radix fill at most the word, so the root copy
has seL4's CNode geometry. -/
theorem cspaceRootSourceAdmitted_dataFits {st : SystemState} {src : CSpaceAddr} {data : UInt64}
    (h : cspaceRootSourceAdmitted st src data = true) :
    ∀ cap id cn, SystemState.lookupSlotCap st src = some cap → cap.target = .object id →
      st.getCNode? id = some cn → data ≠ 0 → (capDataGuardSize data).toNat + cn.radixWidth ≤ 64 := by
  intro cap id cn hL hT hC h0
  unfold cspaceRootSourceAdmitted at h
  rw [hL] at h
  simp only [hT, hC, Option.isSome_some, Bool.true_and, Bool.not_eq_true'] at h
  unfold cspaceRootDataRefused at h
  rw [hC] at h
  simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq, decide_eq_false_iff_not] at h
  rcases h with h | h
  · exact absurd h h0
  · omega

theorem vspaceRootSourceAdmitted_spec {st : SystemState} {src : CSpaceAddr}
    (h : vspaceRootSourceAdmitted st src = true) :
    ∃ cap id, SystemState.lookupSlotCap st src = some cap ∧ cap.target = .object id ∧
      (st.getVSpaceRoot? id).isSome := by
  unfold vspaceRootSourceAdmitted at h
  split at h
  · next cap hL =>
    split at h
    · next id hTg => exact ⟨cap, id, hL, hTg, h⟩
    · cases h
  · cases h

/-- **An admitted fault source holds nothing or an endpoint capability.** -/
theorem faultHandlerSourceAdmitted_spec {st : SystemState} {src : CSpaceAddr}
    (h : faultHandlerSourceAdmitted st src = true) (cap : Capability)
    (hL : SystemState.lookupSlotCap st src = some cap) :
    ∃ id, cap.target = .object id ∧ (st.getEndpoint? id).isSome := by
  unfold faultHandlerSourceAdmitted at h
  rw [hL] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  split at h
  · next id hTg => exact ⟨id, hTg, h⟩
  · cases h

/-- **A thread slot's set keeps the store well formed.** -/
theorem threadSlotSet_objects_invExt (ec : Concurrency.CoreId) {st : SystemState}
    {tid : SeLe4n.ThreadId} {t : TCB} (hObjInv : st.objects.invExt) (hT : st.getTcb? tid = some t)
    (slot : SeLe4n.Slot) (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (rights : AccessRightSet) (data : UInt64) :
    (threadSlotSet ec st tid slot srcCNode srcSlot rights data).objects.invExt := by
  unfold threadSlotSet
  exact (retireFinalObject_frame ec _ _ _
    (threadSlotCopied_tcb hObjInv hT slot srcCNode srcSlot rights data).2).1

/-- **A thread slot's set from a filled source keeps the thread, the slot
filled.** -/
theorem threadSlotSet_filled (ec : Concurrency.CoreId) {st : SystemState}
    {tid : SeLe4n.ThreadId} {t : TCB} (hObjInv : st.objects.invExt) (hT : st.getTcb? tid = some t)
    {slot : SeLe4n.Slot} (hs : slot.toNat < 4) (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (rights : AccessRightSet) (data : UInt64) {cap : Capability}
    (hL : SystemState.lookupSlotCap st { cnode := srcCNode, slot := srcSlot } = some cap) :
    ∃ t', (threadSlotSet ec st tid slot srcCNode srcSlot rights data).getTcb? tid = some t' ∧
      (t'.spaceSlotCap slot).isSome = true := by
  obtain ⟨-, hI⟩ := threadSlotCopied_tcb hObjInv hT slot srcCNode srcSlot rights data
  obtain ⟨t', hT', hF⟩ := threadSlotCopied_slotFilled hObjInv hT hs rights data hL
  refine ⟨t', ?_, hF⟩
  unfold threadSlotSet
  exact retireFinalObject_getTcb?_of_slotCap _ _ _ _ hI hT' hF

/-- **A thread slot's set keeps the thread when another of its slots is
filled**, and that slot filled. -/
theorem threadSlotSet_keepsFilled (ec : Concurrency.CoreId) {st : SystemState}
    {tid : SeLe4n.ThreadId} {t : TCB} (hObjInv : st.objects.invExt) (hT : st.getTcb? tid = some t)
    {slot s : SeLe4n.Slot} (hs : slot.toNat < 4) (hne : s ≠ slot)
    (hF : (t.spaceSlotCap s).isSome = true) (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (rights : AccessRightSet) (data : UInt64) :
    ∃ t', (threadSlotSet ec st tid slot srcCNode srcSlot rights data).getTcb? tid = some t' ∧
      (t'.spaceSlotCap s).isSome = true := by
  obtain ⟨-, t', hT', hW⟩ := threadSlotCopied_frame hObjInv hT slot srcCNode srcSlot rights data
  have hI := (threadSlotCopied_tcb hObjInv hT slot srcCNode srcSlot rights data).2
  have hF' : (t'.spaceSlotCap s).isSome = true := by
    show (t'.withoutLinks.spaceSlotCap s).isSome = true
    rw [hW]
    split
    · rw [TCB.spaceSlotCap_withoutLinks, TCB.spaceSlotCap_removeSpaceCap, if_neg hne]; exact hF
    · rw [TCB.spaceSlotCap_withoutLinks, TCB.spaceSlotCap_insertSpaceCap _ hs, if_neg hne,
        TCB.spaceSlotCap_removeSpaceCap, if_neg hne]; exact hF
  refine ⟨t', ?_, hF'⟩
  unfold threadSlotSet
  exact retireFinalObject_getTcb?_of_slotCap _ _ _ _ hI hT' hF'

/-- **A successful space change is its three slot sets**, each on a stored
thread of a well-formed store: the CSpace root's, the VSpace root's, then the
fault handler's.  The CSpace root slot is filled from the first set on, so no
retire after a set takes the thread. -/
theorem copyThreadSpaces_ok_steps {ec : Concurrency.CoreId} {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr} {cnData : UInt64} {fhSrc : CSpaceAddr}
    (hObjInv : st.objects.invExt)
    (h : copyThreadSpaces ec st vtid cnSrc vrSrc cnData fhSrc = .ok st') :
    ∃ tcb t1 t2, st.getTcb? vtid.val = some tcb ∧
      cspaceRootSourceAdmitted st cnSrc cnData = true ∧ vspaceRootSourceAdmitted st vrSrc = true ∧
      faultHandlerSourceAdmitted st fhSrc = true ∧
      (threadSlotSet ec st vtid.val TCB.cspaceRootSlot cnSrc.cnode cnSrc.slot TCB.cspaceRootRights
        cnData).getTcb? vtid.val = some t1 ∧
      (threadSlotSet ec st vtid.val TCB.cspaceRootSlot cnSrc.cnode cnSrc.slot TCB.cspaceRootRights
        cnData).objects.invExt ∧
      (threadSlotSet ec (threadSlotSet ec st vtid.val TCB.cspaceRootSlot cnSrc.cnode cnSrc.slot
        TCB.cspaceRootRights cnData) vtid.val TCB.vspaceRootSlot vrSrc.cnode vrSrc.slot
        TCB.vspaceRootRights 0).getTcb? vtid.val = some t2 ∧
      (threadSlotSet ec (threadSlotSet ec st vtid.val TCB.cspaceRootSlot cnSrc.cnode cnSrc.slot
        TCB.cspaceRootRights cnData) vtid.val TCB.vspaceRootSlot vrSrc.cnode vrSrc.slot
        TCB.vspaceRootRights 0).objects.invExt ∧
      st' = threadSlotSet ec (threadSlotSet ec (threadSlotSet ec st vtid.val TCB.cspaceRootSlot
        cnSrc.cnode cnSrc.slot TCB.cspaceRootRights cnData) vtid.val TCB.vspaceRootSlot vrSrc.cnode
        vrSrc.slot TCB.vspaceRootRights 0) vtid.val TCB.faultHandlerSlot fhSrc.cnode fhSrc.slot
        TCB.faultHandlerRights 0 := by
  obtain ⟨tcb, hT, -, -, hC, hV, hF, rfl⟩ := copyThreadSpaces_ok h
  obtain ⟨cnCap, -, hCL, -⟩ := cspaceRootSourceAdmitted_spec hC
  obtain ⟨t1, hT1, hF1⟩ := threadSlotSet_filled ec hObjInv hT (slot := TCB.cspaceRootSlot)
    (by decide) cnSrc.cnode cnSrc.slot TCB.cspaceRootRights cnData hCL
  have hI1 := threadSlotSet_objects_invExt ec hObjInv hT TCB.cspaceRootSlot cnSrc.cnode
    cnSrc.slot TCB.cspaceRootRights cnData
  obtain ⟨t2, hT2, -⟩ := threadSlotSet_keepsFilled ec hI1 hT1 (slot := TCB.vspaceRootSlot)
    (by decide) (by decide) hF1 vrSrc.cnode vrSrc.slot TCB.vspaceRootRights 0
  exact ⟨tcb, t1, t2, hT, hC, hV, hF, hT1, hI1, hT2,
    threadSlotSet_objects_invExt ec hI1 hT1 _ _ _ _ _, rfl⟩

/-- **The thread a space change leaves, up to links, from the thread `t`**:
`t`'s CSpace root slot holding the copy of `cnCap` under the root data word
`cnData`, its VSpace root slot the copy of `vrCap`, and its fault-handler slot
the copy of the fault source's capability `fh`, or empty when the source held
none. -/
def spaceChangedTcb (t : TCB) (cnCap vrCap : Capability) (cnData : UInt64)
    (fh : Option Capability) : TCB :=
  let t2 := (((t.removeSpaceCap TCB.cspaceRootSlot).insertSpaceCap TCB.cspaceRootSlot
    (TCB.spaceCopyOf cnCap TCB.cspaceRootRights cnData)).removeSpaceCap TCB.vspaceRootSlot
    ).insertSpaceCap TCB.vspaceRootSlot (TCB.spaceCopyOf vrCap TCB.vspaceRootRights 0)
  match fh with
  | none => t2.removeSpaceCap TCB.faultHandlerSlot
  | some c => (t2.removeSpaceCap TCB.faultHandlerSlot).insertSpaceCap TCB.faultHandlerSlot
      (TCB.spaceCopyOf c TCB.faultHandlerRights 0)

/-- **The payoff**: after a space change each of the thread's root slots holds
the copy of the capability its source slot held, so the thread names the two
roots, each an object of its kind in the pre-state, its fault-handler slot holds
the copy of the fault source's capability (or nothing), and every other field
of it is what it was (up to the slots' derivation links). -/
theorem copyThreadSpaces_ok_tcb {ec : Concurrency.CoreId} {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId}
    {cnSrc vrSrc : CSpaceAddr} {cnData : UInt64} {fhSrc : CSpaceAddr} (hObjInv : st.objects.invExt)
    (h : copyThreadSpaces ec st vtid cnSrc vrSrc cnData fhSrc = .ok st') :
    ∃ tcb cnCap vrCap cnId vrId, st.getTcb? vtid.val = some tcb ∧
      SystemState.lookupSlotCap st cnSrc = some cnCap ∧ cnCap.target = .object cnId ∧
      (st.getCNode? cnId).isSome ∧
      SystemState.lookupSlotCap st vrSrc = some vrCap ∧ vrCap.target = .object vrId ∧
      (st.getVSpaceRoot? vrId).isSome ∧
      ∃ tcb', st'.getTcb? vtid.val = some tcb' ∧ tcb'.cspaceRoot = cnId ∧
        tcb'.vspaceRoot = vrId ∧
        tcb'.withoutLinks =
          (spaceChangedTcb tcb cnCap vrCap cnData (SystemState.lookupSlotCap st fhSrc)).withoutLinks := by
  obtain ⟨tcb, hT, -, -, hC, hV, -, rfl⟩ := copyThreadSpaces_ok h
  obtain ⟨cnCap, cnId, hCL, hCT, hCK⟩ := cspaceRootSourceAdmitted_spec hC
  obtain ⟨vrCap, vrId, hVL, hVT, hVK⟩ := vspaceRootSourceAdmitted_spec hV
  obtain ⟨-, t1, hT1, hW1⟩ := threadSlotCopied_frame hObjInv hT TCB.cspaceRootSlot
    cnSrc.cnode cnSrc.slot TCB.cspaceRootRights cnData
  have hI1 := (threadSlotCopied_tcb hObjInv hT TCB.cspaceRootSlot cnSrc.cnode cnSrc.slot
    TCB.cspaceRootRights cnData).2
  unfold copyThreadSpacesPerform threadSlotSet
  dsimp only
  generalize hS1 : threadSlotCopied st vtid.val TCB.cspaceRootSlot cnSrc.cnode cnSrc.slot
    TCB.cspaceRootRights cnData = s1 at hT1 hI1 ⊢
  generalize hR1 : retireFinalObject ec (slotRetireTarget st vtid.val.toObjId TCB.cspaceRootSlot)
    (recorderFor st (slotRetireTarget st vtid.val.toObjId TCB.cspaceRootSlot) vtid.val.toObjId
      TCB.cspaceRootSlot) s1 = r1
  have hIr1 : r1.objects.invExt := hR1 ▸ (retireFinalObject_frame ec _ _ s1 hI1).1
  have hS1c : (t1.spaceSlotCap TCB.cspaceRootSlot).isSome = true := by
    obtain ⟨t1', hT1', hF⟩ := threadSlotCopied_slotFilled hObjInv hT (slot := TCB.cspaceRootSlot)
      (by decide) TCB.cspaceRootRights cnData (srcCNode := cnSrc.cnode) (srcSlot := cnSrc.slot) hCL
    rw [hS1] at hT1'; rw [hT1] at hT1'; cases hT1'; exact hF
  have hTr1 : r1.getTcb? vtid.val = some t1 := by
    rw [← hR1]; exact retireFinalObject_getTcb?_of_slotCap ec _ _ s1 hI1 hT1 hS1c
  obtain ⟨-, t2, hT2, hW2⟩ := threadSlotCopied_frame hIr1 hTr1 TCB.vspaceRootSlot
    vrSrc.cnode vrSrc.slot TCB.vspaceRootRights 0
  have hI2 := (threadSlotCopied_tcb hIr1 hTr1 TCB.vspaceRootSlot vrSrc.cnode vrSrc.slot
    TCB.vspaceRootRights 0).2
  have hLk1 : ∀ r, SystemState.lookupSlotCap r1 r = SystemState.lookupSlotCap st r := by
    intro r
    rw [← hR1, retireFinalObject_lookupSlotCap ec _ _ s1 hI1, ← hS1,
      threadSlotCopied_lookupSlotCap hObjInv hT]
  rw [hLk1] at hW2
  have hCL' : SystemState.lookupSlotCap st { cnode := cnSrc.cnode, slot := cnSrc.slot } =
      some cnCap := hCL
  have hVL' : SystemState.lookupSlotCap st { cnode := vrSrc.cnode, slot := vrSrc.slot } =
      some vrCap := hVL
  rw [hCL'] at hW1
  rw [hVL'] at hW2
  dsimp only at hW1 hW2
  have hW : t2.withoutLinks = ((((tcb.removeSpaceCap TCB.cspaceRootSlot).insertSpaceCap
      TCB.cspaceRootSlot (TCB.spaceCopyOf cnCap TCB.cspaceRootRights cnData)).removeSpaceCap
      TCB.vspaceRootSlot).insertSpaceCap TCB.vspaceRootSlot
        (TCB.spaceCopyOf vrCap TCB.vspaceRootRights 0)).withoutLinks := by
    rw [hW2]
    show ((t1.withoutLinks).removeSpaceCap _).insertSpaceCap _ _ = _
    rw [hW1]; rfl
  have hSC : ∀ s, t2.spaceSlotCap s = ((((tcb.removeSpaceCap TCB.cspaceRootSlot).insertSpaceCap
      TCB.cspaceRootSlot (TCB.spaceCopyOf cnCap TCB.cspaceRootRights cnData)).removeSpaceCap
      TCB.vspaceRootSlot).insertSpaceCap TCB.vspaceRootSlot
        (TCB.spaceCopyOf vrCap TCB.vspaceRootRights 0)).spaceSlotCap s := fun s => by
    show t2.withoutLinks.spaceSlotCap s = _
    rw [hW]; rfl
  have hne : TCB.cspaceRootSlot ≠ TCB.vspaceRootSlot := by decide
  have hS2c : (t2.spaceSlotCap TCB.vspaceRootSlot).isSome = true := by
    rw [hSC, TCB.spaceSlotCap_insertSpaceCap _ (by decide), if_pos rfl]; rfl
  generalize hS2 : threadSlotCopied r1 vtid.val TCB.vspaceRootSlot vrSrc.cnode vrSrc.slot
    TCB.vspaceRootRights 0 = s2 at hT2 hI2 ⊢
  generalize hR2 : retireFinalObject ec (slotRetireTarget r1 vtid.val.toObjId TCB.vspaceRootSlot)
    (recorderFor r1 (slotRetireTarget r1 vtid.val.toObjId TCB.vspaceRootSlot) vtid.val.toObjId
      TCB.vspaceRootSlot) s2 = r2
  have hIr2 : r2.objects.invExt := hR2 ▸ (retireFinalObject_frame ec _ _ s2 hI2).1
  have hTr2 : r2.getTcb? vtid.val = some t2 := by
    rw [← hR2]; exact retireFinalObject_getTcb?_of_slotCap ec _ _ s2 hI2 hT2 hS2c
  obtain ⟨-, t3, hT3, hW3⟩ := threadSlotCopied_frame hIr2 hTr2 TCB.faultHandlerSlot
    fhSrc.cnode fhSrc.slot TCB.faultHandlerRights 0
  have hI3 := (threadSlotCopied_tcb hIr2 hTr2 TCB.faultHandlerSlot fhSrc.cnode fhSrc.slot
    TCB.faultHandlerRights 0).2
  have hLk2 : ∀ r, SystemState.lookupSlotCap r2 r = SystemState.lookupSlotCap st r := by
    intro r
    rw [← hR2, retireFinalObject_lookupSlotCap ec _ _ s2 hI2, ← hS2,
      threadSlotCopied_lookupSlotCap hIr1 hTr1, hLk1]
  rw [hLk2] at hW3
  have hFh : ∀ s, s ≠ TCB.faultHandlerSlot → t3.spaceSlotCap s = t2.spaceSlotCap s := by
    intro s hs
    show t3.withoutLinks.spaceSlotCap s = _
    rw [hW3]
    split
    · rw [TCB.spaceSlotCap_withoutLinks, TCB.spaceSlotCap_removeSpaceCap, if_neg hs]
    · rw [TCB.spaceSlotCap_withoutLinks, TCB.spaceSlotCap_insertSpaceCap _ (by decide), if_neg hs,
        TCB.spaceSlotCap_removeSpaceCap, if_neg hs]
  have hS3c : (t3.spaceSlotCap TCB.cspaceRootSlot).isSome = true := by
    rw [hFh _ (by decide), hSC, TCB.spaceSlotCap_insertSpaceCap _ (by decide), if_neg hne,
      TCB.spaceSlotCap_removeSpaceCap, if_neg hne, TCB.spaceSlotCap_insertSpaceCap _ (by decide),
      if_pos rfl]; rfl
  refine ⟨tcb, cnCap, vrCap, cnId, vrId, hT, hCL, hCT, hCK, hVL, hVT, hVK, t3,
    retireFinalObject_getTcb?_of_slotCap _ _ _ _ hI3 hT3 hS3c, ?_, ?_, ?_⟩
  · rw [cspaceRoot_eq_slotCap, hFh _ (by decide), hSC, TCB.spaceSlotCap_insertSpaceCap _ (by decide),
      if_neg hne, TCB.spaceSlotCap_removeSpaceCap, if_neg hne,
      TCB.spaceSlotCap_insertSpaceCap _ (by decide), if_pos rfl]
    simp [TCB.spaceCellObject, hCT]
  · rw [vspaceRoot_eq_slotCap, hFh _ (by decide), hSC, TCB.spaceSlotCap_insertSpaceCap _ (by decide),
      if_pos rfl]
    simp [TCB.spaceCellObject, hVT]
  · rw [hW3]
    have e : ({ cnode := fhSrc.cnode, slot := fhSrc.slot } : CSpaceAddr) = fhSrc := rfl
    rw [e]
    unfold spaceChangedTcb
    cases SystemState.lookupSlotCap st fhSrc with
    | none =>
      show (t2.withoutLinks.removeSpaceCap _).withoutLinks = _
      rw [hW]; rfl
    | some c =>
      show ((t2.withoutLinks.removeSpaceCap _).insertSpaceCap _ _).withoutLinks = _
      rw [hW]; rfl

end SeLe4n.Kernel
