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

/-!
# Setting a thread's spaces — seL4's `TCB_SetSpace`

A thread holds its CSpace and VSpace roots as capabilities in two slots of its
own (`TCB.spaceCells`, seL4's `tcbCTable` and `tcbVTable`), and those slots are
derivation nodes like a CNode's.  `copyThreadSpaces` sets them as seL4's
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
thread mid-flight.  Each source slot must hold a capability naming an object of
its kind, a **CNode** for the CSpace root and a **VSpace root** for the VSpace
root, decided here against the store, not trusted of the resolver.

Two cases seL4 names are decided by the model:

* **The source is the thread's own slot.**  It cannot be: the source slots are
  resolved through the caller's CSpace (`resolveSetSpace`), and a CSpace
  resolves to CNode slots alone, while the destination is a slot of a TCB.  The
  delete does not finalise either, so it changes no CNode slot and the source
  still holds its capability when it is read again (seL4's `checkCapAt` asks
  this, since its `cteDelete` may finalise the source's object).
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
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) : SystemState :=
  let stD := spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
    { cnode := tid.toObjId, slot := slot }
  match SystemState.lookupSlotCap stD { cnode := srcCNode, slot := srcSlot } with
  | none => stD
  | some cap =>
    (stD.updateTcb tid (·.insertSpaceCap slot (TCB.spaceCopyOf cap rights))).cdtAddChild
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
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    (SystemState.lookupSlotCap (spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
        { cnode := tid.toObjId, slot := slot }) { cnode := srcCNode, slot := srcSlot } = none ∧
      threadSlotCopied st tid slot srcCNode srcSlot rights =
        spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
          { cnode := tid.toObjId, slot := slot }) ∨
    ∃ cap, SystemState.lookupSlotCap (spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
        { cnode := tid.toObjId, slot := slot }) { cnode := srcCNode, slot := srcSlot } = some cap ∧
      threadSlotCopied st tid slot srcCNode srcSlot rights =
        ((spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
          { cnode := tid.toObjId, slot := slot }).updateTcb tid
            (·.insertSpaceCap slot (TCB.spaceCopyOf cap rights))).cdtAddChild
          { cnode := srcCNode, slot := srcSlot } { cnode := tid.toObjId, slot := slot } .copy := by
  unfold threadSlotCopied
  dsimp only
  split
  · next h => exact .inl ⟨h, rfl⟩
  · next cap h => exact .inr ⟨cap, h, rfl⟩

/-- **A slot copy keeps the thread stored** and the object table well formed. -/
theorem threadSlotCopied_tcb {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hObjInv : st.objects.invExt) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    ((threadSlotCopied st tid slot srcCNode srcSlot rights).getTcb? tid).isSome ∧
      (threadSlotCopied st tid slot srcCNode srcSlot rights).objects.invExt := by
  obtain ⟨⟨t', hT', -⟩, hI⟩ := threadSlotDeleted_tcb hObjInv hT slot
  rcases threadSlotCopied_cases st tid slot srcCNode srcSlot rights with ⟨-, e⟩ | ⟨cap, -, e⟩
  · rw [e, hT']; exact ⟨rfl, hI⟩
  · rw [e]
    have hU := SystemState.updateTcb_preserves_objects_invExt _ tid
      (·.insertSpaceCap slot (TCB.spaceCopyOf cap rights)) hI
    have hR := SystemState.cdtAddChild_reach
      ((spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
        { cnode := tid.toObjId, slot := slot }).updateTcb tid
          (·.insertSpaceCap slot (TCB.spaceCopyOf cap rights)))
      { cnode := srcCNode, slot := srcSlot } { cnode := tid.toObjId, slot := slot } .copy
    refine ⟨?_, hR.invExt hU⟩
    rw [(hR.agree hU).getTcb?_isSome tid]
    show ((SystemState.updateTcb _ tid _).getTcb? tid).isSome = true
    rw [SystemState.updateTcb_getTcb?_self _ _ _ hI, hT']
    rfl

/-- The capability a thread's space slot holds, read through the thread's
record. -/
@[inline] def threadSpaceCell (st : SystemState) (tid : SeLe4n.ThreadId) (slot : SeLe4n.Slot) :
    Option Capability :=
  match st.getTcb? tid with
  | some t => t.spaceSlotCap slot
  | none => none

/-- The slot cell holding the capability of `target` and `rights` alone, written
over the cell `old` and the record it holds (`Capability.overwrite`), so a cell
nothing else holds is rewritten rather than built. -/
@[inline] def spaceCellOver (old : Option Capability) (target : CapTarget)
    (rights : AccessRightSet) : Option Capability :=
  match old with
  | some r => some (r.overwrite target rights SeLe4n.Badge.zero false default default 0 false 0)
  | none => some (Capability.ofFields target rights SeLe4n.Badge.zero false default default 0 false 0)

theorem spaceCellOver_eq (old : Option Capability) (target : CapTarget) (rights : AccessRightSet) :
    spaceCellOver old target rights =
      some ⟨target, rights, SeLe4n.Badge.zero, false, default, default, 0, false, 0⟩ := by
  unfold spaceCellOver
  cases old <;> simp only [Capability.overwrite_eq, Capability.ofFields]

/-- The thread's space slot `slot` written with the cell `spaceCellOver` builds
over `old`.  Out of line, on words, so the update is compiled into it. -/
@[noinline] def threadSpaceCellWritten (st : SystemState) (tid : SeLe4n.ThreadId)
    (slot : SeLe4n.Slot) (old : Option Capability) (target : CapTarget) (rights : AccessRightSet) :
    SystemState :=
  st.updateTcb tid fun t =>
    { t with spaceCells := t.spaceCells.setIfInBounds slot.toNat (spaceCellOver old target rights) }

/-- The insert and edge of `threadSlotCopied`, on the deleted state `stD`, the
capability written over the cell `old` the slot held before its delete. -/
@[noinline] def threadSlotRefilled (old : Option Capability) (stD : SystemState)
    (tid : SeLe4n.ThreadId) (slot : SeLe4n.Slot) (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (rights : AccessRightSet) : SystemState :=
  match SystemState.lookupSlotCap stD { cnode := srcCNode, slot := srcSlot } with
  | none => stD
  | some cap =>
    (threadSpaceCellWritten stD tid slot old cap.target (cap.rights.inter rights)).cdtAddChild
      { cnode := srcCNode, slot := srcSlot } { cnode := tid.toObjId, slot := slot } .copy

/-- `threadSlotCopied` as compiled: the cell the slot holds is read before the
delete clears it, so it outlives the clear and the copy is written over it
(`spaceCellOver`): setting a thread's space builds no capability. -/
@[noinline] def threadSlotCopiedImpl (st : SystemState) (tid : SeLe4n.ThreadId)
    (slot : SeLe4n.Slot) (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (rights : AccessRightSet) : SystemState :=
  let old := threadSpaceCell st tid slot
  threadSlotRefilled old
    (spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st) { cnode := tid.toObjId, slot := slot })
    tid slot srcCNode srcSlot rights

@[csimp] theorem threadSlotCopied_eq_impl : @threadSlotCopied = @threadSlotCopiedImpl := by
  funext st tid slot srcCNode srcSlot rights
  unfold threadSlotCopied threadSlotCopiedImpl threadSlotRefilled threadSpaceCellWritten
  simp only [spaceCellOver_eq]
  split <;> rfl

/-- The CSpace-root source check: the slot holds a capability naming a CNode. -/
@[inline] def cspaceRootSourceAdmitted (st : SystemState) (src : CSpaceAddr) : Bool :=
  match SystemState.lookupSlotCap st src with
  | some cap =>
    match cap.target with
    | .object id => (st.getCNode? id).isSome
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

/-- **The writes of a space change**, on the source slots' words: the CSpace
root slot set from its source, then the VSpace root slot from its. -/
@[inline] def copyThreadSpacesPerform (st : SystemState) (tid : SeLe4n.ThreadId)
    (cnCNode : SeLe4n.ObjId) (cnSlot : SeLe4n.Slot) (vrCNode : SeLe4n.ObjId) (vrSlot : SeLe4n.Slot) :
    SystemState :=
  threadSlotCopied (threadSlotCopied st tid TCB.cspaceRootSlot cnCNode cnSlot TCB.cspaceRootRights)
    tid TCB.vspaceRootSlot vrCNode vrSlot TCB.vspaceRootRights

/-- **Set a suspended thread's CSpace and VSpace root slots from two source
slots** — seL4's `TCB_SetSpace`.  Refused, committing nothing, when the thread
is not a stored TCB (`.objectNotFound`), is not suspended (`.illegalState`), or
either source does not hold a capability naming an object of its kind
(`.invalidCapability`).  Then each slot is set from its source
(`threadSlotCopied`), the CSpace root first. -/
def copyThreadSpaces (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (cnSrc vrSrc : CSpaceAddr) : Except KernelError SystemState :=
  match st.getTcb? vtid.val with
  | none => .error .objectNotFound
  | some tcb =>
    if tcb.threadState != .Inactive || inferThreadState st vtid.val tcb != .Inactive then
      .error .illegalState
    else if !cspaceRootSourceAdmitted st cnSrc then .error .invalidCapability
    else if !vspaceRootSourceAdmitted st vrSrc then .error .invalidCapability
    else .ok (copyThreadSpacesPerform st vtid.val cnSrc.cnode cnSrc.slot vrSrc.cnode vrSrc.slot)

/-- **`copyThreadSpaces`'s checks**, read before anything is written: the thread
is a suspended TCB and each source names an object of its kind.  When they pass
the operation is its writes (`copyThreadSpaces_of_admitted`). -/
@[inline] def copyThreadSpacesAdmitted (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (cnSrc vrSrc : CSpaceAddr) : Bool :=
  match st.getTcb? vtid.val with
  | none => false
  | some tcb =>
    !(tcb.threadState != .Inactive || inferThreadState st vtid.val tcb != .Inactive) &&
      cspaceRootSourceAdmitted st cnSrc && vspaceRootSourceAdmitted st vrSrc

theorem copyThreadSpaces_of_admitted {st : SystemState} {vtid : SeLe4n.ValidThreadId}
    {cnSrc vrSrc : CSpaceAddr} (h : copyThreadSpacesAdmitted st vtid cnSrc vrSrc = true) :
    copyThreadSpaces st vtid cnSrc vrSrc =
      .ok (copyThreadSpacesPerform st vtid.val cnSrc.cnode cnSrc.slot vrSrc.cnode vrSrc.slot) := by
  unfold copyThreadSpacesAdmitted at h
  unfold copyThreadSpaces
  cases hT : st.getTcb? vtid.val with
  | none => rw [hT] at h; cases h
  | some tcb =>
    rw [hT] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hS, hC⟩, hV⟩ := h
    simp only [hS, hC, hV, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- **What a successful space change consists of**: the thread was a suspended
TCB, each source held a capability naming an object of its kind, and the state
is the two slot copies. -/
theorem copyThreadSpaces_ok {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {cnSrc vrSrc : CSpaceAddr} (h : copyThreadSpaces st vtid cnSrc vrSrc = .ok st') :
    ∃ tcb, st.getTcb? vtid.val = some tcb ∧ tcb.threadState = .Inactive ∧
      inferThreadState st vtid.val tcb = .Inactive ∧
      cspaceRootSourceAdmitted st cnSrc = true ∧ vspaceRootSourceAdmitted st vrSrc = true ∧
      st' = copyThreadSpacesPerform st vtid.val cnSrc.cnode cnSrc.slot vrSrc.cnode vrSrc.slot := by
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
      cases hC : cspaceRootSourceAdmitted st cnSrc with
      | false => simp [hC] at h
      | true =>
        cases hV : vspaceRootSourceAdmitted st vrSrc with
        | false => simp [hC, hV] at h
        | true =>
          simp only [hC, hV, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
          exact ⟨tcb, rfl, hS.1, hS.2, rfl, rfl, h.symm⟩
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
theorem copyThreadSpaces_refuses_active (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (cnSrc vrSrc : CSpaceAddr) (tcb : TCB) (hT : st.getTcb? vtid.val = some tcb)
    (hS : inferThreadState st vtid.val tcb ≠ .Inactive) :
    copyThreadSpaces st vtid cnSrc vrSrc = .error .illegalState := by
  have : (tcb.threadState != .Inactive || inferThreadState st vtid.val tcb != .Inactive)
      = true := by simp [hS]
  simp [copyThreadSpaces, hT, this]

/-- **What a slot copy leaves**: every object but the thread's is the
pre-state's up to derivation links, and the thread is the pre-state's with the
slot emptied and, when the source held a capability, its copy put in, up to
links.  A slot lookup reads no link and no thread, so the source is read as in
the pre-state. -/
theorem threadSlotCopied_frame {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hObjInv : st.objects.invExt) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    (∀ k, k ≠ tid.toObjId → SystemState.objectAgreesOffDerivationLinksAt
        (threadSlotCopied st tid slot srcCNode srcSlot rights) st k) ∧
    ∃ t', (threadSlotCopied st tid slot srcCNode srcSlot rights).getTcb? tid = some t' ∧
      t'.withoutLinks =
        (match SystemState.lookupSlotCap st { cnode := srcCNode, slot := srcSlot } with
          | none => t.removeSpaceCap slot
          | some cap => (t.removeSpaceCap slot).insertSpaceCap slot (TCB.spaceCopyOf cap rights)
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
  have hLk : ∀ r, SystemState.lookupSlotCap (spliceDeletedCdtNode (threadSlotCleared tid.toObjId
      slot st) { cnode := tid.toObjId, slot := slot }) r = SystemState.lookupSlotCap st r := by
    intro r
    rw [hA.lookupSlotCap r]
    unfold SystemState.lookupSlotCap SystemState.lookupCNode
    by_cases h : r.cnode = tid.toObjId
    · rw [h, hC, hPre]
    · rw [hCne _ h]
  have hFar : ∀ k, k ≠ tid.toObjId → SystemState.objectAgreesOffDerivationLinksAt
      (spliceDeletedCdtNode (threadSlotCleared tid.toObjId slot st)
        { cnode := tid.toObjId, slot := slot }) st k :=
    fun k h => (hA k).trans (.of_eq (hCne k h))
  obtain ⟨t', hT', hW⟩ := hA.tcb_fwd hC
  rcases threadSlotCopied_cases st tid slot srcCNode srcSlot rights with ⟨hN, e⟩ | ⟨cap, hCap, e⟩
  · rw [e, ← hLk, hN]
    exact ⟨hFar, t', (SystemState.getTcb?_eq_some_iff _ tid t').mpr hT', hW⟩
  · rw [e, ← hLk, hCap]
    have hT'' := (SystemState.getTcb?_eq_some_iff _ tid t').mpr hT'
    have hU := SystemState.updateTcb_preserves_objects_invExt _ tid
      (·.insertSpaceCap slot (TCB.spaceCopyOf cap rights)) hI
    have hAdd := (SystemState.cdtAddChild_agreeObjects hU { cnode := srcCNode, slot := srcSlot }
      { cnode := tid.toObjId, slot := slot } .copy).1
    have hAtU := SystemState.updateTcb_getTcb?_self _ tid
      (·.insertSpaceCap slot (TCB.spaceCopyOf cap rights)) hI
    rw [hT''] at hAtU
    obtain ⟨t'', hT3, hW3⟩ := hAdd.tcb_fwd ((SystemState.getTcb?_eq_some_iff _ tid _).mp hAtU)
    refine ⟨fun k h => (hAdd k).trans ((SystemState.objectAgreesOffDerivationLinksAt.of_eq
      (SystemState.updateTcb_objects_ne _ tid _ k (Ne.symm h) hI)).trans (hFar k h)),
      t'', (SystemState.getTcb?_eq_some_iff _ tid t'').mpr hT3, ?_⟩
    rw [hW3]
    show (t'.withoutLinks).insertSpaceCap slot _ = ((t.removeSpaceCap slot).withoutLinks).insertSpaceCap slot _
    rw [hW]

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
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) (r : SlotRef) :
    SystemState.lookupSlotCap (threadSlotCopied st tid slot srcCNode srcSlot rights) r =
      SystemState.lookupSlotCap st r := by
  obtain ⟨hFar, t', hT', -⟩ := threadSlotCopied_frame hObjInv hT slot srcCNode srcSlot rights
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

theorem cspaceRootSourceAdmitted_spec {st : SystemState} {src : CSpaceAddr}
    (h : cspaceRootSourceAdmitted st src = true) :
    ∃ cap id, SystemState.lookupSlotCap st src = some cap ∧ cap.target = .object id ∧
      (st.getCNode? id).isSome := by
  unfold cspaceRootSourceAdmitted at h
  split at h
  · next cap hL =>
    split at h
    · next id hTg => exact ⟨cap, id, hL, hTg, h⟩
    · cases h
  · cases h

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

/-- **The payoff**: after a space change each of the thread's root slots holds
the copy of the capability its source slot held, so the thread names the two
roots, each an object of its kind in the pre-state, and every other field of it
is what it was (up to the slots' derivation links). -/
theorem copyThreadSpaces_ok_tcb {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {cnSrc vrSrc : CSpaceAddr} (hObjInv : st.objects.invExt)
    (h : copyThreadSpaces st vtid cnSrc vrSrc = .ok st') :
    ∃ tcb cnCap vrCap cnId vrId, st.getTcb? vtid.val = some tcb ∧
      SystemState.lookupSlotCap st cnSrc = some cnCap ∧ cnCap.target = .object cnId ∧
      (st.getCNode? cnId).isSome ∧
      SystemState.lookupSlotCap st vrSrc = some vrCap ∧ vrCap.target = .object vrId ∧
      (st.getVSpaceRoot? vrId).isSome ∧
      ∃ tcb', st'.getTcb? vtid.val = some tcb' ∧ tcb'.cspaceRoot = cnId ∧
        tcb'.vspaceRoot = vrId ∧
        tcb'.withoutLinks =
          ((((tcb.removeSpaceCap TCB.cspaceRootSlot).insertSpaceCap TCB.cspaceRootSlot
            (TCB.spaceCopyOf cnCap TCB.cspaceRootRights)).removeSpaceCap TCB.vspaceRootSlot
            ).insertSpaceCap TCB.vspaceRootSlot
              (TCB.spaceCopyOf vrCap TCB.vspaceRootRights)).withoutLinks := by
  obtain ⟨tcb, hT, -, -, hC, hV, rfl⟩ := copyThreadSpaces_ok h
  obtain ⟨cnCap, cnId, hCL, hCT, hCK⟩ := cspaceRootSourceAdmitted_spec hC
  obtain ⟨vrCap, vrId, hVL, hVT, hVK⟩ := vspaceRootSourceAdmitted_spec hV
  obtain ⟨-, t1, hT1, hW1⟩ := threadSlotCopied_frame hObjInv hT TCB.cspaceRootSlot
    cnSrc.cnode cnSrc.slot TCB.cspaceRootRights
  have hI1 := (threadSlotCopied_tcb hObjInv hT TCB.cspaceRootSlot cnSrc.cnode cnSrc.slot
    TCB.cspaceRootRights).2
  obtain ⟨-, t2, hT2, hW2⟩ := threadSlotCopied_frame hI1 hT1 TCB.vspaceRootSlot
    vrSrc.cnode vrSrc.slot TCB.vspaceRootRights
  rw [threadSlotCopied_lookupSlotCap hObjInv hT] at hW2
  have hCL' : SystemState.lookupSlotCap st { cnode := cnSrc.cnode, slot := cnSrc.slot } =
      some cnCap := hCL
  have hVL' : SystemState.lookupSlotCap st { cnode := vrSrc.cnode, slot := vrSrc.slot } =
      some vrCap := hVL
  rw [hCL'] at hW1
  rw [hVL'] at hW2
  dsimp only at hW1 hW2
  have hW : t2.withoutLinks = ((((tcb.removeSpaceCap TCB.cspaceRootSlot).insertSpaceCap
      TCB.cspaceRootSlot (TCB.spaceCopyOf cnCap TCB.cspaceRootRights)).removeSpaceCap
      TCB.vspaceRootSlot).insertSpaceCap TCB.vspaceRootSlot
        (TCB.spaceCopyOf vrCap TCB.vspaceRootRights)).withoutLinks := by
    rw [hW2]
    show ((t1.withoutLinks).removeSpaceCap _).insertSpaceCap _ _ = _
    rw [hW1]; rfl
  have hSC : ∀ s, t2.spaceSlotCap s = ((((tcb.removeSpaceCap TCB.cspaceRootSlot).insertSpaceCap
      TCB.cspaceRootSlot (TCB.spaceCopyOf cnCap TCB.cspaceRootRights)).removeSpaceCap
      TCB.vspaceRootSlot).insertSpaceCap TCB.vspaceRootSlot
        (TCB.spaceCopyOf vrCap TCB.vspaceRootRights)).spaceSlotCap s := fun s => by
    show t2.withoutLinks.spaceSlotCap s = _
    rw [hW]; rfl
  have hne : TCB.cspaceRootSlot ≠ TCB.vspaceRootSlot := by decide
  refine ⟨tcb, cnCap, vrCap, cnId, vrId, hT, hCL, hCT, hCK, hVL, hVT, hVK, t2, hT2, ?_, ?_, hW⟩
  · rw [cspaceRoot_eq_slotCap, hSC, TCB.spaceSlotCap_insertSpaceCap _ (by decide), if_neg hne,
      TCB.spaceSlotCap_removeSpaceCap, if_neg hne, TCB.spaceSlotCap_insertSpaceCap _ (by decide),
      if_pos rfl]
    simp [TCB.spaceCellObject, hCT]
  · rw [vspaceRoot_eq_slotCap, hSC, TCB.spaceSlotCap_insertSpaceCap _ (by decide), if_pos rfl]
    simp [TCB.spaceCellObject, hVT]

end SeLe4n.Kernel
