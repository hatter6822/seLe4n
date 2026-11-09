-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.DeliveredInPlace
import SeLe4n.Kernel.IPC.DualQueue.WithCaps
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallInPlace

/-!
# A rendezvous whose receiver has no free receive slot

The specification's capability transfer installs each capability it resolves
in the first empty slot of the receiver's CSpace root, scanned from slot 0 over
`maxExtraCaps` slots (`ipcTransferSingleCap`).  When that window holds no empty
slot (`receiveWindowClosed`), every capability comes back `.noSlot` and nothing
is written: the transfer is the identity on the state and installs none
(`receiveTransferCaps_of_windowClosed`), as seL4's `transferCaps` with no
receive slot transfers none.

The window is read in the pre-state; the send rendezvous's writes (the
endpoint's queue ends, the receivers' queue links and message slots, the wake's
run-queue links and scheduler) touch no CNode and no thread's CSpace root
(`CapSpaceAgrees`), so it is the window the specification's transfer scans in
the post-state.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **Is a CSpace's receive window closed?**  `root` is a CNode with no empty
slot among the first `maxExtraCaps` from slot 0. -/
def cspaceWindowClosed (st : SystemState) (root : SeLe4n.ObjId) : Bool :=
  match st.getCNode? root with
  | some cn => (cn.findFirstEmptySlotChecked (SeLe4n.Slot.ofNat 0) maxExtraCaps).isNone
  | none => false

/-- **Is the receiver's receive window closed?**  `r` is a thread whose
CSpace root is a CNode with no empty slot among the first `maxExtraCaps` from
slot 0: a capability transfer to it installs nothing. -/
def receiveWindowClosed (st : SystemState) (r : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? r with
  | some t => cspaceWindowClosed st t.cspaceRoot
  | none => false

/-- The results a transfer pads with `.noSlot` count no installed capability. -/
theorem installedCount_push_noSlot (acc : Array CapTransferResult) :
    CapTransferSummary.installedCount { results := acc.push .noSlot } =
      CapTransferSummary.installedCount { results := acc } := by
  simp only [CapTransferSummary.installedCount, Array.foldl_push]

/-- **The unwrap loop over a closed window**: every capability is `.noSlot`,
the state is unchanged and nothing more is installed. -/
theorem ipcUnwrapCapsLoop_of_windowClosed (caps : Array TransferCap)
    (root : SeLe4n.ObjId) (cn : CNode) (st : SystemState)
    (hCn : st.getCNode? root = some cn)
    (hFull : cn.findFirstEmptySlotChecked (SeLe4n.Slot.ofNat 0) maxExtraCaps = none) :
    ∀ (fuel idx : Nat) (acc : Array CapTransferResult), ∃ res,
      ipcUnwrapCapsLoop caps root idx (SeLe4n.Slot.ofNat 0) acc fuel st =
        .ok ({ results := res }, st) ∧
      CapTransferSummary.installedCount { results := res } =
        CapTransferSummary.installedCount { results := acc } := by
  intro fuel
  induction fuel with
  | zero => intro idx acc; exact ⟨acc, rfl, rfl⟩
  | succ n ih =>
    intro idx acc
    simp only [ipcUnwrapCapsLoop]
    cases caps[idx]? with
    | none => exact ⟨acc, rfl, rfl⟩
    | some tc =>
      have hStep : ipcTransferSingleCap tc.cap tc.srcSlot root (SeLe4n.Slot.ofNat 0)
          maxExtraCaps st = .ok (.noSlot, st) := by
        simp only [ipcTransferSingleCap, hCn, hFull]
      simp only [hStep]
      obtain ⟨res, hRes, hCount⟩ := ih (idx + 1) (acc.push .noSlot)
      exact ⟨res, hRes, hCount.trans (installedCount_push_noSlot acc)⟩

/-- **A transfer into a closed window is the identity and installs none.** -/
theorem receiveTransferCaps_of_windowClosed
    (req : Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat)) (root : SeLe4n.ObjId) (cn : CNode)
    (st : SystemState) (hCn : st.getCNode? root = some cn)
    (hFull : cn.findFirstEmptySlotChecked (SeLe4n.Slot.ofNat 0) maxExtraCaps = none) :
    ∃ s, receiveTransferCaps req root (SeLe4n.Slot.ofNat 0) st = .ok (s, st) ∧
      s.installedCount = 0 := by
  unfold receiveTransferCaps
  rcases req with _ | ⟨sroot, addrs, depth⟩
  · exact ⟨_, rfl, rfl⟩
  · simp only []
    split
    · exact ⟨_, rfl, rfl⟩
    · unfold ipcUnwrapCaps
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨res, hRes, hCount⟩ := ipcUnwrapCapsLoop_of_windowClosed _ root cn st hCn hFull
        _ 0 #[]
      exact ⟨_, hRes, hCount⟩

/-! ### The writes a send rendezvous makes leave every CSpace as it is -/

/-- The CNode an object is, if it is one. -/
@[inline] def objectCNode : Option KernelObject → Option CNode
  | some (.cnode cn) => some cn
  | _ => none

/-- The CSpace root of the thread an object is, if it is one. -/
@[inline] def objectCspaceRoot : Option KernelObject → Option SeLe4n.ObjId
  | some (.tcb t) => some t.cspaceRoot
  | _ => none

/-- **Two object tables agree on every CSpace**: every CNode is the same, and
every thread's CSpace root. -/
def ObjectsCapSpaceAgree (o o' : RobinHood.RHTable SeLe4n.ObjId KernelObject) : Prop :=
  ∀ k : SeLe4n.ObjId, objectCNode o'[k]? = objectCNode o[k]? ∧
    objectCspaceRoot o'[k]? = objectCspaceRoot o[k]?

theorem ObjectsCapSpaceAgree.refl (o : RobinHood.RHTable SeLe4n.ObjId KernelObject) :
    ObjectsCapSpaceAgree o o := fun _ => ⟨rfl, rfl⟩

theorem ObjectsCapSpaceAgree.trans {o o' o'' : RobinHood.RHTable SeLe4n.ObjId KernelObject}
    (h1 : ObjectsCapSpaceAgree o o') (h2 : ObjectsCapSpaceAgree o' o'') :
    ObjectsCapSpaceAgree o o'' :=
  fun k => ⟨(h2 k).1.trans (h1 k).1, (h2 k).2.trans (h1 k).2⟩

/-- **Two states agree on every CSpace** (`ObjectsCapSpaceAgree` on their
object tables). -/
def CapSpaceAgrees (X Y : SystemState) : Prop := ObjectsCapSpaceAgree X.objects Y.objects

theorem CapSpaceAgrees.refl (X : SystemState) : CapSpaceAgrees X X :=
  ObjectsCapSpaceAgree.refl _

theorem CapSpaceAgrees.trans {X Y Z : SystemState} (h1 : CapSpaceAgrees X Y)
    (h2 : CapSpaceAgrees Y Z) : CapSpaceAgrees X Z :=
  ObjectsCapSpaceAgree.trans h1 h2

theorem CapSpaceAgrees.of_objects {X Y : SystemState} (h : Y.objects = X.objects) :
    CapSpaceAgrees X Y := fun k => by rw [h]; exact ⟨rfl, rfl⟩

theorem CapSpaceAgrees.getCNode? {X Y : SystemState} (h : CapSpaceAgrees X Y)
    (k : SeLe4n.ObjId) : Y.getCNode? k = X.getCNode? k := by
  have := (h k).1
  unfold SystemState.getCNode?
  revert this
  cases Y.objects[k]? with
  | none => cases X.objects[k]? with
    | none => intro; rfl
    | some o => cases o <;> simp [objectCNode]
  | some o => cases X.objects[k]? with
    | none => cases o <;> simp [objectCNode]
    | some o' => cases o <;> cases o' <;> simp [objectCNode]

theorem CapSpaceAgrees.cspaceRoot {X Y : SystemState} (h : CapSpaceAgrees X Y)
    (r : SeLe4n.ThreadId) : SeLe4n.Kernel.lookupCspaceRoot Y r = SeLe4n.Kernel.lookupCspaceRoot X r := by
  have := (h r.toObjId).2
  unfold SeLe4n.Kernel.lookupCspaceRoot SystemState.getTcb?
  revert this
  cases Y.objects[r.toObjId]? with
  | none => cases X.objects[r.toObjId]? with
    | none => intro; rfl
    | some o => cases o <;> simp [objectCspaceRoot]
  | some o => cases X.objects[r.toObjId]? with
    | none => cases o <;> simp [objectCspaceRoot]
    | some o' => cases o <;> cases o' <;> simp [objectCspaceRoot]

/-- An object update that keeps every CNode and every thread's CSpace root. -/
def CapSpaceFaithful (F : KernelObject → KernelObject) : Prop :=
  ∀ o, objectCNode (some (F o)) = objectCNode (some o) ∧
    objectCspaceRoot (some (F o)) = objectCspaceRoot (some o)

/-- A slot write through a faithful update agrees on every CSpace. -/
theorem ObjectsCapSpaceAgree.mapValueAt (o : RobinHood.RHTable SeLe4n.ObjId KernelObject)
    (k : SeLe4n.ObjId) (F : KernelObject → KernelObject) (hF : CapSpaceFaithful F) :
    ObjectsCapSpaceAgree o (o.mapValueAt k F) := by
  intro x
  simp only [RHTable_getElem?_eq_get?, RobinHood.RHTable.get?_mapValueAt]
  split
  · cases o.get? x with
    | none => exact ⟨rfl, rfl⟩
    | some o => exact hF o
  · exact ⟨rfl, rfl⟩

theorem CapSpaceAgrees.mapValueAt (X : SystemState) (k : SeLe4n.ObjId)
    (F : KernelObject → KernelObject) (hF : CapSpaceFaithful F) :
    CapSpaceAgrees X { X with objects := X.objects.mapValueAt k F } :=
  ObjectsCapSpaceAgree.mapValueAt X.objects k F hF

/-- A TCB update that keeps the thread's CSpace root is faithful. -/
theorem capSpaceFaithful_mapTcb (g : TCB → TCB) (hg : ∀ t, (g t).cspaceRoot = t.cspaceRoot) :
    CapSpaceFaithful (KernelObject.mapTcb g) := by
  intro o; cases o <;> simp [KernelObject.mapTcb, objectCNode, objectCspaceRoot, hg]

theorem capSpaceFaithful_mapTcbObject (g : TCB → TCB)
    (hg : ∀ t, (g t).cspaceRoot = t.cspaceRoot) :
    CapSpaceFaithful (SystemState.mapTcbObject g) := by
  intro o; cases o <;> simp [SystemState.mapTcbObject, objectCNode, objectCspaceRoot, hg]

theorem capSpaceFaithful_popEndpoint (isReceiveQ : Bool) (nextCode : Nat) :
    CapSpaceFaithful (popEndpoint isReceiveQ nextCode) := by
  intro o
  cases o with
  | endpoint e =>
    simp only [popEndpoint]
    rcases isReceiveQ with _ | _ <;> rcases nextCode with _ | _ <;> exact ⟨rfl, rfl⟩
  | _ => exact ⟨rfl, rfl⟩

theorem CapSpaceAgrees.mapTcbInPlace (X : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB)
    (hg : ∀ t, (g t).cspaceRoot = t.cspaceRoot) : CapSpaceAgrees X (X.mapTcbInPlace t g) :=
  CapSpaceAgrees.mapValueAt X _ _ (capSpaceFaithful_mapTcb g hg)

theorem CapSpaceAgrees.updateTcb (X : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB)
    (hg : ∀ t, (g t).cspaceRoot = t.cspaceRoot) (hNo : X.objects.noResizeDue) :
    CapSpaceAgrees X (X.updateTcb t g) := by
  rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]
  exact CapSpaceAgrees.mapTcbInPlace X t g hg

theorem CapSpaceAgrees.modifyObject (X : SystemState) (k : SeLe4n.ObjId)
    (F : KernelObject → KernelObject) (hF : CapSpaceFaithful F) (hNo : X.objects.noResizeDue) :
    CapSpaceAgrees X (X.modifyObject k F) := by
  rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo]
  exact CapSpaceAgrees.mapValueAt X k F hF

theorem objectCNode_withoutRunLinks (o : Option KernelObject) :
    objectCNode (o.map KernelObject.withoutRunLinks) = objectCNode o := by
  rcases o with _ | o
  · rfl
  · cases o <;> rfl

theorem objectCspaceRoot_withoutRunLinks (o : Option KernelObject) :
    objectCspaceRoot (o.map KernelObject.withoutRunLinks) = objectCspaceRoot o := by
  rcases o with _ | o
  · rfl
  · cases o <;> rfl

/-- States that agree off their run-queue links agree on every CSpace. -/
theorem CapSpaceAgrees.of_offRunLinks {X Y : SystemState}
    (h : SystemState.objectsAgreeOffRunLinks Y X) : CapSpaceAgrees X Y := fun k =>
  ⟨by rw [← objectCNode_withoutRunLinks Y.objects[k]?, h k, objectCNode_withoutRunLinks],
   by rw [← objectCspaceRoot_withoutRunLinks Y.objects[k]?, h k,
     objectCspaceRoot_withoutRunLinks]⟩

/-- A run-queue insert agrees on every CSpace: it writes the thread's state
and run-queue links, and the scheduler. -/
theorem CapSpaceAgrees.enqueueRunnableOnCore (X : SystemState) (c : Concurrency.CoreId)
    (t : SeLe4n.ThreadId) (hNo : X.objects.noResizeDue) :
    CapSpaceAgrees X (SeLe4n.Kernel.enqueueRunnableOnCore X c t) := by
  rw [enqueueRunnableOnCore_eq_impl]
  unfold enqueueRunnableOnCoreImpl
  split
  · split
    · exact CapSpaceAgrees.refl _
    · dsimp only
      have h1 := CapSpaceAgrees.modifyObject X t.toObjId _
        (capSpaceFaithful_mapTcbObject (fun x => x.setIpcState .ready) (fun _ => rfl)) hNo
      refine (h1.trans ?_).trans (CapSpaceAgrees.of_objects rfl)
      exact CapSpaceAgrees.of_offRunLinks
        (SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks _ _ _ _)
  · exact CapSpaceAgrees.refl _

/-- A wake agrees on every CSpace. -/
theorem CapSpaceAgrees.wakeThread (X : SystemState) (t : SeLe4n.ThreadId)
    (core : Concurrency.CoreId) (hNo : X.objects.noResizeDue) :
    CapSpaceAgrees X (SeLe4n.Kernel.wakeThread X t core).1 :=
  CapSpaceAgrees.enqueueRunnableOnCore X _ t hNo

/-- The send rendezvous's writes agree on every CSpace. -/
theorem CapSpaceAgrees.storeSendRendezvous (X : SystemState) (endpointId : SeLe4n.ObjId)
    (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (msg : IpcMessage)
    (hNo : X.objects.noResizeDue) :
    CapSpaceAgrees X (SeLe4n.Kernel.storeSendRendezvous X endpointId head next msg) := by
  have hNo1 := modifyObject_noResizeDue X endpointId (popEndpoint true (ThreadId.optCode next)) hNo
  have h1 := CapSpaceAgrees.modifyObject X endpointId _ (capSpaceFaithful_popEndpoint true
    (ThreadId.optCode next)) hNo
  have hTail : ∀ Y2 : SystemState, Y2.objects.noResizeDue →
      CapSpaceAgrees Y2 ((Y2.updateTcb head tcbOffQueue).updateTcb head (receiveCompleteTcb msg)) :=
    fun Y2 hNo2 => (CapSpaceAgrees.updateTcb Y2 head tcbOffQueue (fun _ => rfl) hNo2).trans
      (CapSpaceAgrees.updateTcb _ head (receiveCompleteTcb msg) (fun _ => rfl)
        (updateTcb_noResizeDue _ _ _ hNo2))
  unfold SeLe4n.Kernel.storeSendRendezvous
  cases next with
  | none => exact h1.trans (hTail _ hNo1)
  | some n =>
    exact (h1.trans (CapSpaceAgrees.updateTcb _ n tcbAsQueueHead (fun _ => rfl) hNo1)).trans
      (hTail _ (updateTcb_noResizeDue _ _ _ hNo1))

/-- A pop off an endpoint queue agrees on every CSpace. -/
theorem CapSpaceAgrees.storePopHead (X : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (hNo : X.objects.noResizeDue) :
    CapSpaceAgrees X (SeLe4n.Kernel.storePopHead X endpointId isReceiveQ head next) ∧
      (SeLe4n.Kernel.storePopHead X endpointId isReceiveQ head next).objects.noResizeDue := by
  have hNo1 := modifyObject_noResizeDue X endpointId
    (popEndpoint isReceiveQ (ThreadId.optCode next)) hNo
  have h1 := CapSpaceAgrees.modifyObject X endpointId _ (capSpaceFaithful_popEndpoint isReceiveQ
    (ThreadId.optCode next)) hNo
  unfold SeLe4n.Kernel.storePopHead
  cases next with
  | none =>
    exact ⟨h1.trans (CapSpaceAgrees.updateTcb _ head tcbOffQueue (fun _ => rfl) hNo1),
      updateTcb_noResizeDue _ _ _ hNo1⟩
  | some n =>
    have hNo2 := updateTcb_noResizeDue _ n tcbAsQueueHead hNo1
    exact ⟨(h1.trans (CapSpaceAgrees.updateTcb _ n tcbAsQueueHead (fun _ => rfl) hNo1)).trans
      (CapSpaceAgrees.updateTcb _ head tcbOffQueue (fun _ => rfl) hNo2),
      updateTcb_noResizeDue _ _ _ hNo2⟩

/-- A reply-waiter link agrees on every CSpace. -/
theorem CapSpaceAgrees.linkReplyWaiter (X : SystemState) (w s : SeLe4n.ThreadId) :
    CapSpaceAgrees X (X.linkReplyWaiter w s) := by
  unfold SystemState.linkReplyWaiter
  dsimp only
  have h1 := CapSpaceAgrees.mapTcbInPlace X w (fun x => { x with
    replyWaiterPrevCode := 0, replyWaiterNextCode := X.replyHeadCode s }) (fun _ => rfl)
  generalize X.mapTcbInPlace w _ = Y1 at h1
  have h2 : CapSpaceAgrees Y1 (Y1.updateTcbAtCode (X.replyHeadCode s)
      fun x => { x with replyWaiterPrevCode := LinkedQueue.code w }) := by
    unfold SystemState.updateTcbAtCode
    split
    · exact CapSpaceAgrees.refl _
    · exact CapSpaceAgrees.mapTcbInPlace _ _ _ (fun _ => rfl)
  generalize Y1.updateTcbAtCode (X.replyHeadCode s)
    (fun x => { x with replyWaiterPrevCode := LinkedQueue.code w }) = Y2 at h2
  exact h1.trans (h2.trans (CapSpaceAgrees.mapTcbInPlace Y2 s (fun x => { x with
    replyWaitersHeadCode := LinkedQueue.code w, replyWaitersCount := x.replyWaitersCount + 1 })
    (fun _ => rfl)))

theorem capSpaceFaithful_replyWithCaller (caller : SeLe4n.ThreadId) :
    CapSpaceFaithful (replyWithCaller caller) := by
  intro o; cases o <;> exact ⟨rfl, rfl⟩

/-- The call rendezvous's writes agree on every CSpace. -/
theorem CapSpaceAgrees.storeCallRendezvous (X : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (msg : IpcMessage) (core : Concurrency.CoreId) (hNo : X.objects.noResizeDue) :
    CapSpaceAgrees X
      (SeLe4n.Kernel.storeCallRendezvous X endpointId caller r next rid msg core) := by
  obtain ⟨h1, hNo1⟩ := CapSpaceAgrees.storePopHead X endpointId true r next hNo
  unfold SeLe4n.Kernel.storeCallRendezvous
  dsimp only
  generalize SeLe4n.Kernel.storePopHead X endpointId true r next = Y1 at h1 hNo1
  have h2 := CapSpaceAgrees.updateTcb Y1 r (callReceiverTcb msg) (fun _ => rfl) hNo1
  have hNo2 := updateTcb_noResizeDue Y1 r (callReceiverTcb msg) hNo1
  generalize Y1.updateTcb r (callReceiverTcb msg) = Y2 at h2 hNo2
  have h3 := CapSpaceAgrees.enqueueRunnableOnCore Y2 (determineTargetCore Y2 r) r hNo2
  have hNo3 := enqueueRunnableOnCore_noResizeDue Y2 (determineTargetCore Y2 r) r hNo2
  generalize SeLe4n.Kernel.enqueueRunnableOnCore Y2 (determineTargetCore Y2 r) r = Y3 at h3 hNo3
  have h4 := CapSpaceAgrees.updateTcb Y3 caller (callCallerTcb endpointId r) (fun _ => rfl) hNo3
  have hNo4 := updateTcb_noResizeDue Y3 caller (callCallerTcb endpointId r) hNo3
  generalize Y3.updateTcb caller (callCallerTcb endpointId r) = Y4 at h4 hNo4
  have h5 := CapSpaceAgrees.modifyObject Y4 rid.toObjId _ (capSpaceFaithful_replyWithCaller caller)
    hNo4
  have hNo5 := modifyObject_noResizeDue Y4 rid.toObjId (replyWithCaller caller) hNo4
  generalize Y4.modifyObject rid.toObjId (replyWithCaller caller) = Y5 at h5 hNo5
  have h6 := CapSpaceAgrees.updateTcb Y5 caller
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) (fun _ => rfl) hNo5
  have hNo6 := updateTcb_noResizeDue Y5 caller
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) hNo5
  generalize Y5.updateTcb caller _ = Y6 at h6 hNo6
  have h7 := CapSpaceAgrees.updateTcb Y6 r (fun t => { t with pendingReceiveReplyCode := 0 })
    (fun _ => rfl) hNo6
  generalize Y6.updateTcb r _ = Y7 at h7
  have h8 := CapSpaceAgrees.of_offRunLinks (removeRunnableOnCore_objectsAgreeOffRunLinks Y7 caller
    core)
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans
    (CapSpaceAgrees.linkReplyWaiter _ caller r))))))))

end SeLe4n.Kernel
