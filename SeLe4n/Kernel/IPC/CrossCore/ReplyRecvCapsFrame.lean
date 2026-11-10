-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.CapTransferDelivered
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvInPlace

/-!
# The reply transfer's frame, for the receive leg after it

seL4's `handleReplyRecv` runs `doReplyTransfer` (whose `doIPCTransfer` installs
the replier's extra capability into the caller's receive slot) and then
`receiveIPC`.  The in-place reply-receive therefore writes the receive leg on
the state the transfer left, and its guard, read on the pre-state, has to hold
there.  This module states what the transfer reads (`capTransferWords`, the
words `capTransferK` hands its continuation, the same on every state that
agrees on buffers and CNodes: `capTransferWords_congr`), when its writes stay
in their slots (`capTransferStoresInPlace`: the receive slot's CNode and the
source slot's CNode each stored where they lie), and what such a transfer
keeps (`transferFrame`): the index, the lifecycle, every key's slot, and every
object but a CNode up to its derivation links.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood

/-! ### The words the transfer reads -/

/-- Everything `capTransferK` hands its continuation, as one record. -/
structure CapTransferWords where
  free : Bool
  dcn : SeLe4n.ObjId
  dsl : SeLe4n.Slot
  n : Nat
  x0 : Capability
  x1 : Capability
  x2 : Capability
  a0 : SeLe4n.ObjId
  b0 : SeLe4n.Slot
  a1 : SeLe4n.ObjId
  b1 : SeLe4n.Slot
  a2 : SeLe4n.ObjId
  b2 : SeLe4n.Slot

/-- The words `capTransferK` reads on `st`. -/
def capTransferWords (st : SystemState) (ep : SeLe4n.ObjId)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId) : CapTransferWords :=
  capTransferK st ep sv sb sroot count rv rb rroot CapTransferWords.mk

/-- **`capTransferK` commutes with any map of its answer.** -/
theorem capTransferK_map {α β : Type} (f : α → β) (st : SystemState) (ep : SeLe4n.ObjId)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId)
    (k : Bool → SeLe4n.ObjId → SeLe4n.Slot → Nat → Capability → Capability → Capability →
      SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId → SeLe4n.Slot → α) :
    f (capTransferK st ep sv sb sroot count rv rb rroot k) =
      capTransferK st ep sv sb sroot count rv rb rroot
        (fun a b c d e g h i j l m n o => f (k a b c d e g h i j l m n o)) := by
  unfold capTransferK transferRefsK extraCapRefK senderCapAddrK
    transferCapsReadK receiveSlotK receivePathSlotK
  simp only [resolveCapAddressKUnrolled_eq, resolveCapAddressK_eq]
  by_cases h1 : hasBufferOf st rv rb = true <;> by_cases h2 : count = 0 <;>
    by_cases h3 : count ≤ 1 <;> by_cases h4 : count ≤ 2 <;>
    simp only [h1, h2, h3, h4, ↓reduceIte, Bool.false_eq_true]
  all_goals (repeat' (first | rfl | split | rw [apply_ite f]))

/-- **`capTransferK` is its continuation at the words it reads.** -/
theorem capTransferK_eq_words {α : Type} (st : SystemState) (ep : SeLe4n.ObjId)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId)
    (k : Bool → SeLe4n.ObjId → SeLe4n.Slot → Nat → Capability → Capability → Capability →
      SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId → SeLe4n.Slot → α) :
    capTransferK st ep sv sb sroot count rv rb rroot k =
      (fun w : CapTransferWords => k w.free w.dcn w.dsl w.n w.x0 w.x1 w.x2 w.a0 w.b0 w.a1 w.b1
        w.a2 w.b2) (capTransferWords st ep sv sb sroot count rv rb rroot) := by
  unfold capTransferWords
  exact (capTransferK_map (fun w : CapTransferWords => k w.free w.dcn w.dsl w.n w.x0 w.x1 w.x2
    w.a0 w.b0 w.a1 w.b1 w.a2 w.b2) st ep sv sb sroot count rv rb rroot CapTransferWords.mk).symm

/-- **The words the transfer reads are the same on states that agree on
buffers and CNodes** (`ipcBufferReadsAgree`). -/
theorem capTransferWords_congr {X st : SystemState} (h : ipcBufferReadsAgree X st)
    (ep : SeLe4n.ObjId) (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId)
    (count : Nat) (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId) :
    capTransferWords X ep sv sb sroot count rv rb rroot =
      capTransferWords st ep sv sb sroot count rv rb rroot := by
  have hC : ∀ id, X.getCNode? id = st.getCNode? id := h.getCNode?
  have hR := resolveCapAddress_congr_getCNode? X st hC
  have hL := lookupSlotCap_congr_getCNode? X st hC
  unfold capTransferWords capTransferK transferRefsK extraCapRefK senderCapAddrK
    transferCapsReadK receiveSlotK receivePathSlotK hasBufferOf bufferWordOf?
  simp only [resolveCapAddressKUnrolled_eq, resolveCapAddressK_eq, h.bufferWordPAddrOf?, h.2, hC,
    hR, hL]

/-! ### What an install in place keeps -/

/-- An object as a reply transfer leaves it: a CNode is any CNode (its slots
and links are the transfer's to write), a thread is its fields off its
derivation links, anything else is itself. -/
def transferView : KernelObject → Option KernelObject
  | .cnode _ => none
  | o => some o.withoutLinks

theorem transferView_setLinkWords (o : KernelObject) (s : SeLe4n.Slot) (f : LinkField) (c w : Nat) :
    transferView (o.setLinkWords s f c w) = transferView o := by
  cases o <;> rfl

theorem transferView_mapCNodeObject (f : CNode → CNode) (o : KernelObject) :
    transferView (SystemState.mapCNodeObject f o) = transferView o := by
  cases o <;> rfl

/-- **A step that keeps what the receive leg's guard reads**: the index, the
lifecycle, every key's slot, and every object as `transferView` reads it. -/
def transferFrame (s' s : SystemState) : Prop :=
  s'.objectIndexSet = s.objectIndexSet ∧ s'.lifecycle = s.lifecycle ∧ s'.objectsKeepFinds s ∧
    ∀ x : SeLe4n.ObjId, (s'.objects[x]?).map transferView = (s.objects[x]?).map transferView

theorem transferFrame.refl (s : SystemState) : transferFrame s s :=
  ⟨rfl, rfl, SystemState.objectsKeepFinds.refl s, fun _ => rfl⟩

theorem transferFrame.trans {a b d : SystemState} (h₂ : transferFrame d b)
    (h₁ : transferFrame b a) : transferFrame d a :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    fun x => (h₂.2.2.2 x).trans (h₁.2.2.2 x)⟩

theorem transferFrame_mapValueAt (s : SystemState) (k : SeLe4n.ObjId)
    (F : KernelObject → KernelObject) (hF : ∀ o, transferView (F o) = transferView o) :
    transferFrame { s with objects := s.objects.mapValueAt k F } s := by
  refine ⟨rfl, rfl, fun _ => RHTable.findsInPlace_mapValueAt _ _ _ _, fun x => ?_⟩
  show ((s.objects.mapValueAt k F)[x]?).map transferView = (s.objects[x]?).map transferView
  simp only [RHTable_getElem?_eq_get?]
  rw [RHTable.get?_mapValueAt]
  split
  · cases s.objects.get? x with
    | none => rfl
    | some o => simp only [Option.map_some, hF]
  · rfl

theorem transferFrame_modifyObject (s : SystemState) (k : SeLe4n.ObjId)
    (F : KernelObject → KernelObject) (hNo : s.objects.noResizeDue)
    (hF : ∀ o, transferView (F o) = transferView o) :
    transferFrame (s.modifyObject k F) s := by
  rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo]
  exact transferFrame_mapValueAt s k F hF

theorem transferFrame_setSlotLinkWords (s : SystemState) (o : SeLe4n.ObjId) (sl : SeLe4n.Slot)
    (f : LinkField) (c w : Nat) (hNo : s.objects.noResizeDue) :
    transferFrame (s.setSlotLinkWords o sl f c w) s := by
  rw [setSlotLinkWords_eq_modifyObject _ _ _ _ _ _ hNo]
  exact transferFrame_modifyObject s o _ hNo (fun x => transferView_setLinkWords x _ _ _ _)

theorem setSlotLinkWords_noResizeDue' (s : SystemState) (o : SeLe4n.ObjId) (sl : SeLe4n.Slot)
    (f : LinkField) (c w : Nat) (hNo : s.objects.noResizeDue) :
    (s.setSlotLinkWords o sl f c w).objects.noResizeDue := by
  rw [setSlotLinkWords_eq_modifyObject _ _ _ _ _ _ hNo, SystemState.modifyObject_eq_mapValueAt _ _ _ hNo]
  exact (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNo

theorem transferFrame_linkAddChild (s : SystemState) (p c : SlotRef)
    (hNo : s.objects.noResizeDue) :
    transferFrame (s.linkAddChild p c) s ∧ (s.linkAddChild p c).objects.noResizeDue := by
  unfold SystemState.linkAddChild
  dsimp only
  have step : ∀ (t : SystemState) (o : SeLe4n.ObjId) (sl : SeLe4n.Slot) (f : LinkField) (c w : Nat),
      transferFrame t s → t.objects.noResizeDue →
      transferFrame (t.setSlotLinkWords o sl f c w) s ∧
        (t.setSlotLinkWords o sl f c w).objects.noResizeDue :=
    fun t o sl f c w h hN => ⟨(transferFrame_setSlotLinkWords t o sl f c w hN).trans h,
      setSlotLinkWords_noResizeDue' t o sl f c w hN⟩
  obtain ⟨h1, n1⟩ := step _ _ _ _ _ _ (transferFrame.refl s) hNo
  obtain ⟨h2, n2⟩ := step _ _ _ _ _ _ h1 n1
  obtain ⟨h3, n3⟩ := step _ _ _ _ _ _ h2 n2
  split
  · exact step _ _ _ _ _ _ h3 n3
  · obtain ⟨h4, n4⟩ := step _ _ _ _ _ _ h3 n3
    exact step _ _ _ _ _ _ h4 n4

theorem transferFrame_cdtAddChild (s : SystemState) (p c : SlotRef) (op : DerivationOp)
    (hNo : s.objects.noResizeDue) :
    transferFrame (s.cdtAddChild p c op) s ∧ (s.cdtAddChild p c op).objects.noResizeDue := by
  unfold SystemState.cdtAddChild
  obtain ⟨h, n⟩ := transferFrame_linkAddChild (s.modifyCdt (·.addEdge p c op)) p c hNo
  exact ⟨h.trans ⟨rfl, rfl, SystemState.objectsKeepFinds.refl s, fun _ => rfl⟩, n⟩

/-- The VSpace-root test, read through `transferView`. -/
@[inline] def notVSpaceRootView : Option KernelObject → Bool
  | some (.vspaceRoot _) => false
  | _ => true

theorem notVSpaceRootView_map (v : Option KernelObject) :
    (match v with | some (.vspaceRoot _) => false | _ => true) =
      ((v.map transferView).map notVSpaceRootView).getD true := by
  cases v with
  | none => rfl
  | some o => cases o <;> rfl

theorem notVSpaceRootAt_of_transferFrame {s' s : SystemState} (h : transferFrame s' s)
    (x : SeLe4n.ObjId) : notVSpaceRootAt s' x = notVSpaceRootAt s x := by
  unfold notVSpaceRootAt
  rw [SystemState.getObject?_eq_getElem, SystemState.getObject?_eq_getElem]
  have a := notVSpaceRootView_map (s'.objects[x]?)
  have b := notVSpaceRootView_map (s.objects[x]?)
  rw [h.2.2.2 x] at a
  exact a.trans b.symm

theorem transferFrame.leaves {s' s : SystemState} (h : transferFrame s' s) {id : SeLe4n.ObjId}
    {ty : KernelObjectType} (hl : storeLeavesIndexAndTypes s id ty = true) :
    storeLeavesIndexAndTypes s' id ty = true :=
  storeLeavesIndexAndTypes_of_frame h.1 h.2.1
    (fun x hx => (notVSpaceRootAt_of_transferFrame h x).trans hx) hl

/-- **A CNode store where the CNode lies** keeps the frame: a CNode is written
in place, anything else is left alone. -/
theorem transferFrame_storeCNodeWith (s : SystemState) (id : SeLe4n.ObjId) (f : CNode → CNode)
    (hNo : s.objects.noResizeDue)
    (hL : (∃ cn, s.objects[id]? = some (.cnode cn)) → storeLeavesIndexAndTypes s id .cnode = true) :
    transferFrame (s.storeCNodeWith id f) s ∧ (s.storeCNodeWith id f).objects.noResizeDue := by
  unfold SystemState.storeCNodeWith
  split
  · next cn hc =>
    rw [if_pos (hL ⟨cn, hc⟩)]
    refine ⟨transferFrame_modifyObject s id _ hNo (transferView_mapCNodeObject f), ?_⟩
    rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo]
    exact (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNo
  · exact ⟨transferFrame.refl s, hNo⟩

/-- The leaves a transfer's CNode stores ask for, as one test: each of `dcn`
and `scn` is no CNode or a CNode stored where it lies. -/
@[inline] def cnodeStoreInPlace (s : SystemState) (id : SeLe4n.ObjId) : Bool :=
  match s.getCNode? id with
  | some _ => storeLeavesIndexAndTypes s id .cnode
  | none => true

theorem cnodeStoreInPlace_imp {s : SystemState} {id : SeLe4n.ObjId}
    (h : cnodeStoreInPlace s id = true) :
    (∃ cn, s.objects[id]? = some (.cnode cn)) → storeLeavesIndexAndTypes s id .cnode = true := by
  rintro ⟨cn, hc⟩
  unfold cnodeStoreInPlace SystemState.getCNode? at h
  simp only [hc] at h
  exact h

/-- The CNode-store test, read through `transferView`: a CNode is the leaves
test, anything else passes. -/
theorem cnodeStoreInPlace_eq (s : SystemState) (id : SeLe4n.ObjId) :
    cnodeStoreInPlace s id =
      (((s.objects[id]?).map transferView).map Option.isSome).elim true
        (fun b => b || storeLeavesIndexAndTypes s id .cnode) := by
  unfold cnodeStoreInPlace SystemState.getCNode?
  cases s.objects[id]? with
  | none => rfl
  | some o => cases o <;> simp [transferView]

theorem transferFrame.cnodeStoreInPlace {s' s : SystemState} (h : transferFrame s' s)
    {id : SeLe4n.ObjId} (hl : cnodeStoreInPlace s id = true) : cnodeStoreInPlace s' id = true := by
  rw [cnodeStoreInPlace_eq] at hl ⊢
  rw [h.2.2.2 id]
  revert hl
  cases ((s.objects[id]?).map transferView).map Option.isSome with
  | none => intro _; rfl
  | some b =>
    simp only [Option.elim, Bool.or_eq_true]
    rintro (hb | hb)
    · exact .inl hb
    · exact .inr (h.leaves hb)

/-- **One install where its CNodes lie** keeps the frame. -/
theorem transferFrame_transferInstallPerform (scn : SeLe4n.ObjId) (ssl : SeLe4n.Slot)
    (dcn : SeLe4n.ObjId) (dsl : SeLe4n.Slot) (cap : Capability) (s : SystemState)
    (hNo : s.objects.noResizeDue) (hD : cnodeStoreInPlace s dcn = true)
    (hS : cnodeStoreInPlace s scn = true) :
    transferFrame (transferInstallPerform scn ssl dcn dsl cap s) s ∧
      (transferInstallPerform scn ssl dcn dsl cap s).objects.noResizeDue := by
  unfold transferInstallPerform
  obtain ⟨f1, n1⟩ := transferFrame_storeCNodeWith s dcn
    (·.insertFields dsl cap.target cap.rights cap.badgeWord cap.badged cap.freeIndex) hNo
    (cnodeStoreInPlace_imp hD)
  obtain ⟨f2, n2⟩ := transferFrame_cdtAddChild _ ⟨scn, ssl⟩ ⟨dcn, dsl⟩ .ipcTransfer n1
  have f12 := f2.trans f1
  refine untypedSourceSetFull_of (P := fun t => transferFrame t s ∧ t.objects.noResizeDue)
    ⟨f12, n2⟩ (fun idx => ?_)
  obtain ⟨f3, n3⟩ := transferFrame_storeCNodeWith _ scn (·.setFreeIndex ssl idx) n2
    (cnodeStoreInPlace_imp (f12.cnodeStoreInPlace hS))
  exact ⟨f3.trans f12, n3⟩

/-! ### The reply's loop: at most one install, at index 0 -/

/-- With the receive slot used up and nothing to unwrap, the loop writes nothing. -/
theorem capStepsApply_noUnwrap_used (ep : SeLe4n.ObjId) (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr)
    (c0 c1 c2 : Capability) (r0c : SeLe4n.ObjId) (r0s : SeLe4n.Slot) (r1c : SeLe4n.ObjId)
    (r1s : SeLe4n.Slot) (r2c : SeLe4n.ObjId) (r2s : SeLe4n.Slot) (dcn : SeLe4n.ObjId)
    (dsl : SeLe4n.Slot) (idx fuel : Nat) (st : SystemState) :
    capStepsApply ep false rv rb c0 c1 c2 r0c r0s r1c r1s r2c r2s dcn dsl idx fuel false st = st := by
  cases fuel with
  | zero => rfl
  | succ f => simp [capStepsApply]

/-- **The reply's loop is at most the install of its first capability.** -/
theorem capStepsApply_noUnwrap_cases (ep : SeLe4n.ObjId) (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr)
    (c0 c1 c2 : Capability) (r0c : SeLe4n.ObjId) (r0s : SeLe4n.Slot) (r1c : SeLe4n.ObjId)
    (r1s : SeLe4n.Slot) (r2c : SeLe4n.ObjId) (r2s : SeLe4n.Slot) (dcn : SeLe4n.ObjId)
    (dsl : SeLe4n.Slot) (fuel : Nat) (free : Bool) (st : SystemState) :
    capStepsApply ep false rv rb c0 c1 c2 r0c r0s r1c r1s r2c r2s dcn dsl 0 fuel free st = st ∨
      (free = true ∧ fuel ≠ 0 ∧
        capStepsApply ep false rv rb c0 c1 c2 r0c r0s r1c r1s r2c r2s dcn dsl 0 fuel free st =
          transferInstallPerform r0c r0s dcn dsl c0 st) := by
  cases fuel with
  | zero => exact .inl rfl
  | succ f =>
    simp only [capStepsApply, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    split
    · next h =>
      right
      simp only [Bool.and_eq_true] at h
      refine ⟨h.1, Nat.succ_ne_zero _, ?_⟩
      rw [capStepsApply_noUnwrap_used]
      rfl
    · exact .inl rfl

/-- **The reply's loop keeps the frame** when its receive slot's CNode and its
first source slot's CNode are stored where they lie. -/
theorem transferFrame_capStepsApply_noUnwrap (ep : SeLe4n.ObjId) (rv : SeLe4n.ObjId)
    (rb : SeLe4n.VAddr) (c0 c1 c2 : Capability) (r0c : SeLe4n.ObjId) (r0s : SeLe4n.Slot)
    (r1c : SeLe4n.ObjId) (r1s : SeLe4n.Slot) (r2c : SeLe4n.ObjId) (r2s : SeLe4n.Slot)
    (dcn : SeLe4n.ObjId) (dsl : SeLe4n.Slot) (fuel : Nat) (free : Bool) (st : SystemState)
    (hNo : st.objects.noResizeDue)
    (hG : free = true → fuel ≠ 0 → cnodeStoreInPlace st dcn = true ∧ cnodeStoreInPlace st r0c = true) :
    transferFrame (capStepsApply ep false rv rb c0 c1 c2 r0c r0s r1c r1s r2c r2s dcn dsl 0 fuel free st) st ∧
      (capStepsApply ep false rv rb c0 c1 c2 r0c r0s r1c r1s r2c r2s dcn dsl 0 fuel free st).objects.noResizeDue := by
  rcases capStepsApply_noUnwrap_cases ep rv rb c0 c1 c2 r0c r0s r1c r1s r2c r2s dcn dsl fuel free st
    with h | ⟨hf, hn, h⟩
  · rw [h]; exact ⟨transferFrame.refl st, hNo⟩
  · rw [h]
    obtain ⟨hD, hS⟩ := hG hf hn
    exact transferFrame_transferInstallPerform r0c r0s dcn dsl c0 st hNo hD hS

/-! ### What the receive leg's guard reads, across the frame -/

/-- The thread an object is, if it is one. -/
@[inline] def tcbOfObject : KernelObject → Option TCB
  | .tcb t => some t
  | _ => none

theorem getTcb?_withoutLinks_eq (s : SystemState) (x : SeLe4n.ThreadId) :
    (s.getTcb? x).map TCB.withoutLinks =
      (((s.objects[x.toObjId]?).map transferView).bind id).bind tcbOfObject := by
  unfold SystemState.getTcb?
  cases s.objects[x.toObjId]? with
  | none => rfl
  | some o => cases o <;> rfl

theorem transferFrame.getTcb? {s' s : SystemState} (h : transferFrame s' s) (x : SeLe4n.ThreadId) :
    (s'.getTcb? x).map TCB.withoutLinks = (s.getTcb? x).map TCB.withoutLinks := by
  rw [getTcb?_withoutLinks_eq, getTcb?_withoutLinks_eq, h.2.2.2]

theorem transferFrame.tcb {s' s : SystemState} (h : transferFrame s' s) {x : SeLe4n.ThreadId}
    {t : TCB} (ht : s.objects[x.toObjId]? = some (.tcb t)) :
    ∃ t', s'.objects[x.toObjId]? = some (.tcb t') ∧ t'.withoutLinks = t.withoutLinks := by
  have e := h.getTcb? x
  rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr ht] at e
  cases e' : s'.getTcb? x with
  | none => rw [e'] at e; cases e
  | some t' =>
    rw [e'] at e
    exact ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mp e', Option.some.inj e⟩

/-- An object the frame reads whole (no CNode, no thread) stays as it is. -/
theorem transferFrame.obj {s' s : SystemState} (h : transferFrame s' s) {x : SeLe4n.ObjId}
    {o : KernelObject} (ho : s.objects[x]? = some o) (hn : transferView o = some o)
    (hc : ∀ o', transferView o' = some o → o' = o) : s'.objects[x]? = some o := by
  have e := h.2.2.2 x
  rw [ho] at e
  cases e' : s'.objects[x]? with
  | none => rw [e'] at e; cases e
  | some o' =>
    rw [e', Option.map_some, Option.map_some, hn] at e
    rw [hc o' (Option.some.inj e)]

theorem transferView_endpoint_back (ep : Endpoint) :
    ∀ o', transferView o' = some (.endpoint ep) → o' = .endpoint ep := by
  intro o' e; cases o' <;> simp_all [transferView, KernelObject.withoutLinks]

theorem transferView_reply_back (r : Reply) :
    ∀ o', transferView o' = some (.reply r) → o' = .reply r := by
  intro o' e; cases o' <;> simp_all [transferView, KernelObject.withoutLinks]

theorem stasherTestAt_eq_view (s : SystemState) (x : SeLe4n.ThreadId) (n : Nat) :
    stasherTestAt s x n = (((s.getTcb? x).map TCB.withoutLinks).map
      (fun t => t.ipcStateCode == 1 && t.pendingReceiveReplyCode == n)).getD false := by
  unfold stasherTestAt
  cases s.getTcb? x <;> rfl

theorem transferFrame.stasherTestAt {s' s : SystemState} (h : transferFrame s' s)
    (x : SeLe4n.ThreadId) (n : Nat) : stasherTestAt s' x n = stasherTestAt s x n := by
  rw [stasherTestAt_eq_view, stasherTestAt_eq_view, h.getTcb? x]

/-- **The receive leg's guard carries across the reply's transfer**: the
endpoint, the receiver and its admission, and `receiveBlocksInPlace`, read on
the state the transfer starts from, hold on the state it leaves. -/
theorem receiveGuard_of_transferFrame {s' s : SystemState} (h : transferFrame s' s)
    {epId : SeLe4n.ObjId} {ep : Endpoint} {tid : SeLe4n.ThreadId} {rt : TCB}
    {tail? : Option SeLe4n.ThreadId} {rid? : Option SeLe4n.ReplyId}
    (hE : s.objects[epId]? = some (.endpoint ep))
    (hR : s.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hG : receiveBlocksInPlace s epId tid tail? rid? = true) :
    s'.objects[epId]? = some (.endpoint ep) ∧
      (∃ rt', s'.objects[tid.toObjId]? = some (.tcb rt') ∧ receiveBlockAdmits rt' = true) ∧
      receiveBlocksInPlace s' epId tid tail? rid? = true := by
  refine ⟨h.obj hE rfl (transferView_endpoint_back ep), ?_, ?_⟩
  · obtain ⟨rt', h1, e⟩ := h.tcb hR
    refine ⟨rt', h1, ?_⟩
    have : receiveBlockAdmits rt' = receiveBlockAdmits rt'.withoutLinks := rfl
    rw [this, e]; exact hA
  · unfold receiveBlocksInPlace at hG ⊢
    simp only [Bool.and_eq_true] at hG ⊢
    obtain ⟨⟨hEnq, hSt⟩, hRec⟩ := hG
    have hV : ∀ x, notVSpaceRootAt s x = true → notVSpaceRootAt s' x = true :=
      fun x hx => (notVSpaceRootAt_of_transferFrame h x).trans hx
    refine ⟨⟨enqueuesInPlace_of_frame _ _ _ h.1 h.2.1 h.2.2.1 hV ?_ hEnq, ?_⟩, ?_⟩
    · intro p hp
      have e := h.getTcb? p
      revert hp e
      cases s.getTcb? p <;> cases s'.getTcb? p <;> simp
    · revert hSt
      cases rid? with
      | none => intro _; rfl
      | some rid =>
        simp only [SystemState.replyStashValid]
        cases hr : s.getReply? rid with
        | none => intro e; cases e
        | some r =>
          intro hs
          have h1 := h.obj ((SystemState.getReply?_eq_some_iff _ _ _).mp hr) rfl
            (transferView_reply_back r)
          rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr h1]
          dsimp only at hs ⊢
          rw [replyStashedAt_eq_stasherTestAt] at hs ⊢
          revert hs
          cases r.stasherCode with
          | zero => exact id
          | succ k => dsimp only; rw [h.stasherTestAt]; exact id
    · revert hRec
      cases rid? with
      | none => exact id
      | some rid =>
        simp only [SeLe4n.ReplyId.optCode, replyRecordsInPlace, Bool.and_eq_true]
        rintro ⟨a, b⟩
        exact ⟨(h.2.2.1 _).trans a, h.leaves b⟩

/-! ### The guard, read before any write -/

/-- `cnodeStoreInPlace` read through `getCNode?`, the index and the lifecycle. -/
theorem cnodeStoreInPlace_eq_getCNode? (s : SystemState) (id : SeLe4n.ObjId) :
    cnodeStoreInPlace s id = (match s.getCNode? id with
      | some _ => s.objectIndexSet.table.holds id () && s.lifecycle.objectTypes.holds id .cnode
      | none => true) := by
  unfold cnodeStoreInPlace storeLeavesIndexAndTypes
  cases h : s.getCNode? id with
  | none => rfl
  | some cn =>
    have hO : s.objects[id]? = some (.cnode cn) := by
      unfold SystemState.getCNode? at h; split at h <;> simp_all
    simp only [hO, Bool.and_true]
    rfl

/-- The CNode-store test is the same on states agreeing on CNodes, the index and the lifecycle. -/
theorem cnodeStoreInPlace_congr {S st : SystemState} (hC : ∀ id, S.getCNode? id = st.getCNode? id)
    (hI : S.objectIndexSet = st.objectIndexSet) (hL : S.lifecycle = st.lifecycle)
    (id : SeLe4n.ObjId) : cnodeStoreInPlace S id = cnodeStoreInPlace st id := by
  rw [cnodeStoreInPlace_eq_getCNode?, cnodeStoreInPlace_eq_getCNode?, hC, hI, hL]

/-- **The reply transfer's stores lie where their CNodes are**, read on the
pre-state `st` over the words the transfer reads (`capTransferK`): it has no
receive slot or nothing to move, or the receive slot's CNode and the first
source slot's CNode are each stored in place (`cnodeStoreInPlace`).  The guard
under which the reply-receive's receive leg may run in place after the reply
leg's transfer (`receiveTransferCaps_reply_transferFrame`). -/
@[inline] def replyTransferStoresInPlace (st : SystemState) (ep : SeLe4n.ObjId)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId) : Bool :=
  capTransferK st ep sv sb sroot count rv rb rroot fun free dcn _ n _ _ _ a0 _ _ _ _ _ =>
    !free || n == 0 || (cnodeStoreInPlace st dcn && cnodeStoreInPlace st a0)

/-- **The specification's reply transfer keeps the frame**: on a state `S`
agreeing with the pre-state `st` on buffers, CNodes, the index and the
lifecycle, the transfer the reply leg runs (no endpoint, the request and the
receive side read on `st`) leaves a state in `transferFrame` of `S`, when
`replyTransferStoresInPlace` holds on `st`. -/
theorem receiveTransferCaps_reply_transferFrame {S st : SystemState}
    (hAg : ipcBufferReadsAgree S st) (hI : S.objectIndexSet = st.objectIndexSet)
    (hL : S.lifecycle = st.lifecycle) (hNo : S.objects.noResizeDue) (ep : SeLe4n.ObjId)
    (stcb rt : TCB) (count : Nat)
    (hG : replyTransferStoresInPlace st ep stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot count
      rt.vspaceRoot rt.ipcBuffer rt.cspaceRoot = true)
    {s : CapTransferSummary} {S' : SystemState}
    (hT : receiveTransferCaps (frameCapRequestOf st stcb count) none (capTargetOf st rt) S =
      .ok (s, S')) :
    transferFrame S' S ∧ S'.objects.noResizeDue := by
  rw [← hAg.frameCapRequestOf, ← hAg.capTargetOf] at hT
  have hK := capTransferK_eq_at S ep false stcb count rt (fun _ Y => Y)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte, hT] at hK
  rw [capTransferK_eq_words, capTransferWords_congr hAg] at hK
  unfold replyTransferStoresInPlace at hG
  rw [capTransferK_eq_words] at hG
  generalize capTransferWords st ep stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot count
    rt.vspaceRoot rt.ipcBuffer rt.cspaceRoot = w at hK hG
  dsimp only at hK hG
  rw [← hK]
  have hC := cnodeStoreInPlace_congr (S := S) (st := st) hAg.getCNode? hI hL
  refine transferFrame_capStepsApply_noUnwrap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S hNo
    (fun hf hn => ?_)
  rw [hf] at hG
  have hn' : (w.n == 0) = false := by simpa using hn
  simp only [Bool.not_true, Bool.false_or, hn', Bool.and_eq_true] at hG
  exact ⟨(hC _).trans hG.1, (hC _).trans hG.2⟩

end SeLe4n.Kernel
