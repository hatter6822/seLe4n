-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.Fault
import SeLe4n.Kernel.Architecture.PageTeardownClears

/-!
# The records every kernel entry carries, and the frame that keeps them

WS-ZA ZA6.37.  Three invariants describe records the kernel keeps beside the
objects they relate, and each reads a small view of the store:

* the reply-waiter queues (`SystemState.replyWaitersConsistent`) read every
  TCB's reply view (`TCB.replyView`);
* the fault records (`SystemState.faultRecordParked`: a thread carrying a fault
  is fault-blocked or `.Inactive`) read every TCB's IPC state, thread state and
  whether it carries a fault;
* the address-space records (`teardownWellFormed`: the object and ASID tables
  well formed and the VSpace bundle) read the ASID table and the VSpace roots;
* the physical-address width the machine reports stays within the 52-bit bound
  the VSpace bundle's address check assumes
  (`SystemState.physicalAddressWidthWithinBound`), so a map checked against the
  machine's own width keeps the bundle.

`SystemState.kernelRecordsSound` is the four together.  A step that keeps every
slot's record view (`recordViewOf`), the ASID table and the machine's
physical-address width keeps it
(`RecordsFrame.preserves`), whatever else it writes: a CNode, an endpoint, a
notification, a scheduling context, a register file, a run-queue link, the
scheduler record.  The steps that write a view — the IPC arms, the cancellations,
the suspend and resume, the fault delivery, the retype, the VSpace writes and the
teardown — keep it by their own theorems, and a kernel entry chains the two
kinds as a `RecordsStage`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  The views
-- ============================================================================

/-- What the carried records read of one TCB: its reply view, its IPC state, its
thread state, whether it carries a fault, its two notification-queue links,
which notification label coherence reads beside the IPC state, and its two
endpoint-queue links, which the endpoint queue's link labels read (the links as
their scalar codes). -/
structure TcbRecordView where
  reply : ReplyView
  ipc : ThreadIpcState
  state : ThreadState
  faulted : Bool
  ntfnPrev : Nat
  ntfnNext : Nat
  queuePrev : Nat
  queueNext : Nat

/-- A TCB's record view. -/
def _root_.SeLe4n.Model.TCB.recordView (t : TCB) : TcbRecordView :=
  ⟨t.replyView, t.ipcState, t.threadState, t.pendingFault.isSome, t.ntfnPrevCode, t.ntfnNextCode,
    t.queuePrevCode, t.queueNextCode⟩

/-- What the address-space records read of one VSpace root: its ASID, its
translations and its mapping epochs (the root's half of
`KernelObject.mappingView`). -/
abbrev RootView :=
  SeLe4n.ASID × RobinHood.RHTable SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions) ×
    RobinHood.RHTable SeLe4n.VAddr Nat

/-- A slot's address-space view: a root's `RootView`, nothing of any other object. -/
def rootViewOf (o : Option KernelObject) : Option RootView :=
  o.bind fun x => x.mappingView.1

/-- What the carried records read of one notification: its bound thread, its
wait queue's head and its tail, as their scalar codes (the fields notification
label coherence reads). -/
abbrev NtfnRecordView := Nat × Nat × Nat

/-- A notification's record view. -/
def _root_.SeLe4n.Model.Notification.recordView (n : Notification) : NtfnRecordView :=
  (n.boundTCBCode, n.waitHeadCode, n.waitTailCode)

/-- What the carried records read of one endpoint: its send queue's head and
tail and its receive queue's head and tail, as their scalar codes (the queue
ends the endpoint queue's link labels read). -/
abbrev EndpointRecordView := Nat × Nat × Nat × Nat

/-- An endpoint's record view. -/
def _root_.SeLe4n.Model.Endpoint.recordView (e : Endpoint) : EndpointRecordView :=
  (e.sendHeadCode, e.sendTailCode, e.recvHeadCode, e.recvTailCode)

/-- What the carried records read of one object slot, by its kind. -/
abbrev RecordView := TcbRecordView ⊕ RootView ⊕ NtfnRecordView ⊕ EndpointRecordView

/-- What the carried records read of one object slot: a TCB's record view, a
VSpace root's ASID, translations and epochs, a notification's record view or an
endpoint's; nothing of any other object. -/
def recordViewOf : Option KernelObject → Option RecordView
  | some (.tcb t) => some (.inl t.recordView)
  | some (.vspaceRoot r) => some (.inr (.inl (r.asid, r.mappings, r.mappingEpochs)))
  | some (.notification n) => some (.inr (.inr (.inl n.recordView)))
  | some (.endpoint e) => some (.inr (.inr (.inr e.recordView)))
  | _ => none

@[simp] theorem recordViewOf_tcb (t : TCB) :
    recordViewOf (some (.tcb t)) = some (.inl t.recordView) := rfl

@[simp] theorem recordViewOf_vspaceRoot (r : VSpaceRoot) :
    recordViewOf (some (.vspaceRoot r)) = some (.inr (.inl (r.asid, r.mappings, r.mappingEpochs))) :=
  rfl

@[simp] theorem recordViewOf_notification (n : Notification) :
    recordViewOf (some (.notification n)) = some (.inr (.inr (.inl n.recordView))) := rfl

@[simp] theorem recordViewOf_endpoint (e : Endpoint) :
    recordViewOf (some (.endpoint e)) = some (.inr (.inr (.inr e.recordView))) := rfl

/-- The address-space half of a record view. -/
def recordRootView? : RecordView → Option RootView
  | .inr (.inl r) => some r
  | _ => none

/-- The address-space view is read off the record view. -/
theorem rootViewOf_eq_bind (o : Option KernelObject) :
    rootViewOf o = (recordViewOf o).bind recordRootView? := by
  cases o with
  | none => rfl
  | some x => cases x <;> rfl

/-- A slot whose address-space view is `v` holds a root with that view. -/
theorem root_of_rootViewOf {o : Option KernelObject} {v : RootView} (h : rootViewOf o = some v) :
    ∃ r, o = some (.vspaceRoot r) ∧ (r.asid, r.mappings, r.mappingEpochs) = v := by
  cases o with
  | none => cases h
  | some x =>
    cases x <;> simp only [rootViewOf, Option.bind_some, KernelObject.mappingView,
      reduceCtorEq, Option.some.injEq] at h
    exact ⟨_, rfl, h⟩

/-- **A root of one store is a root of the other**, with the same ASID,
translations and epochs, when the two stores' address-space views agree. -/
theorem root_of_rootViews {a b : SystemState}
    (hV : ∀ k : SeLe4n.ObjId, rootViewOf b.objects[k]? = rootViewOf a.objects[k]?)
    {k : SeLe4n.ObjId} {r : VSpaceRoot} (h : a.objects[k]? = some (.vspaceRoot r)) :
    ∃ q, b.objects[k]? = some (.vspaceRoot q) ∧ q.asid = r.asid ∧ q.mappings = r.mappings ∧
      q.mappingEpochs = r.mappingEpochs := by
  have hk := hV k
  rw [h] at hk
  obtain ⟨q, hq, he⟩ := root_of_rootViewOf hk
  simp only [Prod.mk.injEq] at he
  exact ⟨q, hq, he.1, he.2.1, he.2.2⟩

/-- **A step that keeps the ASID table and every root's address-space view keeps
the state well formed**: the VSpace bundle reads a root's ASID, translations and
epochs only, so a step may rewrite a root's table slots or base. -/
theorem teardownWellFormed_of_rootViews {st st' : SystemState} (hInv : st'.objects.invExt)
    (hA : st'.asidTable = st.asidTable)
    (hV : ∀ k : SeLe4n.ObjId, rootViewOf st'.objects[k]? = rootViewOf st.objects[k]?)
    (h : teardownWellFormed st) : teardownWellFormed st' := by
  obtain ⟨-, h2, h3⟩ := h
  refine ⟨hInv, hA ▸ h2, ?_⟩
  unfold Architecture.vspaceInvariantBundle Architecture.vspaceAsidRootsUnique
    Architecture.vspaceRootNonOverlap Architecture.asidTableConsistent
    Architecture.wxExclusiveInvariant Architecture.boundedAddressTranslation
    Architecture.vspaceCrossAsidIsolation Architecture.canonicalAddressInvariant
    Architecture.vspaceMappingsWellFormed at h3 ⊢
  obtain ⟨c1, c2, ⟨c3a, c3b⟩, c4, c5, c6, c7, c8⟩ := h3
  have B : ∀ {k : SeLe4n.ObjId} {r : VSpaceRoot}, st'.objects[k]? = some (KernelObject.vspaceRoot r) → ∃ q : VSpaceRoot,
      st.objects[k]? = some (KernelObject.vspaceRoot q) ∧ q.asid = r.asid ∧ q.mappings = r.mappings ∧
        q.mappingEpochs = r.mappingEpochs :=
    fun h => root_of_rootViews (fun k => (hV k).symm) h
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro o1 o2 r1 r2 h1 h2 he
    obtain ⟨q1, hq1, ha1, -, -⟩ := B h1
    obtain ⟨q2, hq2, ha2, -, -⟩ := B h2
    exact c1 o1 o2 q1 q2 hq1 hq2 (by rw [ha1, ha2]; exact he)
  · intro o r h
    obtain ⟨q, hq, -, hm, -⟩ := B h
    have := c2 o q hq
    unfold VSpaceRoot.noVirtualOverlap VSpaceRoot.lookup at this ⊢
    rw [← hm]; exact this
  · intro a o hT
    rw [hA] at hT
    obtain ⟨r, hr, ha⟩ := c3a a o hT
    obtain ⟨q, hq, hqa, -, -⟩ := root_of_rootViews hV hr
    exact ⟨q, hq, hqa.trans ha⟩
  · intro o r h
    obtain ⟨q, hq, ha, -, -⟩ := B h
    rw [hA, ← ha]; exact c3b o q hq
  · intro o r v p q h hm
    obtain ⟨x, hx, -, hmx, -⟩ := B h
    exact c4 o x v p q hx (hmx ▸ hm)
  · intro o r v p q h hm
    obtain ⟨x, hx, -, hmx, -⟩ := B h
    exact c5 o x v p q hx (hmx ▸ hm)
  · intro o1 o2 r1 r2 h1 h2 hne he
    obtain ⟨q1, hq1, ha1, -, -⟩ := B h1
    obtain ⟨q2, hq2, ha2, -, -⟩ := B h2
    exact c6 o1 o2 q1 q2 hq1 hq2 hne (by rw [ha1, ha2]; exact he)
  · intro o r v p q h hm
    obtain ⟨x, hx, -, hmx, -⟩ := B h
    exact c7 o x v p q hx (hmx ▸ hm)
  · intro o r h
    obtain ⟨x, hx, -, hm, he⟩ := B h
    rw [← hm, ← he]; exact c8 o x hx

/-- The machine's physical-address width is within the 52-bit bound the VSpace
bundle's address check assumes (`Architecture.physicalAddressBound`).  The started boot
establishes it (the checked boot refuses a wider configuration). -/
def _root_.SeLe4n.Model.SystemState.physicalAddressWidthWithinBound (st : SystemState) : Prop :=
  st.machine.physicalAddressWidth ≤ 52

/-- **The records every kernel entry carries.** -/
def _root_.SeLe4n.Model.SystemState.kernelRecordsSound (st : SystemState) : Prop :=
  teardownWellFormed st ∧ st.replyWaitersConsistent ∧ st.faultRecordParked ∧
    st.physicalAddressWidthWithinBound

/-- An address below the machine's width is below the bundle's bound. -/
theorem _root_.SeLe4n.Model.SystemState.physicalAddressWidthWithinBound.lt_bound
    {st : SystemState} (h : st.physicalAddressWidthWithinBound) {n : Nat}
    (hn : n < 2 ^ st.machine.physicalAddressWidth) : n < Architecture.physicalAddressBound :=
  by unfold Architecture.physicalAddressBound; exact Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) h)

/-- A step that keeps the machine's width keeps the bound. -/
theorem _root_.SeLe4n.Model.SystemState.physicalAddressWidthWithinBound.of_eq
    {st st' : SystemState}
    (hW : st'.machine.physicalAddressWidth = st.machine.physicalAddressWidth)
    (h : st.physicalAddressWidthWithinBound) : st'.physicalAddressWidthWithinBound := by
  unfold SystemState.physicalAddressWidthWithinBound; rw [hW]; exact h

namespace KernelRecords

theorem objects_invExt {st : SystemState} (h : st.kernelRecordsSound) : st.objects.invExt :=
  h.1.1

/-- A slot whose view is a TCB's holds a TCB with that view. -/
theorem tcb_of_view {o : Option KernelObject} {v : TcbRecordView}
    (h : recordViewOf o = some (.inl v)) : ∃ t, o = some (.tcb t) ∧ t.recordView = v := by
  cases o with
  | none => cases h
  | some o =>
    cases o <;> simp only [recordViewOf, Option.some.injEq, reduceCtorEq, Sum.inl.injEq] at h
    exact ⟨_, rfl, h⟩

/-- A slot whose view is no TCB's holds no reply view: it holds a root, a
notification or an endpoint. -/
theorem objReplyView_none_of_view {o : Option KernelObject}
    {v : RootView ⊕ NtfnRecordView ⊕ EndpointRecordView}
    (h : recordViewOf o = some (.inr v)) : objReplyView o = none := by
  cases o with
  | none => cases h
  | some o =>
    cases o <;> simp only [recordViewOf, Option.some.injEq, reduceCtorEq] at h <;> rfl

/-- The reply view of a slot is read off its record view. -/
theorem objReplyView_eq_of_view {a b : Option KernelObject}
    (h : recordViewOf a = recordViewOf b) : objReplyView a = objReplyView b := by
  cases ha : recordViewOf a with
  | none =>
    have hb : recordViewOf b = none := h ▸ ha
    have hNa : objReplyView a = none := by
      cases a with
      | none => rfl
      | some o => cases o <;> simp_all [recordViewOf, objReplyView]
    have hNb : objReplyView b = none := by
      cases b with
      | none => rfl
      | some o => cases o <;> simp_all [recordViewOf, objReplyView]
    rw [hNa, hNb]
  | some v =>
    rw [ha] at h
    cases v with
    | inl v =>
      obtain ⟨ta, rfl, hva⟩ := tcb_of_view ha
      obtain ⟨tb, rfl, hvb⟩ := tcb_of_view h.symm
      have : ta.replyView = tb.replyView := by
        have := congrArg TcbRecordView.reply (hva.trans hvb.symm); exact this
      simp [objReplyView, this]
    | inr r =>
      rw [objReplyView_none_of_view ha, objReplyView_none_of_view h.symm]

end KernelRecords

/-- The register writes keep the machine's physical-address width. -/
theorem _root_.SeLe4n.MachineState.modifyRegsOnCore_physicalAddressWidth (ms : MachineState)
    (c : Concurrency.CoreId) (f : RegisterFile → RegisterFile) :
    (ms.modifyRegsOnCore c f).physicalAddressWidth = ms.physicalAddressWidth := rfl

theorem _root_.SeLe4n.MachineState.setRegsOnCore_physicalAddressWidth (ms : MachineState)
    (c : Concurrency.CoreId) (r : RegisterFile) :
    (ms.setRegsOnCore c r).physicalAddressWidth = ms.physicalAddressWidth := rfl

-- ============================================================================
-- §2  The frame
-- ============================================================================

/-- **A step that keeps the records' reads**: every slot's record view, the
ASID table and the machine's physical-address width, with the store's
invariant. -/
structure RecordsFrame (st st' : SystemState) : Prop where
  views : ∀ k : SeLe4n.ObjId, recordViewOf st'.objects[k]? = recordViewOf st.objects[k]?
  asid : st'.asidTable = st.asidTable
  invExt : st'.objects.invExt
  width : st'.machine.physicalAddressWidth = st.machine.physicalAddressWidth

namespace RecordsFrame

theorem refl {st : SystemState} (hInv : st.objects.invExt) : RecordsFrame st st :=
  ⟨fun _ => rfl, rfl, hInv, rfl⟩

theorem trans {a b c : SystemState} (h₁ : RecordsFrame a b) (h₂ : RecordsFrame b c) :
    RecordsFrame a c :=
  ⟨fun k => (h₂.views k).trans (h₁.views k), h₂.asid.trans h₁.asid, h₂.invExt,
    h₂.width.trans h₁.width⟩

theorem of_objects_eq {st st' : SystemState} (hInv : st.objects.invExt)
    (hO : st'.objects = st.objects) (hA : st'.asidTable = st.asidTable)
    (hW : st'.machine.physicalAddressWidth = st.machine.physicalAddressWidth := by
      first | rfl | assumption) : RecordsFrame st st' :=
  ⟨fun k => by rw [hO], hA, hO ▸ hInv, hW⟩

theorem of_eq {st st' : SystemState} (hInv : st.objects.invExt) (h : st' = st) :
    RecordsFrame st st' := by subst h; exact refl hInv

/-- A state with another's objects and ASID table is in the same frame. -/
theorem congr {st s s' : SystemState} (h : RecordsFrame st s) (hO : s'.objects = s.objects)
    (hA : s'.asidTable = s.asidTable)
    (hW : s'.machine.physicalAddressWidth = s.machine.physicalAddressWidth := by
      first | rfl | assumption) : RecordsFrame st s' :=
  ⟨fun k => by rw [hO]; exact h.views k, hA.trans h.asid, hO ▸ h.invExt, hW.trans h.width⟩

/-- The record views of every thread are the frame's. -/
theorem getTcb?_view {st st' : SystemState} (F : RecordsFrame st st') {t : SeLe4n.ThreadId}
    {tcb' : TCB} (h : st'.getTcb? t = some tcb') :
    ∃ tcb, st.getTcb? t = some tcb ∧ tcb.recordView = tcb'.recordView := by
  have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp h
  have hv := F.views t.toObjId
  rw [hO, recordViewOf_tcb] at hv
  obtain ⟨tcb, hT, hEq⟩ := KernelRecords.tcb_of_view hv.symm
  exact ⟨tcb, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT, hEq⟩

theorem replyViews {st st' : SystemState} (F : RecordsFrame st st') :
    st'.replyViews = st.replyViews := by
  funext k
  unfold SystemState.replyViews SystemState.getObject?
  simp only [RHTable_getElem?_eq_get?]
  exact KernelRecords.objReplyView_eq_of_view (F.views k)

theorem rootViews {st st' : SystemState} (F : RecordsFrame st st') (k : SeLe4n.ObjId) :
    rootViewOf st'.objects[k]? = rootViewOf st.objects[k]? := by
  rw [rootViewOf_eq_bind, rootViewOf_eq_bind, F.views k]

theorem faultRecordParked {st st' : SystemState} (F : RecordsFrame st st')
    (h : st.faultRecordParked) : st'.faultRecordParked := by
  intro t tcb' hT hF
  obtain ⟨tcb, hT0, hv⟩ := F.getTcb?_view hT
  simp only [TCB.recordView, TcbRecordView.mk.injEq] at hv
  obtain ⟨-, hIpc, hTs, hFl, -, -, -, -⟩ := hv
  rw [← hIpc, ← hTs]
  exact h t tcb hT0 (hFl ▸ hF)

/-- **A step that keeps the records' reads keeps the records.** -/
theorem preserves {st st' : SystemState} (F : RecordsFrame st st')
    (h : st.kernelRecordsSound) : st'.kernelRecordsSound :=
  ⟨teardownWellFormed_of_rootViews F.invExt F.asid F.rootViews h.1,
   SystemState.replyWaitersConsistent.of_views F.replyViews h.2.1,
   F.faultRecordParked h.2.2.1, h.2.2.2.of_eq F.width⟩

end RecordsFrame

-- ============================================================================
-- §2b  The core frame: the records' reads without the queues
-- ============================================================================

/-- A TCB's record view without its notification-queue and endpoint-queue
links. -/
def TcbRecordView.core (v : TcbRecordView) : TcbRecordView :=
  { v with ntfnPrev := 0, ntfnNext := 0, queuePrev := 0, queueNext := 0 }

/-- A record view without the queues: a TCB's without its links, a
notification's and an endpoint's erased. -/
def recordCoreView : RecordView → RecordView
  | .inl v => .inl v.core
  | .inr (.inl r) => .inr (.inl r)
  | .inr (.inr (.inl _)) => .inr (.inr (.inl (0, 0, 0)))
  | .inr (.inr (.inr _)) => .inr (.inr (.inr (0, 0, 0, 0)))

/-- **What kernel records read of one slot**: its record view without the
queues (the TCB's four links, the notification's bound thread and queue ends,
the endpoint's queue ends), which only the queue label facts read. -/
def recordCoreViewOf (o : Option KernelObject) : Option RecordView :=
  (recordViewOf o).map recordCoreView

@[simp] theorem recordCoreViewOf_tcb (t : TCB) :
    recordCoreViewOf (some (.tcb t)) = some (.inl t.recordView.core) := rfl

@[simp] theorem recordCoreViewOf_notification (n : Notification) :
    recordCoreViewOf (some (.notification n)) = some (.inr (.inr (.inl (0, 0, 0)))) := rfl

@[simp] theorem recordCoreViewOf_endpoint (e : Endpoint) :
    recordCoreViewOf (some (.endpoint e)) = some (.inr (.inr (.inr (0, 0, 0, 0)))) := rfl

theorem recordCoreViewOf_congr {a b : Option KernelObject} (h : recordViewOf a = recordViewOf b) :
    recordCoreViewOf a = recordCoreViewOf b := by
  unfold recordCoreViewOf; rw [h]

/-- The address-space view is read off the core view. -/
theorem rootViewOf_eq_core_bind (o : Option KernelObject) :
    rootViewOf o = (recordCoreViewOf o).bind recordRootView? := by
  cases o with
  | none => rfl
  | some x => cases x <;> rfl

/-- The reply view of a slot is read off its core view. -/
theorem objReplyView_eq_of_coreView {a b : Option KernelObject}
    (h : recordCoreViewOf a = recordCoreViewOf b) : objReplyView a = objReplyView b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some y => cases y <;> simp_all [recordCoreViewOf, recordViewOf, objReplyView, recordCoreView]
  | some x =>
    cases b with
    | none => cases x <;> simp_all [recordCoreViewOf, recordViewOf, objReplyView, recordCoreView]
    | some y =>
      cases x <;> cases y <;>
        simp_all [recordCoreViewOf, recordViewOf, objReplyView, recordCoreView, TCB.recordView,
          TcbRecordView.core]

/-- **A step that keeps the kernel records' reads**: every slot's core view,
the ASID table and the machine's physical-address width, with the store's
invariant.  The frame of a write to a notification queue, an endpoint queue or
a thread's queue links (`RecordsFrame` keeps those too). -/
structure RecordsCoreFrame (st st' : SystemState) : Prop where
  views : ∀ k : SeLe4n.ObjId, recordCoreViewOf st'.objects[k]? = recordCoreViewOf st.objects[k]?
  asid : st'.asidTable = st.asidTable
  invExt : st'.objects.invExt
  width : st'.machine.physicalAddressWidth = st.machine.physicalAddressWidth

/-- A frame keeps the core views. -/
theorem RecordsFrame.core {st st' : SystemState} (F : RecordsFrame st st') :
    RecordsCoreFrame st st' :=
  ⟨fun k => recordCoreViewOf_congr (F.views k), F.asid, F.invExt, F.width⟩

namespace RecordsCoreFrame

theorem refl {st : SystemState} (hInv : st.objects.invExt) : RecordsCoreFrame st st :=
  ⟨fun _ => rfl, rfl, hInv, rfl⟩

theorem trans {a b c : SystemState} (h₁ : RecordsCoreFrame a b) (h₂ : RecordsCoreFrame b c) :
    RecordsCoreFrame a c :=
  ⟨fun k => (h₂.views k).trans (h₁.views k), h₂.asid.trans h₁.asid, h₂.invExt,
    h₂.width.trans h₁.width⟩

/-- The core record views of every thread are the frame's. -/
theorem getTcb?_view {st st' : SystemState} (F : RecordsCoreFrame st st') {t : SeLe4n.ThreadId}
    {tcb' : TCB} (h : st'.getTcb? t = some tcb') :
    ∃ tcb, st.getTcb? t = some tcb ∧ tcb.recordView.core = tcb'.recordView.core := by
  have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp h
  have hv := F.views t.toObjId
  rw [hO, recordCoreViewOf_tcb] at hv
  cases hT : st.objects[t.toObjId]? with
  | none => rw [hT] at hv; cases hv
  | some o =>
    rw [hT] at hv
    cases o <;> simp [recordCoreViewOf, recordViewOf, recordCoreView] at hv
    exact ⟨_, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT, hv.symm⟩

/-- The kernel records' reads of a thread are the core view's. -/
theorem _root_.SeLe4n.Kernel.TcbRecordView.core_eq {x y : TCB}
    (h : x.recordView.core = y.recordView.core) :
    x.replyView = y.replyView ∧ x.ipcState = y.ipcState ∧ x.threadState = y.threadState ∧
      x.pendingFault.isSome = y.pendingFault.isSome := by
  simp only [TCB.recordView, TcbRecordView.core, TcbRecordView.mk.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem replyViews {st st' : SystemState} (F : RecordsCoreFrame st st') :
    st'.replyViews = st.replyViews := by
  funext k
  unfold SystemState.replyViews SystemState.getObject?
  simp only [RHTable_getElem?_eq_get?]
  exact objReplyView_eq_of_coreView (F.views k)

theorem rootViews {st st' : SystemState} (F : RecordsCoreFrame st st') (k : SeLe4n.ObjId) :
    rootViewOf st'.objects[k]? = rootViewOf st.objects[k]? := by
  rw [rootViewOf_eq_core_bind, rootViewOf_eq_core_bind, F.views k]

theorem faultRecordParked {st st' : SystemState} (F : RecordsCoreFrame st st')
    (h : st.faultRecordParked) : st'.faultRecordParked := by
  intro t tcb' hT hF
  obtain ⟨tcb, hT0, hv⟩ := F.getTcb?_view hT
  obtain ⟨-, hIpc, hTs, hFl⟩ := TcbRecordView.core_eq hv
  rw [← hIpc, ← hTs]
  exact h t tcb hT0 (hFl ▸ hF)

/-- **A step that keeps the kernel records' reads keeps the records.** -/
theorem preserves {st st' : SystemState} (F : RecordsCoreFrame st st')
    (h : st.kernelRecordsSound) : st'.kernelRecordsSound :=
  ⟨teardownWellFormed_of_rootViews F.invExt F.asid F.rootViews h.1,
   SystemState.replyWaitersConsistent.of_views F.replyViews h.2.1,
   F.faultRecordParked h.2.2.1, h.2.2.2.of_eq F.width⟩

end RecordsCoreFrame

-- ============================================================================
-- §3  The stage
-- ============================================================================

/-- **A step that carries the records**: the unit a kernel entry chains. -/
def RecordsStage (st st' : SystemState) : Prop :=
  st.kernelRecordsSound → st'.kernelRecordsSound

namespace RecordsStage

theorem refl (st : SystemState) : RecordsStage st st := id

theorem trans {a b c : SystemState} (h₁ : RecordsStage a b) (h₂ : RecordsStage b c) :
    RecordsStage a c := h₂ ∘ h₁

theorem of_frame {st st' : SystemState} (F : RecordsFrame st st') : RecordsStage st st' :=
  F.preserves

theorem of_coreFrame {st st' : SystemState} (F : RecordsCoreFrame st st') : RecordsStage st st' :=
  F.preserves

theorem of_eq {st st' : SystemState} (h : st' = st) : RecordsStage st st' := h ▸ refl st

end RecordsStage


-- ============================================================================
-- §4  The primitive writes
-- ============================================================================

namespace RecordsFrame

/-- A raw insert whose object keeps its slot's view, over a slot that held no
root (the ASID table is untouched). -/
theorem insert {st : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hV : recordViewOf (some o) = recordViewOf st.objects[k]?) :
    RecordsFrame st { st with objects := st.objects.insert k o } := by
  refine ⟨fun x => ?_, rfl, RHTable_insert_preserves_invExt _ _ _ hInv, rfl⟩
  show recordViewOf (st.objects.insert k o)[x]? = _
  simp only [RHTable_getElem?_eq_get?] at hV ⊢
  by_cases hx : k = x
  · subst hx; rw [RobinHood.RHTable.getElem?_insert_self _ _ _ hInv]; exact hV
  · rw [RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hx (eq_of_beq hb)) hInv]

/-- A store whose object keeps its slot's view and is no root. -/
theorem storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (h : storeObject k o st = .ok ((), st'))
    (hV : recordViewOf (some o) = recordViewOf st.objects[k]?)
    (hNR : ∀ r, o ≠ .vspaceRoot r) : RecordsFrame st st' := by
  refine ⟨fun x => ?_, ?_, storeObject_preserves_objects_invExt st st' k o hInv h,
    by rw [storeObject_machine_eq st st' k o h]⟩
  · by_cases hx : x = k
    · subst hx; rw [storeObject_objects_eq st st' x o hInv h]; exact hV
    · rw [storeObject_objects_ne st st' k x o hx hInv h]
  · rw [storeObject_asidTable_non_vspaceRoot st st' k o hNR h]
    split
    · rename_i r hr
      rw [hr, recordViewOf_vspaceRoot] at hV
      cases o <;> simp [recordViewOf] at hV
      exact absurd rfl (hNR _)
    · rfl

/-- A typed rewrite whose object keeps its slot's view. -/
theorem rewriteObject {st : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hAdm : st.rewriteAdmissible k o) (hInv : st.objects.invExt)
    (hV : recordViewOf (some o) = recordViewOf st.objects[k]?) :
    RecordsFrame st (st.rewriteObject k o hAdm) :=
  insert hInv hV

/-- **A TCB write that keeps every record view.** -/
theorem updateTcb (st : SystemState) (t : SeLe4n.ThreadId) {f : TCB → TCB}
    (hInv : st.objects.invExt) (hf : ∀ x, (f x).recordView = x.recordView) :
    RecordsFrame st (st.updateTcb t f) := by
  cases hT : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact refl hInv
  | some x =>
    rw [SystemState.updateTcb_eq_of_some hT]
    exact insert hInv (by rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hT]; simp [hf])

/-- The checked TCB write, when it keeps every record view. -/
theorem modifyTcb {st st' : SystemState} {t : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (hf : ∀ x, (f x).recordView = x.recordView)
    (h : _root_.SeLe4n.Kernel.modifyTcb st t f = .ok st') : RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.modifyTcb at h
  split at h
  · cases h
  · rename_i tcb hL
    split at h
    · cases h
    · rename_i st1 hS
      cases h
      have hT : st.objects[t.toObjId]? = some (.tcb tcb) := lookupTcb_some_objects st t tcb hL
      exact storeObject hInv hS (by rw [hT]; simp [hf]) (fun _ => by simp)

end RecordsFrame

namespace RecordsCoreFrame

/-- A store whose object keeps its slot's core view and is no root. -/
theorem storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (h : storeObject k o st = .ok ((), st'))
    (hV : recordCoreViewOf (some o) = recordCoreViewOf st.objects[k]?)
    (hNR : ∀ r, o ≠ .vspaceRoot r) : RecordsCoreFrame st st' := by
  refine ⟨fun x => ?_, ?_, storeObject_preserves_objects_invExt st st' k o hInv h,
    by rw [storeObject_machine_eq st st' k o h]⟩
  · by_cases hx : x = k
    · subst hx; rw [storeObject_objects_eq st st' x o hInv h]; exact hV
    · rw [storeObject_objects_ne st st' k x o hx hInv h]
  · rw [storeObject_asidTable_non_vspaceRoot st st' k o hNR h]
    split
    · rename_i r hr
      rw [hr] at hV
      cases o <;> simp [recordCoreViewOf, recordViewOf, recordCoreView] at hV
      exact absurd rfl (hNR _)
    · rfl

/-- A notification stored over a notification. -/
theorem storeNotification {st st' : SystemState} {nid : SeLe4n.ObjId} {n n' : Notification}
    (hInv : st.objects.invExt) (hObj : st.objects[nid]? = some (.notification n))
    (h : SeLe4n.Model.storeObject nid (.notification n') st = .ok ((), st')) :
    RecordsCoreFrame st st' :=
  storeObject hInv h (by rw [hObj]; rfl) (fun _ h => by cases h)

/-- **The checked TCB write**, when it keeps every core view. -/
theorem modifyTcb {st st' : SystemState} {t : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (hf : ∀ x, (f x).recordView.core = x.recordView.core)
    (h : _root_.SeLe4n.Kernel.modifyTcb st t f = .ok st') : RecordsCoreFrame st st' := by
  unfold _root_.SeLe4n.Kernel.modifyTcb at h
  split at h
  · cases h
  · rename_i tcb hL
    split at h
    · cases h
    · rename_i st1 hS
      cases h
      have hT : st.objects[t.toObjId]? = some (.tcb tcb) := lookupTcb_some_objects st t tcb hL
      exact storeObject hInv hS (by rw [hT]; simp [hf]) (fun _ => by simp)

end RecordsCoreFrame

-- ============================================================================
-- §4b  The endpoint-queue frame: a core frame that keeps the notification queues
-- ============================================================================

/-- What a slot's record view holds of the notification queues: a TCB's two
notification-queue links, a notification's record view; nothing of any other
object.  With the core view it is the record view off the endpoint queues. -/
def recordNtfnViewOf : Option KernelObject → Option ((Nat × Nat) ⊕ NtfnRecordView)
  | some (.tcb t) => some (.inl (t.ntfnPrevCode, t.ntfnNextCode))
  | some (.notification n) => some (.inr n.recordView)
  | _ => none

/-- **A write to the endpoint queues**: a core frame (`RecordsCoreFrame`) that
keeps every slot's notification-queue reads, so the facts carried over the
notification queues hold across it beside the kernel records. -/
structure RecordsEndpointFrame (st st' : SystemState) : Prop where
  core : RecordsCoreFrame st st'
  ntfnViews : ∀ k : SeLe4n.ObjId, recordNtfnViewOf st'.objects[k]? = recordNtfnViewOf st.objects[k]?

namespace RecordsEndpointFrame

theorem refl {st : SystemState} (hInv : st.objects.invExt) : RecordsEndpointFrame st st :=
  ⟨.refl hInv, fun _ => rfl⟩

theorem trans {a b c : SystemState} (h₁ : RecordsEndpointFrame a b)
    (h₂ : RecordsEndpointFrame b c) : RecordsEndpointFrame a c :=
  ⟨h₁.core.trans h₂.core, fun k => (h₂.ntfnViews k).trans (h₁.ntfnViews k)⟩

theorem invExt {st st' : SystemState} (F : RecordsEndpointFrame st st') : st'.objects.invExt :=
  F.core.invExt

/-- The notification-queue reads are read off the record view. -/
theorem recordNtfnViewOf_congr {a b : Option KernelObject} (h : recordViewOf a = recordViewOf b) :
    recordNtfnViewOf a = recordNtfnViewOf b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some y => cases y <;> simp_all [recordViewOf, recordNtfnViewOf]
  | some x =>
    cases b with
    | none => cases x <;> simp_all [recordViewOf, recordNtfnViewOf]
    | some y =>
      cases x <;> cases y <;>
        simp_all [recordViewOf, recordNtfnViewOf, TCB.recordView, Notification.recordView]

theorem andThen {a b c : SystemState} (F : RecordsEndpointFrame a b)
    (G : b.objects.invExt → RecordsEndpointFrame b c) : RecordsEndpointFrame a c :=
  F.trans (G F.invExt)

theorem of_objects_eq {st st' : SystemState} (hInv : st.objects.invExt)
    (hO : st'.objects = st.objects) (hA : st'.asidTable = st.asidTable)
    (hW : st'.machine.physicalAddressWidth = st.machine.physicalAddressWidth := by
      first | rfl | assumption) : RecordsEndpointFrame st st' :=
  ⟨⟨fun k => by rw [hO], hA, hO ▸ hInv, hW⟩, fun k => by rw [hO]⟩

/-- A raw insert whose object keeps its slot's core view and notification-queue
reads, over a slot that held no root (the ASID table is untouched). -/
theorem insert {st : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hV : recordCoreViewOf (some o) = recordCoreViewOf st.objects[k]?)
    (hN : recordNtfnViewOf (some o) = recordNtfnViewOf st.objects[k]?) :
    RecordsEndpointFrame st { st with objects := st.objects.insert k o } := by
  have get : ∀ x, (st.objects.insert k o)[x]? = if k = x then some o else st.objects[x]? := by
    intro x
    simp only [RHTable_getElem?_eq_get?]
    by_cases hx : k = x
    · subst hx; rw [RobinHood.RHTable.getElem?_insert_self _ _ _ hInv]; simp
    · rw [RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hx (eq_of_beq hb)) hInv]; simp [hx]
  refine ⟨⟨fun x => ?_, rfl, RHTable_insert_preserves_invExt _ _ _ hInv, rfl⟩, fun x => ?_⟩
  · show recordCoreViewOf (st.objects.insert k o)[x]? = _
    rw [get]; split
    · rename_i hx; subst hx; exact hV
    · rfl
  · show recordNtfnViewOf (st.objects.insert k o)[x]? = _
    rw [get]; split
    · rename_i hx; subst hx; exact hN
    · rfl

/-- A frame is an endpoint-queue frame. -/
theorem of_frame {st st' : SystemState} (F : RecordsFrame st st') : RecordsEndpointFrame st st' :=
  ⟨F.core, fun k => recordNtfnViewOf_congr (F.views k)⟩

/-- A store whose object keeps its slot's core view and notification-queue
reads, and is no root. -/
theorem storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (h : SeLe4n.Model.storeObject k o st = .ok ((), st'))
    (hV : recordCoreViewOf (some o) = recordCoreViewOf st.objects[k]?)
    (hN : recordNtfnViewOf (some o) = recordNtfnViewOf st.objects[k]?)
    (hNR : ∀ r, o ≠ .vspaceRoot r) : RecordsEndpointFrame st st' := by
  refine ⟨RecordsCoreFrame.storeObject hInv h hV hNR, fun x => ?_⟩
  by_cases hx : x = k
  · subst hx; rw [storeObject_objects_eq st st' x o hInv h]; exact hN
  · rw [storeObject_objects_ne st st' k x o hx hInv h]

/-- An endpoint stored over an endpoint. -/
theorem storeEndpoint {st st' : SystemState} {eid : SeLe4n.ObjId} {e e' : Endpoint}
    (hInv : st.objects.invExt) (hObj : st.objects[eid]? = some (.endpoint e))
    (h : SeLe4n.Model.storeObject eid (.endpoint e') st = .ok ((), st')) :
    RecordsEndpointFrame st st' :=
  storeObject hInv h (by rw [hObj]; rfl) (by rw [hObj]; rfl) (fun _ h => by cases h)

/-- **The unchecked TCB write**, when it keeps every core view and the thread's
notification-queue links. -/
theorem updateTcb (st : SystemState) (t : SeLe4n.ThreadId) {f : TCB → TCB}
    (hInv : st.objects.invExt) (hf : ∀ x, (f x).recordView.core = x.recordView.core)
    (hN : ∀ x, (f x).ntfnPrevCode = x.ntfnPrevCode ∧ (f x).ntfnNextCode = x.ntfnNextCode) :
    RecordsEndpointFrame st (st.updateTcb t f) := by
  cases hT : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact refl hInv
  | some x =>
    rw [SystemState.updateTcb_eq_of_some hT]
    have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
    exact insert hInv (by rw [hO]; simp [hf]) (by rw [hO]; simp [recordNtfnViewOf, hN])

/-- **The checked TCB write**, when it keeps every core view and the thread's
notification-queue links. -/
theorem modifyTcb {st st' : SystemState} {t : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (hf : ∀ x, (f x).recordView.core = x.recordView.core)
    (hN : ∀ x, (f x).ntfnPrevCode = x.ntfnPrevCode ∧ (f x).ntfnNextCode = x.ntfnNextCode)
    (h : _root_.SeLe4n.Kernel.modifyTcb st t f = .ok st') : RecordsEndpointFrame st st' := by
  unfold _root_.SeLe4n.Kernel.modifyTcb at h
  split at h
  · cases h
  · rename_i tcb hL
    split at h
    · cases h
    · rename_i st1 hS
      cases h
      have hT : st.objects[t.toObjId]? = some (.tcb tcb) := lookupTcb_some_objects st t tcb hL
      exact storeObject hInv hS (by rw [hT]; simp [hf]) (by rw [hT]; simp [recordNtfnViewOf, hN])
        (fun _ => by simp)

end RecordsEndpointFrame


-- ============================================================================
-- §5  The erasure frames
-- ============================================================================

namespace RecordsFrame

/-- **Two stores equal modulo an erasure the record views ignore** have the same
views. -/
theorem views_of_erasure {E : KernelObject → KernelObject}
    (hE : ∀ o o', E o = E o' → recordViewOf (some o) = recordViewOf (some o'))
    {st st' : SystemState} (h : ∀ x : SeLe4n.ObjId,
      (st'.objects[x]?).map E = (st.objects[x]?).map E) :
    ∀ k : SeLe4n.ObjId, recordViewOf st'.objects[k]? = recordViewOf st.objects[k]? := by
  intro k
  have hk := h k
  cases ha : st'.objects[k]? <;> cases hb : st.objects[k]? <;> rw [ha, hb] at hk <;>
    simp only [Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at hk
  all_goals first | rfl | exact hE _ _ hk

theorem erasure_taint (o o' : KernelObject) (h : o.eraseTaint = o'.eraseTaint) :
    recordViewOf (some o) = recordViewOf (some o') := by
  cases o <;> cases o' <;>
    simp only [KernelObject.eraseTaint, KernelObject.withTaintWords, reduceCtorEq,
      KernelObject.tcb.injEq, KernelObject.vspaceRoot.injEq,
      KernelObject.notification.injEq, KernelObject.endpoint.injEq] at h ⊢ <;>
    first | rfl | (subst h; rfl) | skip
  · rename_i t t'
    have := congrArg TCB.recordView h
    simpa [TCB.recordView, TCB.withTaintWords] using this
  · rename_i n n'
    have := congrArg Notification.recordView h
    simpa [Notification.recordView, Notification.withTaintWords] using this

theorem erasure_yield (o o' : KernelObject) (h : o.withoutYield = o'.withoutYield) :
    recordViewOf (some o) = recordViewOf (some o') := by
  cases o <;> cases o' <;>
    simp only [KernelObject.withoutYield, reduceCtorEq, KernelObject.tcb.injEq,
      KernelObject.vspaceRoot.injEq, KernelObject.notification.injEq,
      KernelObject.endpoint.injEq] at h ⊢ <;>
    first | rfl | (subst h; rfl) | skip
  rename_i t t'
  have := congrArg TCB.recordView h
  simpa [TCB.recordView] using this

theorem erasure_release (o o' : KernelObject) (h : o.withoutRelease = o'.withoutRelease) :
    recordViewOf (some o) = recordViewOf (some o') := by
  cases o <;> cases o' <;>
    simp only [KernelObject.withoutRelease, reduceCtorEq, KernelObject.tcb.injEq,
      KernelObject.vspaceRoot.injEq, KernelObject.notification.injEq,
      KernelObject.endpoint.injEq] at h ⊢ <;>
    first | rfl | (subst h; rfl)

theorem of_agreeOffTaint {st st' : SystemState} (h : st.objectsAgreeOffTaint st')
    (hA : st'.asidTable = st.asidTable) (hInv : st'.objects.invExt)
    (hW : st'.machine.physicalAddressWidth = st.machine.physicalAddressWidth := by
      first | rfl | assumption) : RecordsFrame st st' :=
  ⟨views_of_erasure erasure_taint h, hA, hInv, hW⟩

theorem of_agreeOffYield {st st' : SystemState} (h : SystemState.objectsAgreeOffYield st' st)
    (hA : st'.asidTable = st.asidTable) (hInv : st'.objects.invExt)
    (hW : st'.machine.physicalAddressWidth = st.machine.physicalAddressWidth := by
      first | rfl | assumption) : RecordsFrame st st' :=
  ⟨views_of_erasure erasure_yield h, hA, hInv, hW⟩

theorem of_agreeOffReleaseLinks {st st' : SystemState}
    (h : SystemState.objectsAgreeOffReleaseLinks st' st)
    (hA : st'.asidTable = st.asidTable) (hInv : st'.objects.invExt)
    (hW : st'.machine.physicalAddressWidth = st.machine.physicalAddressWidth := by
      first | rfl | assumption) : RecordsFrame st st' :=
  ⟨views_of_erasure erasure_release h, hA, hInv, hW⟩

/-- Two slots agreeing off the run links, with the same reply view, have the same
record view: the run links clear the reply links, so the reply view is read on
its own. -/
theorem view_of_runLinks {a b : Option KernelObject}
    (hw : a.map KernelObject.withoutRunLinks = b.map KernelObject.withoutRunLinks)
    (hr : objReplyView a = objReplyView b) : recordViewOf a = recordViewOf b := by
  cases a <;> cases b <;>
    simp only [Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at hw ⊢
  all_goals try rfl
  · rename_i o o'
    cases o <;> cases o' <;>
      simp only [KernelObject.withoutRunLinks, reduceCtorEq, KernelObject.tcb.injEq,
        KernelObject.vspaceRoot.injEq, KernelObject.notification.injEq,
        KernelObject.endpoint.injEq] at hw ⊢ <;>
      first | rfl | (subst hw; rfl) | skip
    rename_i t t'
    simp only [objReplyView, Option.some.injEq] at hr
    show some (Sum.inl t.recordView) = some (Sum.inl t'.recordView)
    unfold TCB.recordView
    rw [hr, TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState hw,
      TCB.proj_eq_of_withoutRunLinks_eq TCB.threadState hw,
      TCB.proj_eq_of_withoutRunLinks_eq (fun x => x.pendingFault.isSome) hw,
      TCB.proj_eq_of_withoutRunLinks_eq TCB.ntfnPrevCode hw,
      TCB.proj_eq_of_withoutRunLinks_eq TCB.ntfnNextCode hw,
      TCB.proj_eq_of_withoutRunLinks_eq TCB.queuePrevCode hw,
      TCB.proj_eq_of_withoutRunLinks_eq TCB.queueNextCode hw]

theorem of_agreeOffRunLinks {st st' : SystemState} (h : st'.objectsAgreeOffRunLinks st)
    (hR : st'.replyViews = st.replyViews)
    (hA : st'.asidTable = st.asidTable) (hInv : st'.objects.invExt)
    (hW : st'.machine.physicalAddressWidth = st.machine.physicalAddressWidth := by
      first | rfl | assumption) : RecordsFrame st st' := by
  refine ⟨fun k => view_of_runLinks (h k) ?_, hA, hInv, hW⟩
  have := congrFun hR k
  unfold SystemState.replyViews SystemState.getObject? at this
  simpa only [RHTable_getElem?_eq_get?] using this

end RecordsFrame

-- ============================================================================
-- §6  The step: a frame for the writes that move a fault record or a state
-- ============================================================================

/-- **An IPC state a fault record may sit on**: blocked on a call, or in a
reply. -/
def ipcParked (s : ThreadIpcState) : Prop :=
  (∃ e, s = .blockedOnCall e) ∨ (∃ e r, s = .blockedOnReply e r)

@[simp] theorem ipcParked_ready : ¬ ipcParked .ready := by
  rintro (⟨_, h⟩ | ⟨_, _, h⟩) <;> cases h

@[simp] theorem ipcParked_blockedOnCall (e : SeLe4n.ObjId) : ipcParked (.blockedOnCall e) :=
  .inl ⟨e, rfl⟩

@[simp] theorem ipcParked_blockedOnReply (e : SeLe4n.ObjId) (r : Option SeLe4n.ThreadId) :
    ipcParked (.blockedOnReply e r) :=
  .inr ⟨e, r, rfl⟩

@[simp] theorem ipcParked_blockedOnSend (e : SeLe4n.ObjId) : ¬ ipcParked (.blockedOnSend e) := by
  rintro (⟨_, h⟩ | ⟨_, _, h⟩) <;> cases h

@[simp] theorem ipcParked_blockedOnReceive (e : SeLe4n.ObjId) :
    ¬ ipcParked (.blockedOnReceive e) := by
  rintro (⟨_, h⟩ | ⟨_, _, h⟩) <;> cases h

@[simp] theorem ipcParked_blockedOnNotification (n : SeLe4n.ObjId) :
    ¬ ipcParked (.blockedOnNotification n) := by
  rintro (⟨_, h⟩ | ⟨_, _, h⟩) <;> cases h

/-- **A thread a fault record may sit on**: `.Inactive`, or blocked on a call or
in a reply (`SystemState.faultRecordParked` reads it of every thread carrying a
fault). -/
def _root_.SeLe4n.Model.TCB.faultParked (t : TCB) : Prop :=
  t.threadState = .Inactive ∨ ipcParked t.ipcState

/-- **The step leaves every fault record parked that was**: a thread carrying a
fault after the step is parked, if the thread at its key before the step was
parked whenever it carried a fault.  A new thread, or one whose fault the step
retired, carries none; a thread whose fault the step records is parked by it;
a thread the step unparks carried no fault.  It composes, and it carries
`SystemState.faultRecordParked` (`FaultsStayParked.preserves`). -/
def FaultsStayParked (st st' : SystemState) : Prop :=
  ∀ t tcb', st'.getTcb? t = some tcb' → tcb'.pendingFault.isSome →
    (∀ tcb, st.getTcb? t = some tcb → tcb.pendingFault.isSome → tcb.faultParked) →
      tcb'.faultParked

namespace FaultsStayParked

theorem refl (st : SystemState) : FaultsStayParked st st := fun _ tcb h hF H => H tcb h hF

theorem trans {a b c : SystemState} (h₁ : FaultsStayParked a b) (h₂ : FaultsStayParked b c) :
    FaultsStayParked a c := fun t tcb h hF H =>
  h₂ t tcb h hF fun tb hb hFb => h₁ t tb hb hFb H

theorem preserves {st st' : SystemState} (F : FaultsStayParked st st')
    (h : st.faultRecordParked) : st'.faultRecordParked := fun t tcb hT hF =>
  F t tcb hT hF fun tcb0 hT0 hF0 => h t tcb0 hT0 hF0

/-- **A step that keeps every thread's fault flag, thread state and IPC state.** -/
theorem of_fields {st st' : SystemState}
    (h : ∀ t tcb', st'.getTcb? t = some tcb' → tcb'.pendingFault.isSome →
      ∃ tcb, st.getTcb? t = some tcb ∧ tcb.pendingFault.isSome = tcb'.pendingFault.isSome ∧
        tcb.threadState = tcb'.threadState ∧ tcb.ipcState = tcb'.ipcState) :
    FaultsStayParked st st' := fun t tcb' hT hF H => by
  obtain ⟨tcb, hT0, hf, hs, hi⟩ := h t tcb' hT hF
  have := H tcb hT0 (hf ▸ hF)
  unfold TCB.faultParked at this ⊢
  rw [← hs, ← hi]; exact this

theorem of_coreFrame {st st' : SystemState} (F : RecordsCoreFrame st st') :
    FaultsStayParked st st' :=
  of_fields fun _ _ hT _ => by
    obtain ⟨tcb, hT0, hv⟩ := F.getTcb?_view hT
    obtain ⟨-, hi, hs, hf⟩ := TcbRecordView.core_eq hv
    exact ⟨tcb, hT0, hf, hs, hi⟩

theorem of_frame {st st' : SystemState} (F : RecordsFrame st st') : FaultsStayParked st st' :=
  of_coreFrame F.core

end FaultsStayParked

/-- **A step that keeps the address-space records and leaves every fault record
parked**: the frame of a write that moves a thread's IPC state or fault record
(an IPC arm, a cancellation, the suspend, the resume).  With the reply-waiter
queues carried by the arm's own theorem it is a `RecordsStage`
(`RecordsStage.of_step`). -/
structure RecordsStep (st st' : SystemState) : Prop where
  rootViews : ∀ k : SeLe4n.ObjId, rootViewOf st'.objects[k]? = rootViewOf st.objects[k]?
  asid : st'.asidTable = st.asidTable
  invExt : st'.objects.invExt
  faults : FaultsStayParked st st'
  width : st'.machine.physicalAddressWidth = st.machine.physicalAddressWidth

namespace RecordsStep

theorem refl {st : SystemState} (hInv : st.objects.invExt) : RecordsStep st st :=
  ⟨fun _ => rfl, rfl, hInv, FaultsStayParked.refl st, rfl⟩

theorem trans {a b c : SystemState} (h₁ : RecordsStep a b) (h₂ : RecordsStep b c) :
    RecordsStep a c :=
  ⟨fun k => (h₂.rootViews k).trans (h₁.rootViews k), h₂.asid.trans h₁.asid, h₂.invExt,
    h₁.faults.trans h₂.faults, h₂.width.trans h₁.width⟩

theorem of_coreFrame {st st' : SystemState} (F : RecordsCoreFrame st st') : RecordsStep st st' :=
  ⟨F.rootViews, F.asid, F.invExt, FaultsStayParked.of_coreFrame F, F.width⟩

theorem of_frame {st st' : SystemState} (F : RecordsFrame st st') : RecordsStep st st' :=
  of_coreFrame F.core

/-- A kind-preserving write keeps every root's address-space view. -/
theorem rootViews_of_kindPreservingWrite {st st' : SystemState} (h : kindPreservingWrite st st') :
    ∀ k : SeLe4n.ObjId, rootViewOf st'.objects[k]? = rootViewOf st.objects[k]? := fun k => by
  rcases h k with e | ⟨pre, post, hp, hq, -, -, -, -, -, -, hm⟩
  · rw [e]
  · rw [hp, hq]; simp only [rootViewOf, Option.bind_some, hm]

/-- A write that keeps every object's mapping facts keeps every root's view. -/
theorem rootViews_of_mappingFactsKept {st st' : SystemState} (h : st.mappingFactsKept st') :
    ∀ k : SeLe4n.ObjId, rootViewOf st'.objects[k]? = rootViewOf st.objects[k]? := fun k => by
  rcases h k with e | ⟨pre, post, hp, hq, -, -, -, hm⟩
  · rw [e]
  · rw [hp, hq]; simp only [rootViewOf, Option.bind_some, hm]

/-- The records carried across the step, given the reply-waiter queues. -/
theorem preserves {st st' : SystemState} (S : RecordsStep st st')
    (hRW : st.replyWaitersConsistent → st'.replyWaitersConsistent)
    (h : st.kernelRecordsSound) : st'.kernelRecordsSound :=
  ⟨teardownWellFormed_of_rootViews S.invExt S.asid S.rootViews h.1, hRW h.2.1,
   S.faults.preserves h.2.2.1, h.2.2.2.of_eq S.width⟩

end RecordsStep

theorem RecordsStage.of_step {st st' : SystemState} (S : RecordsStep st st')
    (hRW : st.replyWaitersConsistent → st'.replyWaitersConsistent) : RecordsStage st st' :=
  S.preserves hRW

end SeLe4n.Kernel
