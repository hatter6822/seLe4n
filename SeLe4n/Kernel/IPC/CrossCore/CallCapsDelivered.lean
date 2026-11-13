-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.CapTransferDelivered
import SeLe4n.Kernel.IPC.CrossCore.LongCallInPlace
import SeLe4n.Kernel.IPC.CrossCore.FaultReceiveInPlace

/-!
# A capability-carrying call rendezvous, delivered in place

The specification's call transfers the caller's capabilities on the state the
call rendezvous left, then decides the scheduling-context donation and walks
the receiver's priority chain on the state the transfer left.  The transfer
writes CNode slots, their derivation links, an untyped source's free index and
the receiver's buffer and space-slot link words, never a thread's state, so a rendezvous that donates
nothing still donates nothing after it (`receiveTransferCaps_keepsBindings`,
which needs no `invExt`: every write lands on a key already present while no
resize is due).  The in-place call (`performCallCapsDelivered`) is the
rendezvous, the transfer in place (`capTransferK`), the priority walk and the
frame carrying the transfer's report (`callRendezvousCaps_eq_delivered`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood

/-! ## The transfer keeps every thread's binding -/

/-- Two threads that differ at most in their space-slot link words. -/
def TCB.sameOffLinks (t t' : TCB) : Prop := t'.withoutLinks = t.withoutLinks

/-- The states after `B` that keep every thread of `B` as it was, up to its
space-slot link words, and make no other object a thread, with no resize
due. -/
def KeepsBindings (B s : SystemState) : Prop :=
  s.objects.noResizeDue ∧ ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
    s.objects[tid.toObjId]? = some (.tcb tcb') →
    ∃ tcb, B.objects[tid.toObjId]? = some (.tcb tcb) ∧ TCB.sameOffLinks tcb tcb'

theorem KeepsBindings.refl (B : SystemState) (h : B.objects.noResizeDue) : KeepsBindings B B :=
  ⟨h, fun _ t h => ⟨t, h, rfl⟩⟩

/-- A thread's scheduling-context binding is not a link word. -/
theorem KeepsBindings.sameSchedContextBindings {B s : SystemState} (h : KeepsBindings B s) :
    sameSchedContextBindings B s := by
  intro tid tcb' hO
  obtain ⟨t, hB, hE⟩ := h.2 tid tcb' hO
  exact ⟨t, hB, (congrArg TCB.schedContextBinding hE).symm⟩

/-- A write of one present key that keeps a thread a thread up to its link
words, and makes nothing else a thread, keeps every thread. -/
theorem KeepsBindings.mapValueAt {B s : SystemState} (h : KeepsBindings B s) (k : SeLe4n.ObjId)
    (F : KernelObject → KernelObject)
    (hF : ∀ o t', F o = .tcb t' → ∃ t, o = .tcb t ∧ TCB.sameOffLinks t t') :
    KeepsBindings B { s with objects := s.objects.mapValueAt k F } := by
  refine ⟨(RHTable.noResizeDue_mapValueAt _ _ _).mpr h.1, ?_⟩
  intro tid tcb' hO
  simp only [RHTable_getElem?_eq_get?, RHTable.get?_mapValueAt] at hO
  split at hO
  · cases hg : s.objects.get? tid.toObjId with
    | none => rw [hg] at hO; cases hO
    | some o =>
      rw [hg] at hO
      simp only [Option.map_some, Option.some.injEq] at hO
      obtain ⟨t, rfl, hb⟩ := hF o tcb' hO
      obtain ⟨t0, h0, e0⟩ := h.2 tid t (by simpa only [RHTable_getElem?_eq_get?] using hg)
      exact ⟨t0, h0, hb.trans e0⟩
  · exact h.2 tid tcb' (by simpa only [RHTable_getElem?_eq_get?] using hO)

theorem KeepsBindings.setSlotLinkWords {B s : SystemState} (h : KeepsBindings B s)
    (o : SeLe4n.ObjId) (sl : SeLe4n.Slot) (f : LinkField) (c w : Nat) :
    KeepsBindings B (s.setSlotLinkWords o sl f c w) := by
  rw [setSlotLinkWords_eq_modifyObject _ _ _ _ _ _ h.1,
    SystemState.modifyObject_eq_mapValueAt _ _ _ h.1]
  refine h.mapValueAt o _ ?_
  intro ob t' hEq
  cases ob <;> simp only [KernelObject.setLinkWords] at hEq <;> try cases hEq
  case tcb t => exact ⟨t, rfl, rfl⟩

theorem KeepsBindings.linkAddChild {B s : SystemState} (h : KeepsBindings B s) (p c : SlotRef) :
    KeepsBindings B (s.linkAddChild p c) := by
  unfold SystemState.linkAddChild
  dsimp only
  split <;> (repeat apply KeepsBindings.setSlotLinkWords) <;> exact h

theorem KeepsBindings.cdtAddChild {B s : SystemState} (h : KeepsBindings B s) (p c : SlotRef)
    (op : DerivationOp) : KeepsBindings B (s.cdtAddChild p c op) :=
  KeepsBindings.linkAddChild (s := s.modifyCdt _) h p c

theorem KeepsBindings.storeObject_cnode {B s s' : SystemState} (h : KeepsBindings B s)
    (k : SeLe4n.ObjId) (cn0 cn : CNode) (hk : s.objects[k]? = some (.cnode cn0))
    (hS : storeObject k (.cnode cn) s = .ok ((), s')) : KeepsBindings B s' := by
  have hg : s.objects.get? k = some (.cnode cn0) := by
    simpa only [RHTable_getElem?_eq_get?] using hk
  unfold storeObject at hS
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hS
  rw [← hS]
  have := h.mapValueAt k (fun _ => .cnode cn) (fun _ _ hE => by cases hE)
  rw [RHTable.insert_eq_mapValueAt _ (RHTable.findsInPlace_of_get? h.1 hg)]
  exact this

theorem KeepsBindings.storeCNodeWith {B s : SystemState} (h : KeepsBindings B s)
    (k : SeLe4n.ObjId) (f : CNode → CNode) : KeepsBindings B (s.storeCNodeWith k f) := by
  rcases SystemState.storeCNodeWith_cases s k f with ⟨cn, hk, hS⟩ | e
  · exact h.storeObject_cnode k cn (f cn) hk hS
  · rw [e]; exact h

theorem KeepsBindings.untypedSourceSetFull {B s : SystemState} (h : KeepsBindings B s)
    (src : CSpaceAddr) (cap : Capability) : KeepsBindings B (untypedSourceSetFull s src cap) :=
  untypedSourceSetFull_of (P := KeepsBindings B) h (fun _ => h.storeCNodeWith _ _)

theorem KeepsBindings.ipcTransferSingleCap {B s s' : SystemState} (h : KeepsBindings B s)
    (cap : Capability) (src : SlotRef) (dst : CSpaceAddr)
    (hT : ipcTransferSingleCap cap src dst s = .ok ((), s')) : KeepsBindings B s' := by
  obtain ⟨_, s2, -, -, -, hIns, rfl⟩ := ipcTransferSingleCap_ok_cases hT
  obtain ⟨cn, hC, -, -, hS⟩ := cspaceInsertSlot_ok_decompose _ _ _ _ hIns
  exact ((h.storeObject_cnode _ cn _ ((SystemState.getCNode?_eq_some_iff _ _ _).mp hC)
    hS).cdtAddChild _ _ _).untypedSourceSetFull _ _

theorem KeepsBindings.recordUnwrappedBadge {B s : SystemState} (h : KeepsBindings B s)
    (rtcb : TCB) (i : Nat) (b : SeLe4n.Badge) :
    KeepsBindings B (recordUnwrappedBadge s rtcb i b) := by
  have hO := recordUnwrappedBadge_objects s rtcb i b
  exact ⟨hO ▸ h.1, fun tid t ht => h.2 tid t (hO ▸ ht)⟩

/-- **The transfer keeps every thread's binding**, with no resize due. -/
theorem receiveTransferCaps_keepsBindings
    (req : Option (Capability × Array SeLe4n.CPtr))
    (endpointId : Option SeLe4n.ObjId) (target? : Option (TCB × Option CSpaceAddr))
    {B Z Z' : SystemState} {r : CapTransferSummary} (hK : KeepsBindings B Z)
    (h : receiveTransferCaps req endpointId target? Z = .ok (r, Z')) : KeepsBindings B Z' := by
  unfold receiveTransferCaps at h
  rcases req with _ | ⟨root, addrs⟩
  · cases h; exact hK
  · simp only [] at h
    split at h
    · cases h; exact hK
    · rcases target? with _ | ⟨rtcb, slot?⟩
      · cases h; exact hK
      · exact ipcUnwrapCapsLoop_rel (fun a b => ∀ B, KeepsBindings B b → KeepsBindings B a)
          (fun _ _ h => h) (fun _ _ _ h1 h2 B h => h1 B (h2 B h)) _ _ rtcb
          (fun s i b B h => h.recordUnwrappedBadge rtcb i b) _ _ _ _ _ _ _
          (fun _ _ _ _ _ _ hT B h => h.ipcTransferSingleCap _ _ _ hT) h B hK

/-- The states after `B` that hold every thread of `B`, up to its space-slot
link words, with no resize due: `KeepsBindings` read forward. -/
def CarriesThreads (B s : SystemState) : Prop :=
  s.objects.noResizeDue ∧ ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    B.objects[tid.toObjId]? = some (.tcb tcb) →
    ∃ tcb', s.objects[tid.toObjId]? = some (.tcb tcb') ∧ TCB.sameOffLinks tcb tcb'

theorem CarriesThreads.refl (B : SystemState) (h : B.objects.noResizeDue) :
    CarriesThreads B B :=
  ⟨h, fun _ t h => ⟨t, h, rfl⟩⟩

/-- A write of one present key that keeps a thread there a thread up to its
link words carries every thread. -/
theorem CarriesThreads.mapValueAt {B s : SystemState} (h : CarriesThreads B s) (k : SeLe4n.ObjId)
    (F : KernelObject → KernelObject)
    (hF : ∀ t, s.objects[k]? = some (.tcb t) → ∃ t', F (.tcb t) = .tcb t' ∧ TCB.sameOffLinks t t') :
    CarriesThreads B { s with objects := s.objects.mapValueAt k F } := by
  refine ⟨(RHTable.noResizeDue_mapValueAt _ _ _).mpr h.1, ?_⟩
  intro tid tcb hB
  obtain ⟨t1, h1, e1⟩ := h.2 tid tcb hB
  simp only [RHTable_getElem?_eq_get?, RHTable.get?_mapValueAt]
  have hg : s.objects.get? tid.toObjId = some (.tcb t1) := by
    simpa only [RHTable_getElem?_eq_get?] using h1
  split
  · next hk =>
    have hk' : k = tid.toObjId := beq_iff_eq.mp hk
    subst hk'
    obtain ⟨t2, hF2, e2⟩ := hF t1 h1
    refine ⟨t2, by rw [hg]; simp only [Option.map_some, hF2], ?_⟩
    exact e2.trans e1
  · exact ⟨t1, hg, e1⟩

theorem CarriesThreads.setSlotLinkWords {B s : SystemState} (h : CarriesThreads B s)
    (o : SeLe4n.ObjId) (sl : SeLe4n.Slot) (f : LinkField) (c w : Nat) :
    CarriesThreads B (s.setSlotLinkWords o sl f c w) := by
  rw [setSlotLinkWords_eq_modifyObject _ _ _ _ _ _ h.1,
    SystemState.modifyObject_eq_mapValueAt _ _ _ h.1]
  refine h.mapValueAt o _ ?_
  intro t _
  exact ⟨_, rfl, rfl⟩

theorem CarriesThreads.linkAddChild {B s : SystemState} (h : CarriesThreads B s) (p c : SlotRef) :
    CarriesThreads B (s.linkAddChild p c) := by
  unfold SystemState.linkAddChild
  dsimp only
  split <;> (repeat apply CarriesThreads.setSlotLinkWords) <;> exact h

theorem CarriesThreads.cdtAddChild {B s : SystemState} (h : CarriesThreads B s) (p c : SlotRef)
    (op : DerivationOp) : CarriesThreads B (s.cdtAddChild p c op) :=
  CarriesThreads.linkAddChild (s := s.modifyCdt _) h p c

theorem CarriesThreads.storeObject_cnode {B s s' : SystemState} (h : CarriesThreads B s)
    (k : SeLe4n.ObjId) (cn0 cn : CNode) (hk : s.objects[k]? = some (.cnode cn0))
    (hS : storeObject k (.cnode cn) s = .ok ((), s')) : CarriesThreads B s' := by
  have hg : s.objects.get? k = some (.cnode cn0) := by
    simpa only [RHTable_getElem?_eq_get?] using hk
  unfold storeObject at hS
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hS
  rw [← hS]
  have := h.mapValueAt k (fun _ => .cnode cn) (fun _ ht => by rw [hk] at ht; cases ht)
  rw [RHTable.insert_eq_mapValueAt _ (RHTable.findsInPlace_of_get? h.1 hg)]
  exact this

theorem CarriesThreads.storeCNodeWith {B s : SystemState} (h : CarriesThreads B s)
    (k : SeLe4n.ObjId) (f : CNode → CNode) : CarriesThreads B (s.storeCNodeWith k f) := by
  rcases SystemState.storeCNodeWith_cases s k f with ⟨cn, hk, hS⟩ | e
  · exact h.storeObject_cnode k cn (f cn) hk hS
  · rw [e]; exact h

theorem CarriesThreads.untypedSourceSetFull {B s : SystemState} (h : CarriesThreads B s)
    (src : CSpaceAddr) (cap : Capability) : CarriesThreads B (untypedSourceSetFull s src cap) :=
  untypedSourceSetFull_of (P := CarriesThreads B) h (fun _ => h.storeCNodeWith _ _)

theorem CarriesThreads.ipcTransferSingleCap {B s s' : SystemState} (h : CarriesThreads B s)
    (cap : Capability) (src : SlotRef) (dst : CSpaceAddr)
    (hT : ipcTransferSingleCap cap src dst s = .ok ((), s')) : CarriesThreads B s' := by
  obtain ⟨_, s2, -, -, -, hIns, rfl⟩ := ipcTransferSingleCap_ok_cases hT
  obtain ⟨cn, hC, -, -, hS⟩ := cspaceInsertSlot_ok_decompose _ _ _ _ hIns
  exact ((h.storeObject_cnode _ cn _ ((SystemState.getCNode?_eq_some_iff _ _ _).mp hC)
    hS).cdtAddChild _ _ _).untypedSourceSetFull _ _

theorem CarriesThreads.recordUnwrappedBadge {B s : SystemState} (h : CarriesThreads B s)
    (rtcb : TCB) (i : Nat) (b : SeLe4n.Badge) :
    CarriesThreads B (recordUnwrappedBadge s rtcb i b) := by
  have hO := recordUnwrappedBadge_objects s rtcb i b
  exact ⟨hO ▸ h.1, fun tid t ht => by rw [hO]; exact h.2 tid t ht⟩

/-- **The transfer carries every thread**, with no resize due. -/
theorem receiveTransferCaps_carriesThreads
    (req : Option (Capability × Array SeLe4n.CPtr))
    (endpointId : Option SeLe4n.ObjId) (target? : Option (TCB × Option CSpaceAddr))
    {B Z Z' : SystemState} {r : CapTransferSummary} (hK : CarriesThreads B Z)
    (h : receiveTransferCaps req endpointId target? Z = .ok (r, Z')) : CarriesThreads B Z' := by
  unfold receiveTransferCaps at h
  rcases req with _ | ⟨root, addrs⟩
  · cases h; exact hK
  · simp only [] at h
    split at h
    · cases h; exact hK
    · rcases target? with _ | ⟨rtcb, slot?⟩
      · cases h; exact hK
      · exact ipcUnwrapCapsLoop_rel (fun a b => ∀ B, CarriesThreads B b → CarriesThreads B a)
          (fun _ _ h => h) (fun _ _ _ h1 h2 B h => h1 B (h2 B h)) _ _ rtcb
          (fun s i b B h => h.recordUnwrappedBadge rtcb i b) _ _ _ _ _ _ _
          (fun _ _ _ _ _ _ hT B h => h.ipcTransferSingleCap _ _ _ hT) h B hK

/-! ## The call, delivered -/

/-- **A call's last writes, with the transfer's report**: the receiver's
priority walk on the state the transfer left, then the frame carrying the
report.  The report comes first, so it is read before the state is handed
over. -/
@[noinline] def finishCallCaps (capInfo : Nat) (Y : SystemState) (r : SeLe4n.ThreadId)
    (core : Concurrency.CoreId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badgeWord : SeLe4n.Badge) (badged : Bool) :
    SystemState :=
  deliverCapsFrame capInfo (PriorityInheritance.propagatePipChainCrossCore Y r core).1 r layout
    rf len badgeWord badged

/-- **The call rendezvous that transfers capabilities, delivered**: the
receiver woken without the message and the caller blocked on the reply, the
transfer in place, the priority walk, then the frame with the transfer's
report.  The caller and the receiver enter as the words the transfer reads of
them (`capTransferK`), read before the rendezvous. -/
@[noinline] def performCallCapsDelivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (nextCode : Nat) (rid : SeLe4n.ReplyId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : Concurrency.CoreId)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  let X := storeCallRendezvousReady st endpointId caller r nextCode rid core
  capTransferK X endpointId sv sb sroot count rv rb rroot fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    finishCallCaps (capStepsInfo endpointId true x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (capStepsApply endpointId true rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X)
      r core layout rf len badgeWord badged

/-- **The staged call rendezvous that transfers capabilities is the delivered
one**, for a message of at most four words read in the caller's registers: the
specification's transfer after the rendezvous, the priority walk, then the
woken receiver's stage with the transfer's report. -/
theorem callRendezvousCaps_eq_delivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : Concurrency.CoreId) (ctcb rt : TCB)
    (count : Nat) (hNo : st.objects.noResizeDue) (hNe : caller ≠ r)
    (hSz : Architecture.regMessageLength layout len ≤ 4) :
    (match receiveTransferCaps (frameCapRequestOf st ctcb count) (some endpointId)
        (capTargetOf st rt)
        (storeCallRendezvous st endpointId caller r next rid
          { registers := Architecture.regMessageBody layout rf len,
            badge := SeLe4n.Badge.opt badgeWord badged } core) with
      | .ok (s, st'') =>
        Architecture.stageWokenDelivery
          (PriorityInheritance.propagatePipChainCrossCore st'' r core).1 (some r) s.capInfo
      | .error _ => st) =
      performCallCapsDelivered st endpointId caller r (ThreadId.optCode next) rid layout rf len
        badgeWord badged core ctcb.vspaceRoot ctcb.ipcBuffer ctcb.spaceCells[0] count rt.vspaceRoot
        rt.ipcBuffer rt.spaceCells[0] := by
  have hNoX := storeCallRendezvousReady_noResizeDue st endpointId caller r
    (ThreadId.optCode next) rid core hNo
  have hA := ipcBufferReadsAgree_storeCallRendezvousReady st endpointId caller r
    (ThreadId.optCode next) rid core hNo
  unfold performCallCapsDelivered
  have hK := capTransferK_eq
    (storeCallRendezvousReady st endpointId caller r (ThreadId.optCode next) rid core)
    endpointId ctcb count rt (fun i Y => finishCallCaps i Y r core layout rf len badgeWord badged)
  simp only at hK
  rw [hK, hA.frameCapRequestOf, hA.capTargetOf,
    storeCallRendezvous_eq_hold _ _ _ _ _ _ _ _ hNo hNe]
  generalize storeCallRendezvousReady st endpointId caller r (ThreadId.optCode next) rid core = X
    at hNoX
  rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) r _ _ _ X hNoX]
  obtain ⟨s, Y1, hT⟩ := receiveTransferCaps_ok (frameCapRequestOf st ctcb count)
    (some endpointId) (capTargetOf st rt) X
  have hNo1 := receiveTransferCaps_noResizeDue _ _ _ X Y1 s hNoX hT
  rw [hT]
  simp only [mapStepState]
  rw [propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNo1, Architecture.stageWokenDelivery_some,
    stageDeliveredMessage_holdMessage_caps _ _ _ _
      (propagatePipChainCrossCore_noResizeDue _ _ _ hNo1)
      (by rw [Architecture.regMessageBody_size]; exact hSz),
    returnFrameOfMessage_regMessageBody_caps]
  rfl

/-- **A checked call to a waiting receiver, in place up to its transfer**: the
in-place call rendezvous, then the specification's transfer of the caller's
request to the receiver's side, both read before the rendezvous, then the
receiver's priority walk.  The transfer writes no thread's binding, so the
rendezvous still donates nothing after it. -/
theorem callDispatchChecked_inPlace_transfer (ctx : LabelingContext) (st : SystemState)
    (endpointId : SeLe4n.ObjId) (ep : Endpoint) (caller r : SeLe4n.ThreadId) (rt : TCB)
    (rid : SeLe4n.ReplyId) (payload : SendPayload) (msg : IpcMessage)
    (core : Concurrency.CoreId)
    (hM : sendPayloadMessage st caller payload = msg)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.receiveQ.head = some r)
    (hT : st.objects[r.toObjId]? = some (.tcb rt)) (hRid : rt.pendingReceiveReply = some rid)
    (hG : callWakesInPlace st endpointId caller r rt rid = true)
    (hFlow : endpointFlowGate ctx endpointId (ctx.threadLabelOf caller)
      (ctx.endpointLabelOf endpointId) = true) :
    ∃ sgi, endpointCallCrossCoreDispatchChecked ctx endpointId caller payload core st =
      match receiveTransferCaps (sendCapRequest st endpointId caller payload) (some endpointId)
          (receiverCapTarget? st r)
          (storeCallRendezvous st endpointId caller r rt.queueNext rid msg core) with
      | .ok (s, st'') =>
        ((PriorityInheritance.propagatePipChainCrossCore st'' r core).1, .ok (s, sgi))
      | .error e => (storeCallRendezvous st endpointId caller r rt.queueNext rid msg core,
          .error e) := by
  have hG' := hG
  simp only [callWakesInPlace, sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG'
  have hCRes : caller.isReserved = false := hG'.1.1.1.1.1.1.1.1.2
  have hRRes : r.isReserved = false := hG'.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  have hNo : st.objects.noResizeDue :=
    RobinHood.RHTable.noResizeDue_of_findsInPlace hG'.1.1.1.1.1.1.1.1.1.1.1.1.2
  have hEp : st.getEndpoint? endpointId = some ep :=
    (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE
  have hK0 : KeepsBindings (storeCallRendezvous st endpointId caller r rt.queueNext rid msg core)
      (storeCallRendezvous st endpointId caller r rt.queueNext rid msg core) := by
    apply KeepsBindings.refl
    rw [storeCallRendezvous_eq_hold _ _ _ _ _ _ _ _ hNo (callWakesInPlace_ne hG)]
    exact (SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr
      (storeCallRendezvousReady_noResizeDue _ _ _ _ _ _ _ hNo)
  obtain ⟨hEq, hDon⟩ := callRendezvous_inPlace st endpointId ep caller r rt rid payload msg core hM
    hE hH hT hRid hG
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff caller).mpr hCRes)
  obtain ⟨rv, hrv⟩ := Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff r).mpr hRRes)
  have hcv' := SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv
  have hrv' := SeLe4n.ThreadId.toValid?_some_val_eq _ _ hrv
  refine ⟨(wakeThread ((storePopHead st endpointId true r rt.queueNext).updateTcb r
    (callReceiverTcb msg)) r core).2, ?_⟩
  obtain ⟨s, st'', hTr⟩ := receiveTransferCaps_ok (sendCapRequest st endpointId caller payload)
    (some endpointId) (receiverCapTarget? st r)
    (storeCallRendezvous st endpointId caller r rt.queueNext rid msg core)
  have hDon' := callDonationSchedContext?_none_of_sameSchedContextBindings
    (receiveTransferCaps_keepsBindings _ _ _ hK0 hTr).sameSchedContextBindings caller r hDon
  rw [hTr]
  unfold endpointCallCrossCoreDispatchChecked
  rw [if_pos hFlow]
  unfold endpointCallCrossCoreDispatch endpointCallWithCapsOnCore
  rw [hEq]
  simp only [hEp, hH, Option.bind_some, hcv, hrv]
  cases hReq : sendCapRequest st endpointId caller payload with
  | none =>
    rw [hReq] at hTr
    simp only [receiveTransferCaps, Except.ok.injEq, Prod.mk.injEq] at hTr
    obtain ⟨rfl, rfl⟩ := hTr
    simp only [Option.isNone_none, ↓reduceIte]
    unfold applyCallDonationOnCore
    rw [applyCallDonation_eq_ok_self_of_no_donation _ _ _ (by rw [hcv', hrv']; exact hDon')]
    simp only [hcv', hrv', hDon']
  | some q =>
    rw [hReq] at hTr
    simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte, hTr]
    unfold applyCallDonationOnCore
    rw [applyCallDonation_eq_ok_self_of_no_donation _ _ _ (by rw [hcv', hrv']; exact hDon')]
    simp only [hcv', hrv', hDon']

/-! ## The take of a blocked send, delivered -/

/-- **A take's last writes, with the transfer's report**: the woken sender's
completion frame on the state the transfer left, then the receiver's frame
carrying the report.  The message words enter as words, read from the sender's
registers before the take: the completion rewrites those registers, so a
register file still held here would be copied. -/
@[noinline] def finishTakeCaps (capInfo : Nat) (Y : SystemState) (s receiver : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (len : Nat) (w0 w2 w3 w4 w5 : UInt64) :
    SystemState :=
  (Architecture.stageWokenSendCompletion Y (some s)).mapTcbInPlace receiver
    (withFrameWords w0 (regMessageInfoWordCaps layout len capInfo) w2 w3 w4 w5)

/-- **The take of a blocked send that transfers capabilities, delivered**: the
sender popped, made ready and woken, the receiver made ready, the transfer in
place, the sender's completion frame, then the receiver's frame with the
transfer's report, its words `w0`, `w2`..`w5` read from the sender's saved
registers before the take.  The sender and the receiver enter as the words the
transfer reads of them (`capTransferK`), read before the take. -/
@[noinline] def performTakeCapsDelivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (nextCode : Nat) (receiver : SeLe4n.ThreadId) (core : Concurrency.CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (len : Nat) (w0 w2 w3 w4 w5 : UInt64)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  let X := (wakeThread ((storePopHead st endpointId false s (ThreadId.ofOptCode nextCode)).updateTcb
    s receiverReady) s core).1.updateTcb receiver receiverReady
  capTransferK X endpointId sv sb sroot count rv rb rroot fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    finishTakeCaps (capStepsInfo endpointId true x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (capStepsApply endpointId true rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X)
      s receiver layout len w0 w2 w3 w4 w5

/-- A thread made ready before a run that keeps every thread's binding is
still ready after it. -/
theorem ready_of_keepsBindings_receiverReady {W Y : SystemState} {r : SeLe4n.ThreadId}
    (hNoW : W.objects.noResizeDue) (hK : KeepsBindings (W.updateTcb r receiverReady) Y)
    {t : TCB} (h : Y.getTcb? r = some t) : t.ipcState = .ready := by
  obtain ⟨t0, h0, e0⟩ := hK.2 r t ((SystemState.getTcb?_eq_some_iff _ _ _).mp h)
  have h0' := (SystemState.getTcb?_eq_some_iff _ _ _).mpr h0
  rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoW,
    SystemState.mapTcbInPlace_getTcb?_self] at h0'
  have hI : t.ipcState = t0.ipcState := by
    have h' := congrArg TCB.ipcState (show t.withoutLinks = t0.withoutLinks from e0)
    exact h'
  cases hW : W.getTcb? r with
  | none => rw [hW] at h0'; cases h0'
  | some w =>
    rw [hW] at h0'
    simp only [Option.map_some, Option.some.injEq] at h0'
    rw [hI, ← h0']
    simp only [receiverReady, TCB.ipcState_setIpcState]

/-- The woken sender's completion frame reads every other thread where it was. -/
theorem stageWokenSendCompletion_getTcb?_ne (Y : SystemState) (s r : SeLe4n.ThreadId)
    (hNe : s ≠ r) (hNo : Y.objects.noResizeDue) :
    (Architecture.stageWokenSendCompletion Y (some s)).getTcb? r = Y.getTcb? r := by
  unfold Architecture.stageWokenSendCompletion
  dsimp only
  split
  · split
    · unfold Architecture.writeReturnFrameToTcb
      rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo, SystemState.getTcb?_mapTcbInPlace,
        if_neg hNe]
    · rfl
  · rfl

/-- The take's state before its transfer reads every buffer and CNode where the
receive found it. -/
theorem ipcBufferReadsAgree_takeReady (st : SystemState) (endpointId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (receiver : SeLe4n.ThreadId)
    (core : Concurrency.CoreId) (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree ((wakeThread ((storePopHead st endpointId false s next).updateTcb
      s receiverReady) s core).1.updateTcb receiver receiverReady) st := by
  have hR : ∀ t : TCB, (receiverReady t).vspaceRoot = t.vspaceRoot ∧
      (receiverReady t).ipcBuffer = t.ipcBuffer := fun _ => ⟨rfl, rfl⟩
  have h1 := storePopHead_noResizeDue st endpointId false s next hNo
  have h2 := updateTcb_noResizeDue _ s receiverReady h1
  have h3 := wakeThread_noResizeDue _ s core h2
  exact (ipcBufferReadsAgree_updateTcb _ receiver receiverReady hR h3).trans
    ((ipcBufferReadsAgree_wakeThread _ s core h2).trans
      ((ipcBufferReadsAgree_updateTcb _ s receiverReady hR h1).trans
        (ipcBufferReadsAgree_storePopHead st endpointId false s next hNo)))

/-! ## The take of a blocked call, delivered -/

/-- **The take of a blocked call that transfers capabilities, delivered**: the
caller popped and blocked on the reply, the reply object linked, the receiver
made ready, the transfer in place, the receiver's priority walk, then the
receiver's frame with the transfer's report, its words read from the caller's
saved registers `rf`, which the take leaves unwritten (the caller stays
blocked).  The caller and the receiver enter as the words the transfer reads
of them (`capTransferK`), read before the take. -/
@[noinline] def performCallTakeCapsDelivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (s : SeLe4n.ThreadId) (nextCode : Nat) (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (core : Concurrency.CoreId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badgeWord : SeLe4n.Badge) (badged : Bool)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  let X := storeReceiveCallReady st endpointId s nextCode receiver rid
  capTransferK X endpointId sv sb sroot count rv rb rroot fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    finishCallCaps (capStepsInfo endpointId true x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (capStepsApply endpointId true rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X)
      receiver core layout rf len badgeWord badged

end SeLe4n.Kernel
