-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.Boot
import SeLe4n.Platform.Boot.CapabilityLinks

/-!
# WS-ZA ZA6.32 — the interrupt nodes the boot creates

seL4's boot creates `intStateIRQNode`, one capability slot per interrupt line,
before it hands out any capability (`init_irqs`).  Here each line `l` of the
board (`irqNodeLineCount`: the configuration's `interruptLineCount`, at most the
model's `InterruptLineSet.capacity`) gets its own CNode of one empty slot at its
reserved id (`irqNodeId l`), installed the way every boot object is
(`createBootObject`).  The boot refuses a configuration that places an object at
one of those ids (`irqNodeIdsReserved`, a `wellFormed` conjunct), so an
install never overwrites an object.

No capability names a node (`capTargetsReservedKernelObject_irqNode`): its slot
holds the notification capability its line is bound to, which only
`seL4_IRQHandler_SetNotification` writes and `seL4_IRQHandler_Clear` empties.
-/

namespace SeLe4n.Platform.Boot

open SeLe4n.Model
open SeLe4n.Kernel.RobinHood

/-- An interrupt node at boot: a CNode of one slot (radix 0), empty. -/
def irqNodeCNode : CNode := CNode.ofList 0 0 0 0 []

/-- The boot object of line `line`'s interrupt node. -/
def irqNodeEntry (line : Nat) : ObjectEntry where
  id := irqNodeId line
  obj := .cnode irqNodeCNode
  hSlots := fun _ h => by cases h; exact CNode.slotsUnique_holds _
  hMappings := fun _ h => nomatch h

/-- **How many interrupt nodes a configuration's boot creates**: one per line of
the board, at most the model's line capacity (a line past it has no state). -/
def irqNodeLineCount (config : PlatformConfig) : Nat :=
  min config.machineConfig.interruptLineCount InterruptLineSet.capacity

/-- The boot objects of the first `n` lines' nodes. -/
def irqNodeEntries (n : Nat) : List ObjectEntry := (List.range n).map irqNodeEntry

/-- **Install the first `n` lines' interrupt nodes.** -/
def installIrqNodes (n : Nat) (ist : IntermediateState) : IntermediateState :=
  foldObjects (irqNodeEntries n) ist

/-- **No object holds one of the first `n` lines' node ids**: what the install
needs to only add (`installIrqNodes_objects_cases`). -/
def irqNodesFresh (n : Nat) (st : SystemState) : Bool :=
  (List.range n).all fun l => (st.getObject? (irqNodeId l)).isNone

-- ============================================================================
-- The install's objects
-- ============================================================================

theorem mem_irqNodeEntries {n : Nat} {e : ObjectEntry} :
    e ∈ irqNodeEntries n ↔ ∃ l, l < n ∧ irqNodeEntry l = e := by
  unfold irqNodeEntries
  simp only [List.mem_map, List.mem_range]

theorem irqNodeEntries_pairwise (n : Nat) :
    (irqNodeEntries n).Pairwise (fun a b => a.id ≠ b.id) := by
  unfold irqNodeEntries
  rw [List.pairwise_map]
  exact List.nodup_range.imp fun hNe hEq => hNe (irqNodeId_injective hEq)

/-- An id in the reserved range of the first `n` lines is a line's node. -/
theorem irqNodeId_of_isIrqNodeObjId {n : Nat} {k : SeLe4n.ObjId}
    (h : isIrqNodeObjId n k = true) :
    k.toNat - irqNodeIdBase < n ∧ irqNodeId (k.toNat - irqNodeIdBase) = k := by
  simp only [isIrqNodeObjId, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨by omega, ?_⟩
  apply SeLe4n.ObjId.ext
  simp only [irqNodeId, SeLe4n.ObjId.ofNat, SeLe4n.ObjId.toNat] at h ⊢
  omega

/-- **What the install stores**: every node of the first `n` lines, and the
state's own object everywhere else. -/
theorem installIrqNodes_objects (n : Nat) (ist : IntermediateState) (k : SeLe4n.ObjId) :
    (installIrqNodes n ist).state.objects[k]? =
      if isIrqNodeObjId n k then some (.cnode irqNodeCNode) else ist.state.objects[k]? := by
  unfold installIrqNodes
  split
  · next h =>
    obtain ⟨hl, hk⟩ := irqNodeId_of_isIrqNodeObjId h
    rw [← hk]
    exact foldObjects_objects_of_mem _ _ (irqNodeEntries_pairwise n) (irqNodeEntry _)
      (mem_irqNodeEntries.mpr ⟨_, hl, rfl⟩)
  · next h =>
    refine foldObjects_objects_ne _ _ _ fun e he hEq => ?_
    obtain ⟨l, hl, rfl⟩ := mem_irqNodeEntries.mp he
    have := isIrqNodeObjId_irqNodeId (count := n) hl
    exact h (hEq ▸ this)

/-- The freshness check, read per line. -/
theorem irqNodesFresh_spec {n : Nat} {st : SystemState} (h : irqNodesFresh n st = true)
    {l : Nat} (hl : l < n) : st.objects[irqNodeId l]? = none := by
  have := List.all_eq_true.mp h l (List.mem_range.mpr hl)
  exact Option.isNone_iff_eq_none.mp (by simpa [SystemState.getObject?] using this)

/-- **Over a fresh state the install only adds**: each id holds the state's own
object, or held nothing and holds an empty node. -/
theorem installIrqNodes_objects_cases {n : Nat} {ist : IntermediateState}
    (hFresh : irqNodesFresh n ist.state = true) (k : SeLe4n.ObjId) :
    (installIrqNodes n ist).state.objects[k]? = ist.state.objects[k]? ∨
      (ist.state.objects[k]? = none ∧
        (installIrqNodes n ist).state.objects[k]? = some (.cnode irqNodeCNode)) := by
  rw [installIrqNodes_objects]
  split
  · next h =>
    obtain ⟨hl, hk⟩ := irqNodeId_of_isIrqNodeObjId h
    exact .inr ⟨hk ▸ irqNodesFresh_spec hFresh hl, rfl⟩
  · exact .inl rfl

/-- The install keeps every object the state holds. -/
theorem installIrqNodes_objects_of_some {n : Nat} {ist : IntermediateState}
    (hFresh : irqNodesFresh n ist.state = true) {k : SeLe4n.ObjId} {o : KernelObject}
    (h : ist.state.objects[k]? = some o) : (installIrqNodes n ist).state.objects[k]? = some o := by
  rcases installIrqNodes_objects_cases hFresh k with e | ⟨e0, -⟩
  · rw [e]; exact h
  · rw [e0] at h; cases h

/-- A reader that sees an empty node as nothing sees the install as nothing. -/
theorem installIrqNodes_reader {α : Type} (f : Option KernelObject → α)
    (hf : f (some (.cnode irqNodeCNode)) = f none) {n : Nat} {ist : IntermediateState}
    (hFresh : irqNodesFresh n ist.state = true) (k : SeLe4n.ObjId) :
    f (installIrqNodes n ist).state.objects[k]? = f ist.state.objects[k]? := by
  rcases installIrqNodes_objects_cases hFresh k with h | ⟨h0, h1⟩
  · rw [h]
  · rw [h0, h1, hf]

/-- **What the install writes**: each step is a boot object's install. -/
theorem installIrqNodes_induct (P : IntermediateState → Prop) (n : Nat)
    (hStep : ∀ ist e, e ∈ irqNodeEntries n → P ist → P (createBootObject ist e))
    (ist : IntermediateState) (h : P ist) : P (installIrqNodes n ist) := by
  unfold installIrqNodes foldObjects
  suffices hL : ∀ (L : List ObjectEntry), (∀ e ∈ L, e ∈ irqNodeEntries n) →
      ∀ i, P i → P (L.foldl createBootObject i) from
    hL _ (fun _ he => he) ist h
  intro L
  induction L with
  | nil => intro _ i hi; exact hi
  | cons e rest ih =>
    intro hSub i hi
    exact ih (fun e' he => hSub e' (List.mem_cons_of_mem _ he)) _
      (hStep i e (hSub e List.mem_cons_self) hi)

/-- A field every boot install keeps, the node install keeps. -/
theorem installIrqNodes_frame {α : Type} (proj : SystemState → α)
    (hStep : ∀ ist e, proj (createBootObject ist e).state = proj ist.state)
    (n : Nat) (ist : IntermediateState) :
    proj (installIrqNodes n ist).state = proj ist.state :=
  installIrqNodes_induct (fun i => proj i.state = proj ist.state) n
    (fun i e _ h => (hStep i e).trans h) ist rfl

@[simp] theorem installIrqNodes_machine (n : Nat) (ist : IntermediateState) :
    (installIrqNodes n ist).state.machine = ist.state.machine :=
  installIrqNodes_frame (·.machine) (fun _ _ => rfl) n ist

@[simp] theorem installIrqNodes_scheduler (n : Nat) (ist : IntermediateState) :
    (installIrqNodes n ist).state.scheduler = ist.state.scheduler :=
  installIrqNodes_frame (·.scheduler) (fun _ _ => rfl) n ist

@[simp] theorem installIrqNodes_cdt (n : Nat) (ist : IntermediateState) :
    (installIrqNodes n ist).state.cdt = ist.state.cdt :=
  installIrqNodes_frame (·.cdt) (fun _ _ => rfl) n ist

@[simp] theorem installIrqNodes_interfaceRegistry (n : Nat) (ist : IntermediateState) :
    (installIrqNodes n ist).state.interfaceRegistry = ist.state.interfaceRegistry :=
  installIrqNodes_frame (·.interfaceRegistry) (fun _ _ => rfl) n ist

/-- A node registers no ASID, so the install keeps the ASID table. -/
@[simp] theorem installIrqNodes_asidTable (n : Nat) (ist : IntermediateState) :
    (installIrqNodes n ist).state.asidTable = ist.state.asidTable :=
  installIrqNodes_induct (fun i => i.state.asidTable = ist.state.asidTable) n
    (fun i e he h => by
      obtain ⟨l, -, rfl⟩ := mem_irqNodeEntries.mp he
      exact h) ist rfl

/-- The install keeps every thread record. -/
theorem installIrqNodes_getTcb? {n : Nat} {ist : IntermediateState}
    (hFresh : irqNodesFresh n ist.state = true) (t : SeLe4n.ThreadId) :
    (installIrqNodes n ist).state.getTcb? t = ist.state.getTcb? t := by
  unfold SystemState.getTcb?
  rcases installIrqNodes_objects_cases hFresh t.toObjId with h | ⟨h0, h1⟩
  · rw [h]
  · rw [h0, h1]

/-- …so every thread's run-queue reading. -/
theorem installIrqNodes_runnableOnSomeCore {n : Nat} {ist : IntermediateState}
    (hFresh : irqNodesFresh n ist.state = true) (t : SeLe4n.ThreadId) :
    SeLe4n.Kernel.runnableOnSomeCore (installIrqNodes n ist).state t =
      SeLe4n.Kernel.runnableOnSomeCore ist.state t := by
  unfold SeLe4n.Kernel.runnableOnSomeCore
  simp only [SystemState.queuedOn_of_getTcb? (installIrqNodes_getTcb? hFresh t)]

/-- The install keeps every started thread started. -/
theorem installIrqNodes_threadStarted {n : Nat} {ist : IntermediateState}
    (hFresh : irqNodesFresh n ist.state = true) {t : SeLe4n.ThreadId}
    (h : SeLe4n.Kernel.threadStarted ist.state t) :
    SeLe4n.Kernel.threadStarted (installIrqNodes n ist).state t :=
  ⟨(installIrqNodes_runnableOnSomeCore hFresh t).trans h.1,
    by rw [installIrqNodes_getTcb? hFresh]; exact h.2⟩

/-- The install keeps the thread-state classification: it stores no thread and
writes no scheduler field. -/
theorem installIrqNodes_threadStateConsistent {n : Nat} {ist : IntermediateState}
    (hFresh : irqNodesFresh n ist.state = true)
    (h : SeLe4n.Kernel.threadStateConsistent ist.state) :
    SeLe4n.Kernel.threadStateConsistent (installIrqNodes n ist).state := by
  intro oid tcb hO
  have hT : ist.state.objects[oid]? = some (.tcb tcb) := by
    rcases installIrqNodes_objects_cases hFresh oid with e | ⟨-, e⟩
    · rw [← e]; exact hO
    · rw [e] at hO; cases hO
  have hE : SeLe4n.Kernel.inferThreadState (installIrqNodes n ist).state ⟨oid.toNat⟩ tcb =
      SeLe4n.Kernel.inferThreadState ist.state ⟨oid.toNat⟩ tcb := by
    unfold SeLe4n.Kernel.inferThreadState SeLe4n.Kernel.threadQueuedOnSomeCore
      SeLe4n.Kernel.threadRunningOnSomeCore
    rw [installIrqNodes_runnableOnSomeCore hFresh]
    simp only [SeLe4n.Kernel.runningOnSomeCore, installIrqNodes_scheduler]
  rw [hE]; exact h oid tcb hT

/-- The install keeps the labeling's declared witnesses installed. -/
theorem installIrqNodes_declaredWitnessesInstalled {n : Nat} {ist : IntermediateState}
    (hFresh : irqNodesFresh n ist.state = true) (ctx : SeLe4n.Kernel.LabelingContext) :
    declaredWitnessesInstalled (installIrqNodes n ist).state ctx =
      declaredWitnessesInstalled ist.state ctx := by
  unfold declaredWitnessesInstalled
  simp only [installIrqNodes_getTcb? hFresh]

/-- The install keeps every slot's capability: a node's slot is empty. -/
theorem installIrqNodes_slotCapAt {n : Nat} {ist : IntermediateState}
    (hFresh : irqNodesFresh n ist.state = true) :
    (installIrqNodes n ist).state.slotCapAt = ist.state.slotCapAt := by
  funext r
  rw [SystemState.slotCapAt_eq_bind, SystemState.slotCapAt_eq_bind]
  exact installIrqNodes_reader (·.bind (·.slotCap r.slot)) (by
    show irqNodeCNode.lookup r.slot = none
    simp only [irqNodeCNode, CNode.ofList, List.foldl_nil, CNode.mk', CNode.lookup,
      CNode.slots_ofSlots, SeLe4n.UniqueSlotMap.get?_filter, SeLe4n.UniqueSlotMap.get?_empty,
      Option.filter_none]) hFresh r.cnode

/-- The install keeps every untyped record: a node is no untyped. -/
theorem installIrqNodes_getUntyped? {n : Nat} {ist : IntermediateState}
    (hFresh : irqNodesFresh n ist.state = true) :
    (installIrqNodes n ist).state.getUntyped? = ist.state.getUntyped? := by
  funext u
  rw [SystemState.getUntyped?_eq_bind, SystemState.getUntyped?_eq_bind]
  exact installIrqNodes_reader (·.bind KernelObject.untyped?) rfl hFresh u

/-- The install keeps every object in the store, and its tree. -/
theorem installIrqNodes_objectPresent {n : Nat} {ist : IntermediateState}
    (hFresh : irqNodesFresh n ist.state = true) (o : SeLe4n.ObjId)
    (h : ist.state.objectPresent o) : (installIrqNodes n ist).state.objectPresent o := by
  refine ⟨?_, SystemState.irqNodeIssued_of_lines
    (SystemState.irqSignalLines_of_cdt (installIrqNodes_cdt n ist)) o h.2⟩
  rcases installIrqNodes_objects_cases hFresh o with e | ⟨e0, -⟩
  · rw [e]; exact h.1
  · exact absurd e0 h.1

/-- An empty node has the boot shape. -/
theorem irqNodeCNode_bootObjectShape : bootObjectShape (.cnode irqNodeCNode) :=
  bootSafeObject_bootObjectShape (bootSafeObjectCheck_sound _ (by decide))
    (fun _ h => nomatch h)

/-- **The install keeps the boot shape**: it adds empty nodes where nothing was,
and writes no thread, queue, notification, untyped, ASID or tree. -/
theorem installIrqNodes_bootStartShape {n : Nat} {ist : IntermediateState}
    (hFresh : irqNodesFresh n ist.state = true) (h : bootStartShape ist) :
    bootStartShape (installIrqNodes n ist) := by
  obtain ⟨hShape, hFields, ⟨hAsid, hRoot⟩, hUnt, ⟨rq, re, rp, hSch⟩, hRun, ⟨hNodup, hQ⟩, hBind⟩ := h
  have hTcb := installIrqNodes_getTcb? hFresh
  refine ⟨fun oid obj hObj => ?_,
    installIrqNodes_induct (fun i => bootQuiescentFields i.state) n
      (fun i e _ hq => createBootObject_bootQuiescentFields i e hq) ist hFields,
    ⟨fun asid oid hA => ?_, fun oid root hR => ?_⟩,
    untypedRegionsDisjoint_of_untyped_subset hUnt fun oid ut hO => ?_,
    ⟨rq, re, rp, (installIrqNodes_scheduler n ist).trans hSch⟩,
    SystemState.runQueueRefined_of_frame
      (fun c t => SystemState.runLinkOn_of_getTcb? (hTcb t) c)
      (congrArg SchedulerState.runQueue (installIrqNodes_scheduler n ist))
      (congrArg SchedulerState.runQueueEnds (installIrqNodes_scheduler n ist)) hRun,
    ⟨by rw [installIrqNodes_scheduler]; exact hNodup, fun tid hm => ?_⟩,
    fun k => ?_⟩
  · rcases installIrqNodes_objects_cases hFresh oid with e | ⟨-, e⟩
    · rw [e] at hObj; exact hShape oid obj hObj
    · rw [e] at hObj; cases hObj; exact irqNodeCNode_bootObjectShape
  · rw [installIrqNodes_asidTable] at hA
    obtain ⟨root, hr, ha⟩ := hAsid asid oid hA
    rcases installIrqNodes_objects_cases hFresh oid with e | ⟨e0, -⟩
    · exact ⟨root, by rw [e]; exact hr, ha⟩
    · rw [e0] at hr; cases hr
  · rw [installIrqNodes_asidTable]
    rcases installIrqNodes_objects_cases hFresh oid with e | ⟨-, e⟩
    · rw [e] at hR; exact hRoot oid root hR
    · rw [e] at hR; cases hR
  · rcases installIrqNodes_objects_cases hFresh oid with e | ⟨-, e⟩
    · rw [e] at hO; exact hO
    · rw [e] at hO; cases hO
  · rw [installIrqNodes_scheduler] at hm
    obtain ⟨tcb, ht, rest⟩ := hQ tid hm
    refine ⟨tcb, ?_, by rw [installIrqNodes_scheduler]; exact rest⟩
    rcases installIrqNodes_objects_cases hFresh tid.toObjId with e | ⟨e0, -⟩
    · rw [e]; exact ht
    · rw [e0] at ht; cases ht
  · have hB := fun k => installIrqNodes_reader SeLe4n.Kernel.notificationBindingCodes rfl hFresh k
    simp only [hB]
    exact hBind k

/-- **The install keeps what the linking reads of the slots**: every slot's
capability, every untyped record, and every named object's presence. -/
theorem installIrqNodes_linkInputs {n : Nat} {ist : IntermediateState}
    (hFresh : irqNodesFresh n ist.state = true) (rs : List SlotRef)
    (hListed : bootSlotsListed rs ist.state)
    (hLive : ∀ r o, SystemState.namesAt ist.state.slotCapAt r o → ist.state.objectPresent o)
    (hUnique : ∀ u r r', SystemState.untypedCapAt ist.state.slotCapAt ist.state.getUntyped? r u →
      SystemState.untypedCapAt ist.state.slotCapAt ist.state.getUntyped? r' u → r = r')
    (hUncarved : ∀ u U, ist.state.getUntyped? u = some U → U.children = [])
    (hNamedU : ∀ r u, SystemState.namesAt ist.state.slotCapAt r u → ist.state.getUntyped? u ≠ none →
      SystemState.untypedCapAt ist.state.slotCapAt ist.state.getUntyped? r u) :
    let st := (installIrqNodes n ist).state
    bootSlotsListed rs st ∧
    (∀ r o, SystemState.namesAt st.slotCapAt r o → st.objectPresent o) ∧
    (∀ u r r', SystemState.untypedCapAt st.slotCapAt st.getUntyped? r u →
      SystemState.untypedCapAt st.slotCapAt st.getUntyped? r' u → r = r') ∧
    (∀ u U, st.getUntyped? u = some U → U.children = []) ∧
    (∀ r u, SystemState.namesAt st.slotCapAt r u → st.getUntyped? u ≠ none →
      SystemState.untypedCapAt st.slotCapAt st.getUntyped? r u) := by
  intro st
  have hC : st.slotCapAt = ist.state.slotCapAt := installIrqNodes_slotCapAt hFresh
  have hU : st.getUntyped? = ist.state.getUntyped? := installIrqNodes_getUntyped? hFresh
  refine ⟨fun r hr => hListed r (by rw [← hC]; exact hr), fun r o hn => ?_, ?_, ?_, ?_⟩
  · rw [hC] at hn; exact installIrqNodes_objectPresent hFresh o (hLive r o hn)
  · rw [hC, hU]; exact hUnique
  · rw [hU]; exact hUncarved
  · rw [hC, hU]; exact hNamedU

-- ============================================================================
-- The configured objects leave the nodes' ids free
-- ============================================================================

/-- An idle thread's slot is no interrupt node's. -/
theorem idleThreadId_toObjId_ne_irqNodeId (c : SeLe4n.Kernel.Concurrency.CoreId) (l : Nat) :
    (SeLe4n.Kernel.idleThreadId c).toObjId ≠ irqNodeId l := by
  intro h
  have h1 := congrArg SeLe4n.ObjId.toNat h
  have hc : c.val < 4 := c.isLt
  simp only [SeLe4n.Kernel.idleThreadId, SeLe4n.ThreadId.toObjId, SeLe4n.ThreadId.ofNat,
    SeLe4n.ThreadId.toNat, irqNodeId, SeLe4n.ObjId.ofNat, SeLe4n.ObjId.toNat] at h1
  simp only [SeLe4n.Kernel.idleThreadIdBase, irqNodeIdBase] at h1
  omega

/-- **The idle boot of a configuration that reserves the nodes' ids holds no
object at any of them.** -/
theorem bootFromPlatformCheckedWithIdleThreadsFor_irqNode_none
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (base : IntermediateState) (h : bootFromPlatformCheckedWithIdleThreadsFor cores config = .ok base)
    {l : Nat} (hl : l < InterruptLineSet.capacity) :
    base.state.objects[irqNodeId l]? = none := by
  have hN := isIrqNodeObjId_irqNodeId (count := InterruptLineSet.capacity) hl
  cases hChecked : bootFromPlatformChecked config with
  | error e =>
    rw [bootFromPlatformCheckedWithIdleThreadsFor_rejects_invalid cores config e hChecked] at h
    cases h
  | ok ist0 =>
    have hRes := config.wellFormed_irqNodeIdsReserved
      (bootFromPlatformChecked_ok_shape config ist0 hChecked).1
    simp only [irqNodeIdsReserved, Bool.and_eq_true] at hRes
    obtain ⟨hObjs, hRoot⟩ := hRes
    rw [List.all_eq_true] at hObjs
    have hNd := bootFromPlatformCheckedWithIdleThreadsFor_ok_nodup cores config base h
    rw [bootFromPlatformCheckedWithIdleThreadsFor_map_ok cores config ist0 hChecked
      (bootFromPlatformCheckedWithIdleThreadsFor_ok_affinitiesDeclared cores config base h)
      hNd] at h
    injection h with h
    subst h
    rw [foldl_storeIdleThread_objects_frame_of_not_idle _ _ _
      (fun c _ => idleThreadId_toObjId_ne_irqNodeId c l)]
    obtain ⟨_, _, hShape⟩ := bootFromPlatformChecked_ok_shape config ist0 hChecked
    cases hO : ist0.state.objects[irqNodeId l]? with
    | none => rfl
    | some obj =>
      exfalso
      have hCfg : (bootFromPlatform config).state.objects[irqNodeId l]? = some obj → False :=
        fun hB => by
          obtain ⟨e, he, hid, -⟩ := bootFromPlatform_objects_of_config config _ obj hB
          have := hObjs e he
          rw [hid, hN] at this
          simp at this
      rcases hShape with ⟨_, rfl⟩ | ⟨entry, hE, rfl⟩
      · rw [bootEnableInterruptsOp_objects_eq] at hO; exact hCfg hO
      · rw [bootEnableInterruptsOp_objects_eq] at hO
        by_cases hEq : entry.id = irqNodeId l
        · rw [hE] at hRoot
          simp [Option.all, hEq, hN] at hRoot
        · rw [installBootVSpaceRoot_objects_ne _ _ _ _ _ hEq] at hO; exact hCfg hO

end SeLe4n.Platform.Boot
