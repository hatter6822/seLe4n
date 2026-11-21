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
# WS-SX SX5.3 — the boot builds the root task's IPC buffer

seL4's boot gives its initial thread an IPC buffer before the thread first runs:
`create_rootserver_objects` cuts the buffer frame and the tables of the root
task's address space from the rootserver region, `create_it_address_space`
installs the tables, `create_ipcbuf_frame_cap` maps the frame and puts its
capability in the root CNode (`seL4_CapInitThreadIPCBuffer`), and
`create_initial_thread` derives that capability into the thread's `tcbBuffer`
slot and sets `tcbIPCBuffer`.  This module is that stage
(`installRootServer`), run after the interrupt nodes are installed and before
the capabilities are linked.

From the configuration's reservation (`RootServerReservation`, placed by the
`rootServerPlaced` conjunct of `PlatformConfig.wellFormed`) it builds:

* the buffer frame on the reservation's first page, mapped once (`mapEpoch` 1);
* the tables of levels 1, 2 and 3 on its next three pages, each installed in the
  root task's address space on the walk to the buffer address
  (`PageTableObject.installedAt`);
* the address space with those three table slots, the buffer's translation and
  its mapping epoch 0, as `.pageTableMap` and `.vspaceMap` would leave it;
* in the root CNode, the frame's capability recording that mapping, then the
  three tables' capabilities (seL4's `create_it_pt_cap`);
* in the thread, the frame's capability derived into the buffer slot
  (`TCB.ipcBufferSlot`), carrying no mapping record — seL4's `deriveCap` clears
  a frame capability's mapped address on AArch64 — and the buffer address.

The pages' scrub and the four descriptor stores are owed to memory: the stage
records them (`rootServerWrites`) and the boot entry performs and drains them
before the first schedule (WS-SX decision D15).  The linking then places the
root CNode's frame capability in the derivation tree first, so the thread's
copy is its child, as seL4's `cteInsert` makes it.

A reservation the state cannot take — its objects' ids held, its slots
occupied, its thread, CNode or address space not the kind it names
(`rootServerInstallable`) — leaves the state as it is; a well-formed
configuration's always can.
-/

namespace SeLe4n.Platform.Boot

open SeLe4n.Model
open SeLe4n.Model.Builder
open SeLe4n.Kernel
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.RobinHood

-- ============================================================================
-- §1  What the stage builds
-- ============================================================================

/-- The buffer's permissions: read-write, user, cacheable and never executable,
    seL4's `VMReadWrite` frame of `create_ipcbuf_frame_cap` (mapped with
    `executable = false`). -/
def rootServerBufferPerms : PagePermissions :=
  { read := true, write := true, execute := false, user := true, cacheable := true }

/-- The buffer frame: the reservation's first page, mapped once, so its next
    mapping takes epoch 1 (`tagFrameMapping` hands the current epoch and
    advances it). -/
def rootServerFrame (r : RootServerReservation) : FrameObject :=
  { base := r.pageAddr 0, mapEpoch := 1 }

/-- The level-`l` table: the reservation's page `l`, installed in address space
    `vsId` at the slot the walk to the buffer address takes. -/
def rootServerTable (r : RootServerReservation) (vsId : SeLe4n.ObjId) (l : Nat) :
    PageTableObject :=
  ({ base := r.pageAddr l } : PageTableObject).installedAt vsId l
    (PageTableSlot.indexOf l r.bufferVAddr)

/-- The table slot of level `l` on the walk to the buffer address. -/
def rootServerTableSlot (r : RootServerReservation) (l : Nat) : PageTableSlot :=
  ⟨l, PageTableSlot.indexOf l r.bufferVAddr, r.objId l⟩

/-- The root task's address space once the stage has run: the three table slots
    after its own, the buffer's translation, and its mapping epoch 0. -/
def rootServerVSpace (r : RootServerReservation) (vs : VSpaceRoot) : VSpaceRoot :=
  { vs with
    tables := vs.tables ++ [rootServerTableSlot r 1, rootServerTableSlot r 2, rootServerTableSlot r 3]
    mappings := vs.mappings.insert r.bufferVAddr (r.pageAddr 0, rootServerBufferPerms)
    mappingEpochs := vs.mappingEpochs.insert r.bufferVAddr 0 }

/-- The frame's capability in the root CNode: a carved frame's
    (`frameCapability`), recording the buffer's mapping in address space `asid`
    under epoch 0. -/
def rootServerFrameCap (r : RootServerReservation) (asid : SeLe4n.ASID) : Capability :=
  (frameCapability (r.objId 0)).setMapped asid r.bufferVAddr 0

/-- The thread's buffer-slot capability: the frame's, derived — its mapping
    record cleared, as seL4's AArch64 `Arch_deriveCap` clears a frame
    capability's mapped address and ASID. -/
def rootServerBufferCap (r : RootServerReservation) : Capability :=
  frameCapability (r.objId 0)

/-- The root CNode once the stage has run: the frame's capability in the
    reservation's first slot, the three tables' (`pageTableCapability`) in the
    next three. -/
def rootServerCNode (r : RootServerReservation) (asid : SeLe4n.ASID) (cn : CNode) : CNode :=
  (((cn.insert (r.cnodeSlot 0) (rootServerFrameCap r asid)).insert (r.cnodeSlot 1)
    (pageTableCapability (r.objId 1))).insert (r.cnodeSlot 2)
    (pageTableCapability (r.objId 2))).insert (r.cnodeSlot 3) (pageTableCapability (r.objId 3))

/-- The root task once the stage has run: the derived frame capability in its
    buffer slot and the buffer address set (seL4's `tcbBuffer`,
    `tcbIPCBuffer`). -/
def rootServerThread (r : RootServerReservation) (t : TCB) : TCB :=
  { t.insertSpaceCap TCB.ipcBufferSlot (rootServerBufferCap r) with ipcBuffer := r.bufferVAddr }

/-- **The state can take the reservation**: the thread's buffer slot is empty,
    the four root CNode slots are in range and empty, the address space owns
    its top-level table page, holds no table slot and does not map the buffer
    address, none of the four object ids holds an object or is an interrupt
    node's, the four pages are page aligned below the LPA bound and the buffer
    address is canonical. -/
def rootServerInstallable (st : SystemState) (r : RootServerReservation) (t : TCB) (cn : CNode)
    (vs : VSpaceRoot) : Bool :=
  t.spaceCells[2].isNone &&
    (List.range rootServerPages).all (fun i =>
      decide ((r.cnodeSlot i).toNat < cn.cells.size) && (cn.lookup (r.cnodeSlot i)).isNone &&
        (st.getObject? (r.objId i)).isNone) &&
    vs.tableBase.isSome && vs.tables.isEmpty && (vs.mappings[r.bufferVAddr]?).isNone &&
    decide (t.cspaceRoot ≠ r.thread.toObjId) && decide (t.vspaceRoot ≠ r.thread.toObjId) &&
    decide (t.cspaceRoot ≠ t.vspaceRoot) &&
    (List.range rootServerPages).all (fun i => decide ((r.pageAddr i).toNat % SeLe4n.pageBytes = 0) &&
      !isIrqNodeObjId InterruptLineSet.capacity (r.objId i)) &&
    decide ((r.pageAddr 0).toNat < 2 ^ 52) && r.bufferVAddr.isCanonical

/-- The entries the stage installs, in order: the frame, the three tables, the
    address space, the root CNode and the thread. -/
def rootServerEntries (r : RootServerReservation) (tid : SeLe4n.ObjId) (t : TCB) (cn : CNode)
    (vs : VSpaceRoot) (hvs : vs.mappings.invExt) : List ObjectEntry :=
  [ { id := r.objId 0, obj := .frame (rootServerFrame r)
      hSlots := fun _ h => (nomatch h), hMappings := fun _ h => (nomatch h) }
  , { id := r.objId 1, obj := .pageTable (rootServerTable r t.vspaceRoot 1)
      hSlots := fun _ h => (nomatch h), hMappings := fun _ h => (nomatch h) }
  , { id := r.objId 2, obj := .pageTable (rootServerTable r t.vspaceRoot 2)
      hSlots := fun _ h => (nomatch h), hMappings := fun _ h => (nomatch h) }
  , { id := r.objId 3, obj := .pageTable (rootServerTable r t.vspaceRoot 3)
      hSlots := fun _ h => (nomatch h), hMappings := fun _ h => (nomatch h) }
  , { id := t.vspaceRoot, obj := .vspaceRoot (rootServerVSpace r vs)
      hSlots := fun _ h => (nomatch h)
      hMappings := fun _ h => by
        cases h; exact RHTable.insert_preserves_invExt _ _ _ hvs }
  , { id := t.cspaceRoot, obj := .cnode (rootServerCNode r vs.asid cn)
      hSlots := fun _ h => by cases h; exact CNode.slotsUnique_holds _
      hMappings := fun _ h => (nomatch h) }
  , { id := tid, obj := .tcb (rootServerThread r t)
      hSlots := fun _ h => (nomatch h), hMappings := fun _ h => (nomatch h) } ]

/-- Install entries with the builder's `createObject` — no ASID registration,
    since the one address space among them is already registered under its
    ASID. -/
def createEntries (objs : List ObjectEntry) (ist : IntermediateState) : IntermediateState :=
  objs.foldl (fun i e => createObject i e.id e.obj e.hSlots e.hMappings) ist

/-- The physical writes the stage owes, read off the state it built: the four
    pages scrubbed (seL4 zeroes the rootserver region), then the table
    descriptor of each level's slot and the buffer's page descriptor. -/
def rootServerWrites (st : SystemState) (r : RootServerReservation) (vs : VSpaceRoot) :
    List PhysicalWrite :=
  [.zeroPage (r.pageAddr 0), .zeroPage (r.pageAddr 1), .zeroPage (r.pageAddr 2),
    .zeroPage (r.pageAddr 3)] ++
  (slotStore? st vs 1 (PageTableSlot.indexOf 1 r.bufferVAddr)).toList ++
  (slotStore? st vs 2 (PageTableSlot.indexOf 2 r.bufferVAddr)).toList ++
  (slotStore? st vs 3 (PageTableSlot.indexOf 3 r.bufferVAddr)).toList ++
  (mappingStore? st vs r.bufferVAddr).toList

/-- Record physical writes on an intermediate state: the ledger alone moves. -/
def recordBootPhysicalWrites (ist : IntermediateState) (ws : List PhysicalWrite) :
    IntermediateState where
  state := recordPhysicalWrites ist.state ws
  hAllTables := ist.hAllTables
  hPerObjectSlots := ist.hPerObjectSlots
  hPerObjectMappings := ist.hPerObjectMappings
  hLifecycleConsistent := ist.hLifecycleConsistent.of_frame rfl rfl (fun _ => rfl)
    ist.hLifecycleConsistent.types

/-- **WS-SX SX5.3 (D15): the boot's state with its physical-write ledger
    drained** — what the boot entry installs once it has performed the writes
    the boot owes (`Platform.FFI.bootAndInitialiseFromPlatformOn`). -/
def drainBootPhysicalWrites (ist : IntermediateState) : IntermediateState where
  state := clearPhysicalWrites ist.state
  hAllTables := ist.hAllTables
  hPerObjectSlots := ist.hPerObjectSlots
  hPerObjectMappings := ist.hPerObjectMappings
  hLifecycleConsistent := ist.hLifecycleConsistent.of_frame rfl rfl (fun _ => rfl)
    ist.hLifecycleConsistent.types

/-- **The stage at reservation `r`**: build the root task's buffer if the state
    can take it (`rootServerInstallable`), and record the writes it owes. -/
def installRootServerAt (r : RootServerReservation) (ist : IntermediateState) :
    IntermediateState :=
  match ist.state.getTcb? r.thread with
  | some t =>
    match ist.state.getCNode? t.cspaceRoot with
    | some cn =>
      match hV : ist.state.getVSpaceRoot? t.vspaceRoot with
      | some vs =>
        if rootServerInstallable ist.state r t cn vs then
          let built := createEntries
            (rootServerEntries r r.thread.toObjId t cn vs
              (ist.hPerObjectMappings _ vs ((SystemState.getVSpaceRoot?_eq_some_iff _ _ _).1 hV))) ist
          recordBootPhysicalWrites built (rootServerWrites built.state r (rootServerVSpace r vs))
        else ist
      | none => ist
    | none => ist
  | none => ist

/-- **WS-SX SX5.3: the boot's root-server stage** — the configuration's
    reservation installed (`installRootServerAt`), or nothing without one. -/
def installRootServer (config : PlatformConfig) (ist : IntermediateState) : IntermediateState :=
  match config.rootServer with
  | none => ist
  | some r => installRootServerAt r ist

-- ============================================================================
-- §2  What the stage stores
-- ============================================================================

@[simp] theorem createObject_objects (ist : IntermediateState) (id : SeLe4n.ObjId)
    (obj : KernelObject) (h1 h2) :
    (createObject ist id obj h1 h2).state.objects = ist.state.objects.insert id obj := rfl

/-- What the installs keep away from their ids. -/
theorem createEntries_objects_ne (objs : List ObjectEntry) (ist : IntermediateState)
    (oid : SeLe4n.ObjId) (h : ∀ e ∈ objs, e.id ≠ oid) :
    (createEntries objs ist).state.objects[oid]? = ist.state.objects[oid]? := by
  induction objs generalizing ist with
  | nil => rfl
  | cons e rest ih =>
      show (createEntries rest (createObject ist e.id e.obj e.hSlots e.hMappings)).state.objects[oid]? = _
      rw [ih _ (fun e' hMem => h e' (List.mem_cons_of_mem _ hMem)), createObject_objects]
      have hNe : ¬((e.id == oid) = true) := fun hEq => h e List.mem_cons_self (eq_of_beq hEq)
      exact RHTable.getElem?_insert_ne _ _ _ _ hNe ist.hAllTables.objects.1

/-- What the installs store at their ids, when the ids are distinct. -/
theorem createEntries_objects_of_mem (objs : List ObjectEntry) (ist : IntermediateState)
    (hUniq : objs.Pairwise (fun a b => a.id ≠ b.id)) (e : ObjectEntry) (hMem : e ∈ objs) :
    (createEntries objs ist).state.objects[e.id]? = some e.obj := by
  induction objs generalizing ist with
  | nil => cases hMem
  | cons x rest ih =>
      rw [List.pairwise_cons] at hUniq
      show (createEntries rest (createObject ist x.id x.obj x.hSlots x.hMappings)).state.objects[e.id]? = _
      rcases List.mem_cons.mp hMem with rfl | hRest
      · rw [createEntries_objects_ne _ _ _ (fun e' hE' => (hUniq.1 e' hE').symm),
          createObject_objects]
        exact RHTable.getElem?_insert_self _ _ _ ist.hAllTables.objects.1
      · exact ih _ hUniq.2 hRest

/-- A field every `createObject` keeps, the installs keep. -/
theorem createEntries_frame {α : Type} (proj : SystemState → α)
    (hStep : ∀ (ist : IntermediateState) id obj h1 h2,
      proj (createObject ist id obj h1 h2).state = proj ist.state)
    (objs : List ObjectEntry) (ist : IntermediateState) :
    proj (createEntries objs ist).state = proj ist.state := by
  induction objs generalizing ist with
  | nil => rfl
  | cons e rest ih => exact (ih _).trans (hStep _ _ _ _ _)

/-- The installable check, read clause by clause. -/
theorem rootServerInstallable_spec {st : SystemState} {r : RootServerReservation} {t : TCB}
    {cn : CNode} {vs : VSpaceRoot} (h : rootServerInstallable st r t cn vs = true) :
    t.spaceCells[2] = none ∧
    (∀ i, i < rootServerPages → (r.cnodeSlot i).toNat < cn.cells.size ∧
      cn.lookup (r.cnodeSlot i) = none ∧ st.objects[r.objId i]? = none) ∧
    vs.tableBase.isSome = true ∧ vs.tables = [] ∧ vs.mappings[r.bufferVAddr]? = none ∧
    t.cspaceRoot ≠ r.thread.toObjId ∧ t.vspaceRoot ≠ r.thread.toObjId ∧
    t.cspaceRoot ≠ t.vspaceRoot ∧
    (∀ i, i < rootServerPages → (r.pageAddr i).toNat % SeLe4n.pageBytes = 0 ∧
      isIrqNodeObjId InterruptLineSet.capacity (r.objId i) = false) ∧
    (r.pageAddr 0).toNat < 2 ^ 52 ∧ r.bufferVAddr.isCanonical = true := by
  unfold rootServerInstallable at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, hBound⟩, hCanon⟩ := h
  refine ⟨Option.isNone_iff_eq_none.mp h1, fun i hi => ?_, h3, List.isEmpty_iff.mp h4,
    Option.isNone_iff_eq_none.mp h5, of_decide_eq_true h6, of_decide_eq_true h7,
    of_decide_eq_true h8, fun i hi => ?_, of_decide_eq_true hBound, hCanon⟩
  · have := List.all_eq_true.mp h2 i (List.mem_range.mpr hi)
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have := List.all_eq_true.mp h9 i (List.mem_range.mpr hi)
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at this
    exact this

/-- **The objects the stage stores** over the store `old`: the four new objects
    at the reservation's ids, the address space, root CNode and thread rewritten,
    and `old` everywhere else. -/
def rootServerObjects (r : RootServerReservation) (t : TCB) (cn : CNode) (vs : VSpaceRoot)
    (old : SeLe4n.ObjId → Option KernelObject) (k : SeLe4n.ObjId) : Option KernelObject :=
  if k = r.objId 0 then some (.frame (rootServerFrame r))
  else if k = r.objId 1 then some (.pageTable (rootServerTable r t.vspaceRoot 1))
  else if k = r.objId 2 then some (.pageTable (rootServerTable r t.vspaceRoot 2))
  else if k = r.objId 3 then some (.pageTable (rootServerTable r t.vspaceRoot 3))
  else if k = t.vspaceRoot then some (.vspaceRoot (rootServerVSpace r vs))
  else if k = t.cspaceRoot then some (.cnode (rootServerCNode r vs.asid cn))
  else if k = r.thread.toObjId then some (.tcb (rootServerThread r t))
  else old k

/-- The stage's entries have distinct ids, over a state that can take them. -/
theorem rootServerEntries_pairwise {ist : IntermediateState} {r : RootServerReservation}
    {t : TCB} {cn : CNode} {vs : VSpaceRoot} (hvs : vs.mappings.invExt)
    (hT : ist.state.objects[r.thread.toObjId]? = some (.tcb t))
    (hC : ist.state.objects[t.cspaceRoot]? = some (.cnode cn))
    (hV : ist.state.objects[t.vspaceRoot]? = some (.vspaceRoot vs))
    (hI : rootServerInstallable ist.state r t cn vs = true) :
    (rootServerEntries r r.thread.toObjId t cn vs hvs).Pairwise (fun a b => a.id ≠ b.id) := by
  obtain ⟨-, hS, -, -, -, hCT, hVT, hCV, -⟩ := rootServerInstallable_spec hI
  have hFresh : ∀ i, i < rootServerPages → ∀ k o, ist.state.objects[k]? = some o →
      r.objId i ≠ k := fun i hi k o hk e => by
    rw [← e, (hS i hi).2.2] at hk; cases hk
  have hd : ∀ i j, i < rootServerPages → j < rootServerPages → i ≠ j → r.objId i ≠ r.objId j :=
    fun i j _ _ hij e => hij (r.objId_injective e)
  have p : rootServerPages = 4 := rfl
  simp only [rootServerEntries, List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
  refine ⟨⟨hd 0 1 (by omega) (by omega) (by omega), hd 0 2 (by omega) (by omega) (by omega),
      hd 0 3 (by omega) (by omega) (by omega), hFresh 0 (by omega) _ _ hV,
      hFresh 0 (by omega) _ _ hC, hFresh 0 (by omega) _ _ hT⟩,
    ⟨hd 1 2 (by omega) (by omega) (by omega), hd 1 3 (by omega) (by omega) (by omega),
      hFresh 1 (by omega) _ _ hV, hFresh 1 (by omega) _ _ hC, hFresh 1 (by omega) _ _ hT⟩,
    ⟨hd 2 3 (by omega) (by omega) (by omega), hFresh 2 (by omega) _ _ hV,
      hFresh 2 (by omega) _ _ hC, hFresh 2 (by omega) _ _ hT⟩,
    ⟨hFresh 3 (by omega) _ _ hV, hFresh 3 (by omega) _ _ hC, hFresh 3 (by omega) _ _ hT⟩,
    ⟨fun e => hCV e.symm, hVT⟩, hCT, fun _ h => h.elim⟩

/-- The stage's ids, over a state that can take it: the four fresh ids hold
    nothing, so differ from the thread, CNode and address space, which differ
    from one another. -/
theorem rootServer_ids_ne {st : SystemState} {r : RootServerReservation} {t : TCB} {cn : CNode}
    {vs : VSpaceRoot} (hT : st.objects[r.thread.toObjId]? = some (.tcb t))
    (hC : st.objects[t.cspaceRoot]? = some (.cnode cn))
    (hV : st.objects[t.vspaceRoot]? = some (.vspaceRoot vs))
    (hI : rootServerInstallable st r t cn vs = true) :
    (∀ i, i < rootServerPages → r.objId i ≠ r.thread.toObjId ∧ r.objId i ≠ t.cspaceRoot ∧
      r.objId i ≠ t.vspaceRoot) ∧
    t.cspaceRoot ≠ r.thread.toObjId ∧ t.vspaceRoot ≠ r.thread.toObjId ∧
    t.vspaceRoot ≠ t.cspaceRoot := by
  obtain ⟨-, hS, -, -, -, hCT, hVT, hCV, -⟩ := rootServerInstallable_spec hI
  refine ⟨fun i hi => ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩, hCT, hVT, fun e => hCV e.symm⟩
  · rw [← e, (hS i hi).2.2] at hT; cases hT
  · rw [← e, (hS i hi).2.2] at hC; cases hC
  · rw [← e, (hS i hi).2.2] at hV; cases hV

theorem rootServerObjects_thread {st : SystemState} {r : RootServerReservation} {t : TCB}
    {cn : CNode} {vs : VSpaceRoot} (hT : st.objects[r.thread.toObjId]? = some (.tcb t))
    (hC : st.objects[t.cspaceRoot]? = some (.cnode cn))
    (hV : st.objects[t.vspaceRoot]? = some (.vspaceRoot vs))
    (hI : rootServerInstallable st r t cn vs = true) (old : SeLe4n.ObjId → Option KernelObject) :
    rootServerObjects r t cn vs old r.thread.toObjId = some (.tcb (rootServerThread r t)) := by
  obtain ⟨hF, hCT, hVT, -⟩ := rootServer_ids_ne hT hC hV hI
  unfold rootServerObjects
  rw [if_neg (fun e => (hF 0 (by decide)).1 e.symm), if_neg (fun e => (hF 1 (by decide)).1 e.symm),
    if_neg (fun e => (hF 2 (by decide)).1 e.symm), if_neg (fun e => (hF 3 (by decide)).1 e.symm),
    if_neg (fun e => hVT e.symm), if_neg (fun e => hCT e.symm), if_pos rfl]

theorem rootServerObjects_cnode {st : SystemState} {r : RootServerReservation} {t : TCB}
    {cn : CNode} {vs : VSpaceRoot} (hT : st.objects[r.thread.toObjId]? = some (.tcb t))
    (hC : st.objects[t.cspaceRoot]? = some (.cnode cn))
    (hV : st.objects[t.vspaceRoot]? = some (.vspaceRoot vs))
    (hI : rootServerInstallable st r t cn vs = true) (old : SeLe4n.ObjId → Option KernelObject) :
    rootServerObjects r t cn vs old t.cspaceRoot = some (.cnode (rootServerCNode r vs.asid cn)) := by
  obtain ⟨hF, -, -, hVC⟩ := rootServer_ids_ne hT hC hV hI
  unfold rootServerObjects
  rw [if_neg (fun e => (hF 0 (by decide)).2.1 e.symm), if_neg (fun e => (hF 1 (by decide)).2.1 e.symm),
    if_neg (fun e => (hF 2 (by decide)).2.1 e.symm), if_neg (fun e => (hF 3 (by decide)).2.1 e.symm),
    if_neg (fun e => hVC e.symm), if_pos rfl]

theorem rootServerObjects_vspace {st : SystemState} {r : RootServerReservation} {t : TCB}
    {cn : CNode} {vs : VSpaceRoot} (hT : st.objects[r.thread.toObjId]? = some (.tcb t))
    (hC : st.objects[t.cspaceRoot]? = some (.cnode cn))
    (hV : st.objects[t.vspaceRoot]? = some (.vspaceRoot vs))
    (hI : rootServerInstallable st r t cn vs = true) (old : SeLe4n.ObjId → Option KernelObject) :
    rootServerObjects r t cn vs old t.vspaceRoot = some (.vspaceRoot (rootServerVSpace r vs)) := by
  obtain ⟨hF, -, -, -⟩ := rootServer_ids_ne hT hC hV hI
  unfold rootServerObjects
  rw [if_neg (fun e => (hF 0 (by decide)).2.2 e.symm), if_neg (fun e => (hF 1 (by decide)).2.2 e.symm),
    if_neg (fun e => (hF 2 (by decide)).2.2 e.symm), if_neg (fun e => (hF 3 (by decide)).2.2 e.symm),
    if_pos rfl]

theorem rootServerObjects_table {r : RootServerReservation} {t : TCB} {cn : CNode}
    {vs : VSpaceRoot} (old : SeLe4n.ObjId → Option KernelObject) {l : Nat} (hl1 : 1 ≤ l)
    (hl3 : l ≤ 3) :
    rootServerObjects r t cn vs old (r.objId l) =
      some (.pageTable (rootServerTable r t.vspaceRoot l)) := by
  have hne : ∀ j, j ≠ l → r.objId l ≠ r.objId j := fun j hj e => hj (r.objId_injective e).symm
  unfold rootServerObjects
  rcases (by omega : l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl
  · rw [if_neg (hne 0 (by decide)), if_pos rfl]
  · rw [if_neg (hne 0 (by decide)), if_neg (hne 1 (by decide)), if_pos rfl]
  · rw [if_neg (hne 0 (by decide)), if_neg (hne 1 (by decide)), if_neg (hne 2 (by decide)),
      if_pos rfl]

theorem rootServerObjects_frame {r : RootServerReservation} {t : TCB} {cn : CNode}
    {vs : VSpaceRoot} (old : SeLe4n.ObjId → Option KernelObject) :
    rootServerObjects r t cn vs old (r.objId 0) = some (.frame (rootServerFrame r)) := by
  unfold rootServerObjects; rw [if_pos rfl]

theorem rootServerObjects_other {r : RootServerReservation} {t : TCB} {cn : CNode}
    {vs : VSpaceRoot} (old : SeLe4n.ObjId → Option KernelObject) {k : SeLe4n.ObjId}
    (hk : ∀ i, i < rootServerPages → k ≠ r.objId i) (hv : k ≠ t.vspaceRoot)
    (hc : k ≠ t.cspaceRoot) (ht : k ≠ r.thread.toObjId) :
    rootServerObjects r t cn vs old k = old k := by
  unfold rootServerObjects
  rw [if_neg (hk 0 (by decide)), if_neg (hk 1 (by decide)), if_neg (hk 2 (by decide)),
    if_neg (hk 3 (by decide)), if_neg hv, if_neg hc, if_neg ht]

/-- The installs store `rootServerObjects`. -/
theorem createEntries_rootServerEntries_objects {ist : IntermediateState}
    {r : RootServerReservation} {t : TCB} {cn : CNode} {vs : VSpaceRoot} (hvs : vs.mappings.invExt)
    (hT : ist.state.objects[r.thread.toObjId]? = some (.tcb t))
    (hC : ist.state.objects[t.cspaceRoot]? = some (.cnode cn))
    (hV : ist.state.objects[t.vspaceRoot]? = some (.vspaceRoot vs))
    (hI : rootServerInstallable ist.state r t cn vs = true) (k : SeLe4n.ObjId) :
    (createEntries (rootServerEntries r r.thread.toObjId t cn vs hvs) ist).state.objects[k]? =
      rootServerObjects r t cn vs (fun k => ist.state.objects[k]?) k := by
  have hP := rootServerEntries_pairwise hvs hT hC hV hI
  have hMem := fun (e : ObjectEntry) (he : e ∈ rootServerEntries r r.thread.toObjId t cn vs hvs) =>
    createEntries_objects_of_mem _ ist hP e he
  have hAt := fun (i : Nat) (hi : i < 7) =>
    hMem _ (List.getElem_mem (l := rootServerEntries r r.thread.toObjId t cn vs hvs) (n := i)
      (by simpa [rootServerEntries] using hi))
  unfold rootServerObjects
  split
  · next h => subst h; exact hAt 0 (by omega)
  split
  · next h => subst h; exact hAt 1 (by omega)
  split
  · next h => subst h; exact hAt 2 (by omega)
  split
  · next h => subst h; exact hAt 3 (by omega)
  split
  · next h => subst h; exact hAt 4 (by omega)
  split
  · next h => subst h; exact hAt 5 (by omega)
  split
  · next h => subst h; exact hAt 6 (by omega)
  · next h0 h1 h2 h3 h4 h5 h6 =>
    refine createEntries_objects_ne _ _ _ fun e he hEq => ?_
    simp only [rootServerEntries, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact h0 hEq.symm | exact h1 hEq.symm | exact h2 hEq.symm | exact h3 hEq.symm
      | exact h4 hEq.symm | exact h5 hEq.symm | exact h6 hEq.symm

/-- **What the stage does**: nothing, or — over a thread, CNode and address
    space the state can take the reservation in — store `rootServerObjects` and
    record `rootServerWrites` of the state it built. -/
theorem installRootServerAt_cases (r : RootServerReservation) (ist : IntermediateState) :
    installRootServerAt r ist = ist ∨
    ∃ (t : TCB) (cn : CNode) (vs : VSpaceRoot) (hvs : vs.mappings.invExt),
      ist.state.objects[r.thread.toObjId]? = some (.tcb t) ∧
      ist.state.objects[t.cspaceRoot]? = some (.cnode cn) ∧
      ist.state.objects[t.vspaceRoot]? = some (.vspaceRoot vs) ∧
      rootServerInstallable ist.state r t cn vs = true ∧
      installRootServerAt r ist =
        recordBootPhysicalWrites (createEntries (rootServerEntries r r.thread.toObjId t cn vs hvs) ist)
          (rootServerWrites
            (createEntries (rootServerEntries r r.thread.toObjId t cn vs hvs) ist).state r
            (rootServerVSpace r vs)) := by
  unfold installRootServerAt
  split
  · next t hT =>
    split
    · next cn hC =>
      split
      · next vs hV =>
        split
        · next hI =>
          have hV' := (SystemState.getVSpaceRoot?_eq_some_iff _ _ _).1 hV
          exact .inr ⟨t, cn, vs, ist.hPerObjectMappings _ vs hV',
            (SystemState.getTcb?_eq_some_iff _ _ _).1 hT,
            (SystemState.getCNode?_eq_some_iff _ _ _).1 hC, hV', hI, rfl⟩
        · exact .inl rfl
      · exact .inl rfl
    · exact .inl rfl
  · exact .inl rfl

/-- A field every object install and the ledger's record keep, the stage
    keeps. -/
theorem installRootServer_frame {α : Type} (proj : SystemState → α)
    (hStep : ∀ (ist : IntermediateState) id obj h1 h2,
      proj (createObject ist id obj h1 h2).state = proj ist.state)
    (hRec : ∀ st ws, proj (recordPhysicalWrites st ws) = proj st)
    (config : PlatformConfig) (ist : IntermediateState) :
    proj (installRootServer config ist).state = proj ist.state := by
  unfold installRootServer
  split
  · rfl
  · next r _ =>
    rcases installRootServerAt_cases r ist with e | ⟨t, cn, vs, hvs, -, -, -, -, e⟩
    · rw [e]
    · rw [e]
      exact (hRec _ _).trans (createEntries_frame proj hStep _ _)

@[simp] theorem installRootServer_machine (config : PlatformConfig) (ist : IntermediateState) :
    (installRootServer config ist).state.machine = ist.state.machine :=
  installRootServer_frame (·.machine) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) config ist

@[simp] theorem installRootServer_scheduler (config : PlatformConfig) (ist : IntermediateState) :
    (installRootServer config ist).state.scheduler = ist.state.scheduler :=
  installRootServer_frame (·.scheduler) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) config ist

@[simp] theorem installRootServer_cdt (config : PlatformConfig) (ist : IntermediateState) :
    (installRootServer config ist).state.cdt = ist.state.cdt :=
  installRootServer_frame (·.cdt) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) config ist

@[simp] theorem installRootServer_asidTable (config : PlatformConfig) (ist : IntermediateState) :
    (installRootServer config ist).state.asidTable = ist.state.asidTable :=
  installRootServer_frame (·.asidTable) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) config ist

@[simp] theorem installRootServer_interfaceRegistry (config : PlatformConfig)
    (ist : IntermediateState) :
    (installRootServer config ist).state.interfaceRegistry = ist.state.interfaceRegistry :=
  installRootServer_frame (·.interfaceRegistry) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) config ist

@[simp] theorem recordBootPhysicalWrites_objects (ist : IntermediateState) (ws : List PhysicalWrite) :
    (recordBootPhysicalWrites ist ws).state.objects = ist.state.objects := rfl

/-- **What the stage stores, per id**: the state's object, or one of the four
    new objects where the state held none, or the address space, root CNode or
    thread rewritten as the stage rewrites it. -/
theorem installRootServer_objects_cases (config : PlatformConfig) (ist : IntermediateState)
    (k : SeLe4n.ObjId) :
    (installRootServer config ist).state.objects[k]? = ist.state.objects[k]? ∨
    ∃ r, config.rootServer = some r ∧
      ((ist.state.objects[k]? = none ∧
        ((installRootServer config ist).state.objects[k]? = some (.frame (rootServerFrame r)) ∨
         ∃ vsId l, (installRootServer config ist).state.objects[k]? =
           some (.pageTable (rootServerTable r vsId l)))) ∨
       (∃ vs, ist.state.objects[k]? = some (.vspaceRoot vs) ∧
          (installRootServer config ist).state.objects[k]? = some (.vspaceRoot (rootServerVSpace r vs))) ∨
       (∃ cn asid, ist.state.objects[k]? = some (.cnode cn) ∧
          (installRootServer config ist).state.objects[k]? = some (.cnode (rootServerCNode r asid cn))) ∨
       (∃ t, k = r.thread.toObjId ∧ ist.state.objects[k]? = some (.tcb t) ∧
          (installRootServer config ist).state.objects[k]? = some (.tcb (rootServerThread r t)))) := by
  unfold installRootServer
  split
  · exact .inl rfl
  · next r hr =>
    rcases installRootServerAt_cases r ist with e | ⟨t, cn, vs, hvs, hT, hC, hV, hI, e⟩
    · rw [e]; exact .inl rfl
    · rw [e, recordBootPhysicalWrites_objects, createEntries_rootServerEntries_objects hvs hT hC hV hI]
      obtain ⟨-, hS, -⟩ := rootServerInstallable_spec hI
      have hFresh : ∀ i, i < rootServerPages → ist.state.objects[r.objId i]? = none :=
        fun i hi => (hS i hi).2.2
      unfold rootServerObjects
      split
      · next h => subst h; exact .inr ⟨r, hr, .inl ⟨hFresh 0 (by decide), .inl rfl⟩⟩
      split
      · next h => subst h; exact .inr ⟨r, hr, .inl ⟨hFresh 1 (by decide), .inr ⟨_, _, rfl⟩⟩⟩
      split
      · next h => subst h; exact .inr ⟨r, hr, .inl ⟨hFresh 2 (by decide), .inr ⟨_, _, rfl⟩⟩⟩
      split
      · next h => subst h; exact .inr ⟨r, hr, .inl ⟨hFresh 3 (by decide), .inr ⟨_, _, rfl⟩⟩⟩
      split
      · next h => subst h; exact .inr ⟨r, hr, .inr (.inl ⟨vs, hV, rfl⟩)⟩
      split
      · next h => subst h; exact .inr ⟨r, hr, .inr (.inr (.inl ⟨cn, _, hC, rfl⟩))⟩
      split
      · next h => subst h; exact .inr ⟨r, hr, .inr (.inr (.inr ⟨t, rfl, hT, rfl⟩))⟩
      · exact .inl rfl

-- ============================================================================
-- §3  What the stage keeps of the threads and the scheduler
-- ============================================================================

/-- The rewritten thread keeps every field but its buffer slot and address. -/
@[simp] theorem rootServerThread_runCoreCode (r : RootServerReservation) (t : TCB) :
    (rootServerThread r t).runCoreCode = t.runCoreCode := rfl
@[simp] theorem rootServerThread_threadState (r : RootServerReservation) (t : TCB) :
    (rootServerThread r t).threadState = t.threadState := rfl
@[simp] theorem rootServerThread_ipcState (r : RootServerReservation) (t : TCB) :
    (rootServerThread r t).ipcState = t.ipcState := rfl

/-- **Every thread record after the stage** is the state's, or the root task's
    rewritten. -/
theorem installRootServer_getTcb? (config : PlatformConfig) (ist : IntermediateState)
    (tid : SeLe4n.ThreadId) :
    (installRootServer config ist).state.getTcb? tid = ist.state.getTcb? tid ∨
    ∃ r t, config.rootServer = some r ∧ ist.state.getTcb? tid = some t ∧
      (installRootServer config ist).state.getTcb? tid = some (rootServerThread r t) := by
  unfold SystemState.getTcb?
  rcases installRootServer_objects_cases config ist tid.toObjId with e | ⟨r, hr, h⟩
  · exact .inl (by rw [e])
  · rcases h with ⟨h0, h1 | ⟨_, _, h1⟩⟩ | ⟨vs, h0, h1⟩ | ⟨cn, _, h0, h1⟩ | ⟨t, -, h0, h1⟩
    · exact .inl (by rw [h0, h1])
    · exact .inl (by rw [h0, h1])
    · exact .inl (by rw [h0, h1])
    · exact .inl (by rw [h0, h1])
    · exact .inr ⟨r, t, hr, by rw [h0], by rw [h1]⟩

/-- The stage keeps every thread's presence. -/
theorem installRootServer_getTcb?_isSome (config : PlatformConfig) (ist : IntermediateState)
    (tid : SeLe4n.ThreadId) :
    ((installRootServer config ist).state.getTcb? tid).isSome = (ist.state.getTcb? tid).isSome := by
  rcases installRootServer_getTcb? config ist tid with e | ⟨r, t, -, h0, h1⟩
  · rw [e]
  · rw [h0, h1]; rfl

/-- The stage keeps every thread's run-queue core. -/
theorem installRootServer_queuedOn (config : PlatformConfig) (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (tid : SeLe4n.ThreadId) :
    (installRootServer config ist).state.queuedOn c tid = ist.state.queuedOn c tid := by
  unfold SystemState.queuedOn
  rcases installRootServer_getTcb? config ist tid with e | ⟨r, t, -, h0, h1⟩
  · rw [e]
  · rw [h0, h1]; rfl

theorem installRootServer_runnableOnSomeCore (config : PlatformConfig) (ist : IntermediateState)
    (tid : SeLe4n.ThreadId) :
    SeLe4n.Kernel.runnableOnSomeCore (installRootServer config ist).state tid =
      SeLe4n.Kernel.runnableOnSomeCore ist.state tid := by
  unfold SeLe4n.Kernel.runnableOnSomeCore
  simp only [installRootServer_queuedOn]

/-- The stage keeps every started thread started. -/
theorem installRootServer_threadStarted {config : PlatformConfig} {ist : IntermediateState}
    {tid : SeLe4n.ThreadId} (h : SeLe4n.Kernel.threadStarted ist.state tid) :
    SeLe4n.Kernel.threadStarted (installRootServer config ist).state tid := by
  refine ⟨(installRootServer_runnableOnSomeCore config ist tid).trans h.1, ?_⟩
  obtain ⟨t, ht, hs⟩ := h.2
  rcases installRootServer_getTcb? config ist tid with e | ⟨r, t', -, h0, h1⟩
  · exact ⟨t, e.trans ht, hs⟩
  · rw [ht] at h0; cases h0
    exact ⟨_, h1, hs⟩

/-- The stage keeps every thread's run links. -/
theorem installRootServer_runLinkOn (config : PlatformConfig) (ist : IntermediateState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (tid : SeLe4n.ThreadId) :
    (installRootServer config ist).state.runLinkOn c tid = ist.state.runLinkOn c tid := by
  unfold SystemState.runLinkOn
  rcases installRootServer_getTcb? config ist tid with e | ⟨r, t, -, h0, h1⟩
  · rw [e]
  · rw [h0, h1]; rfl

/-- The stage keeps every thread's state fields and affinity, so it is
    state-monotone. -/
theorem installRootServer_stateMono (config : PlatformConfig) (ist : IntermediateState) :
    SystemState.StateMono ist.state (installRootServer config ist).state :=
  SystemState.StateMono.of_stateFields fun tid => by
    rcases installRootServer_getTcb? config ist tid with e | ⟨r, t, -, h0, h1⟩
    · rw [e]
    · rw [h0, h1]; rfl

/-- The stage keeps the thread-state classification: it moves no thread on or
    off a core and rewrites the root task's buffer alone. -/
theorem installRootServer_threadStateConsistent {config : PlatformConfig}
    {ist : IntermediateState} (h : SeLe4n.Kernel.threadStateConsistent ist.state) :
    SeLe4n.Kernel.threadStateConsistent (installRootServer config ist).state := by
  intro oid tcb hO
  have hE : ∀ t : TCB, SeLe4n.Kernel.inferThreadState (installRootServer config ist).state
      ⟨oid.toNat⟩ t = SeLe4n.Kernel.inferThreadState ist.state ⟨oid.toNat⟩ t := by
    intro t
    unfold SeLe4n.Kernel.inferThreadState SeLe4n.Kernel.threadQueuedOnSomeCore
      SeLe4n.Kernel.threadRunningOnSomeCore
    rw [installRootServer_runnableOnSomeCore]
    simp only [SeLe4n.Kernel.runningOnSomeCore, installRootServer_scheduler]
  rw [hE]
  rcases installRootServer_objects_cases config ist oid with e | ⟨r, -, hc⟩
  · rw [e] at hO; exact h oid tcb hO
  · rcases hc with ⟨-, h1 | ⟨_, _, h1⟩⟩ | ⟨vs, -, h1⟩ | ⟨cn, _, -, h1⟩ | ⟨t, -, h0, h1⟩
    all_goals (rw [h1] at hO; try cases hO)
    have := h oid t h0
    unfold SeLe4n.Kernel.inferThreadState at this ⊢
    exact this

/-- The stage keeps the labeling's declared witnesses installed. -/
theorem installRootServer_declaredWitnessesInstalled (config : PlatformConfig)
    (ist : IntermediateState) (ctx : SeLe4n.Kernel.LabelingContext) :
    declaredWitnessesInstalled (installRootServer config ist).state ctx =
      declaredWitnessesInstalled ist.state ctx := by
  unfold declaredWitnessesInstalled
  simp only [installRootServer_getTcb?_isSome]

-- ============================================================================
-- §4  What the stage writes in the root CNode and the thread
-- ============================================================================

theorem CNode.insert_cells_size (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability) :
    (cn.insert slot cap).cells.size = cn.cells.size := by
  unfold CNode.insert; split <;> simp

theorem CNode.lookup_insert_of_lt (cn : CNode) (slot s : SeLe4n.Slot) (cap : Capability)
    (h : slot.toNat < cn.cells.size) :
    (cn.insert slot cap).lookup s = if s = slot then some cap else cn.lookup s := by
  split
  · next e =>
    subst e
    exact CNode.lookup_insert_eq cn s cap (CNode.slotsUnique_holds cn)
      ((CNode.slotAddressable_iff_lt_cells cn s).2 h)
  · next e => exact CNode.lookup_insert_ne cn slot s cap (fun h' => e h'.symm) (CNode.slotsUnique_holds cn)

/-- **The root CNode's slots after the stage**: the tables' capabilities in the
    reservation's last three slots, the mapped frame's in its first, and the
    CNode's own everywhere else. -/
theorem rootServerCNode_lookup (r : RootServerReservation) (asid : SeLe4n.ASID) (cn : CNode)
    (hIn : ∀ i, i < rootServerPages → (r.cnodeSlot i).toNat < cn.cells.size) (s : SeLe4n.Slot) :
    (rootServerCNode r asid cn).lookup s =
      if s = r.cnodeSlot 3 then some (pageTableCapability (r.objId 3))
      else if s = r.cnodeSlot 2 then some (pageTableCapability (r.objId 2))
      else if s = r.cnodeSlot 1 then some (pageTableCapability (r.objId 1))
      else if s = r.cnodeSlot 0 then some (rootServerFrameCap r asid)
      else cn.lookup s := by
  unfold rootServerCNode
  rw [CNode.lookup_insert_of_lt _ _ _ _ (by simpa [CNode.insert_cells_size] using hIn 3 (by decide)),
    CNode.lookup_insert_of_lt _ _ _ _ (by simpa [CNode.insert_cells_size] using hIn 2 (by decide)),
    CNode.lookup_insert_of_lt _ _ _ _ (by simpa [CNode.insert_cells_size] using hIn 1 (by decide)),
    CNode.lookup_insert_of_lt _ _ _ _ (hIn 0 (by decide))]

@[simp] theorem rootServerCNode_radixWidth (r : RootServerReservation) (asid : SeLe4n.ASID)
    (cn : CNode) : (rootServerCNode r asid cn).radixWidth = cn.radixWidth := by
  simp [rootServerCNode]

@[simp] theorem rootServerCNode_cells_size (r : RootServerReservation) (asid : SeLe4n.ASID)
    (cn : CNode) : (rootServerCNode r asid cn).cells.size = cn.cells.size := by
  simp [rootServerCNode, CNode.insert_cells_size]

/-- **The thread's space slots after the stage**: the derived frame capability
    in its buffer slot, its roots where they were. -/
theorem rootServerThread_spaceSlotCap (r : RootServerReservation) (t : TCB) (s : SeLe4n.Slot) :
    (rootServerThread r t).spaceSlotCap s =
      if s = TCB.ipcBufferSlot then some (rootServerBufferCap r) else t.spaceSlotCap s :=
  TCB.spaceSlotCap_insertSpaceCap t (by decide) _ s

@[simp] theorem rootServerThread_cspaceRoot (r : RootServerReservation) (t : TCB) :
    (rootServerThread r t).cspaceRoot = t.cspaceRoot := by
  show TCB.spaceCellObject (t.spaceCells.setIfInBounds 2 _)[0] = TCB.spaceCellObject t.spaceCells[0]
  rw [Vector.getElem_setIfInBounds_ne (by decide) (by decide)]

@[simp] theorem rootServerThread_vspaceRoot (r : RootServerReservation) (t : TCB) :
    (rootServerThread r t).vspaceRoot = t.vspaceRoot := by
  show TCB.spaceCellObject (t.spaceCells.setIfInBounds 2 _)[1] = TCB.spaceCellObject t.spaceCells[1]
  rw [Vector.getElem_setIfInBounds_ne (by decide) (by decide)]

/-- **A capability the stage makes**: the mapped frame's (in the root CNode),
    its derived copy (in the buffer slot), or a table's. -/
def rootServerCap (r : RootServerReservation) (c : Capability) : Prop :=
  (∃ asid, c = rootServerFrameCap r asid) ∨ c = rootServerBufferCap r ∨
    ∃ l, 1 ≤ l ∧ l ≤ 3 ∧ c = pageTableCapability (r.objId l)

/-- **Every slot after the stage** holds what it held, or held nothing and is
    one of the slots the stage fills (`rootServerSlotRefs`), now holding one of
    the stage's capabilities. -/
theorem installRootServer_slotCapAt_cases (config : PlatformConfig) (ist : IntermediateState)
    (ref : SlotRef) :
    (installRootServer config ist).state.slotCapAt ref = ist.state.slotCapAt ref ∨
    (ist.state.slotCapAt ref = none ∧
      ref ∈ rootServerSlotRefs config (installRootServer config ist).state ∧
      ∃ r c, config.rootServer = some r ∧
        (installRootServer config ist).state.slotCapAt ref = some c ∧ rootServerCap r c) := by
  unfold installRootServer
  split
  · exact .inl rfl
  · next r hr =>
    rcases installRootServerAt_cases r ist with e | ⟨t, cn, vs, hvs, hT, hC, hV, hI, e⟩
    · rw [e]; exact .inl rfl
    · rw [e]
      have hO := createEntries_rootServerEntries_objects hvs hT hC hV hI
      obtain ⟨-, hS, -⟩ := rootServerInstallable_spec hI
      have hFresh : ∀ i, i < rootServerPages → ist.state.objects[r.objId i]? = none :=
        fun i hi => (hS i hi).2.2
      have hRefs : rootServerSlotRefs config
          (recordBootPhysicalWrites (createEntries (rootServerEntries r r.thread.toObjId t cn vs hvs) ist)
            (rootServerWrites (createEntries (rootServerEntries r r.thread.toObjId t cn vs hvs) ist).state r
              (rootServerVSpace r vs))).state =
          (List.range rootServerPages).map (fun i => ⟨t.cspaceRoot, r.cnodeSlot i⟩) ++
            [⟨r.thread.toObjId, TCB.ipcBufferSlot⟩] := by
        unfold rootServerSlotRefs
        rw [hr]
        simp only [SystemState.getTcb?, recordBootPhysicalWrites_objects, hO,
          rootServerObjects_thread hT hC hV hI, rootServerThread_cspaceRoot]
      rw [SystemState.slotCapAt_eq_bind, SystemState.slotCapAt_eq_bind, recordBootPhysicalWrites_objects,
        hO, hRefs]
      obtain ⟨hF, hCT, hVT, hVC⟩ := rootServer_ids_ne hT hC hV hI
      obtain ⟨hB, -⟩ := rootServerInstallable_spec hI
      have hIn : ∀ i, i < rootServerPages → (r.cnodeSlot i).toNat < cn.cells.size :=
        fun i hi => (hS i hi).1
      by_cases hk : ∃ i, i < rootServerPages ∧ ref.cnode = r.objId i
      · obtain ⟨i, hi, hk⟩ := hk
        left
        rw [hk, hFresh i hi]
        rcases (by unfold rootServerPages at hi; omega : i = 0 ∨ 1 ≤ i ∧ i ≤ 3) with rfl | ⟨h1, h3⟩
        · rw [rootServerObjects_frame]; rfl
        · rw [rootServerObjects_table _ h1 h3]; rfl
      have hk' : ∀ i, i < rootServerPages → ref.cnode ≠ r.objId i := fun i hi e => hk ⟨i, hi, e⟩
      by_cases hv : ref.cnode = t.vspaceRoot
      · left; rw [hv, rootServerObjects_vspace hT hC hV hI, hV]; rfl
      by_cases hc : ref.cnode = t.cspaceRoot
      · rw [hc, rootServerObjects_cnode hT hC hV hI, hC]
        simp only [Option.bind_some, KernelObject.slotCap]
        rw [rootServerCNode_lookup r vs.asid cn hIn]
        have hNew : ∀ i, i < rootServerPages → ref.slot = r.cnodeSlot i →
            cn.lookup ref.slot = none ∧
            (⟨t.cspaceRoot, ref.slot⟩ : SlotRef) ∈ (List.range rootServerPages).map
              (fun i => (⟨t.cspaceRoot, r.cnodeSlot i⟩ : SlotRef)) ++
              [⟨r.thread.toObjId, TCB.ipcBufferSlot⟩] := fun i hi e => by
          refine ⟨e ▸ (hS i hi).2.1, List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, ?_⟩)⟩
          rw [e]
        have hRef : ref = ⟨t.cspaceRoot, ref.slot⟩ := by cases ref; simp_all
        split
        · next e => obtain ⟨h0, hm⟩ := hNew 3 (by decide) e
                    exact .inr ⟨h0, hRef ▸ hm, r, _, hr, rfl, .inr (.inr ⟨3, by decide, by decide, rfl⟩)⟩
        split
        · next e => obtain ⟨h0, hm⟩ := hNew 2 (by decide) e
                    exact .inr ⟨h0, hRef ▸ hm, r, _, hr, rfl, .inr (.inr ⟨2, by decide, by decide, rfl⟩)⟩
        split
        · next e => obtain ⟨h0, hm⟩ := hNew 1 (by decide) e
                    exact .inr ⟨h0, hRef ▸ hm, r, _, hr, rfl, .inr (.inr ⟨1, by decide, by decide, rfl⟩)⟩
        split
        · next e => obtain ⟨h0, hm⟩ := hNew 0 (by decide) e
                    exact .inr ⟨h0, hRef ▸ hm, r, _, hr, rfl, .inl ⟨_, rfl⟩⟩
        · exact .inl rfl
      by_cases ht : ref.cnode = r.thread.toObjId
      · rw [ht, rootServerObjects_thread hT hC hV hI, hT]
        simp only [Option.bind_some, KernelObject.slotCap]
        rw [rootServerThread_spaceSlotCap]
        split
        · next e =>
          have hRef : ref = ⟨r.thread.toObjId, TCB.ipcBufferSlot⟩ := by cases ref; simp_all
          refine .inr ⟨?_, hRef ▸ List.mem_append_right _ (List.mem_singleton_self _), r, _, hr, rfl,
            .inr (.inl rfl)⟩
          rw [e]; exact hB
        · exact .inl rfl
      · left; rw [rootServerObjects_other _ hk' hv hc ht]


-- ============================================================================
-- §5  The shape the stage leaves
-- ============================================================================

/-- **What the stage does, read off the store**: nothing, or — over a thread,
    CNode and address space the state can take the reservation in — every key
    holds `rootServerObjects` over the old store. -/
theorem installRootServer_installed (config : PlatformConfig) (ist : IntermediateState) :
    installRootServer config ist = ist ∨
    ∃ r t cn vs, config.rootServer = some r ∧
      ist.state.objects[r.thread.toObjId]? = some (.tcb t) ∧
      ist.state.objects[t.cspaceRoot]? = some (.cnode cn) ∧
      ist.state.objects[t.vspaceRoot]? = some (.vspaceRoot vs) ∧
      rootServerInstallable ist.state r t cn vs = true ∧
      ∀ k, (installRootServer config ist).state.objects[k]? =
        rootServerObjects r t cn vs (fun k => ist.state.objects[k]?) k := by
  unfold installRootServer
  split
  · exact .inl rfl
  · next r hr =>
    rcases installRootServerAt_cases r ist with e | ⟨t, cn, vs, hvs, hT, hC, hV, hI, e⟩
    · exact .inl e
    · refine .inr ⟨r, t, cn, vs, hr, hT, hC, hV, hI, fun k => ?_⟩
      rw [e, recordBootPhysicalWrites_objects, createEntries_rootServerEntries_objects hvs hT hC hV hI]

/-- The stage keeps the quiescent fields: it writes objects and the ledger. -/
theorem installRootServer_bootQuiescentFields (config : PlatformConfig) (ist : IntermediateState)
    (h : bootQuiescentFields ist.state) : bootQuiescentFields (installRootServer config ist).state := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨(installRootServer_cdt config ist).trans h0,
    (installRootServer_frame (·.tlb) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) config ist).trans h1,
    (installRootServer_frame (·.tlbShootdown) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) config ist).trans h2,
    (installRootServer_frame (·.perCoreTlb) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) config ist).trans h3,
    (installRootServer_frame (·.perCoreICache) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) config ist).trans h4,
    (installRootServer_frame (·.declassificationAuditLog) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl)
      config ist).trans h5⟩

/-- The buffer frame has the boot shape: a whole page of RAM. -/
theorem rootServerFrame_bootObjectShape {r : RootServerReservation}
    (h : (r.pageAddr 0).toNat % SeLe4n.pageBytes = 0) :
    bootObjectShape (.frame (rootServerFrame r)) :=
  ⟨⟨fun _ e => (by cases e), fun _ e => (by cases e), fun _ e => (by cases e),
    fun _ e => (by cases e), fun _ e => (by cases e), fun _ e => (by cases e),
    fun _ e => (by cases e), fun f e => by cases e; exact ⟨h, rfl⟩, fun _ e => (by cases e)⟩,
   fun _ e => (by cases e), fun _ e => (by cases e)⟩

/-- A table on the buffer's walk has the boot shape: a whole page. -/
theorem rootServerTable_bootObjectShape {r : RootServerReservation} {vsId : SeLe4n.ObjId} {l : Nat}
    (h : (r.pageAddr l).toNat % SeLe4n.pageBytes = 0) :
    bootObjectShape (.pageTable (rootServerTable r vsId l)) :=
  ⟨⟨fun _ e => (by cases e), fun _ e => (by cases e), fun _ e => (by cases e),
    fun _ e => (by cases e), fun _ e => (by cases e), fun _ e => (by cases e),
    fun _ e => (by cases e), fun _ e => (by cases e), fun p e => by cases e; exact h⟩,
   fun _ e => (by cases e), fun _ e => (by cases e)⟩

/-- **The root task's address space keeps its mapping facts**: the buffer's
    translation is read-write and never executable, to a page below the LPA
    bound, at a canonical address, and both tables keep their room. -/
theorem rootServerVSpace_mappingsSafe {r : RootServerReservation} {vs : VSpaceRoot}
    (hS : SeLe4n.Platform.RPi5.VSpaceBoot.bootVSpaceRootMappingsSafe vs) (hvs : vs.mappings.invExt)
    (hP : (r.pageAddr 0).toNat < 2 ^ 52) (hC : r.bufferVAddr.isCanonical = true) :
    SeLe4n.Platform.RPi5.VSpaceBoot.bootVSpaceRootMappingsSafe (rootServerVSpace r vs) := by
  obtain ⟨hM, hLt, hCap, hE⟩ := hS
  have hK := RHTable.insert_preserves_invExtK vs.mappings r.bufferVAddr
    (r.pageAddr 0, rootServerBufferPerms) ⟨hvs, hLt, hCap⟩
  refine ⟨fun v p perms hm => ?_, hK.2.1, hK.2.2, RHTable.insert_preserves_invExtK _ _ _ hE⟩
  change (vs.mappings.insert r.bufferVAddr (r.pageAddr 0, rootServerBufferPerms)).get? v = _ at hm
  by_cases hv : r.bufferVAddr = v
  · subst hv
    rw [RHTable.getElem?_insert_self _ _ _ hvs] at hm
    cases hm
    exact ⟨by decide, hP, hC⟩
  · rw [RHTable.getElem?_insert_ne _ _ _ _ (fun h => hv (eq_of_beq h)) hvs] at hm
    exact hM v p perms hm

/-- **The root CNode keeps its shape**: the four capabilities it gains carry no
    badge and none is a reply capability. -/
theorem rootServerCNode_bootCNodeShape {r : RootServerReservation} {asid : SeLe4n.ASID} {cn : CNode}
    (h : bootCNodeShape cn)
    (hIn : ∀ i, i < rootServerPages → (r.cnodeSlot i).toNat < cn.cells.size) :
    bootCNodeShape (rootServerCNode r asid cn) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by simpa using h1, by simpa using h2, fun slot cap badge hl hb => ?_,
    fun slot cap rid hl ht => ?_⟩
  · rw [rootServerCNode_lookup r asid cn hIn] at hl
    split at hl
    · cases hl; cases hb
    split at hl
    · cases hl; cases hb
    split at hl
    · cases hl; cases hb
    split at hl
    · cases hl; cases hb
    · exact h3 slot cap badge hl hb
  · rw [rootServerCNode_lookup r asid cn hIn] at hl
    split at hl
    · cases hl; cases ht
    split at hl
    · cases hl; cases ht
    split at hl
    · cases hl; cases ht
    split at hl
    · cases hl; cases ht
    · exact h4 slot cap rid hl ht

@[simp] theorem rootServerCNode_linksClear (r : RootServerReservation) (asid : SeLe4n.ASID)
    (cn : CNode) : (rootServerCNode r asid cn).linksClear = cn.linksClear := by
  simp [rootServerCNode, CNode.linksClear, CNode.insert_links]

/-- **The root task keeps its shape**: the derived frame capability in its
    buffer slot carries no badge and no mapping record, and is no reply
    capability. -/
theorem rootServerThread_bootTcbShape {r : RootServerReservation} {t : TCB} (h : bootTcbShape t) :
    bootTcbShape (rootServerThread r t) := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, ⟨c1, c2, c3⟩, t17,
    t18⟩ := h
  refine ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15,
    ⟨fun s cap b hc hb => ?_, fun s cap rid hc ht => ?_, fun s cap hc => ?_⟩, t17, t18⟩
  · rw [rootServerThread_spaceSlotCap] at hc
    split at hc
    · cases hc; cases hb
    · exact c1 s cap b hc hb
  · rw [rootServerThread_spaceSlotCap] at hc
    split at hc
    · cases hc; cases ht
    · exact c2 s cap rid hc ht
  · rw [rootServerThread_spaceSlotCap] at hc
    split at hc
    · cases hc; rfl
    · exact c3 s cap hc

@[simp] theorem rootServerThread_spaceLinksClear (r : RootServerReservation) (t : TCB) :
    (rootServerThread r t).spaceLinksClear = t.spaceLinksClear := rfl

/-- The root CNode, after the stage, holds the mapped frame's capability in the
    reservation's first slot. -/
theorem rootServerCNode_lookup_frame (r : RootServerReservation) (asid : SeLe4n.ASID) (cn : CNode)
    (hIn : ∀ i, i < rootServerPages → (r.cnodeSlot i).toNat < cn.cells.size) :
    (rootServerCNode r asid cn).lookup (r.cnodeSlot 0) = some (rootServerFrameCap r asid) := by
  rw [rootServerCNode_lookup r asid cn hIn,
    if_neg (fun h => absurd (r.cnodeSlot_injective h) (by decide)),
    if_neg (fun h => absurd (r.cnodeSlot_injective h) (by decide)),
    if_neg (fun h => absurd (r.cnodeSlot_injective h) (by decide)), if_pos rfl]

/-- Every key the stage does not write holds what the old store held. -/
theorem rootServerObjects_cases (r : RootServerReservation) (t : TCB) (cn : CNode) (vs : VSpaceRoot)
    (old : SeLe4n.ObjId → Option KernelObject) (k : SeLe4n.ObjId) :
    rootServerObjects r t cn vs old k = old k ∨ (∃ i, i < rootServerPages ∧ k = r.objId i) ∨
      k = t.vspaceRoot ∨ k = t.cspaceRoot ∨ k = r.thread.toObjId := by
  by_cases h : ∃ i, i < rootServerPages ∧ k = r.objId i
  · exact .inr (.inl h)
  have hk : ∀ i, i < rootServerPages → k ≠ r.objId i := fun i hi e => h ⟨i, hi, e⟩
  by_cases hv : k = t.vspaceRoot
  · exact .inr (.inr (.inl hv))
  by_cases hc : k = t.cspaceRoot
  · exact .inr (.inr (.inr (.inl hc)))
  by_cases ht : k = r.thread.toObjId
  · exact .inr (.inr (.inr (.inr ht)))
  exact .inl (rootServerObjects_other old hk hv hc ht)

/-- The stage's objects have the boot shape. -/
theorem installRootServer_objectShape {config : PlatformConfig} {ist : IntermediateState}
    {r : RootServerReservation} {t : TCB} {cn : CNode} {vs : VSpaceRoot}
    (hT : ist.state.objects[r.thread.toObjId]? = some (.tcb t))
    (hC : ist.state.objects[t.cspaceRoot]? = some (.cnode cn))
    (hV : ist.state.objects[t.vspaceRoot]? = some (.vspaceRoot vs))
    (hI : rootServerInstallable ist.state r t cn vs = true)
    (hO : ∀ k, (installRootServer config ist).state.objects[k]? =
      rootServerObjects r t cn vs (fun k => ist.state.objects[k]?) k)
    (hShape : ∀ (oid : SeLe4n.ObjId) (obj : KernelObject),
      ist.state.objects[oid]? = some obj → bootObjectShape obj) :
    ∀ (oid : SeLe4n.ObjId) (obj : KernelObject),
      (installRootServer config ist).state.objects[oid]? = some obj → bootObjectShape obj := by
  obtain ⟨-, hS, -, -, -, -, -, -, hAl, hP, hCan⟩ := rootServerInstallable_spec hI
  have hFresh : ∀ i, i < rootServerPages → ist.state.objects[r.objId i]? = none :=
    fun i hi => (hS i hi).2.2
  have hIn : ∀ i, i < rootServerPages → (r.cnodeSlot i).toNat < cn.cells.size :=
    fun i hi => (hS i hi).1
  have hvs := ist.hPerObjectMappings _ vs hV
  intro oid obj hObj
  rw [hO] at hObj; unfold rootServerObjects at hObj
  split at hObj
  · rename_i h0; cases hObj; exact rootServerFrame_bootObjectShape (hAl 0 (by decide)).1
  split at hObj
  · rename_i h1; cases hObj; exact rootServerTable_bootObjectShape (hAl 1 (by decide)).1
  split at hObj
  · rename_i h2; cases hObj; exact rootServerTable_bootObjectShape (hAl 2 (by decide)).1
  split at hObj
  · rename_i h3; cases hObj; exact rootServerTable_bootObjectShape (hAl 3 (by decide)).1
  split at hObj
  · rename_i h4; cases hObj
    have hs := ((hShape _ _ hV).1.2.2.2.2.1 vs rfl)
    exact ⟨⟨fun _ e => (by cases e), fun _ e => (by cases e), fun _ e => (by cases e),
      fun _ e => (by cases e), fun x e => by cases e; exact rootServerVSpace_mappingsSafe hs hvs hP hCan,
      fun _ e => (by cases e), fun _ e => (by cases e), fun _ e => (by cases e),
      fun _ e => (by cases e)⟩, fun _ e => (by cases e), fun _ e => (by cases e)⟩
  split at hObj
  · rename_i h5; cases hObj
    have hs := (hShape _ _ hC).1.2.2.1 cn rfl
    have hl := (hShape _ _ hC).2.1 cn rfl
    exact ⟨⟨fun _ e => (by cases e), fun _ e => (by cases e),
      fun x e => by cases e; exact rootServerCNode_bootCNodeShape hs hIn,
      fun _ e => (by cases e), fun _ e => (by cases e),
      fun _ e => (by cases e), fun _ e => (by cases e), fun _ e => (by cases e),
      fun _ e => (by cases e)⟩, fun x e => by cases e; rw [rootServerCNode_linksClear]; exact hl,
      fun _ e => (by cases e)⟩
  split at hObj
  · rename_i h6; cases hObj
    have hs := (hShape _ _ hT).1.2.2.2.1 t rfl
    have hl := (hShape _ _ hT).2.2 t rfl
    exact ⟨⟨fun _ e => (by cases e), fun _ e => (by cases e), fun _ e => (by cases e),
      fun x e => by cases e; exact rootServerThread_bootTcbShape hs,
      fun _ e => (by cases e), fun _ e => (by cases e), fun _ e => (by cases e),
      fun _ e => (by cases e), fun _ e => (by cases e)⟩, fun _ e => (by cases e),
      fun x e => by cases e; rw [rootServerThread_spaceLinksClear]; exact hl⟩
  · exact hShape oid obj hObj


/-- The stage keeps the mappings recorded: the buffer's new translation is
    witnessed by the root CNode's frame capability, and the buffer slot's
    derived copy records nothing. -/
theorem installRootServer_liveMappingsRecorded {config : PlatformConfig} {ist : IntermediateState}
    {r : RootServerReservation} {t : TCB} {cn : CNode} {vs : VSpaceRoot}
    (hT : ist.state.objects[r.thread.toObjId]? = some (.tcb t))
    (hC : ist.state.objects[t.cspaceRoot]? = some (.cnode cn))
    (hV : ist.state.objects[t.vspaceRoot]? = some (.vspaceRoot vs))
    (hI : rootServerInstallable ist.state r t cn vs = true)
    (hO : ∀ k, (installRootServer config ist).state.objects[k]? =
      rootServerObjects r t cn vs (fun k => ist.state.objects[k]?) k)
    (hShape : ∀ (oid : SeLe4n.ObjId) (obj : KernelObject),
      ist.state.objects[oid]? = some obj → bootObjectShape obj)
    (hMaps : ist.state.liveMappingsRecorded) :
    (installRootServer config ist).state.liveMappingsRecorded := by
  obtain ⟨-, hS, -, -, -, -, -, -, hAl, hP, hCan⟩ := rootServerInstallable_spec hI
  have hFresh : ∀ i, i < rootServerPages → ist.state.objects[r.objId i]? = none :=
    fun i hi => (hS i hi).2.2
  have hIn : ∀ i, i < rootServerPages → (r.cnodeSlot i).toNat < cn.cells.size :=
    fun i hi => (hS i hi).1
  have hvs := ist.hPerObjectMappings _ vs hV
  -- every frame where it was, and every slot's capability where it was
  have hKept : SystemState.mappingRecordsKept ist.state (installRootServer config ist).state :=
    SystemState.mappingRecordsKept.of_fwd
      (fun ref cap hc _ => ⟨ref, cap, (by
        rcases installRootServer_slotCapAt_cases config ist ref with e | ⟨hn, -⟩
        · rw [e]; exact hc
        · rw [hn] at hc; cases hc), rfl, rfl⟩)
      (fun fid f hf => ⟨f, (by
        rw [hO]; unfold rootServerObjects
        split
        · rename_i h0; subst h0; rw [hFresh 0 (by decide)] at hf; cases hf
        split
        · rename_i h1; subst h1; rw [hFresh 1 (by decide)] at hf; cases hf
        split
        · rename_i h2; subst h2; rw [hFresh 2 (by decide)] at hf; cases hf
        split
        · rename_i h3; subst h3; rw [hFresh 3 (by decide)] at hf; cases hf
        split
        · rename_i h4; subst h4; rw [hV] at hf; cases hf
        split
        · rename_i h5; subst h5; rw [hC] at hf; cases hf
        split
        · rename_i h6; subst h6; rw [hT] at hf; cases hf
        · exact hf), rfl⟩)
  refine ⟨?_, ?_⟩
  · intro rid root v p perms ep hR hM hE
    rw [hO] at hR; unfold rootServerObjects at hR
    split at hR
    · rename_i h0; cases hR
    split at hR
    · rename_i h1; cases hR
    split at hR
    · rename_i h2; cases hR
    split at hR
    · rename_i h3; cases hR
    split at hR
    · rename_i h4; cases hR
      subst h4
      change (vs.mappings.insert r.bufferVAddr (r.pageAddr 0, rootServerBufferPerms)).get? v = _ at hM
      change (vs.mappingEpochs.insert r.bufferVAddr 0).get? v = _ at hE
      by_cases hv : r.bufferVAddr = v
      · subst hv
        rw [RHTable.getElem?_insert_self _ _ _ hvs] at hM
        rw [RHTable.getElem?_insert_self _ _ _ ((hShape _ _ hV).1.2.2.2.2.1 vs rfl).2.2.2.1] at hE
        cases hM; cases hE
        refine ⟨⟨t.cspaceRoot, r.cnodeSlot 0⟩, rootServerFrameCap r vs.asid, r.objId 0,
          rootServerFrame r, ?_, rfl, ?_, rfl, rfl⟩
        · rw [SystemState.slotCapAt_eq_bind, hO, rootServerObjects_cnode hT hC hV hI]
          exact rootServerCNode_lookup_frame r vs.asid cn hIn
        · rw [hO, rootServerObjects_frame]
      · rw [RHTable.getElem?_insert_ne _ _ _ _ (fun h => hv (eq_of_beq h)) hvs] at hM
        rw [RHTable.getElem?_insert_ne _ _ _ _ (fun h => hv (eq_of_beq h))
          ((hShape _ _ hV).1.2.2.2.2.1 vs rfl).2.2.2.1] at hE
        exact hKept _ _ _ _ (hMaps.1 _ vs v p perms ep hV hM hE)
    split at hR
    · rename_i h5; cases hR
    split at hR
    · rename_i h6; cases hR
    · exact hKept _ _ _ _ (hMaps.1 rid root v p perms ep hR hM hE)
  · intro tid t' s cap hT' hc
    rcases rootServerObjects_cases r t cn vs (fun k => ist.state.objects[k]?) tid with
      e | ⟨i, hi, e⟩ | e | e | e
    · rw [hO, e] at hT'; exact hMaps.2 tid t' s cap hT' hc
    · rw [hO, e] at hT'
      rcases (by unfold rootServerPages at hi; omega : i = 0 ∨ 1 ≤ i ∧ i ≤ 3) with rfl | ⟨h1, h3⟩
      · rw [rootServerObjects_frame] at hT'; cases hT'
      · rw [rootServerObjects_table _ h1 h3] at hT'; cases hT'
    · rw [hO, e, rootServerObjects_vspace hT hC hV hI] at hT'; cases hT'
    · rw [hO, e, rootServerObjects_cnode hT hC hV hI] at hT'; cases hT'
    · rw [hO, e, rootServerObjects_thread hT hC hV hI] at hT'; cases hT'
      rw [rootServerThread_spaceSlotCap] at hc
      by_cases hs : s = TCB.ipcBufferSlot
      · rw [if_pos hs] at hc; cases hc; rfl
      · rw [if_neg hs] at hc; exact hMaps.2 _ t s cap hT hc


/-- **WS-SX SX5.3: the stage keeps the boot shape.**  The four objects it adds
    are whole pages where nothing was; the address space gains the buffer's
    translation, read-write and never executable, under epoch 0; the root CNode
    gains the frame's and the tables' capabilities, the frame's recording that
    translation, which so witnesses it; the thread gains the derived capability,
    recording nothing, and its buffer address.  No queue, binding, untyped,
    ASID or tree moves. -/
theorem installRootServer_bootStartShape (config : PlatformConfig) (ist : IntermediateState)
    (h : bootStartShape ist) : bootStartShape (installRootServer config ist) := by
  rcases installRootServer_installed config ist with e | ⟨r, t, cn, vs, hr, hT, hC, hV, hI, hO⟩
  · rw [e]; exact h
  obtain ⟨hShape, hFields, ⟨hAsid, hRoot⟩, hUnt, ⟨rq, re, rp, hSch⟩, hRun, ⟨hNodup, hQ⟩, hBind,
    hMaps⟩ := h
  obtain ⟨-, hS, -, -, -, -, -, -, hAl, hP, hCan⟩ := rootServerInstallable_spec hI
  obtain ⟨-, hCT, hVT, hVC⟩ := rootServer_ids_ne hT hC hV hI
  have hFresh : ∀ i, i < rootServerPages → ist.state.objects[r.objId i]? = none :=
    fun i hi => (hS i hi).2.2
  have hIn : ∀ i, i < rootServerPages → (r.cnodeSlot i).toNat < cn.cells.size :=
    fun i hi => (hS i hi).1
  have hsch := installRootServer_scheduler config ist
  have hvs := ist.hPerObjectMappings _ vs hV
  refine ⟨fun oid obj hObj => ?_, installRootServer_bootQuiescentFields config ist hFields,
    ⟨fun asid oid hA => ?_, fun oid root hR => ?_⟩,
    untypedRegionsDisjoint_of_untyped_subset hUnt fun oid ut hU => ?_,
    ⟨rq, re, rp, hsch.trans hSch⟩,
    SystemState.runQueueRefined_of_frame (fun c tid => ?_)
      (congrArg SchedulerState.runQueue hsch) (congrArg SchedulerState.runQueueEnds hsch) hRun,
    ⟨by rw [hsch]; exact hNodup, fun tid hm => ?_⟩, fun k => ?_, ⟨?_, ?_⟩⟩
  · exact installRootServer_objectShape hT hC hV hI hO hShape oid obj hObj
  · -- every registered ASID names a root with that ASID
    rw [installRootServer_asidTable] at hA
    obtain ⟨root, hr', ha⟩ := hAsid asid oid hA
    rcases rootServerObjects_cases r t cn vs (fun k => ist.state.objects[k]?) oid with
      e | ⟨i, hi, e⟩ | e | e | e
    · rw [hO, e]; exact ⟨root, hr', ha⟩
    · rw [e, hFresh i hi] at hr'; cases hr'
    · rw [e, hV] at hr'; cases hr'
      rw [hO, e, rootServerObjects_vspace hT hC hV hI]; exact ⟨_, rfl, ha⟩
    · rw [e, hC] at hr'; cases hr'
    · rw [e, hT] at hr'; cases hr'
  · -- every root is registered under its ASID
    rw [installRootServer_asidTable]
    rw [hO] at hR; unfold rootServerObjects at hR
    split at hR
    · rename_i h0; cases hR
    split at hR
    · rename_i h1; cases hR
    split at hR
    · rename_i h2; cases hR
    split at hR
    · rename_i h3; cases hR
    split at hR
    · rename_i h4; cases hR; subst h4; exact hRoot _ vs hV
    split at hR
    · rename_i h5; cases hR
    split at hR
    · rename_i h6; cases hR
    · exact hRoot oid root hR
  · -- every untyped was one
    rw [hO] at hU; unfold rootServerObjects at hU
    repeat' split at hU
    all_goals first | cases hU | exact hU
  · -- every run link where it was
    unfold SystemState.runLinkOn
    rcases installRootServer_getTcb? config ist tid with e | ⟨r', t', -, h0, h1⟩
    · rw [e]
    · rw [h0, h1]; rfl
  · -- every queued thread's record
    rw [hsch] at hm
    obtain ⟨tcb, ht, rest⟩ := hQ tid hm
    rw [hsch]
    rcases rootServerObjects_cases r t cn vs (fun k => ist.state.objects[k]?) tid.toObjId with
      e | ⟨i, hi, e⟩ | e | e | e
    · rw [hO, e]; exact ⟨tcb, ht, rest⟩
    · rw [e, hFresh i hi] at ht; cases ht
    · rw [e, hV] at ht; cases ht
    · rw [e, hC] at ht; cases ht
    · rw [e, hT] at ht; cases ht
      rw [hO, e, rootServerObjects_thread hT hC hV hI]; exact ⟨_, rfl, rest⟩
  · -- every binding code where it was
    have hB : ∀ k, SeLe4n.Kernel.notificationBindingCodes (installRootServer config ist).state.objects[k]? =
        SeLe4n.Kernel.notificationBindingCodes ist.state.objects[k]? := fun k => by
      rw [hO]
      rcases rootServerObjects_cases r t cn vs (fun k => ist.state.objects[k]?) k with
        e | ⟨i, hi, e⟩ | e | e | e
      · rw [e]
      · rw [e, hFresh i hi]
        rcases (by unfold rootServerPages at hi; omega : i = 0 ∨ 1 ≤ i ∧ i ≤ 3) with rfl | ⟨h1, h3⟩
        · rw [rootServerObjects_frame]; rfl
        · rw [rootServerObjects_table _ h1 h3]; rfl
      · rw [e, rootServerObjects_vspace hT hC hV hI, hV]; rfl
      · rw [e, rootServerObjects_cnode hT hC hV hI, hC]; rfl
      · rw [e, rootServerObjects_thread hT hC hV hI, hT]; rfl
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · rw [hB] at hc ⊢; exact (hBind k).1 c hc
    · rw [hB] at hc ⊢; exact (hBind k).2 c hc
  · exact (installRootServer_liveMappingsRecorded hT hC hV hI hO hShape hMaps).1
  · exact (installRootServer_liveMappingsRecorded hT hC hV hI hO hShape hMaps).2

-- ============================================================================
-- §6  What the stage leaves the linking
-- ============================================================================

/-- A capability the stage makes names one of its four pages. -/
theorem rootServerCap_target {r : RootServerReservation} {c : Capability} (h : rootServerCap r c) :
    ∃ i, i < rootServerPages ∧ c.target = .object (r.objId i) := by
  rcases h with ⟨asid, rfl⟩ | rfl | ⟨l, h1, h3, rfl⟩
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨l, by unfold rootServerPages; omega, rfl⟩

/-- **Every key after the stage, against the key before**: unchanged, one of
    the four fresh pages, or the address space, root CNode or thread
    rewritten. -/
theorem installRootServer_keyCases {config : PlatformConfig} {ist : IntermediateState}
    {r : RootServerReservation} {t : TCB} {cn : CNode} {vs : VSpaceRoot}
    (hT : ist.state.objects[r.thread.toObjId]? = some (.tcb t))
    (hC : ist.state.objects[t.cspaceRoot]? = some (.cnode cn))
    (hV : ist.state.objects[t.vspaceRoot]? = some (.vspaceRoot vs))
    (hI : rootServerInstallable ist.state r t cn vs = true)
    (hO : ∀ k, (installRootServer config ist).state.objects[k]? =
      rootServerObjects r t cn vs (fun k => ist.state.objects[k]?) k) (k : SeLe4n.ObjId) :
    (installRootServer config ist).state.objects[k]? = ist.state.objects[k]? ∨
    (ist.state.objects[k]? = none ∧
      ((installRootServer config ist).state.objects[k]? = some (.frame (rootServerFrame r)) ∨
       ∃ l, (installRootServer config ist).state.objects[k]? =
         some (.pageTable (rootServerTable r t.vspaceRoot l)))) ∨
    (ist.state.objects[k]? = some (.vspaceRoot vs) ∧
      (installRootServer config ist).state.objects[k]? = some (.vspaceRoot (rootServerVSpace r vs))) ∨
    (ist.state.objects[k]? = some (.cnode cn) ∧
      (installRootServer config ist).state.objects[k]? = some (.cnode (rootServerCNode r vs.asid cn))) ∨
    (ist.state.objects[k]? = some (.tcb t) ∧
      (installRootServer config ist).state.objects[k]? = some (.tcb (rootServerThread r t))) := by
  obtain ⟨-, hS, -⟩ := rootServerInstallable_spec hI
  rcases rootServerObjects_cases r t cn vs (fun k => ist.state.objects[k]?) k with
    e | ⟨i, hi, e⟩ | e | e | e
  · exact .inl ((hO k).trans e)
  · subst e
    refine .inr (.inl ⟨(hS i hi).2.2, ?_⟩)
    rw [hO]
    rcases (by unfold rootServerPages at hi; omega : i = 0 ∨ 1 ≤ i ∧ i ≤ 3) with rfl | ⟨h1, h3⟩
    · exact .inl (rootServerObjects_frame _)
    · exact .inr ⟨i, rootServerObjects_table _ h1 h3⟩
  · subst e; exact .inr (.inr (.inl ⟨hV, (hO _).trans (rootServerObjects_vspace hT hC hV hI _)⟩))
  · subst e; exact .inr (.inr (.inr (.inl ⟨hC, (hO _).trans (rootServerObjects_cnode hT hC hV hI _)⟩)))
  · subst e; exact .inr (.inr (.inr (.inr ⟨hT, (hO _).trans (rootServerObjects_thread hT hC hV hI _)⟩)))

/-- The stage keeps every untyped record: it adds and rewrites none. -/
theorem installRootServer_getUntyped? (config : PlatformConfig) (ist : IntermediateState) :
    (installRootServer config ist).state.getUntyped? = ist.state.getUntyped? := by
  funext k
  rw [SystemState.getUntyped?_eq_bind, SystemState.getUntyped?_eq_bind]
  rcases installRootServer_installed config ist with e | ⟨r, t, cn, vs, -, hT, hC, hV, hI, hO⟩
  · rw [e]
  rcases installRootServer_keyCases hT hC hV hI hO k with e | ⟨e0, e | ⟨l, e⟩⟩ | ⟨e0, e⟩ | ⟨e0, e⟩ | ⟨e0, e⟩
  · rw [e]
  all_goals (rw [e, e0]; rfl)

/-- The stage keeps every object present and adds four. -/
theorem installRootServer_objects_ne_none (config : PlatformConfig) (ist : IntermediateState)
    (k : SeLe4n.ObjId) (h : ist.state.objects[k]? ≠ none) :
    (installRootServer config ist).state.objects[k]? ≠ none := by
  rcases installRootServer_installed config ist with e | ⟨r, t, cn, vs, -, hT, hC, hV, hI, hO⟩
  · rw [e]; exact h
  rcases installRootServer_keyCases hT hC hV hI hO k with e | ⟨e0, -⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩
  · rw [e]; exact h
  · exact absurd e0 h
  all_goals (rw [e]; exact fun h => nomatch h)

/-- The stage keeps every object present. -/
theorem installRootServer_objectPresent (config : PlatformConfig) (ist : IntermediateState)
    (o : SeLe4n.ObjId) (h : ist.state.objectPresent o) :
    (installRootServer config ist).state.objectPresent o :=
  ⟨installRootServer_objects_ne_none config ist o h.1,
    SystemState.irqNodeIssued_of_lines
      (SystemState.irqSignalLines_of_cdt (installRootServer_cdt config ist)) o h.2⟩

/-- **The slots after the stage, read for the linking**: a slot holding a
    capability held it before, or the capability is the stage's, naming one of
    its four pages, now present and no interrupt node. -/
theorem installRootServer_slotCapAt_some (config : PlatformConfig) (ist : IntermediateState)
    (ref : SlotRef) (c : Capability) (h : (installRootServer config ist).state.slotCapAt ref = some c) :
    ist.state.slotCapAt ref = some c ∨
    (ist.state.slotCapAt ref = none ∧ ∃ o, c.target = .object o ∧ ist.state.objects[o]? = none ∧
      (installRootServer config ist).state.objectPresent o ∧
      (installRootServer config ist).state.getCNode? o = none) := by
  rcases installRootServer_slotCapAt_cases config ist ref with e | ⟨hn, -, r', c', hr', hc, hcap⟩
  · rw [← e]; exact .inl h
  rw [h] at hc; cases hc
  refine .inr ⟨hn, ?_⟩
  obtain ⟨i, hi, ht⟩ := rootServerCap_target hcap
  rcases installRootServer_installed config ist with e | ⟨r, t, cn, vs, hr, hT, hC, hV, hI, hO⟩
  · rw [e] at h; rw [h] at hn; cases hn
  have hrr : r = r' := Option.some.inj (hr.symm.trans hr')
  subst hrr
  obtain ⟨-, hS, -, -, -, -, -, -, hAl, -⟩ := rootServerInstallable_spec hI
  have hNew : (installRootServer config ist).state.objects[r.objId i]? =
      rootServerObjects r t cn vs (fun k => ist.state.objects[k]?) (r.objId i) := hO _
  refine ⟨r.objId i, ht, (hS i hi).2.2, ⟨?_, SystemState.irqNodeIssued_of_not_node _ (hAl i hi).2⟩, ?_⟩
  · rw [hNew]
    rcases (by unfold rootServerPages at hi; omega : i = 0 ∨ 1 ≤ i ∧ i ≤ 3) with rfl | ⟨h1, h3⟩
    · rw [rootServerObjects_frame]; exact fun h => nomatch h
    · rw [rootServerObjects_table _ h1 h3]; exact fun h => nomatch h
  · unfold SystemState.getCNode?
    rw [hNew]
    rcases (by unfold rootServerPages at hi; omega : i = 0 ∨ 1 ≤ i ∧ i ≤ 3) with rfl | ⟨h1, h3⟩
    · rw [rootServerObjects_frame]
    · rw [rootServerObjects_table _ h1 h3]

/-- A slot holding a capability before the stage holds it after. -/
theorem installRootServer_slotCapAt_of_some (config : PlatformConfig) (ist : IntermediateState)
    (ref : SlotRef) (c : Capability) (h : ist.state.slotCapAt ref = some c) :
    (installRootServer config ist).state.slotCapAt ref = some c := by
  rcases installRootServer_slotCapAt_cases config ist ref with e | ⟨hn, -⟩
  · rw [e]; exact h
  · rw [hn] at h; cases h

/-- **An untyped's capability after the stage was one before**: the stage's
    capabilities name its pages, none an untyped. -/
theorem installRootServer_untypedCapAt (config : PlatformConfig) (ist : IntermediateState)
    (r : SlotRef) (u : SeLe4n.ObjId)
    (h : SystemState.untypedCapAt (installRootServer config ist).state.slotCapAt
      (installRootServer config ist).state.getUntyped? r u) :
    SystemState.untypedCapAt ist.state.slotCapAt ist.state.getUntyped? r u := by
  obtain ⟨c, hc, ht, hu⟩ := h
  rw [installRootServer_getUntyped?] at hu
  rcases installRootServer_slotCapAt_some config ist r c hc with h | ⟨-, o, ho, h0, -⟩
  · exact ⟨c, h, ht, hu⟩
  · rw [ho] at ht; cases ht
    rw [SystemState.getUntyped?_eq_bind, h0] at hu; exact absurd rfl hu

/-- Every capability the stage makes has a zero free index: none is an
    untyped's. -/
theorem installRootServer_freeIndexZero (config : PlatformConfig) (ist : IntermediateState)
    (h : ∀ r c, ist.state.slotCapAt r = some c → c.freeIndex = 0) :
    ∀ r c, (installRootServer config ist).state.slotCapAt r = some c → c.freeIndex = 0 := by
  intro r c hc
  rcases installRootServer_slotCapAt_cases config ist r with e | ⟨-, -, r', c', -, hc', hcap⟩
  · rw [e] at hc; exact h r c hc
  · rw [hc] at hc'; cases hc'
    rcases hcap with ⟨asid, rfl⟩ | rfl | ⟨l, -, -, rfl⟩ <;> rfl

/-- **The stage keeps what the linking reads of the slots**, with its own slots
    listed after the configuration's (`bootLinkOrder`): every slot's
    capability is listed, names a present object, and an untyped's capability
    is unique, uncarved and the one naming it. -/
theorem installRootServer_linkInputs (config : PlatformConfig) (ist : IntermediateState)
    (hListed : bootSlotsListed (bootCapabilitySlots config.initialObjects) ist.state)
    (hLive : ∀ r o, SystemState.namesAt ist.state.slotCapAt r o → ist.state.objectPresent o)
    (hUnique : ∀ u r r', SystemState.untypedCapAt ist.state.slotCapAt ist.state.getUntyped? r u →
      SystemState.untypedCapAt ist.state.slotCapAt ist.state.getUntyped? r' u → r = r')
    (hUncarved : ∀ u U, ist.state.getUntyped? u = some U → U.children = [])
    (hNamedU : ∀ r u, SystemState.namesAt ist.state.slotCapAt r u → ist.state.getUntyped? u ≠ none →
      SystemState.untypedCapAt ist.state.slotCapAt ist.state.getUntyped? r u) :
    let st := (installRootServer config ist).state
    bootSlotsListed (bootLinkOrder config st) st ∧
    (∀ r o, SystemState.namesAt st.slotCapAt r o → st.objectPresent o) ∧
    (∀ u r r', SystemState.untypedCapAt st.slotCapAt st.getUntyped? r u →
      SystemState.untypedCapAt st.slotCapAt st.getUntyped? r' u → r = r') ∧
    (∀ u U, st.getUntyped? u = some U → U.children = []) ∧
    (∀ r u, SystemState.namesAt st.slotCapAt r u → st.getUntyped? u ≠ none →
      SystemState.untypedCapAt st.slotCapAt st.getUntyped? r u) := by
  intro st
  have hU : st.getUntyped? = ist.state.getUntyped? := installRootServer_getUntyped? config ist
  have hUC := installRootServer_untypedCapAt config ist
  refine ⟨fun r hr => ?_, fun r o ⟨c, hc, hn⟩ => ?_, fun u r r' h h' => hUnique u r r' (hUC r u h)
    (hUC r' u h'), fun u U h => hUncarved u U (hU ▸ h), fun r u ⟨c, hc, hn⟩ hu => ?_⟩
  · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hr
    rcases installRootServer_slotCapAt_cases config ist r with e | ⟨-, hm, -⟩
    · exact mem_bootCapabilitySlots_extra (hListed r (by rw [← e]; exact hr)) _
    · exact mem_bootCapabilitySlots_of_extra hm
  · rcases installRootServer_slotCapAt_some config ist r c hc with h | ⟨-, o', ho, -, hp, -⟩
    · exact installRootServer_objectPresent config ist o (hLive r o ⟨c, h, hn⟩)
    · unfold Capability.namedObject at hn; rw [ho] at hn; cases hn; exact hp
  · rw [hU] at hu
    rcases installRootServer_slotCapAt_some config ist r c hc with h | ⟨-, o', ho, h0, -⟩
    · obtain ⟨c', hc', ht', hu'⟩ := hNamedU r u ⟨c, h, hn⟩ hu
      rw [h] at hc'; cases hc'
      exact ⟨c, hc, ht', hU ▸ hu'⟩
    · unfold Capability.namedObject at hn; rw [ho] at hn; cases hn
      rw [SystemState.getUntyped?_eq_bind, h0] at hu; exact absurd rfl hu

/-- The stage keeps every reply and every CNode present. -/
theorem installRootServer_getReply?_ne_none (config : PlatformConfig) (ist : IntermediateState)
    (rid : SeLe4n.ReplyId) (h : ist.state.getReply? rid ≠ none) :
    (installRootServer config ist).state.getReply? rid ≠ none := by
  rcases installRootServer_installed config ist with e | ⟨r, t, cn, vs, -, hT, hC, hV, hI, hO⟩
  · rw [e]; exact h
  unfold SystemState.getReply? at h ⊢
  rcases installRootServer_keyCases hT hC hV hI hO rid.toObjId with
    e | ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨e0, -⟩
  · rw [e]; exact h
  all_goals (rw [e0] at h; exact absurd rfl h)

/-- **Every CNode after the stage was one before, with its radix.** -/
theorem installRootServer_getCNode? (config : PlatformConfig) (ist : IntermediateState)
    (id : SeLe4n.ObjId) (cn' : CNode) (h : (installRootServer config ist).state.getCNode? id = some cn') :
    ∃ cn, ist.state.getCNode? id = some cn ∧ cn'.radixWidth = cn.radixWidth := by
  rw [SystemState.getCNode?_eq_some_iff] at h
  rcases installRootServer_installed config ist with e | ⟨r, t, cn, vs, -, hT, hC, hV, hI, hO⟩
  · rw [e] at h; exact ⟨cn', (SystemState.getCNode?_eq_some_iff _ _ _).mpr h, rfl⟩
  rcases installRootServer_keyCases hT hC hV hI hO id with
    e | ⟨-, e | ⟨l, e⟩⟩ | ⟨-, e⟩ | ⟨e0, e⟩ | ⟨-, e⟩
  · rw [e] at h; exact ⟨cn', (SystemState.getCNode?_eq_some_iff _ _ _).mpr h, rfl⟩
  · rw [e] at h; cases h
  · rw [e] at h; cases h
  · rw [e] at h; cases h
  · rw [e] at h; cases h
    exact ⟨cn, (SystemState.getCNode?_eq_some_iff _ _ _).mpr e0, rootServerCNode_radixWidth _ _ _⟩
  · rw [e] at h; cases h

/-- The stage keeps every capability's target backed: the ones it adds name
    objects. -/
theorem installRootServer_capTargetKindBacked (config : PlatformConfig) (ist : IntermediateState)
    (h : SeLe4n.Kernel.capTargetKindBacked ist.state) :
    SeLe4n.Kernel.capTargetKindBacked (installRootServer config ist).state := by
  intro oid o slot c hO hc
  have hS : (installRootServer config ist).state.slotCapAt ⟨oid, slot⟩ = some c := by
    rw [SystemState.slotCapAt_of_object hO]; exact hc
  rcases installRootServer_slotCapAt_some config ist _ c hS with h' | ⟨-, o', ho, -⟩
  · refine SeLe4n.Kernel.capTargetKindBackedAt_mono
      (installRootServer_getReply?_ne_none config ist) (fun cn hC => ?_) _ (h.slotCapAt h')
    obtain ⟨c0, hc0⟩ := Option.ne_none_iff_exists'.mp hC
    rcases installRootServer_installed config ist with e | ⟨r, t, cn', vs, -, hT, hC', hV, hI, hO'⟩
    · rw [e, hc0]; exact fun h => nomatch h
    rw [SystemState.getCNode?_eq_some_iff] at hc0
    have := installRootServer_objects_ne_none config ist cn (by rw [hc0]; exact fun h => nomatch h)
    rcases installRootServer_keyCases hT hC' hV hI hO' cn with
      e | ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨e0, e⟩ | ⟨e0, -⟩
    · unfold SystemState.getCNode?; rw [e, hc0]; exact fun h => nomatch h
    · rw [e0] at hc0; cases hc0
    · rw [e0] at hc0; cases hc0
    · unfold SystemState.getCNode?; rw [e]; exact fun h => nomatch h
    · rw [e0] at hc0; cases hc0
  · rw [ho]; trivial

/-- The stage keeps every capability's CNode geometry: the ones it adds carry
    no guard and name no CNode. -/
theorem installRootServer_cnodeCapGeometry (config : PlatformConfig) (ist : IntermediateState)
    (h : SeLe4n.Kernel.cnodeCapGeometry ist.state) :
    SeLe4n.Kernel.cnodeCapGeometry (installRootServer config ist).state := by
  intro oid o slot c hO hc
  have hS : (installRootServer config ist).state.slotCapAt ⟨oid, slot⟩ = some c := by
    rw [SystemState.slotCapAt_of_object hO]; exact hc
  rcases installRootServer_slotCapAt_some config ist _ c hS with h' | ⟨hn0, o', ho, -, -, hN⟩
  · exact SeLe4n.Kernel.cnodeCapGeometryAt_mono (installRootServer_getCNode? config ist) c
      (h.slotCapAt h')
  · obtain ⟨r, -, hcap⟩ : ∃ r, config.rootServer = some r ∧ rootServerCap r c := by
      rcases installRootServer_slotCapAt_cases config ist ⟨oid, slot⟩ with
        e | ⟨-, -, r, c', hr, hc', hcap⟩
      · rw [e] at hS; rw [hS] at hn0; cases hn0
      · rw [hS] at hc'; cases hc'; exact ⟨r, hr, hcap⟩
    refine ⟨?_, fun id cn hT hC => ?_⟩
    · rcases hcap with ⟨asid, rfl⟩ | rfl | ⟨l, -, -, rfl⟩ <;> exact Nat.two_pow_pos _
    · rw [ho] at hT; cases hT; rw [hN] at hC; cases hC

-- ============================================================================
-- §7  What the stage adds to the object index
-- ============================================================================

/-- An install at a present id adds no index entry. -/
theorem createObject_objectIndex_of_present (ist : IntermediateState) (id : SeLe4n.ObjId)
    (obj : KernelObject) (h1 h2) (h : ist.state.objects[id]? ≠ none) :
    (createObject ist id obj h1 h2).state.objectIndex = ist.state.objectIndex := by
  have hs : (ist.state.objects[id]?).isSome = true := Option.isSome_iff_ne_none.mpr h
  unfold createObject
  simp [hs]

/-- An install keeps every present id present. -/
theorem createObject_objects_ne_none (ist : IntermediateState) (id : SeLe4n.ObjId)
    (obj : KernelObject) (h1 h2) (k : SeLe4n.ObjId) (h : ist.state.objects[k]? ≠ none) :
    (createObject ist id obj h1 h2).state.objects[k]? ≠ none := by
  rw [createObject_objects]
  by_cases hk : id = k
  · subst hk
    have e : (ist.state.objects.insert id obj)[id]? = some obj :=
      RHTable.getElem?_insert_self _ _ _ ist.hAllTables.objects.1
    rw [e]; exact fun h => nomatch h
  · have e : (ist.state.objects.insert id obj)[k]? = ist.state.objects[k]? :=
      RHTable.getElem?_insert_ne _ _ _ _ (fun e => hk (eq_of_beq e)) ist.hAllTables.objects.1
    rw [e]; exact h

@[simp] theorem recordBootPhysicalWrites_objectIndex (ist : IntermediateState) (ws : List PhysicalWrite) :
    (recordBootPhysicalWrites ist ws).state.objectIndex = ist.state.objectIndex := rfl

/-- **The installs add one index entry per id absent before them.** -/
theorem createEntries_objectIndex_length_le (objs : List ObjectEntry) (ist : IntermediateState) :
    (createEntries objs ist).state.objectIndex.length ≤
      ist.state.objectIndex.length + objs.countP (fun e => (ist.state.objects[e.id]?).isNone) := by
  induction objs generalizing ist with
  | nil => exact Nat.le_add_right _ _
  | cons e rest ih =>
    show (createEntries rest (createObject ist e.id e.obj e.hSlots e.hMappings)).state.objectIndex.length ≤ _
    refine Nat.le_trans (ih _) ?_
    have hMono : rest.countP (fun x =>
          ((createObject ist e.id e.obj e.hSlots e.hMappings).state.objects[x.id]?).isNone) ≤
        rest.countP (fun x => (ist.state.objects[x.id]?).isNone) :=
      List.countP_mono_left fun x _ hx => by
        simp only [Option.isNone_iff_eq_none] at hx ⊢
        cases h' : ist.state.objects[x.id]? with
        | none => rfl
        | some o => exact absurd hx (createObject_objects_ne_none ist e.id e.obj e.hSlots e.hMappings
            x.id (by rw [h']; exact fun h => nomatch h))
    rw [List.countP_cons]
    by_cases hp : (ist.state.objects[e.id]?).isNone = true
    · have := createObject_objectIndex_length_le ist e.id e.obj e.hSlots e.hMappings
      simp only [hp, if_true]; omega
    · have hne : ist.state.objects[e.id]? ≠ none := fun h => hp (by rw [h]; rfl)
      rw [createObject_objectIndex_of_present _ _ _ _ _ hne]
      simp only [hp]; omega

/-- **The stage adds at most one index entry per page**: the four objects at
    fresh ids; the address space, root CNode and thread are rewritten in
    place. -/
theorem installRootServer_objectIndex_length_le (config : PlatformConfig) (ist : IntermediateState) :
    (installRootServer config ist).state.objectIndex.length ≤
      ist.state.objectIndex.length + rootServerPages := by
  unfold installRootServer
  split
  · omega
  · next r _ =>
    rcases installRootServerAt_cases r ist with e | ⟨t, cn, vs, hvs, hT, hC, hV, hI, e⟩
    · rw [e]; omega
    rw [e, recordBootPhysicalWrites_objectIndex]
    refine Nat.le_trans (createEntries_objectIndex_length_le _ ist) (Nat.add_le_add_left ?_ _)
    obtain ⟨-, hS, -⟩ := rootServerInstallable_spec hI
    have hF : ∀ i, i < rootServerPages → (ist.state.objects[r.objId i]?).isNone = true :=
      fun i hi => by rw [(hS i hi).2.2]; rfl
    simp only [rootServerEntries, List.countP_cons, List.countP_nil, hF 0 (by decide),
      hF 1 (by decide), hF 2 (by decide), hF 3 (by decide), hV, hC, hT, Option.isNone_some,
      if_true, if_false, Bool.false_eq_true]
    decide

-- ============================================================================
-- §8  The drained state
-- ============================================================================

@[simp] theorem drainBootPhysicalWrites_objects (ist : IntermediateState) :
    (drainBootPhysicalWrites ist).state.objects = ist.state.objects := rfl

private theorem ipcInvariantFull_clearPhysicalWrites {st : SystemState}
    (h : ipcInvariantFull st) : ipcInvariantFull (clearPhysicalWrites st) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10,
          c11, c12, c14, c15, c16, c17, c18, c19, c20⟩ := h
  exact ⟨c1, dualQueueSystemInvariant_of_readViewAgreement (s1 := st)
           (s2 := clearPhysicalWrites st) (.of_getElem_eq (fun _ => rfl)) c2,
         c3, c4, c5, c6, c7, c8, c9, c10,
         c11, c12, c14, c15, c16, c17, c18, c19, c20⟩

private theorem crossSubsystemInvariant_clearPhysicalWrites {st : SystemState}
    (h : crossSubsystemInvariant st) : crossSubsystemInvariant (clearPhysicalWrites st) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := h
  exact ⟨d1, d2, d3, d4, d5, d6, d7,
         PriorityInheritance.blockingAcyclic_frame st _ d8
           (fun tid => PriorityInheritance.blockingServer_congr_objects _ _ tid rfl) rfl,
         d9, d10⟩

/-- **The drain keeps the proof-layer bundle**: it sets the ledger's drained
    flag, which no conjunct reads — the carriage the refusal ledger's writer has
    (`proofLayerInvariantBundle_setDeclassificationRefusals`). -/
theorem proofLayerInvariantBundle_drainBootPhysicalWrites (ist : IntermediateState)
    (h : proofLayerInvariantBundle ist.state) :
    proofLayerInvariantBundle (drainBootPhysicalWrites ist).state := by
  obtain ⟨bSched, bCap, bCoreIpc, bCoupling, bLifecycle, bService, bVSpace,
          bCross, bTlb, bSchedExt, bNtfn, bPending, bPerCoreTlb,
          bIcache, bAck, bAudit, bRun, bMap, bRel, bRefill, bYield, bBook, bNtfnLinks⟩ := h
  exact ⟨bSched, bCap, ⟨bCoreIpc.1, bCoreIpc.2.1, ipcInvariantFull_clearPhysicalWrites bCoreIpc.2.2⟩,
         ⟨⟨bCoupling.1.1, bCoupling.1.2.1, ipcInvariantFull_clearPhysicalWrites bCoupling.1.2.2⟩,
           bCoupling.2.1, bCoupling.2.2.1, bCoupling.2.2.2⟩,
         bLifecycle, bService, bVSpace,
         crossSubsystemInvariant_clearPhysicalWrites bCross,
         bTlb, bSchedExt, (notificationWaiterConsistent_of_objects_eq (st := ist.state) rfl bNtfn),
         bPending, bPerCoreTlb, bIcache, bAck, bAudit, bRun, bMap, bRel, bRefill, bYield,
         bBook.of_objects_ghosts rfl ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩, bNtfnLinks⟩

/-- An object the stage neither adds nor rewrites — no thread, CNode or
    address space — is where it was. -/
theorem installRootServer_objects_of_some {config : PlatformConfig} {ist : IntermediateState}
    {k : SeLe4n.ObjId} {o : KernelObject} (h : ist.state.objects[k]? = some o)
    (hT : ∀ t, o ≠ .tcb t) (hC : ∀ cn, o ≠ .cnode cn) (hV : ∀ vs, o ≠ .vspaceRoot vs) :
    (installRootServer config ist).state.objects[k]? = some o := by
  rcases installRootServer_installed config ist with e | ⟨r, t, cn, vs, -, hT', hC', hV', hI, hO⟩
  · rw [e]; exact h
  rcases installRootServer_keyCases hT' hC' hV' hI hO k with
    e | ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨e0, -⟩
  · rw [e]; exact h
  · rw [e0] at h; cases h
  · rw [e0] at h; cases h; exact absurd rfl (hV vs)
  · rw [e0] at h; cases h; exact absurd rfl (hC cn)
  · rw [e0] at h; cases h; exact absurd rfl (hT t)

end SeLe4n.Platform.Boot
