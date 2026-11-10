/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.ResidentsHaveTcbs

/-!
# The saved-register frame and the capability-only dispatch's object arms

WS-ZA ZA6.23.  Most of the capability-only dispatch's arms write objects that
hold no registers: CNodes, the derivation tree's slot links, untyped objects,
VSpace roots, page tables, frames and endpoints' service records.  Their census
(`savedRegsKeptOffCore`) is a frame, not a free-ness argument.

`savedRegsKept pre post` is that frame: every saved context `pre` holds is held
by `post` unchanged.  It admits a new TCB (the retype carves one into an empty
slot) but no write to an existing one's registers.  It composes
(`savedRegsKept.trans`) and is built per write: a store over a slot that held no
TCB (`savedRegsKept.storeObject`), a slot-link write, which rewrites a thread's
space-slot links alone (`savedRegsKept.of_linkReach`), and the frames the arms
already state (`vspaceRootOnlyWrite`, `ServiceRecordRewrite`).  Under the
syscall's premises every thread another core holds has a TCB (a current thread
is active, `currentDequeuedUnique.currentActive`; a resident has one,
`residentsHaveTcbs`), so the frame gives the census
(`savedRegsKeptOffCore_of_savedRegsKept`).

The arms: the reply-capability mint (the CSpace arm that deletes nothing), the
untyped retype and reset, the VSpace map, unmap and instruction unification, the
page-table map and unmap, and the service revoke, each `*_savedRegsKept`; the
service query stages its answer into the caller alone
(`writeReturnFrameToTcb_savedRegsKeptOffCore`).
`dispatchCapabilityOnly_savedRegsKeptOffCore` collects them over the whole
dispatch with the final delete and revoke (ZA6.24, `SavedRegistersFinalise.lean`)
and the TCB and scheduling-context arms (ZA6.25,
`SavedRegistersCapabilityDispatch.lean`).
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- A thread's saved registers are its TCB's, read off the object store. -/
theorem savedRegs_eq_some_iff {st : SystemState} {t : SeLe4n.ThreadId} {r : SeLe4n.RegisterFile} :
    st.savedRegs t = some r ↔
      ∃ x, st.objects[t.toObjId]? = some (.tcb x) ∧ x.registerContext = r := by
  unfold SystemState.savedRegs SystemState.getTcb?
  split
  · rename_i x hx
    simp only [Option.map_some, Option.some.injEq, hx, KernelObject.tcb.injEq, exists_eq_left']
  · rename_i hx
    simp only [Option.map_none, reduceCtorEq, false_iff, not_exists, not_and]
    intro x h; exact absurd h (hx x)

/-- WS-ZA ZA6.23: **every saved context of `pre` is a saved context of `post`**:
the step writes no existing thread's saved registers and removes no TCB. -/
def savedRegsKept (pre post : SystemState) : Prop :=
  ∀ t r, pre.savedRegs t = some r → post.savedRegs t = some r

namespace savedRegsKept

theorem refl (st : SystemState) : savedRegsKept st st := fun _ _ h => h

theorem trans {a b d : SystemState} (h₁ : savedRegsKept a b) (h₂ : savedRegsKept b d) :
    savedRegsKept a d := fun t r h => h₂ t r (h₁ t r h)

/-- **The frame, slot by slot**: every TCB of `pre` is a TCB of `post` with the
same registers. -/
theorem of_objectsAt {pre post : SystemState}
    (h : ∀ (oid : SeLe4n.ObjId) (x : TCB), pre.objects[oid]? = some (.tcb x) →
      ∃ y, post.objects[oid]? = some (.tcb y) ∧ y.registerContext = x.registerContext) :
    savedRegsKept pre post := fun t r hr => by
  obtain ⟨x, hx, rfl⟩ := savedRegs_eq_some_iff.mp hr
  obtain ⟨y, hy, hyx⟩ := h _ x hx
  exact savedRegs_eq_some_iff.mpr ⟨y, hy, hyx⟩

/-- **A write that leaves every slot alone or writes one that held no TCB.** -/
theorem of_unchangedOrNoTcb {pre post : SystemState}
    (h : ∀ oid : SeLe4n.ObjId, post.objects[oid]? = pre.objects[oid]? ∨
      ∀ x : TCB, pre.objects[oid]? ≠ some (.tcb x)) :
    savedRegsKept pre post :=
  of_objectsAt fun oid x hx => by
    rcases h oid with e | hN
    · exact ⟨x, e.trans hx, rfl⟩
    · exact absurd hx (hN x)

theorem of_objects_eq {pre post : SystemState} (h : post.objects = pre.objects) :
    savedRegsKept pre post :=
  of_unchangedOrNoTcb fun oid => .inl (by rw [h])

/-- A store over a slot that held no TCB: an empty slot (the retype's child) or
an object of another kind. -/
theorem storeObject {st st' : SystemState} {oid : SeLe4n.ObjId} {obj : KernelObject}
    (hInv : st.objects.invExt) (hStore : SeLe4n.Model.storeObject oid obj st = .ok ((), st'))
    (hPre : ∀ x : TCB, st.objects[oid]? ≠ some (.tcb x)) : savedRegsKept st st' :=
  of_unchangedOrNoTcb fun k => by
    by_cases hk : k = oid
    · subst hk; exact .inr hPre
    · exact .inl (storeObject_objects_ne _ _ _ _ _ hk hInv hStore)

/-- The slot-link writes rewrite CNodes and threads' space-slot links, which
hold no registers. -/
theorem of_linkReach {st₀ st : SystemState} (hR : SystemState.linkReach st₀ st)
    (hInv : st₀.objects.invExt) : savedRegsKept st₀ st :=
  of_objectsAt fun oid x hx => by
    rcases hR.agree hInv oid with e | ⟨_, _, ha, _, _⟩ | ⟨t, t', ha, hb, hw⟩
    · exact ⟨x, e.trans hx, rfl⟩
    · rw [ha] at hx; cases hx
    · rw [ha] at hx; cases hx
      exact ⟨t', hb, TCB.proj_eq_of_withoutLinks_eq TCB.registerContext hw⟩

/-- A tree write followed by its slot-link writes. -/
theorem of_withCdt_linkReach {st st' : SystemState} {c : CapDerivationTree}
    (hR : SystemState.linkReach { st with cdt := c } st') (hInv : st.objects.invExt) :
    savedRegsKept st st' :=
  of_linkReach (st₀ := { st with cdt := c }) hR hInv

/-- The derivation edge every `WithCdt` form ends with. -/
theorem cdtAddChild (st : SystemState) (src dst : CSpaceAddr) (kind : DerivationOp)
    (hInv : st.objects.invExt) : savedRegsKept st (st.cdtAddChild src dst kind) :=
  of_withCdt_linkReach (SystemState.cdtAddChild_reach st src dst kind) hInv

/-- A write of VSpace roots alone. -/
theorem of_vspaceRootOnlyWrite {st st' : SystemState} (h : vspaceRootOnlyWrite st st') :
    savedRegsKept st st' :=
  of_unchangedOrNoTcb fun oid => by
    rcases h oid with e | ⟨⟨r, hr⟩, -⟩
    · exact .inl e
    · exact .inr fun x hx => by rw [hr] at hx; cases hx

/-- The registry's one object write, an endpoint's service record. -/
theorem of_serviceRecordRewrite {st st' : SystemState} (hInv : st.objects.invExt)
    (hW : ServiceRecordRewrite st.objects st'.objects) : savedRegsKept st st' :=
  of_unchangedOrNoTcb fun oid => by
    rcases hW.lookup hInv oid with e | ⟨_, _, h0, -⟩
    · exact .inl e
    · exact .inr fun x hx => by rw [h0] at hx; cases hx

/-- A capability insert stores a CNode over a CNode. -/
theorem cspaceInsertSlot {st st' : SystemState} {addr : CSpaceAddr} {cap : Capability}
    (hInv : st.objects.invExt) (hStep : SeLe4n.Kernel.cspaceInsertSlot addr cap st = .ok ((), st')) :
    savedRegsKept st st' :=
  of_unchangedOrNoTcb fun oid => by
    by_cases hk : oid = addr.cnode
    · subst hk
      obtain ⟨cn, hPre, -⟩ := cspaceInsertSlot_objects_eq st st' addr cap hInv hStep
      exact .inr fun x hx => by rw [hPre] at hx; cases hx
    · exact .inl (cspaceInsertSlot_preserves_objects_ne st st' addr cap oid hk hInv hStep)

/-- A free-index write stores a CNode over a CNode, or writes nothing. -/
theorem setCapFreeIndex (st : SystemState) (addr : CSpaceAddr) (idx : Nat)
    (hInv : st.objects.invExt) : savedRegsKept st (SeLe4n.Kernel.setCapFreeIndex st addr idx) := by
  cases hO : st.objects[addr.cnode]? with
  | some o =>
    cases o with
    | cnode cn =>
      exact storeObject hInv (setCapFreeIndex_eq_storeObject (idx := idx) hO)
        (fun x hx => by rw [hO] at hx; cases hx)
    | _ =>
      unfold SeLe4n.Kernel.setCapFreeIndex SystemState.storeCNodeWith; rw [hO]
      exact refl st
  | none =>
    unfold SeLe4n.Kernel.setCapFreeIndex SystemState.storeCNodeWith; rw [hO]
    exact refl st

end savedRegsKept

/-! ### The frame gives the census -/

/-- WS-ZA ZA6.23: **a step that writes no existing thread's saved registers
writes none another core holds**: a thread current or resident on another core
after the step was held there before it (`hK`, `hR`), so it had a TCB — a
current thread is active (`currentDequeuedUnique`), a resident has one
(`residentsHaveTcbs`) — whose registers the frame keeps. -/
theorem savedRegsKeptOffCore_of_savedRegsKept {e : CoreId} {pre post : SystemState}
    (hF : savedRegsKept pre post) (hD : pre.currentDequeuedUnique)
    (hRT : pre.residentsHaveTcbs)
    (hK : currentKeptOffCore e pre post) (hR : residentKeptOffCore e pre post) :
    savedRegsKeptOffCore e pre post := fun d hd t ht => by
  have hT : (pre.getTcb? t).isSome := by
    rcases ht with h | h
    · obtain ⟨x, hx, -⟩ := hD.currentActive d t (hK d hd t h)
      rw [hx]; rfl
    · exact hRT d t (hR d hd t h)
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hT
  have hS : pre.savedRegs t = some x.registerContext := by
    unfold SystemState.savedRegs; rw [hx]; rfl
  rw [hS]; exact hF t _ hS

/-! ### The CSpace and untyped arms -/

/-- **The reply-capability mint**: a lookup, a capability insert into a CNode
and the derivation edge. -/
theorem mintReplyCapWithCdt_savedRegsKept {st st' : SystemState} {src dst : CSpaceAddr}
    (hInv : st.objects.invExt) (hStep : mintReplyCapWithCdt src dst st = .ok ((), st')) :
    savedRegsKept st st' := by
  unfold mintReplyCapWithCdt at hStep
  split at hStep
  · contradiction
  · rename_i stM hMint
    cases hStep
    have hM : savedRegsKept st stM ∧ stM.objects.invExt := by
      unfold mintReplyCap at hMint
      split at hMint
      · contradiction
      · rename_i parent stMid hLk
        have hMid : stMid = st := cspaceLookupSlot_state_eq st stMid src parent hLk
        subst hMid
        split at hMint
        · dsimp only [] at hMint
          split at hMint
          · exact ⟨savedRegsKept.cspaceInsertSlot hInv hMint,
              cspaceInsertSlot_preserves_objects_invExt _ _ _ _ hInv hMint⟩
          · contradiction
        · contradiction
    exact hM.1.trans (savedRegsKept.cdtAddChild stM src dst .mint hM.2)

/-- **The untyped reset**: the invoked slot's free-index rewind. -/
theorem untypedResetFromCap_savedRegsKept {tid : SeLe4n.ThreadId} {srcAddr : SeLe4n.CPtr}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (hStep : untypedResetFromCap tid srcAddr st = .ok ((), st')) : savedRegsKept st st' := by
  obtain ⟨_, _, _, -, -, hS⟩ := untypedResetFromCap_ok _ _ st st' hStep
  rw [untypedResetSlot_ok_frame hS]
  exact savedRegsKept.setCapFreeIndex _ _ _ hInv

/-- **The carve**: the untyped object's store, the child's store into a slot that
was empty, the free-index store into the authority's CNode, the scrub (memory
alone), the capability insert and the derivation edge.  The child may be a TCB;
it is a new one, so no saved context of the pre-state is touched. -/
theorem untypedRetypeObject_savedRegsKept {src dst : CSpaceAddr} {childId : SeLe4n.ObjId}
    {req : CarveRequest} {st st' : SystemState} (hInv : st.objects.invExt)
    (hStep : untypedRetypeObject src childId dst req st = .ok ((), st')) :
    savedRegsKept st st' := by
  obtain ⟨utCap, untypedId, ut, st1, st2, _, _, _, hRt, hIns, rfl⟩ :=
    untypedRetypeObject_ok_decompose src dst childId req st st' hInv hStep
  have hFresh := retypeFromUntyped_childId_fresh src untypedId childId _ _ st st1 hRt
  obtain ⟨_, _, _, stUt, _, stCh, cn, hUt, _, _, _, _, _, _, _, _, _, hStUt, hStCh, hOCh,
    hStIdx⟩ := retypeFromUntyped_ok_stores st st1 src untypedId childId _ _ hInv hRt
  have hNe : childId ≠ untypedId := by
    intro h; rw [h, hUt] at hFresh; simp at hFresh
  have hAbs : st.objects[childId]? = none := by
    cases h : st.objects[childId]? with
    | none => rfl
    | some _ => rw [h] at hFresh; simp at hFresh
  have hInvUt := storeObject_preserves_objects_invExt _ _ _ _ hInv hStUt
  have hInvCh := storeObject_preserves_objects_invExt _ _ _ _ hInvUt hStCh
  have hInv1 := storeObject_preserves_objects_invExt _ _ _ _ hInvCh hStIdx
  have k1 := savedRegsKept.storeObject hInv hStUt (fun x hx => by rw [hUt] at hx; cases hx)
  have k2 := savedRegsKept.storeObject hInvUt hStCh (fun x hx => by
    rw [storeObject_objects_ne _ _ _ _ _ hNe hInv hStUt, hAbs] at hx; cases hx)
  have k3 := savedRegsKept.storeObject hInvCh hStIdx (fun x hx => by rw [hOCh] at hx; cases hx)
  have kZ : savedRegsKept st1 (req.scrub st1 ut (req.carveIndex ut (retypeFreeIndex st src utCap))) :=
    savedRegsKept.of_objects_eq (CarveRequest.scrub_objects _ _ _ _)
  have hInvZ : (req.scrub st1 ut (req.carveIndex ut (retypeFreeIndex st src utCap))).objects.invExt := by
    rw [CarveRequest.scrub_objects]; exact hInv1
  have kI := savedRegsKept.cspaceInsertSlot hInvZ hIns
  exact ((((k1.trans k2).trans k3).trans kZ).trans kI).trans
    (savedRegsKept.cdtAddChild st2 src dst .retype
      (cspaceInsertSlot_preserves_objects_invExt _ _ _ _ hInvZ hIns))

/-- **The untyped retype**, through the carve. -/
theorem untypedRetypeFromCap_savedRegsKept {tid : SeLe4n.ThreadId} {ec : CoreId}
    {srcAddr : SeLe4n.CPtr} {args? : Except KernelError Architecture.SyscallArgDecode.UntypedRetypeArgs}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (hStep : untypedRetypeFromCap tid ec srcAddr args? st = .ok ((), st')) :
    savedRegsKept st st' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hU⟩ := untypedRetypeFromCap_ok _ _ _ _ _ _ hStep
  exact untypedRetypeObject_savedRegsKept hInv hU

/-! ### The VSpace arms -/

/-- The mapping tag: a store of the address space's root over its root and of
the frame over the frame. -/
theorem tagFrameMapping_savedRegsKept {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    {frameId : SeLe4n.ObjId} {st st' : SystemState} {e : Nat} (hInv : st.objects.invExt)
    (hStep : tagFrameMapping asid vaddr frameId st = .ok (e, st')) : savedRegsKept st st' := by
  obtain ⟨f, rootId, root, st1, hF, hR, -, h1, h2⟩ :=
    tagFrameMapping_ok asid vaddr frameId st st' e hStep
  have hRootPre := (Architecture.resolveAsidRoot_some_implies_obj st asid rootId root hR).2.1
  have hFramePre := (SystemState.getFrame?_eq_some_iff st frameId f).mp hF
  have hNe : frameId ≠ rootId := by
    intro hEq; rw [hEq, hRootPre] at hFramePre; cases hFramePre
  have hFrame1 : st1.objects[frameId]? = some (.frame f) := by
    rw [storeObject_objects_ne st st1 _ _ _ hNe hInv h1]; exact hFramePre
  exact (savedRegsKept.storeObject hInv h1 fun x hx => by rw [hRootPre] at hx; cases hx).trans
    (savedRegsKept.storeObject (storeObject_preserves_objects_invExt _ _ _ _ hInv h1) h2
      fun x hx => by rw [hFrame1] at hx; cases hx)

/-- The mapping record: a store of a CNode over its CNode. -/
theorem cspaceRecordFrameMapping_savedRegsKept {addr : CSpaceAddr} {m : FrameMapping}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (hStep : cspaceRecordFrameMapping addr m st = .ok ((), st')) : savedRegsKept st st' := by
  obtain ⟨cn, cap, hCn, -, hStore⟩ := cspaceRecordFrameMapping_ok_decompose addr m st st' hStep
  have hPre : st.objects[addr.cnode]? = some (.cnode cn) :=
    (SystemState.getCNode?_eq_some_iff st addr.cnode cn).mp hCn
  exact savedRegsKept.storeObject hInv hStore fun x hx => by rw [hPre] at hx; cases hx

/-- **The VSpace map**: the page's install (VSpace roots alone), the mapping tag
and the mapping record. -/
theorem vspaceMapFromFrameCap_savedRegsKept {tid : SeLe4n.ThreadId} {ec : CoreId}
    {args : Architecture.SyscallArgDecode.VSpaceMapArgs} {st st' : SystemState}
    (hInv : st.objects.invExt) (hStep : vspaceMapFromFrameCap tid ec args st = .ok ((), st')) :
    savedRegsKept st st' := by
  obtain ⟨_, _, _, st1, _, _, _, _, _, hMap, epoch, st2, hT, hRec⟩ :=
    vspaceMapFromFrameCap_ok tid ec args st st' hStep
  have k1 := vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_frame _ _ _ _ _ st st1 hInv hMap
  have hInv2 := (tagFrameMapping_keyFrame _ _ _ st1 st2 epoch k1.1 hT).2.2
  exact ((savedRegsKept.of_vspaceRootOnlyWrite k1.2.1).trans
    (tagFrameMapping_savedRegsKept k1.1 hT)).trans (cspaceRecordFrameMapping_savedRegsKept hInv2 hRec)

/-- **The VSpace unmap** writes VSpace roots alone. -/
theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_savedRegsKept {ec : CoreId}
    {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr} {st st' : SystemState} (hInv : st.objects.invExt)
    (hStep : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast ec asid vaddr st
      = .ok ((), st')) : savedRegsKept st st' :=
  savedRegsKept.of_vspaceRootOnlyWrite
    (vspaceUnmapPageWithShootdownAndIcacheBroadcast_ok_frame _ _ _ _ _ hInv hStep).2.1

/-- **The VSpace map or seL4's remap**: the unmap and the fresh map, each
keeping every saved register file. -/
theorem vspaceMapOrRemapFromFrameCap_savedRegsKept {tid : SeLe4n.ThreadId} {ec : CoreId}
    {args : Architecture.SyscallArgDecode.VSpaceMapArgs} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (hStep : vspaceMapOrRemapFromFrameCap tid ec args st = .ok ((), st')) :
    savedRegsKept st st' := by
  rcases vspaceMapOrRemapFromFrameCap_cases hStep with hM | ⟨st0, hU, hM | rfl⟩
  · exact vspaceMapFromFrameCap_savedRegsKept hInv hM
  · exact (vspaceUnmapPageWithShootdownAndIcacheBroadcast_savedRegsKept hInv hU).trans
      (vspaceMapFromFrameCap_savedRegsKept
        (vspaceUnmapPageWithShootdownAndIcacheBroadcast_ok_frame _ _ _ _ _ hInv hU).1 hM)
  · exact vspaceUnmapPageWithShootdownAndIcacheBroadcast_savedRegsKept hInv hU

/-- **The instruction unification** is cache maintenance: it writes no object. -/
theorem vspaceUnifyInstructionPage_savedRegsKept {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    {st st' : SystemState}
    (hStep : Architecture.vspaceUnifyInstructionPage asid vaddr st = .ok ((), st')) :
    savedRegsKept st st' :=
  savedRegsKept.of_objects_eq (Architecture.vspaceUnifyInstructionPage_frame hStep).1

/-- WS-ZA ZA6.32: **the interrupt acknowledge** writes the line's mask and the
physical write ledger, no object. -/
theorem irqHandlerAck_savedRegsKept {line : Nat} {st st' : SystemState}
    (hStep : Architecture.irqHandlerAck line st = .ok ((), st')) : savedRegsKept st st' := by
  rw [Architecture.irqHandlerAck_ok hStep]
  exact savedRegsKept.of_objects_eq rfl

/-- **The page-table map**: a store of the table over the table, the physical
write ledger, and a store of the root over the root. -/
theorem pageTableMap_savedRegsKept {tableId rootId : SeLe4n.ObjId} {vaddr : SeLe4n.VAddr}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (hStep : Architecture.pageTableMap tableId rootId vaddr st = .ok ((), st')) :
    savedRegsKept st st' := by
  obtain ⟨table, root, level, st1, hT, hR, -, -, -, -, hS1, hS2⟩ :=
    Architecture.pageTableMap_ok tableId rootId vaddr st st' hStep
  have hT' := (SystemState.getPageTable?_eq_some_iff st tableId table).mp hT
  have hR' := (SystemState.getVSpaceRoot?_eq_some_iff st rootId root).mp hR
  have hNe : rootId ≠ tableId := by
    intro hEq; subst hEq; rw [hT'] at hR'; cases hR'
  have hR1 : st1.objects[rootId]? = some (.vspaceRoot root) := by
    rw [storeObject_objects_ne _ _ _ _ _ hNe hInv hS1]; exact hR'
  have hInv1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS1
  exact ((savedRegsKept.storeObject hInv hS1 fun x hx => by rw [hT'] at hx; cases hx).trans
    (savedRegsKept.of_objects_eq (Architecture.recordPhysicalWrites_objects _ _))).trans
    (savedRegsKept.storeObject (by rw [Architecture.recordPhysicalWrites_objects]; exact hInv1) hS2
      fun x hx => by
        simp only [Architecture.recordPhysicalWrites_objects, hR1] at hx; cases hx)

/-- **The page-table unmap**: a store of the table over the table, and, when it
was installed, the physical write ledger and a store of the root over the
root. -/
theorem pageTableUnmap_savedRegsKept {tableId : SeLe4n.ObjId} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (hStep : Architecture.pageTableUnmap tableId st = .ok ((), st')) : savedRegsKept st st' := by
  unfold Architecture.pageTableUnmap at hStep
  cases hT : st.getPageTable? tableId with
  | none => rw [hT] at hStep; cases hStep
  | some table =>
    rw [hT] at hStep
    have hT' := (SystemState.getPageTable?_eq_some_iff st tableId table).mp hT
    have hNT : ∀ x : TCB, st.objects[tableId]? ≠ some (.tcb x) := fun x hx => by
      rw [hT'] at hx; cases hx
    simp only at hStep
    cases hI : table.installedIn with
    | none =>
      rw [hI] at hStep; cases hStep
      exact savedRegsKept.refl _
    | some inst =>
      rw [hI] at hStep
      simp only at hStep
      cases hR : st.getVSpaceRoot? inst.root with
      | none =>
        rw [hR] at hStep
        exact savedRegsKept.storeObject hInv hStep hNT
      | some root =>
        rw [hR] at hStep
        have hR' := (SystemState.getVSpaceRoot?_eq_some_iff st inst.root root).mp hR
        simp only at hStep
        split at hStep
        · split at hStep
          · cases hStep
          · cases hS1 : storeObject tableId _ st with
            | error e => rw [hS1] at hStep; cases hStep
            | ok p =>
              obtain ⟨⟨⟩, st1⟩ := p
              rw [hS1] at hStep
              have hNe : inst.root ≠ tableId := by
                intro hEq; rw [hEq, hT'] at hR'; cases hR'
              have hR1 : st1.objects[inst.root]? = some (.vspaceRoot root) := by
                rw [storeObject_objects_ne _ _ _ _ _ hNe hInv hS1]; exact hR'
              have hInv1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS1
              exact ((savedRegsKept.storeObject hInv hS1 hNT).trans
                (savedRegsKept.of_objects_eq (Architecture.recordPhysicalWrites_objects _ _))).trans
                (savedRegsKept.storeObject
                  (by rw [Architecture.recordPhysicalWrites_objects]; exact hInv1) hStep
                  fun x hx => by
                    simp only [Architecture.recordPhysicalWrites_objects, hR1] at hx; cases hx)
        · exact savedRegsKept.storeObject hInv hStep hNT

/-! ### The service arms -/

/-- **The service revoke** clears the invoked endpoint's service record. -/
theorem revokeServiceByRecordedRegistration_savedRegsKept {epId : SeLe4n.ObjId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (hStep : revokeServiceByRecordedRegistration epId st = .ok ((), st')) :
    savedRegsKept st st' := by
  obtain ⟨_, h⟩ := revokeServiceByRecordedRegistration_revokeService hStep
  exact savedRegsKept.of_serviceRecordRewrite hInv (revokeService_serviceRecordRewrite h)

/-- **The service query's answer names the caller**: the lookup is read-only and
the registration's id is staged into the caller's saved context, the executing
core's current thread, which no other core holds. -/
theorem writeReturnFrameToTcb_savedRegsKeptOffCore {e : CoreId} {st : SystemState}
    {tid : SeLe4n.ThreadId} (frame : Architecture.SyscallReturnFrame)
    (hInv : st.objects.invExt) (hCur : st.scheduler.currentOnCore e = some tid)
    (hU : currentsUnique st) (hN : st.currentNotResidentElsewhere) :
    savedRegsKeptOffCore e st (Architecture.writeReturnFrameToTcb st tid frame) := by
  unfold Architecture.writeReturnFrameToTcb
  exact savedRegsKeptOffCore_updateTcb hInv (offCoreFree_of_current hCur hU hN)
    (currentKeptOffCore_of_eq fun _ _ => by rw [SystemState.updateTcb_scheduler])
    (residentKeptOffCore_of_eq (by rw [SystemState.updateTcb_machine]))

end SeLe4n.Kernel
