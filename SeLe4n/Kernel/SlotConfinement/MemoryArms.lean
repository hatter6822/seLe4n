-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SlotConfinement.PriorityArms

/-!
# Per-core slot confinement — the live memory and lifecycle arms

§5j: the VSpace, untyped and CSpace arms, confined to no core at all;
§5k: `.lifecycleRetype`, a sweep over every core bounded by the cores the
destroyed thread occupied in the pre-state.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)
open SeLe4n.Kernel.Lifecycle.Suspend
open SeLe4n.Kernel.PriorityInheritance

-- ============================================================================
-- §5j The live memory-subsystem arms
-- ============================================================================
--
-- `.vspaceMap`, `.vspaceUnmap` and `.lifecycleRetype` route through per-core
-- wrappers (they take an `executingCore`), so round 15's inventory-completeness
-- check demands an entry for each. Their entry is the **strongest** one this
-- module can carry: an *empty* write set. Every field these wrappers touch
-- beyond the object store — `tlb`, `perCoreTlb`, `tlbShootdown`,
-- `perCoreICache`, `pendingIcacheMaintenance` — is proven outside the per-core
-- observer's read set by SM8.A (`onCore_perCore_independence` and its
-- corollaries), and none of them writes a scheduler slot or a register bank on
-- any core at all.
--
-- Stating that as a theorem rather than as an exception matters: an allowlist
-- entry is invisible to `crossCoreNiTheorem_count` and friends, so four live
-- arms would have been excluded from every coverage count in this file — the
-- same "reports coverage it does not have" failure that retired
-- `crossCoreRemoteWriterPendingAudit` earlier in this PR.

/-- SM8.B.2: caching a per-core TLB view writes no scheduler slot. -/
@[simp] theorem setTlbOnCore_scheduler (st : SystemState) (c : CoreId)
    (t : TlbState) :
    (Architecture.setTlbOnCore st c t).scheduler = st.scheduler := rfl

@[simp] theorem setTlbOnCore_machine (st : SystemState) (c : CoreId)
    (t : TlbState) :
    (Architecture.setTlbOnCore st c t).machine = st.machine := rfl

/-- SM8.B.2: the initiator's own TLB drain is likewise scheduler-silent. -/
@[simp] theorem drainInitiatorPerCoreView_scheduler (st : SystemState) (c : CoreId)
    (ops : List Architecture.TlbInvalidation) :
    (Architecture.drainInitiatorPerCoreView st c ops).scheduler = st.scheduler := rfl

@[simp] theorem drainInitiatorPerCoreView_machine (st : SystemState) (c : CoreId)
    (ops : List Architecture.TlbInvalidation) :
    (Architecture.drainInitiatorPerCoreView st c ops).machine = st.machine := rfl

/-- SM8.B.2: the whole memory-subsystem surface is scheduler- and
register-silent. One lemma per layer, each `rfl` or a one-step composition, so
the wrappers below reduce to `storeObject`'s frames at the leaf.

`SchedulerMachineFramed` bundles the pair because every layer needs both and
carrying them separately doubles the chain. -/
abbrev SchedulerMachineFramed (st st' : SystemState) : Prop :=
  st'.scheduler = st.scheduler ∧ st'.machine = st.machine

theorem observableSlotsConfinedToCores_nil_of_framed {st st' : SystemState}
    (h : SchedulerMachineFramed st st') :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq h.1 h.2

/-- SM8.B.2: unmapping a page is one `storeObject` of the rewritten root. -/
theorem vspaceUnmapPage_framed (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (st st' : SystemState)
    (h : Architecture.vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  unfold Architecture.vspaceUnmapPage at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · exact ⟨storeObject_scheduler_eq (Architecture.recordPhysicalWrites st _) _ _ _ h,
        storeObject_machine_eq (Architecture.recordPhysicalWrites st _) _ _ _ h⟩

/-- SM8.B.2: the TLB flush the unmap appends writes only `tlb`. -/
theorem vspaceUnmapPageWithFlush_framed (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (st st' : SystemState)
    (h : Architecture.vspaceUnmapPageWithFlush asid vaddr st = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  unfold Architecture.vspaceUnmapPageWithFlush at h
  split at h
  · exact absurd h (by simp)
  · next stMid hMid =>
    rw [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hs⟩ := h
    subst hs
    exact vspaceUnmapPage_framed asid vaddr st stMid hMid

/-- SM8.B.2: posting a shootdown round writes only `tlbShootdown`. -/
theorem withShootdownRound_framed (executingCore : CoreId)
    (op : Architecture.TlbInvalidation) (st st' : SystemState)
    (h : Architecture.withShootdownRound executingCore op st = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  rw [Architecture.withShootdownRound_total, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, hs⟩ := h
  subst hs
  exact ⟨rfl, rfl⟩

/-- SM8.B.2: unmap-with-round — page table, TLB, then the posted round. -/
theorem vspaceUnmapPageWithShootdown_framed (executingCore : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (st st' : SystemState)
    (h : Architecture.vspaceUnmapPageWithShootdown executingCore asid vaddr st
      = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  unfold Architecture.vspaceUnmapPageWithShootdown at h
  split at h
  · exact absurd h (by simp)
  · next stFlush hFlush =>
    obtain ⟨hs1, hm1⟩ := vspaceUnmapPageWithFlush_framed asid vaddr st stFlush hFlush
    obtain ⟨hs2, hm2⟩ := withShootdownRound_framed executingCore _ stFlush st' h
    exact ⟨by rw [hs2, hs1], by rw [hm2, hm1]⟩

/-- SM8.B.2: the initiator-atomic unmap — page table, TLB, round, initiator
view — writes no scheduler slot and no register bank. -/
theorem vspaceUnmapPageWithShootdownPerCore_framed (executingCore : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (st st' : SystemState)
    (h : Architecture.vspaceUnmapPageWithShootdownPerCore executingCore asid vaddr st
      = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  unfold Architecture.vspaceUnmapPageWithShootdownPerCore at h
  split at h
  · exact absurd h (by simp)
  · next stRound hRound =>
    rw [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hs⟩ := h
    subst hs
    obtain ⟨hs1, hm1⟩ :=
      vspaceUnmapPageWithShootdown_framed executingCore asid vaddr st stRound hRound
    exact ⟨by rw [drainInitiatorPerCoreView_scheduler, hs1],
           by rw [drainInitiatorPerCoreView_machine, hm1]⟩

/-- SM8.B.2: caching a walked translation is `perCoreTlb`-only. -/
@[simp] theorem tlbFillOnCore_scheduler (st : SystemState) (c : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) :
    (Architecture.tlbFillOnCore st c asid vaddr).scheduler = st.scheduler := by
  unfold Architecture.tlbFillOnCore
  split <;> rfl

@[simp] theorem tlbFillOnCore_machine (st : SystemState) (c : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) :
    (Architecture.tlbFillOnCore st c asid vaddr).machine = st.machine := by
  unfold Architecture.tlbFillOnCore
  split <;> rfl

/-- SM8.B.2: mapping a page is one `storeObject` of the rewritten root. -/
theorem vspaceMapPage_framed (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions) (st st' : SystemState)
    (h : Architecture.vspaceMapPage asid vaddr paddr perms st = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  unfold Architecture.vspaceMapPage at h
  repeat' split at h
  all_goals first
    | exact absurd h (by simp)
    | exact ⟨storeObject_scheduler_eq (Architecture.recordPhysicalWrites st _) _ _ _ h,
        storeObject_machine_eq (Architecture.recordPhysicalWrites st _) _ _ _ h⟩

/-- SM8.B.2: the checked map wrapper adds only guards and a `tlb` write. -/
theorem vspaceMapPageCheckedWithFlushFromState_framed (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr) (perms : PagePermissions)
    (st st' : SystemState)
    (h : Architecture.vspaceMapPageCheckedWithFlushFromState asid vaddr paddr perms st
      = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  unfold Architecture.vspaceMapPageCheckedWithFlushFromState
    Architecture.vspaceMapPageWithFlush at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · next stMap hMap =>
          rw [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, hs⟩ := h
          subst hs
          exact vspaceMapPage_framed asid vaddr paddr perms st stMap hMap

/-- SM8.B.2: a *remap* posts a round; a fresh map does not. Either way the
scheduler and the register banks frame. -/
theorem vspaceMapPageCheckedWithShootdownFromState_framed (executingCore : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions) (st st' : SystemState)
    (h : Architecture.vspaceMapPageCheckedWithShootdownFromState executingCore asid vaddr
      paddr perms st = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  unfold Architecture.vspaceMapPageCheckedWithShootdownFromState at h
  simp only [] at h
  split at h
  · exact absurd h (by simp)
  · next stFlush hFlush =>
    obtain ⟨hs1, hm1⟩ :=
      vspaceMapPageCheckedWithFlushFromState_framed asid vaddr paddr perms st stFlush hFlush
    split at h
    · obtain ⟨hs2, hm2⟩ := withShootdownRound_framed executingCore _ stFlush st' h
      exact ⟨by rw [hs2, hs1], by rw [hm2, hm1]⟩
    · rw [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, hs⟩ := h
      subst hs
      exact ⟨hs1, hm1⟩

/-- SM8.B.2 (**the live `.vspaceMap` bound**): the initiator-atomic map writes
**no core** — page tables, the scalar TLB, an optional remap round, the
initiator's drain and the fresh fill are all outside the observer's read set. -/
theorem vspaceMapPageCheckedWithShootdownFromStatePerCore_confinedToCores
    (executingCore : CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions) (st st' : SystemState)
    (hStep : Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore executingCore
      asid vaddr paddr perms st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] := by
  refine observableSlotsConfinedToCores_nil_of_framed ?_
  unfold Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore at hStep
  split at hStep
  · exact absurd hStep (by simp)
  · next stRound hRound =>
    rw [Except.ok.injEq, Prod.mk.injEq] at hStep
    obtain ⟨-, hs⟩ := hStep
    subst hs
    obtain ⟨hs1, hm1⟩ := vspaceMapPageCheckedWithShootdownFromState_framed executingCore
      asid vaddr paddr perms st stRound hRound
    exact ⟨by rw [tlbFillOnCore_scheduler, drainInitiatorPerCoreView_scheduler, hs1],
           by rw [tlbFillOnCore_machine, drainInitiatorPerCoreView_machine, hm1]⟩

/-- **WS-BP BP7.1**: the live `.vspaceMap` arm past its address-space check —
the frame-capability resolution in front of the per-core map — writes **no
core**.  The resolution and both admission checks are reads; the arm's writes
are the per-core map and, since `v0.36.7`, the frame capability's mapping record
(`vspaceMapFromFrameCap_ok`) — one CNode store, which writes neither the
scheduler nor the machine — so the bound is the per-core map's own. -/
theorem vspaceMapFromFrameCap_confinedToCores
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (args : Architecture.SyscallArgDecode.VSpaceMapArgs) (st st' : SystemState)
    (hStep : vspaceMapFromFrameCap tid executingCore args st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] := by
  obtain ⟨_, _, frame, st1, -, -, -, -, -, hMap, epoch, st2, hT, hRec⟩ :=
    vspaceMapFromFrameCap_ok tid executingCore args st st' hStep
  -- WS-BP BP7.1 (`v0.36.7`): the mapping record is one CNode store, and
  -- (PR #904 review, `v0.36.41`) the epoch tag a root store and a frame store —
  -- none writes the scheduler or the machine.
  obtain ⟨_, _, _, _, hStore⟩ := cspaceRecordFrameMapping_ok_decompose _ _ st2 st' hRec
  obtain ⟨hTS, hTM⟩ := tagFrameMapping_scheduler_machine _ _ _ st1 st2 epoch hT
  exact observableSlotsConfinedToCores_trans
    (observableSlotsConfinedToCores_trans
      (vspaceMapPageCheckedWithShootdownFromStatePerCore_confinedToCores _ _ _
        frame.base _ st st1 hMap)
      (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq hTS hTM))
    (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
      (storeObject_scheduler_eq _ _ _ _ hStore) (storeObject_machine_eq _ _ _ _ hStore))

/-- SM8.B.2: the I-cache broadcast seam writes only `perCoreICache` and the
maintenance ledger, so it frames whatever its wrapped transition frames. -/
theorem withIcacheBroadcast_framed
    (mkOp : SystemState → Option Architecture.ICacheInvalidation) (k : Kernel Unit)
    (st st' : SystemState)
    (hk : ∀ s s', k s = .ok ((), s') → SchedulerMachineFramed s s')
    (h : Architecture.withIcacheBroadcast mkOp k st = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  unfold Architecture.withIcacheBroadcast at h
  simp only [] at h
  split at h
  · exact absurd h (by simp)
  · next stK hK =>
    obtain ⟨hs, hm⟩ := hk st stK hK
    split at h
    · rw [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, he⟩ := h
      subst he
      exact ⟨hs, hm⟩
    · rw [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, he⟩ := h
      subst he
      exact ⟨hs, hm⟩

/-- SM8.B.2 (**the live `.vspaceUnmap` bound**): the unmap seam writes **no
core**. Page tables, the scalar TLB, the shootdown round, the initiator's own
per-core view and the I-cache ledger — none of them is a scheduler slot or a
register bank, on any core. -/
theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_confinedToCores
    (executingCore : CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (st st' : SystemState)
    (hStep : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast executingCore
      asid vaddr st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_framed
    (withIcacheBroadcast_framed _ _ st st'
      (fun _ _ hk => vspaceUnmapPageWithShootdownPerCore_framed executingCore asid vaddr _ _ hk)
      hStep)

/-- WS-BP BP7.1: the page teardown (`unmapLivePages`, shared by the untyped
reset and a frame capability's destruction) is a sequence of the `.vspaceUnmap`
arm's own transition, each step taken only while its page is still live, so it
frames what one unmap frames. -/
theorem unmapLivePages_framed (executingCore : CoreId) :
    ∀ (ps : List MappedPage) (st st' : SystemState),
      unmapLivePages executingCore ps st = .ok ((), st') →
      SchedulerMachineFramed st st'
  | [], st, st', h => by
      simp only [unmapLivePages, Except.ok.injEq, Prod.mk.injEq, true_and] at h
      subst h; exact ⟨rfl, rfl⟩
  | p :: rest, st, st', h => by
      simp only [unmapLivePages] at h
      split at h
      · cases h1 : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast
            executingCore p.asid p.vaddr st with
        | error e => rw [h1] at h; cases h
        | ok pr =>
          obtain ⟨u, st1⟩ := pr; cases u
          rw [h1] at h
          obtain ⟨hs1, hm1⟩ := withIcacheBroadcast_framed _ _ st st1
            (fun _ _ hk => vspaceUnmapPageWithShootdownPerCore_framed executingCore p.asid
              p.vaddr _ _ hk) h1
          obtain ⟨hs2, hm2⟩ := unmapLivePages_framed executingCore rest st1 st' h
          exact ⟨hs2.trans hs1, hm2.trans hm1⟩
      · exact unmapLivePages_framed executingCore rest st st' h

/-- WS-BP BP7.1 (slice 3, carved subtrees at slice 4): retiring carved objects
writes the object table and its bookkeeping — never the scheduler, never the
machine. -/
theorem retireCarvedObjects_framed :
    ∀ (ids : List SeLe4n.ObjId) (st : SystemState),
      SchedulerMachineFramed st (retireCarvedObjects st ids)
  | [], _ => ⟨rfl, rfl⟩
  | id :: rest, st => by
      have hOne : SchedulerMachineFramed st (retireCarvedObject st id) := by
        unfold retireCarvedObject; split <;> exact ⟨rfl, rfl⟩
      obtain ⟨hs, hm⟩ := retireCarvedObjects_framed rest (retireCarvedObject st id)
      exact ⟨hs.trans hOne.1, hm.trans hOne.2⟩

/-- WS-BP BP7.1 (slice 3) (**the live `.untypedReset` bound**): a reset writes
**no core**.  Its unmap pass is the `.vspaceUnmap` arm's own transition, whose
bound is already empty; retiring the carved subtree and storing the rewound
untyped write the object table alone.  An executing core is taken only to
initiate the shootdown rounds, exactly as the `.vspaceUnmap` arm takes it. -/
theorem untypedReset_confinedToCores
    (executingCore : CoreId) (untypedId : SeLe4n.ObjId) (st st' : SystemState)
    (hStep : untypedReset executingCore untypedId st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] := by
  apply observableSlotsConfinedToCores_nil_of_framed
  obtain ⟨_, ids, st1, -, -, -, -, -, -, -, hUnmap, -, -, -, -, hSt⟩ :=
    untypedReset_ok_decompose executingCore untypedId st st' hStep
  obtain ⟨hs1, hm1⟩ := unmapLivePages_framed executingCore _ st st1 hUnmap
  obtain ⟨hs2, hm2⟩ := retireCarvedObjects_framed ids st1
  exact ⟨(storeObject_scheduler_eq _ _ _ _ hSt).trans (hs2.trans hs1),
    (storeObject_machine_eq _ _ _ _ hSt).trans (hm2.trans hm1)⟩

/-- **`v0.36.37`: the live `.untypedReset` arm writes no core.**  The arm is the
reset followed by the `.aside1` round fold, which writes neither the scheduler
nor the machine (`untypedResetWithShootdown_ok_frame`). -/
theorem untypedResetWithShootdown_confinedToCores
    (executingCore : CoreId) (untypedId : SeLe4n.ObjId) (st st' : SystemState)
    (hStep : untypedResetWithShootdown executingCore untypedId st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] := by
  apply observableSlotsConfinedToCores_nil_of_framed
  obtain ⟨st1, hR, -, hs, hm, -⟩ :=
    untypedResetWithShootdown_ok_frame executingCore untypedId st st' hStep
  obtain ⟨_, ids, st2, -, -, -, -, -, -, -, hUnmap, -, -, -, -, hSt⟩ :=
    untypedReset_ok_decompose executingCore untypedId st st1 hR
  obtain ⟨hs1, hm1⟩ := unmapLivePages_framed executingCore _ st st2 hUnmap
  obtain ⟨hs2, hm2⟩ := retireCarvedObjects_framed ids st2
  exact ⟨hs.trans ((storeObject_scheduler_eq _ _ _ _ hSt).trans (hs2.trans hs1)),
    hm.trans ((storeObject_machine_eq _ _ _ _ hSt).trans (hm2.trans hm1))⟩

/-- WS-BP BP7.1 (`v0.36.12`): the finalisation a destroying capability
operation owes — the page-table detach, stores to VSpace roots, and the page
teardown, the `.vspaceUnmap` arm's own transition — writes no scheduler and no
machine state. -/
theorem finaliseDestroyedCapabilities_framed (executingCore : CoreId) (pre : SystemState)
    (pages : List MappedPage) (st st' : SystemState)
    (h : finaliseDestroyedCapabilities executingCore pre pages st = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  obtain ⟨st1, hD, hF, -⟩ := finaliseDestroyedCapabilities_ok executingCore pre pages st st' h
  obtain ⟨hs1, hm1⟩ := detachPageTables_ok_scheduler_machine _ st st1 hD
  obtain ⟨hs2, hm2⟩ :=
    unmapLivePages_framed executingCore _ st1 st' (finaliseFramePages_ok _ _ _ _ hF).1
  exact ⟨hs2.trans hs1, hm2.trans hm1⟩

/-- WS-BP BP7.1 (`v0.36.7`): **the live `.cspaceDelete` arm writes no core.**  The
delete writes a CNode and the CDT; the teardown that removes the destroyed frame
capability's mapping is the `.vspaceUnmap` arm's own transition, whose rounds the
executing core only initiates. -/
theorem cspaceDeleteSlotFinalising_confinedToCores
    (executingCore : CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (hStep : cspaceDeleteSlotFinalising executingCore addr st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] := by
  obtain ⟨st1, hD, hF⟩ := cspaceDeleteSlotFinalising_ok executingCore addr st st' hStep
  obtain ⟨hs1, hm1⟩ := cspaceDeleteSlot_scheduler_machine addr st st1 hD
  obtain ⟨hs2, hm2⟩ := finaliseDestroyedCapabilities_framed executingCore st _ st1 st' hF
  exact observableSlotsConfinedToCores_nil_of_framed ⟨hs2.trans hs1, hm2.trans hm1⟩

/-- WS-BP BP7.1 (`v0.36.7`): **the live `.cspaceRevoke` arm writes no core.**  The
revocation writes CNodes, the CDT and parked messages in TCB records; the
teardown is the `.vspaceUnmap` arm's own transition. -/
theorem cspaceRevokeCdtFinalising_confinedToCores
    (executingCore : CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (hStep : cspaceRevokeCdtFinalising executingCore addr st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] := by
  obtain ⟨pages, st1, hR, hF⟩ := cspaceRevokeCdtFinalising_ok executingCore addr st st' hStep
  obtain ⟨hs1, hm1⟩ := cspaceRevokeCdt_scheduler_machine addr st st1 pages hR
  obtain ⟨hs2, hm2⟩ := finaliseDestroyedCapabilities_framed executingCore st _ st1 st' hF
  exact observableSlotsConfinedToCores_nil_of_framed ⟨hs2.trans hs1, hm2.trans hm1⟩

-- ============================================================================
-- §5k The live `.lifecycleRetype` arm — a sweep bounded by occupancy
-- ============================================================================
--
-- The third and last routing-allowlist exception, and the only one of the three
-- that genuinely writes scheduler state: destroying a TCB sweeps it out of
-- **every** core's run queue and current slot, because a destroy has no home
-- core to key on.
--
-- The naive bound is therefore `allCores`, which is true and says nothing. The
-- honest one is the set of cores the destroyed thread actually occupied in the
-- pre-state, and it is available only because review round 17 rewrote the
-- sweep's step to be *guarded* by `threadOccupiesCore`: an unoccupied core is
-- left literally untouched rather than rewritten with equal values.
--
-- Everything else the retype pipeline does — the donation return, the
-- `scThreadIndex` removal, the two IPC-reference sweeps, the service-registration
-- cleanup, the CDT detach, the memory scrub, the object store, the ASID
-- shootdown rounds, the initiator's own TLB drain and the I-cache broadcast —
-- writes no scheduler slot and no register bank, and each of those is discharged
-- by a frame rather than by an argument.

/-- SM8.B.2: the I-cache broadcast seam preserves whatever confinement its
wrapped transition has.

The `withIcacheBroadcast_framed` sibling, keyed on the write set rather than on
whole-machine equality — the retype needs this one because its memory scrub
genuinely writes `machine`, so the `Framed` form is unavailable. -/
theorem withIcacheBroadcast_confinedToCores
    (mkOp : SystemState → Option Architecture.ICacheInvalidation) (k : Kernel Unit)
    (cs : List CoreId) (st st' : SystemState)
    (hk : ∀ s', k st = .ok ((), s') → observableSlotsConfinedToCores st s' cs)
    (h : Architecture.withIcacheBroadcast mkOp k st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' cs := by
  unfold Architecture.withIcacheBroadcast at h
  simp only [] at h
  split at h
  · exact absurd h (by simp)
  · next stK hK =>
    have hInner := hk stK hK
    split at h <;>
      · rw [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, he⟩ := h
        subst he
        exact observableSlotsConfinedToCores_of_framed_suffix (stMid := stK) rfl rfl hInner

-- WS-RR RR8.12 Cut C3b-iii (`v0.35.169`): `lifecycleRetypeWriteSetOf` and
-- `lifecycleRetypeWriteSet` moved to the production
-- `SeLe4n/Kernel/SyscallSchedFootprint.lean`, beside
-- `schedLockSet_lifecycleRetypeOnCore`, whose run segment IS the second.  Same
-- names, same namespace; the confinement theorems below stay here.

-- `v0.35.164`: `tcbCleanupArm_confinedToCores` is gone with the two mid-states it
-- abstracted over; the pipeline's first step is the reservation arm, composed
-- below through `cancelDonationArmOnCore_confinedToCores`.

/-- SM8.B.2 (**the cleanup pipeline's bound**): the pre-retype cleanup writes no
core outside the destroyed object's write set.

The case split is the definition's own: the TCB arm carries the sweep, the CNode
and endpoint arms are frames, and the remaining kinds return the state
unchanged. The TCB arm's prefix — the reservation arm
(`cancelDonationArmOnCore`, `v0.35.164`: an unbind with a replenish purge, or a
return with a replenish migration) and, on the error path, the reply-link
rejection — is per-core silent and keeps every run queue and current slot
(`cancelDonationArmOnCore_runQueue_current_eq`), which is why the write set may
be read at the pipeline's entry state rather than at the sweep's: the occupancy
set is the same on both. -/
theorem lifecyclePreRetypeCleanup_confinedToCores
    (st stClean : SystemState) (target : SeLe4n.ObjId) (currentObj newObj : KernelObject)
    (hOk : lifecyclePreRetypeCleanup st target currentObj newObj = .ok stClean) :
    observableSlotsConfinedToCores st stClean (lifecycleRetypeWriteSetOf st currentObj) := by
  cases currentObj with
  | tcb tcb =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    -- Round 39: the running-target rejection is vacuous on the `.ok` path.
    rw [if_neg (by
      intro hRun
      rw [if_pos hRun] at hOk
      exact absurd hOk (by simp))] at hOk
    cases hArm : cancelDonationArmOnCore st tcb.tid tcb with
    | error e => rw [hArm] at hOk; contradiction
    | ok stArm =>
      rw [hArm] at hOk
      simp only [] at hOk
      have hRO : tcb.replyObject.isSome = false := by
        cases hr : tcb.replyObject.isSome with
        | false => rfl
        | true => rw [if_pos hr] at hOk; exact absurd hOk (by simp)
      rw [if_neg (by simp [hRO])] at hOk
      injection hOk with hOk; subst hOk
      simp only [lifecycleRetypeWriteSetOf]
      -- The arm writes no observable slot; the sweep's write set at the arm's
      -- post-state is the entry state's, because the arm keeps every run queue
      -- and current slot.
      have hOcc : threadOccupiedCores stArm tcb.tid = threadOccupiedCores st tcb.tid :=
        threadOccupiedCores_congr_of_runQueue_current tcb.tid
          (fun c => cancelDonationArmOnCore_runQueue_current_eq st stArm tcb.tid tcb c hArm)
      have hTrans := observableSlotsConfinedToCores_trans
        (cancelDonationArmOnCore_confinedToCores st stArm tcb.tid tcb hArm)
        (cleanupTcbReferences_confinedToCores stArm tcb.tid)
      rw [List.nil_append, hOcc] at hTrans
      exact hTrans
  | cnode cn =>
    simp only [lifecyclePreRetypeCleanup, lifecycleRetypeWriteSetOf] at hOk ⊢
    have hDetach : observableSlotsConfinedToCores st (detachCNodeSlots st target cn) [] :=
      observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
        (detachCNodeSlots_scheduler_eq st target cn)
        (detachCNodeSlots_machine_eq st target cn)
    -- The derivation-parent guard rejects (vacuous on the `.ok` path); past it
    -- the cleanup is the detach, whatever the replacement's shape.
    split at hOk
    · cases hOk
    · split at hOk
      · cases hOk
      · injection hOk with hOk; subst hOk; exact hDetach
  | endpoint _ =>
    simp only [lifecyclePreRetypeCleanup, lifecycleRetypeWriteSetOf] at hOk ⊢
    injection hOk with hOk; subst hOk
    exact observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
      (cleanupEndpointServiceRegistrations_scheduler_eq st target)
      (cleanupEndpointServiceRegistrations_machine_eq st target)
  | reply _ =>
    simp only [lifecyclePreRetypeCleanup, lifecycleRetypeWriteSetOf] at hOk ⊢
    split at hOk
    · cases hOk
    · injection hOk with hOk; subst hOk; exact observableSlotsConfinedToCores_refl _ _
  | frame _ | pageTable _ | untyped _ | vspaceRoot _ =>
    -- WS-BP BP7.1: a frame target is refused — and since slice 4a (`v0.36.8`)
    -- an untyped one, and since `v0.36.35` a VSpace root — so there is no
    -- `.ok` post-state.
    simp [lifecyclePreRetypeCleanup] at hOk
  | notification _ =>
    simp only [lifecyclePreRetypeCleanup, lifecycleRetypeWriteSetOf] at hOk ⊢
    injection hOk with hOk; subst hOk; exact observableSlotsConfinedToCores_refl _ _
  | schedContext _ =>
    -- WS-OD OD5.4: a context heading a reply stack is refused (vacuous on `.ok`).
    -- `v0.35.165`: past that guard the arm RELEASES the binding, which writes no
    -- confined slot -- the replenish queue is not one of the six.
    simp only [lifecyclePreRetypeCleanup, lifecycleRetypeWriteSetOf] at hOk ⊢
    split at hOk
    · cases hOk
    · injection hOk with hOk; subst hOk
      exact releaseSchedContextBinding_confinedToCores _ _ _

-- **WS-RR RR8.12 Cut C6g (`v0.35.180`)**: `lifecycleRetypeDirect_framed` is
-- deleted.  It was a `private` copy of what is now the production
-- `lifecycleRetypeDirect_scheduler_machine_eq` (`Lifecycle/Operations/RetypeWrappers.lean`,
-- beside the step) — the same body, in a staged module, where no production asker
-- could reach it.  Every use below reads the public one.

/-- SM8.B.2: the base retype-with-cleanup writes no core outside the write set.

Three of its four steps are frames — the well-formedness reject, the memory
scrub (`machine.memory`, and `machine.regs` is a field beside it) and the object
store — so the whole transition's bound is the cleanup's. -/
theorem lifecycleRetypeDirectWithCleanup_confinedToCores
    (authCap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st st' : SystemState)
    (h : lifecycleRetypeDirectWithCleanup authCap target newObj st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' (lifecycleRetypeWriteSet st target) := by
  unfold lifecycleRetypeDirectWithCleanup SystemState.getObject? at h
  simp only [lifecycleRetypeWriteSet, SystemState.getObject?_eq_getElem]
  split at h
  · exact absurd h (by simp)
  · next =>
    split at h
    · -- absent target: the direct store errors or replaces, either way scheduler-silent
      next hNone =>
        rw [hNone]
        obtain ⟨hs, hm⟩ := lifecycleRetypeDirect_scheduler_machine_eq authCap target newObj st st' h
        exact observableSlotsConfinedToCores_nil_of_scheduler_machine_eq hs hm
    · next currentObj hSome =>
      rw [hSome]
      split at h
      · exact absurd h (by simp)
      · next stClean hClean =>
        have hCleanConf :=
          lifecyclePreRetypeCleanup_confinedToCores st stClean target currentObj newObj hClean
        obtain ⟨hs, hm⟩ := lifecycleRetypeDirect_scheduler_machine_eq authCap target newObj _ st' h
        -- the scrub writes `machine.memory`, so the suffix frame here is the
        -- register-bank one rather than whole-machine equality
        refine observableSlotsConfinedToCores_of_framed_suffix_regs
          (hs.trans (scrubObjectMemory_scheduler_eq stClean target currentObj.objectType))
          (fun c => by
            rw [hm, scrubObjectMemory_regsOnCore]) hCleanConf

-- **WS-RR RR8.12 Cut C6g (`v0.35.180`)**: `retypeInitiatorDrain_scheduler` and
-- `retypeInitiatorDrain_machine` moved to `Lifecycle/Operations/RetypeWrappers.lean`,
-- beside the definition they frame.  They were declared here — in a STAGED module —
-- while the step is production, so the production retype footprint's replenish frame
-- could not read them: *when a question has one owner and an asker that cannot see
-- it, the owner is in the wrong layer* (`v0.35.59`).  Their sibling
-- `retypeAsidRoundFold_scheduler` had been in that production module all along, which
-- is what made the split visible.

/-- SM8.B.2: adding the ASID shootdown rounds does not widen the write set —
TLB maintenance is not scheduling. -/
theorem lifecycleRetypeDirectWithCleanupShootdown_confinedToCores
    (executingCore : CoreId) (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) (st st' : SystemState)
    (h : lifecycleRetypeDirectWithCleanupShootdown executingCore authCap target newObj st
      = .ok ((), st')) :
    observableSlotsConfinedToCores st st' (lifecycleRetypeWriteSet st target) := by
  unfold lifecycleRetypeDirectWithCleanupShootdown at h
  cases hBase : lifecycleRetypeDirectWithCleanup authCap target newObj st with
  | error e => rw [hBase] at h; exact absurd h (by simp)
  | ok pair =>
    obtain ⟨u, stBase⟩ := pair
    cases u
    rw [hBase] at h
    simp only [] at h
    rw [retypeShootdownAsids_eq] at h
    rw [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, he⟩ := h
    subst he
    exact observableSlotsConfinedToCores_of_framed_suffix
      (retypeAsidRoundFold_scheduler _ _ _) (retypeAsidRoundFold_machine _ _ _)
      (lifecycleRetypeDirectWithCleanup_confinedToCores authCap target newObj st stBase hBase)

/-- SM8.B.2: nor does the initiator's own per-core view drain. -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCore_confinedToCores
    (executingCore : CoreId) (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) (st st' : SystemState)
    (h : lifecycleRetypeDirectWithCleanupShootdownPerCore executingCore authCap target
      newObj st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' (lifecycleRetypeWriteSet st target) := by
  unfold lifecycleRetypeDirectWithCleanupShootdownPerCore at h
  cases hRound : lifecycleRetypeDirectWithCleanupShootdown executingCore authCap target
      newObj st with
  | error e => rw [hRound] at h; exact absurd h (by simp)
  | ok pair =>
    obtain ⟨u, stRound⟩ := pair
    cases u
    rw [hRound] at h
    simp only [] at h
    rw [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, he⟩ := h
    subst he
    exact observableSlotsConfinedToCores_of_framed_suffix
      (retypeInitiatorDrain_scheduler _ _ _) (retypeInitiatorDrain_machine _ _ _)
      (lifecycleRetypeDirectWithCleanupShootdown_confinedToCores executingCore authCap target
        newObj st stRound hRound)

/-- SM8.B.2 (**the live `.lifecycleRetype` bound**): a retype writes no core the
destroyed object did not occupy.

The third routing-allowlist exception discharged, and the sharp statement rather
than the trivially-true `allCores` one: destroying a thread that no core held
(suspended, or queued nowhere) is invisible on **every** core, and destroying a
running one is visible only where it ran. Retyping anything that is not a TCB
has an empty write set outright. -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_confinedToCores
    (executingCore : CoreId) (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) (st st' : SystemState)
    (h : lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache executingCore authCap
      target newObj st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' (lifecycleRetypeWriteSet st target) :=
  withIcacheBroadcast_confinedToCores _ _ _ st st'
    (fun _ hk => lifecycleRetypeDirectWithCleanupShootdownPerCore_confinedToCores
      executingCore authCap target newObj st _ hk) h

/-- SM8.B.2: destroying an object that is not a TCB writes **no** core.

The load-bearing sharpness check on the other side from
`removeRunnableFromAllCores_confinedToCores`: the write set is not merely
*smaller* than `allCores`, it is empty for six of the seven object kinds. -/
theorem lifecycleRetypeWriteSet_nil_of_not_tcb (st : SystemState) (target : SeLe4n.ObjId)
    (h : ∀ tcb : TCB, st.objects[target]? ≠ some (.tcb tcb)) :
    lifecycleRetypeWriteSet st target = [] := by
  unfold lifecycleRetypeWriteSet SystemState.getObject?
  cases hObj : st.objects[target]? with
  | none => rfl
  | some obj =>
    cases obj with
    | tcb tcb => exact absurd hObj (h tcb)
    | _ => rfl

end SeLe4n.Kernel
