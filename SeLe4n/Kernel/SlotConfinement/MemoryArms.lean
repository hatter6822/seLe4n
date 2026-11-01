-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SlotConfinement.PriorityArms
import SeLe4n.Kernel.Lifecycle.Operations.CleanupFootprint

/-!
# Per-core slot confinement — the live memory and lifecycle arms

§5j: the VSpace, untyped and CSpace arms, confined to no core at all;
§5k: `.untypedRetype`, confined to no core, and the destroy path's cleanup, a
sweep over every core bounded by the cores the destroyed thread occupied in the
pre-state.
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
-- `.vspaceMap`, `.vspaceUnmap` and `.untypedRetype` route through per-core
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
  split <;> simp

@[simp] theorem tlbFillOnCore_machine (st : SystemState) (c : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) :
    (Architecture.tlbFillOnCore st c asid vaddr).machine = st.machine := by
  unfold Architecture.tlbFillOnCore
  split <;> simp

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

/-- The initiator-atomic map writes neither the scheduler nor the machine. -/
theorem vspaceMapPageCheckedWithShootdownFromStatePerCore_framed
    (executingCore : CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions) (st st' : SystemState)
    (hStep : Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore executingCore
      asid vaddr paddr perms st = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
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

/-- SM8.B.2 (**the live `.vspaceMap` bound**): the initiator-atomic map writes
**no core** — page tables, the scalar TLB, an optional remap round, the
initiator's drain and the fresh fill are all outside the observer's read set. -/
theorem vspaceMapPageCheckedWithShootdownFromStatePerCore_confinedToCores
    (executingCore : CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions) (st st' : SystemState)
    (hStep : Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore executingCore
      asid vaddr paddr perms st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_framed
    (vspaceMapPageCheckedWithShootdownFromStatePerCore_framed executingCore asid vaddr paddr
      perms st st' hStep)

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

/-- The verified unmap with its instruction-cache broadcast writes neither the
scheduler nor the machine. -/
theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_framed
    (executingCore : CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (st st' : SystemState)
    (hStep : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast executingCore
      asid vaddr st = .ok ((), st')) :
    SchedulerMachineFramed st st' :=
  withIcacheBroadcast_framed _ _ st st'
    (fun _ _ hk => vspaceUnmapPageWithShootdownPerCore_framed executingCore asid vaddr _ _ hk)
    hStep

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
    (vspaceUnmapPageWithShootdownAndIcacheBroadcast_framed executingCore asid vaddr st st' hStep)

/-- WS-BP BP7.1: the page teardown (`unmapLivePages`, run when a frame
capability is destroyed) is a sequence of the `.vspaceUnmap`
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
          obtain ⟨hs1, hm1⟩ := vspaceUnmapPageWithShootdownAndIcacheBroadcast_framed
            executingCore p.asid p.vaddr st st1 h1
          obtain ⟨hs2, hm2⟩ := unmapLivePages_framed executingCore rest st1 st' h
          exact ⟨hs2.trans hs1, hm2.trans hm1⟩
      · exact unmapLivePages_framed executingCore rest st st' h

/-- **The live `.untypedReset` arm writes no core** (WS-ZA ZA5.4).  The reset
writes `0` to the invoked capability's free index — one CNode store — and
nothing else, so it writes neither the scheduler nor the machine. -/
theorem untypedResetSlot_confinedToCores
    (srcCnode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (st st' : SystemState)
    (hStep : untypedResetSlot srcCnode srcSlot st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] := by
  apply observableSlotsConfinedToCores_nil_of_framed
  rw [untypedResetSlot_ok_frame hStep]
  exact ⟨setCapFreeIndex_scheduler _ _ _, setCapFreeIndex_machine _ _ _⟩

/-- WS-BP BP7.1 (`v0.36.12`): the finalisation a destroying capability
operation owes — the page-table detach, stores to VSpace roots, and the page
teardown, the `.vspaceUnmap` arm's own transition — writes no scheduler and no
machine state. -/
theorem finaliseDestroyedCapabilities_framed (executingCore : CoreId) (named : List SeLe4n.ObjId)
    (pages : List MappedPage) (st st' : SystemState)
    (h : finaliseDestroyedCapabilities executingCore named pages st = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  obtain ⟨st1, hD, hF⟩ := finaliseDestroyedCapabilities_ok executingCore named pages st st' h
  obtain ⟨hs1, hm1⟩ := detachPageTables_ok_scheduler_machine _ st st1 hD
  obtain ⟨hs2, hm2⟩ := unmapLivePages_framed executingCore _ st1 st' hF
  exact ⟨hs2.trans hs1, hm2.trans hm1⟩

/-- **Every step is confined to every core**: the write set a transition
declares when it may wake a thread on any core. -/
theorem observableSlotsConfinedToCores_allCores (st st' : SystemState) :
    observableSlotsConfinedToCores st st' Concurrency.allCores :=
  ⟨fun c hc => absurd (Concurrency.mem_allCores c) hc,
   fun c hc => absurd (Concurrency.mem_allCores c) hc,
   fun c hc => absurd (Concurrency.mem_allCores c) hc,
   fun c hc => absurd (Concurrency.mem_allCores c) hc,
   fun c hc => absurd (Concurrency.mem_allCores c) hc,
   fun c hc => absurd (Concurrency.mem_allCores c) hc⟩

/-- WS-ZA ZA5.4 part 23: **the cores a finalising delete of slot `addr` may
write.**  None when the delete destroys no final capability
(`slotRetireTarget` is `0`), since the delete, the page teardown and the retire
write no scheduler and no machine state; every core otherwise, since the
finalisation of the object the final capability names (`finaliseFinalObject`)
wakes each waiter it cancels on that waiter's own core. -/
def cspaceDeleteSlotFinalisingCores (st : SystemState) (addr : CSpaceAddr) : List CoreId :=
  if slotRetireTarget st addr.cnode addr.slot = 0 then [] else Concurrency.allCores

/-- A finalising delete that destroys no final capability writes no scheduler
and no machine state. -/
theorem cspaceDeleteSlotFinalising_framed
    (executingCore : CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (hStep : cspaceDeleteSlotFinalising executingCore addr st = .ok ((), st'))
    (h0 : slotRetireTarget st addr.cnode addr.slot = 0) :
    SchedulerMachineFramed st st' := by
  obtain ⟨st1, st2, hD, hF, rfl⟩ := cspaceDeleteSlotFinalising_ok executingCore addr st st' hStep
  obtain ⟨hs1, hm1⟩ := cspaceDeleteSlot_scheduler_machine addr st st1 hD
  obtain ⟨hs2, hm2⟩ := finaliseDestroyedCapabilities_framed executingCore _ _ st1 st2 hF
  rw [h0, retireFinalisedObject_zero]
  exact ⟨hs2.trans hs1, hm2.trans hm1⟩

/-- WS-BP BP7.1 (`v0.36.7`), WS-ZA ZA5.4 part 23: **the live `.cspaceDelete` arm
writes only the cores `cspaceDeleteSlotFinalisingCores` names.**  The delete
writes a CNode and the CDT; the teardown that removes the destroyed frame
capability's mapping is the `.vspaceUnmap` arm's own transition, whose rounds the
executing core only initiates; the finalisation of a final capability's
endpoint or notification wakes the waiters it cancels. -/
theorem cspaceDeleteSlotFinalising_confinedToCores
    (executingCore : CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (hStep : cspaceDeleteSlotFinalising executingCore addr st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' (cspaceDeleteSlotFinalisingCores st addr) := by
  unfold cspaceDeleteSlotFinalisingCores
  split
  · exact observableSlotsConfinedToCores_nil_of_framed
      (cspaceDeleteSlotFinalising_framed executingCore addr st st' hStep ‹_›)
  · exact observableSlotsConfinedToCores_allCores st st'

/-- WS-ZA ZA5.4 part 26: **the live `.cspaceDelete` arm, the zombie delete,
writes only the cores `cspaceDeleteSlotFinalisingCores` names**: when its slot
retires nothing it is the one finalising delete
(`cspaceDeleteSlotZombie_of_target_zero`); otherwise every core is named. -/
theorem cspaceDeleteSlotZombie_confinedToCores
    (executingCore : CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (hStep : cspaceDeleteSlotZombie executingCore addr st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' (cspaceDeleteSlotFinalisingCores st addr) := by
  by_cases h0 : slotRetireTarget st addr.cnode addr.slot = 0
  · rw [cspaceDeleteSlotZombie_of_target_zero h0] at hStep
    exact cspaceDeleteSlotFinalising_confinedToCores executingCore addr st st' hStep
  · unfold cspaceDeleteSlotFinalisingCores
    rw [if_neg h0]
    exact observableSlotsConfinedToCores_allCores st st'

/-- WS-BP BP7.1 (`v0.36.7`), WS-ZA ZA5.4 part 23: **the live `.cspaceRevoke`
arm.**  Each delete of the revocation may destroy a final capability, whose
finalisation wakes the waiters it cancels on their own cores, so the revocation
declares every core. -/
theorem cspaceRevokeCdtFinalising_confinedToCores
    (executingCore : CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (_hStep : cspaceRevokeCdtFinalising executingCore addr st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' Concurrency.allCores :=
  observableSlotsConfinedToCores_allCores st st'

-- ============================================================================
-- §5j.1 The live `.tcbSetSpace` arm
-- ============================================================================
--
-- WS-ZA ZA5.4 part 22: the space change retires what each slot's old capability
-- took with it (`threadSlotSet`), so it takes the executing core for the retire
-- of a root, whose acknowledged ASID round writes the TLB state alone.  It
-- writes no core: the slot copies are the object store and the CDT, and the
-- retire keeps the scheduler and the machine (`retireFinalObject_fields`).

/-- A thread space slot's copy writes no scheduler and no machine state: the
slot delete, the thread's record and the derivation edge. -/
theorem threadSlotCopied_framed {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot) (srcCNode : SeLe4n.ObjId)
    (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    SchedulerMachineFramed st (threadSlotCopied st tid slot srcCNode srcSlot rights) := by
  obtain ⟨hs, hm⟩ := cspaceDeleteSlot_scheduler_machine _ st _ (copyIntoThreadSlot_delete hT slot)
  rcases threadSlotCopied_cases st tid slot srcCNode srcSlot rights with ⟨-, e⟩ | ⟨cap, -, e⟩
  · rw [e]; exact ⟨hs, hm⟩
  · rw [e]
    exact ⟨(SystemState.cdtAddChild_scheduler _ _ _ _).trans
        ((SystemState.updateTcb_scheduler _ _ _).trans hs),
      (SystemState.cdtAddChild_machine _ _ _ _).trans
        ((SystemState.updateTcb_machine _ _ _).trans hm)⟩

/-- A thread space slot's set writes no scheduler and no machine state: the
copy, then the retire. -/
theorem threadSlotSet_framed (ec : CoreId) {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot) (srcCNode : SeLe4n.ObjId)
    (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    SchedulerMachineFramed st (threadSlotSet ec st tid slot srcCNode srcSlot rights) := by
  obtain ⟨hs, hm⟩ := threadSlotCopied_framed hT slot srcCNode srcSlot rights
  obtain ⟨-, hs2, hm2⟩ := retireFinalObject_fields ec (slotRetireTarget st tid.toObjId slot)
    (recorderFor st (slotRetireTarget st tid.toObjId slot) tid.toObjId slot)
    (threadSlotCopied st tid slot srcCNode srcSlot rights)
  exact ⟨hs2.trans hs, hm2.trans hm⟩

/-- WS-ZA ZA5.4 part 22: **the live `.tcbSetSpace` arm writes no core.**  Its
two slot sets each copy into the thread's slot and retire what the old
capability took with it, writing the object store, the CDT and (for a root) the
TLB state, never a scheduler slot or a register bank. -/
theorem copyThreadSpaces_confinedToCores (ec : CoreId) (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (cnSrc vrSrc : CSpaceAddr) (hInv : st.objects.invExt)
    (hStep : copyThreadSpaces ec st vtid cnSrc vrSrc = .ok st') :
    observableSlotsConfinedToCores st st' [] := by
  obtain ⟨tcb, hT, -, -, hCn, -, rfl⟩ := copyThreadSpaces_ok hStep
  obtain ⟨cnCap, -, hCL, -⟩ := cspaceRootSourceAdmitted_spec hCn
  obtain ⟨-, hI1⟩ := threadSlotCopied_tcb hInv hT TCB.cspaceRootSlot cnSrc.cnode cnSrc.slot
    TCB.cspaceRootRights
  obtain ⟨t1', hT1', hF⟩ := threadSlotCopied_slotFilled hInv hT (slot := TCB.cspaceRootSlot)
    (by decide) TCB.cspaceRootRights hCL
  obtain ⟨t1, hT1⟩ := Option.isSome_iff_exists.mp
    (show ((threadSlotSet ec st vtid.val TCB.cspaceRootSlot cnSrc.cnode cnSrc.slot
        TCB.cspaceRootRights).getTcb? vtid.val).isSome by
      unfold threadSlotSet; dsimp only
      rw [retireFinalObject_getTcb?_of_slotCap _ _ _ _ hI1 hT1' hF]; rfl)
  obtain ⟨hs1, hm1⟩ := threadSlotSet_framed ec hT TCB.cspaceRootSlot cnSrc.cnode cnSrc.slot
    TCB.cspaceRootRights
  obtain ⟨hs2, hm2⟩ := threadSlotSet_framed ec hT1 TCB.vspaceRootSlot vrSrc.cnode vrSrc.slot
    TCB.vspaceRootRights
  exact observableSlotsConfinedToCores_nil_of_framed ⟨hs2.trans hs1, hm2.trans hm1⟩

/-- **The cores a space change through the zombie delete may write**: none when
its old CSpace root names nothing holding a capability, so it is the plain
space change; otherwise every core, since the zombie loop's finalisations wake
the waiters they cancel on their own cores, as the zombie delete does. -/
def copyThreadSpacesZombieCores (st : SystemState) (vtid : SeLe4n.ValidThreadId) : List CoreId :=
  if zombieSlotClass st vtid.val.toObjId TCB.cspaceRootSlot vtid.val.toObjId TCB.cspaceRootSlot = 0
  then [] else Concurrency.allCores

/-- WS-ZA ZA5.4 part 26: **the live `.tcbSetSpace` arm, through the zombie
delete, writes only the cores `copyThreadSpacesZombieCores` names**: with a
leaf old CSpace root it is the plain space change, which writes no core
(`copyThreadSpaces_confinedToCores`); otherwise every core is named. -/
theorem copyThreadSpacesZombie_confinedToCores (ec : CoreId) (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (cnSrc vrSrc : CSpaceAddr) (hInv : st.objects.invExt)
    (hStep : copyThreadSpacesZombie ec st vtid cnSrc vrSrc = .ok st') :
    observableSlotsConfinedToCores st st' (copyThreadSpacesZombieCores st vtid) := by
  unfold copyThreadSpacesZombieCores
  split
  · next h0 =>
    have hPlain : copyThreadSpaces ec st vtid cnSrc vrSrc = .ok st' := by
      unfold copyThreadSpacesZombie at hStep
      split at hStep
      · next hA =>
        unfold copyThreadSpacesZombiePerform at hStep
        rw [if_pos h0] at hStep
        rw [copyThreadSpaces_of_admitted hA]; exact hStep
      · exact hStep
    exact copyThreadSpaces_confinedToCores ec st st' vtid cnSrc vrSrc hInv hPlain
  · exact observableSlotsConfinedToCores_allCores st st'

-- ============================================================================
-- §5k The live `.untypedRetype` arm, and the destroy path's cleanup
-- ============================================================================
--
-- WS-ZA ZA5.4 part 14: every kernel object is carved from an untyped, and the
-- carve takes the executing core (a carved thread's domain and affinity are
-- that core's).  It writes no core: the untyped's record, the child, the
-- authority's free index, the new capability and its derivation edge are the
-- object store and the CDT, and the scrub writes memory, never a register
-- bank.
--
-- The cleanup below is the destroy path's: the in-place retype that ran it is
-- retired, and the finalisation a kernel object's final delete will run calls
-- it (`docs/REGISTERED_DEBT.md`).  Destroying a TCB sweeps it out of **every**
-- core's run queue and current slot, bounded by the cores the destroyed thread
-- occupied in the pre-state — available only because review round 17 rewrote
-- the sweep's step to be *guarded* by `threadOccupiesCore`.

/-- WS-ZA ZA5.4 part 14: **the carve writes no core.**  Its three object stores,
the scrub, the capability insertion and the derivation edge keep the scheduler,
and the scrub writes memory alone, so every core's register bank is kept. -/
theorem untypedRetypeObject_confinedToCores (src dst : CSpaceAddr)
    (childId : SeLe4n.ObjId) (req : CarveRequest) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : untypedRetypeObject src childId dst req st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] := by
  obtain ⟨utCap, untypedId, ut, st1, st2, _, _, _, hRt, hIns, rfl⟩ :=
    untypedRetypeObject_ok_decompose src dst childId req st st' hObjInv hStep
  obtain ⟨_, _, _, stUt, _, stCh, _, _, _, _, _, _, _, _, _, _, _, hStUt, hStCh, _, hStIdx⟩ :=
    retypeFromUntyped_ok_stores st st1 src untypedId childId _ _ hObjInv hRt
  have hS1 : st1.scheduler = st.scheduler :=
    (storeObject_scheduler_eq _ _ _ _ hStIdx).trans
      ((storeObject_scheduler_eq _ _ _ _ hStCh).trans (storeObject_scheduler_eq _ _ _ _ hStUt))
  have hM1 : st1.machine = st.machine :=
    (storeObject_machine_eq _ _ _ _ hStIdx).trans
      ((storeObject_machine_eq _ _ _ _ hStCh).trans (storeObject_machine_eq _ _ _ _ hStUt))
  have hS2 : st2.scheduler = st.scheduler := by
    rw [cspaceInsertSlot_preserves_scheduler _ st2 dst _ hIns, CarveRequest.scrub_scheduler, hS1]
  refine observableSlotsConfinedToCores_nil_of_scheduler_regs_eq
    (by rw [SystemState.cdtAddChild_scheduler, hS2]) (fun c => ?_)
  rw [SystemState.cdtAddChild_machine, cspaceInsertSlot_preserves_machine _ st2 dst _ hIns, ← hM1]
  cases req <;> simp only [CarveRequest.scrub, carveZeroFrame] <;> (try split) <;> rfl

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
    (hInv : st.objects.invExt)
    (hOk : lifecyclePreRetypeCleanup st target currentObj newObj = .ok stClean) :
    observableSlotsConfinedToCores st stClean (preRetypeCleanupWriteSetOf st currentObj) := by
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
      have hRO : (tcb.replyObject.isSome || tcb.replyWaitersHeadCode != 0) = false := by
        cases hr : (tcb.replyObject.isSome || tcb.replyWaitersHeadCode != 0) with
        | false => rfl
        | true => rw [if_pos hr] at hOk; exact absurd hOk (by simp)
      rw [if_neg (by simp only [hRO]; exact Bool.false_ne_true)] at hOk
      obtain rfl := Except.ok.inj hOk
      simp only [preRetypeCleanupWriteSetOf]
      -- The arm writes no observable slot; the sweep's write set at the arm's
      -- post-state is the entry state's, because the arm keeps every run queue
      -- and current slot.
      have hOcc : threadOccupiedCores stArm tcb.tid = threadOccupiedCores st tcb.tid :=
        threadOccupiedCores_congr_of_runCores_current tcb.tid
          (cancelDonationArmOnCore_runCoresAgree hInv hArm)
          (fun c => (cancelDonationArmOnCore_runQueue_current_eq st stArm tcb.tid tcb c hArm).2)
      -- WS-ZA ZA6.6: the held context's yield completion (seL4-MCS's
      -- `unbindFromSC`) writes objects alone, and keeps every run-core code.
      let stC := completeHeldYield stArm tcb.scBindingScCode
      have hInvArm := cancelDonationArmOnCore_preserves_objects_invExt st stArm tcb.tid tcb hInv hArm
      have hC : observableSlotsConfinedToCores stArm stC [] :=
        observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
          (SystemState.completeHeldYield_scheduler stArm tcb.scBindingScCode)
          (by show (completeHeldYield _ _).machine = _; rw [SystemState.completeHeldYield_eq_objects])
      have hOccC : threadOccupiedCores stC tcb.tid = threadOccupiedCores stArm tcb.tid :=
        threadOccupiedCores_congr_of_runCores_current tcb.tid
          (SystemState.completeHeldYield_objectsAgreeOffYield stArm _ hInvArm).runCoresAgree
          (fun c => by rw [SystemState.completeHeldYield_scheduler])
      have hTrans := observableSlotsConfinedToCores_trans
        (observableSlotsConfinedToCores_trans
          (cancelDonationArmOnCore_confinedToCores st stArm tcb.tid tcb hArm) hC)
        (cleanupTcbReferences_confinedToCores stC tcb.tid)
      -- The suspend's yield cancel (seL4-MCS's `suspend`) writes objects alone.
      have hTrans' := observableSlotsConfinedToCores_trans hTrans
        (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
          (SystemState.cancelYieldTo_scheduler (cleanupTcbReferences stC tcb.tid) tcb.tid)
          (SystemState.cancelYieldTo_machine (cleanupTcbReferences stC tcb.tid) tcb.tid))
      -- The slot detach writes link words alone: no scheduler, no machine.
      have hTrans'' := observableSlotsConfinedToCores_trans hTrans'
        (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
          (detachTcbSlots_scheduler_eq (cancelYieldTo (cleanupTcbReferences stC tcb.tid) tcb.tid)
            target)
          (detachTcbSlots_machine_eq (cancelYieldTo (cleanupTcbReferences stC tcb.tid) tcb.tid)
            target))
      simp only [List.nil_append, List.append_nil] at hTrans''
      rw [hOccC, hOcc] at hTrans''
      exact hTrans''
  | cnode cn =>
    simp only [lifecyclePreRetypeCleanup, preRetypeCleanupWriteSetOf] at hOk ⊢
    have hDetach : observableSlotsConfinedToCores st (detachCNodeSlots st target cn) [] :=
      observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
        (detachCNodeSlots_scheduler_eq st target cn)
        (detachCNodeSlots_machine_eq st target cn)
    -- The frame-mapping and installed-page-table guard rejects (vacuous on the
    -- `.ok` path); past it the cleanup is the detach, whatever the replacement's
    -- shape.
    split at hOk
    · cases hOk
    · injection hOk with hOk; subst hOk; exact hDetach
  | endpoint _ =>
    simp only [lifecyclePreRetypeCleanup, preRetypeCleanupWriteSetOf] at hOk ⊢
    injection hOk with hOk; subst hOk; exact observableSlotsConfinedToCores_refl _ _
  | reply _ =>
    simp only [lifecyclePreRetypeCleanup, preRetypeCleanupWriteSetOf] at hOk ⊢
    split at hOk
    · cases hOk
    · injection hOk with hOk; subst hOk; exact observableSlotsConfinedToCores_refl _ _
  | frame _ | pageTable _ | untyped _ | vspaceRoot _ =>
    -- WS-BP BP7.1: a frame target is refused — and since slice 4a (`v0.36.8`)
    -- an untyped one, and since `v0.36.35` a VSpace root — so there is no
    -- `.ok` post-state.
    simp [lifecyclePreRetypeCleanup] at hOk
  | notification _ =>
    simp only [lifecyclePreRetypeCleanup, preRetypeCleanupWriteSetOf] at hOk ⊢
    injection hOk with hOk; subst hOk; exact observableSlotsConfinedToCores_refl _ _
  | schedContext _ =>
    -- WS-OD OD5.4: a context heading a reply stack is refused (vacuous on `.ok`).
    -- `v0.35.165`: past that guard the arm RELEASES the binding, which writes no
    -- confined slot -- the replenish queue is not one of the six.
    simp only [lifecyclePreRetypeCleanup, preRetypeCleanupWriteSetOf] at hOk ⊢
    split at hOk
    · cases hOk
    · injection hOk with hOk; subst hOk
      -- WS-ZA ZA6.6: then the yield it records completed, objects alone.
      simpa only [List.append_nil] using observableSlotsConfinedToCores_trans
        (releaseSchedContextBinding_confinedToCores _ _ _)
        (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
          (SystemState.completeYieldFrom_scheduler _ _)
          (by rw [SystemState.completeYieldFrom_eq_objects]))

end SeLe4n.Kernel
