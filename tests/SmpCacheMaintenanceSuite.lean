-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.CacheModel
import SeLe4n.Kernel.Architecture.PerCoreCacheModel
import SeLe4n.Kernel.Lifecycle.Operations.RetypeWrappers
import SeLe4n.Kernel.SyscallDispatchEntry
import SeLe4n.Kernel.API
import SeLe4n.Platform.FFI
import SeLe4n.Model.State
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM7.D — Cache maintenance broadcast suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase
SM7.D deliverables (`docs/planning/SMP_TLB_SHOOTDOWN_PLAN.md` §5,
sub-tasks SM7.D.1–SM7.D.4):

* **SM7.D.1** — the instruction-cache broadcast.  `IC IALLU` reaches only
  the executing PE (the SMP hazard); `IC IALLUIS` / `IC IVAU` reach every
  core of the shareability domain.
* **SM7.D.2** — data-cache maintenance by VA to the Point of Coherency is
  system-wide, with no target set to get wrong; and the *clean-to-PoU*
  obligation kernel code-write sites carry, which the re-type discharges
  by emission (§3.13) and boot still owes (SM10.E).
* **SM7.D.3** — the DMA scope boundary, machine-checked as a tripwire.
* **SM7.D.4** — `icacheCoherent_perCore`, the 14th
  `proofLayerInvariantBundle` conjunct, and its live-path preservation.

Structure:

* **§1 Surface anchors** — every public SM7.D symbol resolves at
  elaboration time (a rename or removal fails the build).
* **§2 Elaboration-time witnesses** — decidable examples and theorem
  applications for the headline SM7.D facts.
* **§3 Runtime assertions** — `lake exe smp_cache_maintenance_suite`
  computes the actual per-core cache evolutions on concrete scenarios,
  including real page-table-backed states driven through the **live**
  `.vspaceUnmap` and `.lifecycleRetype` dispatch arms.
-/

namespace SeLe4n.Testing.SmpCacheMaintenance

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  Surface anchors (Tier-3)
-- ============================================================================

-- SM7.D.1 granularity contract (page operand vs line-granular instruction):
#check @pageBytes
#check @cacheLineBytes
#check @icacheLinesPerPage
#check @icacheLinesPerPage_covers_page
#check @icacheLinesPerPage_eq

-- SM7.D.1 the emission ledger (exact runtime operand recovery):
#check @ICacheInvalidation.covers
#check @ICacheInvalidation.covers_refl
#check @ICacheInvalidation.covers_trans
#check @ICacheInvalidation.iallu_covers_ivauPage
#check @ICacheInvalidation.iallu_not_covers_unifyPage
#check @ICacheInvalidation.ivauPage_not_covers_of_ne
#check @byteRangeContains
#check @byteRangeContains_iff
#check @byteRangeContains_refl
#check @byteRangeContains_trans
#check @ICacheInvalidation.isDomainWide
#check @ICacheInvalidation.cleanRangeIallu_covers_iallu
#check @ICacheInvalidation.cleanRangeIallu_covers_ivauPage
#check @ICacheInvalidation.cleanRangeIallu_covers_unifyPage
#check @ICacheInvalidation.iallu_not_covers_cleanRangeIallu
#check @ICacheInvalidation.unifyPage_not_covers_cleanRangeIallu
#check @recordIcacheMaintenanceList
#check @recordIcacheMaintenanceList_nil
#check @recordIcacheMaintenanceList_ne_nil
#check @recordIcacheMaintenanceList_covered
#check @recordIcacheMaintenanceList_mem_of_mem
#check @recordIcacheMaintenanceList_length_le
#check @icacheLineMatches_of_covers
#check @applyICacheInvalidation_subset_of_covers
#check @SeLe4n.Model.SystemState.pendingIcacheMaintenance
#check @SeLe4n.Model.default_pendingIcacheMaintenance
#check @SeLe4n.Model.storeObject_pendingIcacheMaintenance_eq
#check @recordIcacheMaintenance
#check @recordIcacheMaintenance_ne_nil
#check @recordIcacheMaintenance_covered
#check @recordIcacheMaintenance_of_nil
#check @clearIcacheMaintenance
#check @clearIcacheMaintenance_pending
#check @clearIcacheMaintenance_frame
#check @clearIcacheMaintenance_preserves_icacheCoherent_perCore
#check @clearIcacheMaintenance_preserves_tlbInvalidationConsistent_perCore
#check @SeLe4n.Model.freeze_preserves_pendingIcacheMaintenance
#check @SeLe4n.Kernel.OffSchedulerAgrees.pendingIcacheMaintenance
#check @SeLe4n.Platform.Boot.bootFromPlatform_pendingIcacheMaintenance_eq
#check @SeLe4n.Kernel.pendingIcacheMaintenance_write_preserves_projection

-- SM7.D the user-facing code-publication path (`.vspaceUnifyInstruction`):
#check @unifyTargetPaddr
#check @unifyTargetPaddr_of_mapped
#check @vspaceUnifyInstructionPage
#check @vspaceUnifyInstructionPage_asid_unbound
#check @vspaceUnifyInstructionPage_unmapped
#check @vspaceUnifyInstructionPage_ok
#check @vspaceUnifyInstructionPage_frame
#check @vspaceUnifyInstructionPage_records_unify
#check @vspaceUnifyInstructionPage_invalidates_all_cores
#check @vspaceUnifyInstructionPage_preserves_icacheCoherent_perCore
#check @vspaceUnifyInstructionPage_preserves_tlbInvalidationConsistent_perCore
#check @ICacheInvalidation.unifyPage_opTag
#check @ICacheInvalidation.unifyPage_toPaddr
#check @ICacheInvalidation.unifyPage_covers_ivauPage
#check @icacheLineMatches_unifyPage
#check @SeLe4n.Kernel.dispatchWithCap_vspaceUnifyInstruction_delegates
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeVSpaceUnifyInstructionArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeVSpaceUnifyInstructionArgs_eq
#check @SeLe4n.Kernel.Concurrency.lockSet_vspaceUnifyInstruction
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_vspaceUnifyInstruction

-- SM7.D.2 the data-side dual: the clean-to-PoU obligation + its tripwire:
#check @KernelCodeWriteSite
#check @kernelCodeWriteSites
#check @kernelCodeWriteSites_complete
#check @kernelCodeWriteOwesPoUClean
#check @kernelCodeWriteSites_owe_pou_clean
#check @dischargesPoUClean
#check @dischargesPoUClean_isDomainWide
#check @kernelCodeWriteEmitted
#check @kernelCodeWriteSites_emission_pending

-- SM7.D.1 typed operand + FFI encoding:
#check @ICacheInvalidation
#check @ICacheInvalidation.toOpTag
#check @ICacheInvalidation.toPaddr
#check @ICacheInvalidation.toOpTag_in_range
#check @ICacheInvalidation.toOpTag_distinct_constructors
#check @ICacheInvalidation.iallu_opTag
#check @ICacheInvalidation.ivauPage_opTag
#check @ICacheInvalidation.iallu_zero_operand
#check @ICacheInvalidation.ivauPage_toPaddr
#check @ICacheInvalidation.toSize
#check @ICacheInvalidation.toSize_zero_of_not_range
#check @ICacheInvalidation.cleanRangeIallu_opTag
#check @ICacheInvalidation.cleanRangeIallu_operands

-- SM7.D.1 line/state model (mounted in SystemState):
#check @ICacheLine
#check @ICacheLine.toTranslation
#check @ICacheState
#check @ICacheState.empty
#check @SystemState.perCoreICache
#check @default_perCoreICache

-- SM7.D.1 invalidation effect algebra:
#check @icacheLineMatches
#check @applyICacheInvalidation
#check @mem_applyICacheInvalidation_iff
#check @applyICacheInvalidation_removes
#check @applyICacheInvalidation_preserves_other
#check @mem_of_mem_applyICacheInvalidation
#check @applyICacheInvalidation_idempotent
#check @applyICacheInvalidation_iallu
#check @applyICacheInvalidation_domainWide
#check @icacheLineMatches_domainWide
#check @icacheLineMatches_ivauPage
#check @icacheLineMatches_iallu
#check @applyICacheInvalidation_survivor_paddr_ne

-- SM7.D.1 per-core accessors (SM4.B path-a discipline):
#check @icacheOnCore
#check @setIcacheOnCore
#check @setIcacheOnCore_icacheOnCore_self
#check @setIcacheOnCore_icacheOnCore_ne
#check @default_icacheOnCore

-- SM7.D.1 model operations:
#check @icFetchOnCore
#check @icFetchOnCore_mem
#check @icFetchOnCore_icacheOnCore_ne
#check @icFetchOnCore_frame
#check @icInvalidateOnCore
#check @icInvalidateOnCore_removes
#check @icInvalidateOnCore_icacheOnCore_ne
#check @icInvalidateOnCore_subset
#check @icInvalidateOnCore_frame

-- SM7.D.1 the broadcast + its reach:
#check @setIcacheViewOnCore
#check @icBroadcastViews
#check @icBroadcastViews_get
#check @icInvalidateBroadcast
#check @icInvalidateBroadcast_icacheOnCore
#check @icInvalidateBroadcast_subset
#check @icInvalidateBroadcast_frame
#check @icBroadcastReach
#check @icBroadcastReach_cover
#check @icBroadcastReach_nodup
#check @icInvalidateBroadcast_reaches_all_cores
#check @icInvalidateBroadcast_platform_reaches_all_cores
#check @icInvalidateBroadcast_iallu_empties

-- SM7.D.2 data-cache maintenance at the Point of Coherency:
#check @DCacheMaintenance
#check @applyDCacheMaintenance
#check @DCacheViews
#check @dcMaintenanceAllCores
#check @dcMaintenanceAllCores_get
#check @dcMaintenanceByVA_reaches_all_cores
#check @dcacheCoherentAcrossCores
#check @dcacheCoherentAcrossCores_cold
#check @dcMaintenanceAllCores_preserves_dcacheCoherentAcrossCores
#check @icInvalidateOnCore_vs_dcMaintenance_reach
#check @icInvalidateOnCore_remote_line_survives

-- SM7.D.3 the DMA scope tripwire:
#check @CoherentAgent
#check @modeledCoherentAgents
#check @mem_modeledCoherentAgents
#check @modeledCoherentAgents_no_dma_master
#check @dcMaintenance_covers_all_modeled_agents

-- SM7.D.4 the invariant + its decidable checker:
#check @icacheLineConsistent
#check @icacheCoherent_perCore
#check @icacheLineConsistent_of_frame
#check @default_icacheCoherent_perCore
#check @icacheCoherent_perCore_bootCore
#check @icInvalidateOnCore_preserves_icacheCoherent_perCore
#check @icInvalidateBroadcast_preserves_icacheCoherent_perCore
#check @icFetchOnCore_preserves_icacheCoherent_perCore
#check @icFetchOnCore_line_was_authorised
#check @icacheLineConsistentCheck
#check @icacheLineConsistentCheck_iff
#check @icacheCoherentCheck_perCore
#check @icacheCoherentCheck_perCore_iff
#check @cacheCoherency_cross_subsystem
#check @icInvalidateBroadcast_preserves_tlbInvalidationConsistent_perCore
#check @icInvalidateBroadcast_preserves_perCore_memory_invariants

-- SM7.D.1 live wiring (the `.vspaceUnmap` seam):
#check @withIcacheBroadcast
#check @withIcacheBroadcast_error_iff
#check @withIcacheBroadcast_none_inert
#check @withIcacheBroadcast_some_ok
#check @withIcacheBroadcast_frame
#check @unmapExecutablePaddr
#check @unmapIcacheOperand
#check @unmapExecutablePaddr_of_executable
#check @unmapExecutablePaddr_eq_some
#check @unmapIcacheOperand_eq_some_iff
#check @unmapIcacheOperand_eq_none_iff
#check @vspaceUnmapPageWithShootdownAndIcacheBroadcast
#check @vspaceUnmapPageWithShootdownAndIcacheBroadcast_error_iff
#check @vspaceUnmapPageWithShootdownAndIcacheBroadcast_non_executable_inert
#check @vspaceUnmapPageWithShootdownPerCore_perCoreICache_eq
#check @unmapSurvivor_not_target
#check @vspaceUnmapPageWithShootdownAndIcacheBroadcast_preserves_icacheCoherent_perCore
#check @vspaceUnmapPageWithShootdownAndIcacheBroadcast_preserves_tlbInvalidationConsistent_perCore
#check @vspaceUnmapPageWithShootdownAndIcacheBroadcast_preserves_perCore_memory_invariants

-- SM7.D.1 live wiring (the `.lifecycleRetype` seam, both authority forms):
#check @SeLe4n.Model.SystemState.getObjectType?
#check @SeLe4n.Model.SystemState.getObjectType?_eq_some_of_getElem
#check @SeLe4n.Model.SystemState.getObjectType?_eq_none_of_getElem
#check @SeLe4n.Kernel.retypeIcacheOp
#check @SeLe4n.Kernel.retypeIcacheOperand
#check @SeLe4n.Kernel.retypeIcacheOperand_eq
#check @SeLe4n.Kernel.retypeIcacheOp_isDomainWide
#check @SeLe4n.Kernel.retypeIcacheOp_cleans_scrub_extent
#check @SeLe4n.Kernel.retypeIcacheOp_discharges_scrub_obligation
#check @SeLe4n.Kernel.lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache
#check @SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdownPerCoreIcache
#check @SeLe4n.Kernel.lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_error_iff
#check @SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdownPerCoreIcache_error_iff
#check @SeLe4n.Kernel.lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_ok
#check @SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdownPerCoreIcache_ok
#check @SeLe4n.Kernel.lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_preserves_icacheCoherent_perCore
#check @SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdownPerCoreIcache_preserves_icacheCoherent_perCore
#check @SeLe4n.Kernel.lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_preserves_perCore_memory_invariants

-- SM7.D carriage: freeze, congruence, boot, information flow, FFI seam:
#check @SeLe4n.Model.FrozenSystemState.perCoreICache
#check @SeLe4n.Model.freeze_preserves_perCoreICache
#check @SeLe4n.Model.storeObject_perCoreICache_eq
#check @SeLe4n.Kernel.OffSchedulerAgrees.perCoreICache
#check @SeLe4n.Platform.Boot.bootFromPlatform_perCoreICache_eq
#check @SeLe4n.Kernel.perCoreICache_write_preserves_projection
#check @SeLe4n.Platform.FFI.ffiIcIalluIs
#check @SeLe4n.Platform.FFI.ffiIcMaintenance
#check @SeLe4n.Platform.FFI.icMaintenanceBroadcast
#check @SeLe4n.Platform.FFI.icMaintenanceBroadcast_iallu_encoding
#check @SeLe4n.Platform.FFI.icMaintenanceBroadcast_ivauPage_encoding
#check @SeLe4n.Platform.FFI.icMaintenanceBroadcast_cleanRangeIallu_encoding
#check @SeLe4n.Kernel.completeIcacheMaintenance
#check @SeLe4n.Kernel.completeIcacheMaintenance_nil
#check @SeLe4n.Kernel.completeIcacheMaintenance_singleton
#check @SeLe4n.Kernel.completeIcacheMaintenance_cons

-- The 14th `proofLayerInvariantBundle` conjunct is live (the bundle's
-- boot witness elaborates only if the conjunct is present and provable).
#check @SeLe4n.Kernel.Architecture.default_system_state_proofLayerInvariantBundle
#check @SeLe4n.Kernel.Architecture.vspaceUnmapPage_perCoreICache_eq

-- ============================================================================
-- §2  Elaboration-time witnesses
-- ============================================================================

-- SM7.D.1: the FFI op-tag encoding is decidable and matches the Rust
-- `cache::decode_icache_invalidation` discriminants (0 = Iallu, 1 = Ivau).
example : ICacheInvalidation.iallu.toOpTag = 0 := by decide
example : (ICacheInvalidation.ivauPage (SeLe4n.PAddr.ofNat 0x3000)).toOpTag = 1 := by decide
example : ICacheInvalidation.iallu.toPaddr = 0 := by decide

-- SM7.D.1: `iallu` covers everything, `ivau p` covers exactly the lines
-- tagged `p` (PIPT identity).
example (l : ICacheLine) : icacheLineMatches .iallu l = true := rfl

-- SM7.D.1: the boot state's caches are cold, so the SM7.D.4 invariant holds.
example : icacheCoherent_perCore (default : SystemState) :=
  default_icacheCoherent_perCore

-- SM7.D.1: the broadcast reaches every core on this platform (BCM2712: all
-- four PEs share one Inner Shareable domain).
example (st : SystemState) (op : ICacheInvalidation) (c : CoreId) (l : ICacheLine)
    (h : icacheLineMatches op l = true) :
    l ∉ (icacheOnCore (icInvalidateBroadcast st icBroadcastReach op) c).lines :=
  icInvalidateBroadcast_platform_reaches_all_cores st op c h

-- SM7.D.2: a `DC CIVAC` by VA to PoC leaves no core holding the line — no
-- reach parameter, no protocol.
example (views : DCacheViews) (p : SeLe4n.PAddr) (c : CoreId) :
    ((dcMaintenanceAllCores views (.cleanInvalidateByVA p)).get c).dcache p = .invalid :=
  (dcMaintenanceByVA_reaches_all_cores views p).2 c

-- SM7.D.3: the model contains no non-coherent bus master (the tripwire).
example : ∀ a ∈ modeledCoherentAgents, ∃ c : CoreId, a = .core c :=
  modeledCoherentAgents_no_dma_master

-- SM7.D.4: the memory-subsystem capstone applies.
example (st : SystemState) (op : ICacheInvalidation)
    (h : icacheCoherent_perCore st) :
    (∀ (c : CoreId) {l : ICacheLine}, icacheLineMatches op l = true →
        l ∉ (icacheOnCore (icInvalidateBroadcast st icBroadcastReach op) c).lines) ∧
    icacheCoherent_perCore (icInvalidateBroadcast st icBroadcastReach op) :=
  cacheCoherency_cross_subsystem st icBroadcastReach_cover op h

-- ============================================================================
-- §3  Runtime assertions
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

-- Concrete cores of the 4-core RPi5 topology.
private def core0 : CoreId := ⟨0, by decide⟩
private def core1 : CoreId := ⟨1, by decide⟩
private def core2 : CoreId := ⟨2, by decide⟩
private def core3 : CoreId := ⟨3, by decide⟩

private def asid5 : SeLe4n.ASID := ⟨5⟩
private def vaddrPage : SeLe4n.VAddr := SeLe4n.VAddr.ofNat 0x1000
private def vaddrOther : SeLe4n.VAddr := SeLe4n.VAddr.ofNat 0x9000
private def paddrPage : SeLe4n.PAddr := SeLe4n.PAddr.ofNat 0x2000
private def paddrOther : SeLe4n.PAddr := SeLe4n.PAddr.ofNat 0x8000

/-- Read + execute (W^X compliant: no write). -/
private def permsExec : PagePermissions :=
  { read := true, write := false, execute := true, user := true, cacheable := true }

/-- A cached instruction line for the scenario's executable mapping. -/
private def lineExec : ICacheLine :=
  { asid := asid5, vaddr := vaddrPage, paddr := paddrPage, perms := permsExec }

/-- A cached line for a *different* physical page (the selectivity witness). -/
private def lineOther : ICacheLine :=
  { asid := asid5, vaddr := vaddrOther, paddr := paddrOther, perms := permsExec }

-- ----------------------------------------------------------------------------
-- §3.1  SM7.D.1 — operand encoding + the invalidation effect algebra
-- ----------------------------------------------------------------------------

private def runOperandChecks : IO Unit := do
  IO.println "-- §3.1 SM7.D.1 operand encoding + effect algebra"
  assertBool "iallu encodes to op tag 0 with a zero operand"
    (ICacheInvalidation.iallu.toOpTag == 0 && ICacheInvalidation.iallu.toPaddr == 0)
  assertBool "ivau encodes to op tag 1 carrying its physical address"
    ((ICacheInvalidation.ivauPage paddrPage).toOpTag == 1 &&
     (ICacheInvalidation.ivauPage paddrPage).toPaddr == UInt64.ofNat paddrPage.toNat)
  assertBool "the two op tags are distinct (Rust match arms cannot overlap)"
    (ICacheInvalidation.iallu.toOpTag != (ICacheInvalidation.ivauPage paddrPage).toOpTag)
  assertBool "every op tag is in [0, 2) (the Rust decoder's range)"
    ([ICacheInvalidation.iallu, .ivauPage paddrPage].all fun op => op.toOpTag.toNat < 2)
  -- Effect algebra on a two-line cache.
  let ic : ICacheState := { lines := [lineExec, lineOther] }
  assertBool "iallu empties the view"
    ((applyICacheInvalidation ic .iallu).lines.isEmpty)
  assertBool "ivau removes exactly the lines tagged with its address"
    (!((applyICacheInvalidation ic (.ivauPage paddrPage)).lines.contains lineExec))
  assertBool "ivau leaves other physical pages cached (selectivity)"
    ((applyICacheInvalidation ic (.ivauPage paddrPage)).lines.contains lineOther)
  assertBool "invalidation is idempotent"
    (applyICacheInvalidation (applyICacheInvalidation ic (.ivauPage paddrPage))
      (.ivauPage paddrPage) == applyICacheInvalidation ic (.ivauPage paddrPage))
  assertBool "invalidation never adds lines"
    ((applyICacheInvalidation ic (.ivauPage paddrPage)).lines.all fun l => ic.lines.contains l)

-- ----------------------------------------------------------------------------
-- §3.2  SM7.D.1 — per-core accessors + the cold boot cache
-- ----------------------------------------------------------------------------

private def runAccessorChecks : IO Unit := do
  IO.println "-- §3.2 SM7.D.1 per-core accessors + cold boot cache"
  let st0 : SystemState := default
  assertBool "every core boots with a cold instruction cache"
    (allCores.all fun c => (icacheOnCore st0 c).lines.isEmpty)
  let stW := setIcacheOnCore st0 core2 { lines := [lineExec] }
  assertBool "reading the slot just written returns the written view"
    ((icacheOnCore stW core2).lines == [lineExec])
  assertBool "writing one core's slot frames every other core's view"
    ([core0, core1, core3].all fun c => (icacheOnCore stW c).lines.isEmpty)
  assertBool "the boot state satisfies the 14th bundle conjunct (checker)"
    (icacheCoherentCheck_perCore st0)

-- ----------------------------------------------------------------------------
-- §3.3  SM7.D.1 — the SMP hazard: IC IALLU is PE-local, IC IALLUIS is not
-- ----------------------------------------------------------------------------

private def runBroadcastReachChecks : IO Unit := do
  IO.println "-- §3.3 SM7.D.1 broadcast reach vs the PE-local hazard"
  -- Every core holds the same line — the state a real SMP kernel reaches when
  -- several PEs have executed the same page.
  let stAll : SystemState :=
    allCores.foldl (fun st c => icFetchOnCore st c lineExec) (default : SystemState)
  assertBool "the scenario caches the line on all four cores"
    (allCores.all fun c => (icacheOnCore stAll c).lines.contains lineExec)
  -- (a) PE-local `IC IALLU` on core0: only core0 is cleaned.
  let stLocal := icInvalidateOnCore stAll core0 .iallu
  assertBool "IC IALLU cleans the executing PE"
    ((icacheOnCore stLocal core0).lines.isEmpty)
  assertBool "IC IALLU leaves EVERY other core stale (the SMP hazard)"
    ([core1, core2, core3].all fun c => (icacheOnCore stLocal c).lines.contains lineExec)
  -- (b) domain broadcast: no core retains the line (SM7.D.1 headline).
  let stBcast := icInvalidateBroadcast stAll icBroadcastReach .iallu
  assertBool "IC IALLUIS reaches every core (icInvalidateBroadcast_reaches_all_cores)"
    (allCores.all fun c => (icacheOnCore stBcast c).lines.isEmpty)
  -- (c) the targeted broadcast is selective across cores AND addresses.
  let stMixed := icFetchOnCore stAll core1 lineOther
  let stIvau := icInvalidateBroadcast stMixed icBroadcastReach (.ivauPage paddrPage)
  assertBool "IC IVAU drops the addressed line on every core"
    (allCores.all fun c => !((icacheOnCore stIvau c).lines.contains lineExec))
  assertBool "IC IVAU keeps other physical pages cached (targeted, not a full flush)"
    ((icacheOnCore stIvau core1).lines.contains lineOther)
  assertBool "the broadcast reach covers all four cores on BCM2712"
    (allCores.all fun c => icBroadcastReach.contains c)
  assertBool "the broadcast reach is duplicate-free"
    (icBroadcastReach.length == numCores)

-- ----------------------------------------------------------------------------
-- §3.4  SM7.D.2 — D-cache by VA at PoC is system-wide (no reach parameter)
-- ----------------------------------------------------------------------------

/-- A per-core D-cache view set in which core `dirtyOn` holds one dirty line. -/
private def dcViews (dirtyOn : CoreId) (addr : SeLe4n.PAddr) : DCacheViews :=
  (_root_.Vector.replicate numCores CacheState.empty).set dirtyOn.val
    (dcZeroByVA CacheState.empty addr) dirtyOn.isLt

private def runDCachePoCChecks : IO Unit := do
  IO.println "-- §3.4 SM7.D.2 D-cache by VA at PoC is system-wide"
  let views := dcViews core3 paddrPage
  assertBool "the scenario leaves a dirty line on core3 only"
    ((views.get core3).dcache paddrPage == .dirty &&
     [core0, core1, core2].all fun c => (views.get c).dcache paddrPage == .invalid)
  -- A DC CIVAC issued *anywhere* takes effect on every core's view: the model
  -- has no target-set parameter at all, which is the SM7.D.2 statement.
  let cleaned := dcMaintenanceAllCores views (.cleanInvalidateByVA paddrPage)
  assertBool "DC CIVAC at PoC leaves NO core holding the line"
    (allCores.all fun c => (cleaned.get c).dcache paddrPage == .invalid)
  assertBool "DC IVAC at PoC likewise reaches every core"
    (allCores.all fun c =>
      ((dcMaintenanceAllCores views (.invalidateByVA paddrPage)).get c).dcache paddrPage
        == .invalid)
  assertBool "DC CVAC downgrades the dirty line to clean on every core"
    (allCores.all fun c =>
      ((dcMaintenanceAllCores views (.cleanByVA paddrPage)).get c).dcache paddrPage
        != .dirty)
  assertBool "maintenance frames other addresses"
    ((cleaned.get core3).dcache paddrOther == .invalid)
  -- The asymmetry, computed: the I-cache local op frames remote cores while
  -- the D-cache op does not.
  let stAll : SystemState :=
    allCores.foldl (fun st c => icFetchOnCore st c lineExec) (default : SystemState)
  assertBool "asymmetry: I-cache local op frames remote cores, D-cache op does not"
    ((icacheOnCore (icInvalidateOnCore stAll core0 .iallu) core1).lines.contains lineExec &&
     (cleaned.get core0).dcache paddrPage == .invalid)

-- ----------------------------------------------------------------------------
-- §3.5  SM7.D.3 — the DMA scope boundary (tripwire)
-- ----------------------------------------------------------------------------

private def runDmaScopeChecks : IO Unit := do
  IO.println "-- §3.5 SM7.D.3 DMA scope boundary (tripwire)"
  assertBool "the modelled coherent agents are exactly the platform's PEs"
    (modeledCoherentAgents.length == numCores)
  assertBool "every core is a modelled coherent agent"
    (allCores.all fun c => modeledCoherentAgents.contains (.core c))
  assertBool "no modelled agent is a non-coherent bus master (no DMA in v1.0.0)"
    (modeledCoherentAgents.all fun a => match a with | .core _ => true)

-- ----------------------------------------------------------------------------
-- §3.6  SM7.D.4 — the invariant on a real page-table-backed state
-- ----------------------------------------------------------------------------

private def udVsp : SeLe4n.ObjId := ⟨700⟩
private def udCn : SeLe4n.ObjId := ⟨701⟩
private def udCaller : SeLe4n.ThreadId := ⟨702⟩

private def cacheState (slots : List (SeLe4n.Slot × Capability)) : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject udVsp (.vspaceRoot { asid := asid5, mappings := {} })
    |>.withObject udCn (.cnode
        { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
          slots := SeLe4n.UniqueSlotMap.ofListWF slots })
    |>.withObject udCaller.toObjId (.tcb
        { tid := udCaller, priority := ⟨40⟩, domain := ⟨0⟩,
          cspaceRoot := udCn, vspaceRoot := udVsp,
          ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := .ready })
    |>.withRunnable [udCaller]
    |>.build)

private def runInvariantChecks : IO Unit := do
  IO.println "-- §3.6 SM7.D.4 per-core coherency on a page-table-backed state"
  match vspaceMapPageWithFlush asid5 vaddrPage paddrPage permsExec (cacheState []) with
  | .error _ => assertBool "the scenario maps the executable page" false
  | .ok ((), stMapped) => do
    -- A fetch through the live executable mapping caches a *coherent* line.
    let stFetched := icFetchOnCore stMapped core0 lineExec
    assertBool "a fetch through a live executable mapping caches a line"
      ((icacheOnCore stFetched core0).lines.contains lineExec)
    assertBool "the cached line is coherent (checker green)"
      (icacheCoherentCheck_perCore stFetched)
    assertBool "the fetch is local — other cores stay cold"
      ([core1, core2, core3].all fun c => (icacheOnCore stFetched c).lines.isEmpty)
    -- Unmapping the page WITHOUT maintenance makes the line genuinely stale:
    -- the invariant must reject it.  This is the non-vacuity witness — the
    -- checker distinguishes a real hazard from a satisfied state.
    match vspaceUnmapPageWithFlush asid5 vaddrPage stFetched with
    | .error _ => assertBool "the scenario unmaps the page" false
    | .ok ((), stStale) => do
      assertBool "a cached line whose mapping was removed FAILS the coherency check"
        (!(icacheCoherentCheck_perCore stStale))
      -- The maintenance restores it — on every core, not just the initiator.
      let stClean := icInvalidateBroadcast stStale icBroadcastReach (.ivauPage paddrPage)
      assertBool "the domain broadcast restores coherency"
        (icacheCoherentCheck_perCore stClean)
      -- A PE-LOCAL invalidate on a *different* core does NOT restore it —
      -- the precise reason the kernel must use the broadcast variant.
      assertBool "a PE-local invalidate on another core does NOT restore coherency"
        (!(icacheCoherentCheck_perCore (icInvalidateOnCore stStale core1 .iallu)))
    -- A line whose mapping loses execute permission is likewise inadmissible:
    -- an instruction fetch can only have happened through an executable one.
    let lineNonExec : ICacheLine :=
      { asid := asid5, vaddr := vaddrPage, paddr := paddrPage, perms := .readOnly }
    assertBool "a non-executable cached line is inadmissible (fetch authorisation)"
      (!(icacheLineConsistentCheck stMapped lineNonExec))

-- ----------------------------------------------------------------------------
-- §3.7  SM7.D.1 live wiring — the `.vspaceUnmap` production seam
-- ----------------------------------------------------------------------------

private def runLiveUnmapChecks : IO Unit := do
  IO.println "-- §3.7 SM7.D.1 live `.vspaceUnmap` instruction-cache seam"
  match vspaceMapPageWithFlush asid5 vaddrPage paddrPage permsExec (cacheState []) with
  | .error _ => assertBool "the scenario maps the executable page" false
  | .ok ((), stMapped) => do
    -- Every core has fetched the page (the SMP steady state).
    let stAll : SystemState :=
      allCores.foldl (fun st c => icFetchOnCore st c lineExec) stMapped
    assertBool "the pre-state caches the line on all four cores"
      (allCores.all fun c => (icacheOnCore stAll c).lines.contains lineExec)
    assertBool "the pre-state is coherent (every line has its live mapping)"
      (icacheCoherentCheck_perCore stAll)
    -- The unmap owes a targeted `IC IVAU` at the page's physical address.
    assertBool "the seam recovers the executable page's physical address"
      (unmapExecutablePaddr stAll asid5 vaddrPage == some paddrPage)
    assertBool "the recovered operand is the targeted IC IVAU"
      (unmapIcacheOperand stAll asid5 vaddrPage == some (.ivauPage paddrPage))
    -- Run the production seam from core0.
    match vspaceUnmapPageWithShootdownAndIcacheBroadcast core0 asid5 vaddrPage stAll with
    | .error _ => assertBool "the live unmap seam commits" false
    | .ok ((), stPost) => do
      assertBool "after the live unmap NO core retains the line (all four cleaned)"
        (allCores.all fun c => !((icacheOnCore stPost c).lines.contains lineExec))
      assertBool "the post-state satisfies the 14th conjunct (icacheCoherent_perCore)"
        (icacheCoherentCheck_perCore stPost)
      assertBool "the post-state also satisfies the 13th conjunct (per-core TLB)"
        (tlbInvalidationConsistentCheck_perCore stPost)
      assertBool "the unmap still posts its cross-core TLB shootdown round"
        (!(shootdownQuiescent stPost.tlbShootdown))
    -- A NON-executable mapping owes nothing: the seam is provably inert.
    match vspaceMapPageWithFlush asid5 vaddrOther paddrOther .readOnly stMapped with
    | .error _ => assertBool "the scenario maps a read-only page" false
    | .ok ((), stRO) => do
      assertBool "a read-only mapping owes no instruction-cache maintenance"
        (unmapExecutablePaddr stRO asid5 vaddrOther == none)
      -- Inertness, observed on the state: the read-only unmap leaves every
      -- core's instruction cache exactly as it found it (the `none` branch
      -- commits the base wrapper's result unchanged — `…_non_executable_inert`).
      let stROAll : SystemState :=
        allCores.foldl (fun st c => icFetchOnCore st c lineExec) stRO
      match vspaceUnmapPageWithShootdownAndIcacheBroadcast core0 asid5 vaddrOther
          stROAll with
      | .error _ => assertBool "the read-only unmap commits" false
      | .ok ((), stROPost) =>
        assertBool "a non-executable unmap performs NO instruction-cache maintenance"
          (allCores.all fun c => (icacheOnCore stROPost c).lines.contains lineExec)

-- ----------------------------------------------------------------------------
-- §3.8  SM7.D.1 live wiring — the `.lifecycleRetype` production seam
-- ----------------------------------------------------------------------------

private def runLiveRetypeChecks : IO Unit := do
  IO.println "-- §3.8 SM7.D.1 live `.lifecycleRetype` instruction-cache seam"
  match vspaceMapPageWithFlush asid5 vaddrPage paddrPage permsExec (cacheState []) with
  | .error _ => assertBool "the scenario maps the executable page" false
  | .ok ((), stMapped) => do
    let stAll : SystemState :=
      allCores.foldl (fun st c => icFetchOnCore st c lineExec) stMapped
    let authCap : Capability :=
      { target := .object udVsp,
        rights := AccessRightSet.ofList [.read, .write, .grant, .retype] }
    match SeLe4n.Kernel.lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache
        core0 authCap udVsp
        (.untyped { regionBase := SeLe4n.PAddr.ofNat 0, regionSize := 4096 })
        stAll with
    | .error _ => assertBool "the live retype seam commits" false
    | .ok ((), stPost) => do
      -- The retype re-purposes the target's backing memory: every core's
      -- instruction cache is dropped (IC IALLUIS), so the post-state is
      -- unconditionally coherent — no page-table side conditions needed.
      assertBool "after the live retype EVERY core's instruction cache is cold"
        (allCores.all fun c => (icacheOnCore stPost c).lines.isEmpty)
      assertBool "the post-state satisfies the 14th conjunct unconditionally"
        (icacheCoherentCheck_perCore stPost)
      assertBool "the retype still posts its `.aside1` cross-core TLB round"
        (!(shootdownQuiescent stPost.tlbShootdown))

-- ----------------------------------------------------------------------------
-- §3.9  SM7.D — runtime seam + FFI encoding conformance
-- ----------------------------------------------------------------------------

private def runSeamConformanceChecks : IO Unit := do
  IO.println "-- §3.9 SM7.D runtime seam + FFI encoding conformance"
  -- (The dispatch-entry bracket's inertness for a commit that posted no
  -- round is the definitional `completeIcacheMaintenance_nil`, anchored in
  -- §1; `BaseIO` actions are not comparable at runtime.)
  -- The FFI encoding the typed wrapper emits, pinned against the Rust
  -- `cache::decode_icache_invalidation` discriminants.
  assertBool "the FFI wrapper emits (0, 0) for the domain-wide invalidate"
    ((ICacheInvalidation.iallu).toOpTag == 0 && (ICacheInvalidation.iallu).toPaddr == 0)
  assertBool "the FFI wrapper emits (1, page base) for the targeted invalidate"
    ((ICacheInvalidation.ivauPage paddrPage).toOpTag == 1 &&
     (ICacheInvalidation.ivauPage paddrPage).toPaddr == 0x2000)
  -- The information-flow projection cannot see the instruction caches (no
  -- covert timing channel), so the maintenance is trace-invisible.
  let st0 : SystemState := default
  let stW := icFetchOnCore st0 core0 lineExec
  assertBool "an instruction-cache write leaves the object store untouched"
    (stW.objectIndex == st0.objectIndex)

-- ----------------------------------------------------------------------------
-- §3.10  SM7.D.1 — the emission ledger: the runtime gets the model's exact
--         operand, and nothing at all when nothing is owed.
-- ----------------------------------------------------------------------------

private def runLedgerChecks : IO Unit := do
  IO.println "-- §3.10 SM7.D.1 emission ledger (exact runtime operand)"
  -- Granularity contract: one page operand expands to 64 line invalidations.
  assertBool "the page/line constants agree (icacheLinesPerPage * line = page)"
    (icacheLinesPerPage * cacheLineBytes == pageBytes)
  assertBool "one page operand expands to 64 IC IVAU instructions"
    (icacheLinesPerPage == 64)
  -- Coverage preorder: reflexive, `iallu` subsumes page invalidates, `unifyPage`
  -- subsumes the bare invalidate of its page — and, critically, `iallu` does
  -- NOT subsume a `unifyPage` (it issues no `DC CVAU`).
  assertBool "coverage is reflexive on every operand"
    ([ICacheInvalidation.iallu, .ivauPage paddrPage, .unifyPage paddrPage].all
      fun a => a.covers a)
  assertBool "iallu covers any page INVALIDATE"
    (ICacheInvalidation.iallu.covers (.ivauPage paddrPage))
  assertBool "iallu does NOT cover a unify (IC IALLUIS issues no DC CVAU)"
    (!(ICacheInvalidation.iallu.covers (.unifyPage paddrPage)))
  assertBool "unify covers the bare invalidate of the same page"
    ((ICacheInvalidation.unifyPage paddrPage).covers (.ivauPage paddrPage))
  assertBool "coverage is semantically grounded: a covering operand retires the covered one's lines"
    ([ICacheInvalidation.iallu, .ivauPage paddrPage, .unifyPage paddrPage].all fun a =>
      [ICacheInvalidation.iallu, .ivauPage paddrPage, .unifyPage paddrPage].all fun b =>
        !(a.covers b) ||
          [lineExec, lineOther].all fun l =>
            !(icacheLineMatches b l) || icacheLineMatches a l)
  assertBool "distinct pages are incomparable (neither discharges the other)"
    (!((ICacheInvalidation.ivauPage paddrPage).covers (.ivauPage paddrOther)) &&
     !((ICacheInvalidation.ivauPage paddrOther).covers (.ivauPage paddrPage)))
  -- Ledger lifecycle on a real state.
  let st0 : SystemState := default
  assertBool "the boot state owes no maintenance"
    (st0.pendingIcacheMaintenance == [])
  let stRec := recordIcacheMaintenance st0 (.ivauPage paddrPage)
  assertBool "recording into an empty ledger stores the operand VERBATIM"
    (stRec.pendingIcacheMaintenance == [ICacheInvalidation.ivauPage paddrPage])
  assertBool "re-recording a COVERED operand adds nothing (sound dedup)"
    ((recordIcacheMaintenance stRec (.ivauPage paddrPage)).pendingIcacheMaintenance ==
      [ICacheInvalidation.ivauPage paddrPage])
  assertBool "recording an INCOMPARABLE operand keeps BOTH (nothing is lost)"
    ((recordIcacheMaintenance stRec (.ivauPage paddrOther)).pendingIcacheMaintenance ==
      [ICacheInvalidation.ivauPage paddrPage, .ivauPage paddrOther])
  -- The defect this design rules out: a pending unify must survive a later
  -- domain-wide invalidate, because `IC IALLUIS` performs no clean to PoU.
  let stUnify := recordIcacheMaintenance st0 (.unifyPage paddrPage)
  assertBool "a pending UNIFY survives a later iallu (the clean is NOT dropped)"
    ((recordIcacheMaintenance stUnify .iallu).pendingIcacheMaintenance ==
      [ICacheInvalidation.unifyPage paddrPage, .iallu])
  assertBool "a bare invalidate of the unified page IS absorbed by the pending unify"
    ((recordIcacheMaintenance stUnify (.ivauPage paddrPage)).pendingIcacheMaintenance ==
      [ICacheInvalidation.unifyPage paddrPage])
  assertBool "the drain empties the ledger"
    ((clearIcacheMaintenance stRec).pendingIcacheMaintenance == [])
  assertBool "recording frames the per-core instruction caches"
    (allCores.all fun c => (icacheOnCore stRec c).lines.isEmpty)
  -- The live seams: the ledger carries the model's operand to the runtime.
  match vspaceMapPageWithFlush asid5 vaddrPage paddrPage permsExec (cacheState []) with
  | .error _ => assertBool "the scenario maps the executable page" false
  | .ok ((), stMapped) => do
    match vspaceUnmapPageWithShootdownAndIcacheBroadcast core0 asid5 vaddrPage
        stMapped with
    | .error _ => assertBool "the executable unmap commits" false
    | .ok ((), stPost) =>
      assertBool "an EXECUTABLE unmap records the TARGETED page operand (not a full flush)"
        (stPost.pendingIcacheMaintenance == [ICacheInvalidation.ivauPage paddrPage])
    -- The non-executable unmap: the whole point of the ledger — the runtime
    -- learns there is nothing to do, where the shootdown-diff key would have
    -- fired a domain-wide invalidate.
    match vspaceMapPageWithFlush asid5 vaddrOther paddrOther .readOnly stMapped with
    | .error _ => assertBool "the scenario maps a read-only page" false
    | .ok ((), stRO) => do
      match vspaceUnmapPageWithShootdownAndIcacheBroadcast core0 asid5 vaddrOther
          stRO with
      | .error _ => assertBool "the read-only unmap commits" false
      | .ok ((), stROPost) => do
        assertBool "a NON-executable unmap records NOTHING (no spurious full flush)"
          (stROPost.pendingIcacheMaintenance == [])
        assertBool "the non-executable unmap still posts its TLB shootdown round"
          (!(shootdownQuiescent stROPost.tlbShootdown))
    -- Retype records its clean-then-invalidate operand even though its own
    -- shootdown round may be absent — the residual the shootdown-diff key
    -- could not see.
    let stAll : SystemState :=
      allCores.foldl (fun st c => icFetchOnCore st c lineExec) stMapped
    let authCap : Capability :=
      { target := .object udVsp,
        rights := AccessRightSet.ofList [.read, .write, .grant, .retype] }
    match SeLe4n.Kernel.lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache
        core0 authCap udVsp
        (.untyped { regionBase := SeLe4n.PAddr.ofNat 0, regionSize := 4096 })
        stAll with
    | .error _ => assertBool "the retype seam commits" false
    | .ok ((), stPost) =>
      -- The target is a `.vspaceRoot`, whose `objectTypeAllocSize` is 4096, so
      -- the scrub zeroes [udVsp × 4096, +4096) and the operand cleans exactly
      -- that before the domain-wide invalidate.
      assertBool "a retype records the clean-then-invalidate range operand"
        (stPost.pendingIcacheMaintenance ==
          [ICacheInvalidation.cleanRangeIallu
            (SeLe4n.PAddr.ofNat (udVsp.toNat * 4096)) 4096])

-- ----------------------------------------------------------------------------
-- §3.11  SM7.D.2 — the data-side dual: the clean-to-PoU obligation tripwire.
-- ----------------------------------------------------------------------------

private def runCodeWriteObligationChecks : IO Unit := do
  IO.println "-- §3.11 SM7.D.2 kernel code-write clean-to-PoU obligation"
  assertBool "both kernel code-write sites are enumerated"
    (kernelCodeWriteSites.length == 2)
  assertBool "every constructor is listed (the tripwire)"
    ([KernelCodeWriteSite.retypeScrub, .bootImageLoad].all fun st =>
      kernelCodeWriteSites.contains st)
  assertBool "the canonical D→I sequence covers the barriers the obligation names"
    (armv8DCacheToICacheSequence.covers CacheBarrierKind.dsb_ish &&
     armv8DCacheToICacheSequence.covers CacheBarrierKind.isb)
  -- The emission partition: the re-type's clean is live, boot's is not.
  assertBool "the re-type site's clean-to-PoU is EMITTED by a live transition"
    (kernelCodeWriteEmitted .retypeScrub)
  assertBool "the boot-image site's emission is still pending (SM10.E)"
    (!(kernelCodeWriteEmitted .bootImageLoad))
  assertBool "exactly one site still owes an emission"
    (kernelCodeWriteSites.filter (fun s => !kernelCodeWriteEmitted s) ==
      [KernelCodeWriteSite.bootImageLoad])

-- ----------------------------------------------------------------------------
-- §3.12  SM7.D — the user-facing code-publication path
--         (`.vspaceUnifyInstruction`, seLe4n's Page_Unify_Instruction).
-- ----------------------------------------------------------------------------

private def unifyDecoded : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat 0,
    msgInfo := { length := 2, extraCaps := 0, label := 0 },
    syscallId := .vspaceUnifyInstruction,
    msgRegs := #[SeLe4n.RegValue.ofNat 5, SeLe4n.RegValue.ofNat 0x1000] }

private def runUnifyInstructionChecks : IO Unit := do
  IO.println "-- §3.12 SM7.D `.vspaceUnifyInstruction` (code publication)"
  -- ABI: the syscall is in the modeled set at discriminant 29, with the
  -- write-right authority the dispatch gate enforces.
  assertBool "the syscall encodes to 29 and round-trips"
    (SyscallId.vspaceUnifyInstruction.toNat == 29 &&
      SyscallId.ofNat? 29 == some .vspaceUnifyInstruction)
  -- Stated as a RELATION rather than a literal: the count moves whenever a
  -- syscall is added (SM8.C took it to 31, SM9.A to 33), and what this group
  -- needs is that 29 is inside the modeled set — which a literal cannot say and
  -- which is why the label above it had already drifted to "30".
  assertBool "…and 29 is inside the modeled set, so the discriminant is in range"
    (SyscallId.vspaceUnifyInstruction.toNat < SyscallId.count)
  assertBool "unify requires the write right"
    (syscallRequiredRight .vspaceUnifyInstruction == .write)
  -- The operand encodes to FFI tag 2 (the full D→I sequence), distinct from a
  -- bare page invalidate: dropping to `ivauPage` would silently lose the clean.
  assertBool "the unify operand encodes to op tag 2 carrying the page base"
    ((ICacheInvalidation.unifyPage paddrPage).toOpTag == 2 &&
     (ICacheInvalidation.unifyPage paddrPage).toPaddr == 0x2000)
  assertBool "unify dominates a bare invalidate on the same page in the coverage order"
    ((ICacheInvalidation.unifyPage paddrPage).covers (.ivauPage paddrPage))
  assertBool "and iallu does NOT dominate it (the clean-to-PoU is irreplaceable)"
    (!(ICacheInvalidation.iallu.covers (.unifyPage paddrPage)))
  -- Fail-closed paths: an unbound ASID and an unmapped address are rejected,
  -- so the operation cannot be used to maintain memory the caller has no
  -- mapping for.
  let st0 := cacheState []
  assertBool "an unbound ASID is rejected (asidNotBound)"
    (match vspaceUnifyInstructionPage (SeLe4n.ASID.ofNat 99) vaddrPage st0 with
      | .error .asidNotBound => true | _ => false)
  assertBool "an unmapped address is rejected (translationFault)"
    (match vspaceUnifyInstructionPage asid5 vaddrPage st0 with
      | .error .translationFault => true | _ => false)
  -- The success path.  Note the mapping is deliberately **not** executable —
  -- the operation exists for the writer publishing code through a data
  -- mapping, so gating it on execute would make it useless.
  match vspaceMapPageWithFlush asid5 vaddrPage paddrPage
      { read := true, write := true, execute := false, user := true,
        cacheable := true } st0 with
  | .error _ => assertBool "the scenario maps a writable (non-executable) page" false
  | .ok ((), stMapped) => do
    -- Every core holds a stale line from a previous incarnation of the frame.
    let staleLine : ICacheLine :=
      { asid := asid5, vaddr := vaddrPage, paddr := paddrPage, perms := permsExec }
    let stAll : SystemState :=
      allCores.foldl (fun st c => icFetchOnCore st c staleLine) stMapped
    assertBool "the pre-state holds a stale line on all four cores"
      (allCores.all fun c => (icacheOnCore stAll c).lines.contains staleLine)
    match vspaceUnifyInstructionPage asid5 vaddrPage stAll with
    | .error _ => assertBool "unify commits on a writable mapping" false
    | .ok ((), stPost) => do
      assertBool "after unify NO core retains a line for the page"
        (allCores.all fun c => !((icacheOnCore stPost c).lines.contains staleLine))
      assertBool "unify records the UNIFY operand (not a bare invalidate)"
        (stPost.pendingIcacheMaintenance == [ICacheInvalidation.unifyPage paddrPage])
      assertBool "unify modifies no page table (pure cache operation)"
        (stPost.objectIndex == stAll.objectIndex &&
         stPost.tlbShootdown == stAll.tlbShootdown)
      assertBool "the post-state satisfies the 14th conjunct"
        (icacheCoherentCheck_perCore stPost)
      assertBool "the post-state satisfies the 13th conjunct"
        (tlbInvalidationConsistentCheck_perCore stPost)
    -- The live dispatch: CSpace cap resolution + authority gate.
    let vspCap : Capability :=
      { target := .object udVsp,
        rights := AccessRightSet.ofList [.read, .write] }
    let roCap : Capability :=
      { target := .object udVsp, rights := AccessRightSet.ofList [.read] }
    match vspaceMapPageWithFlush asid5 vaddrPage paddrPage
        { read := true, write := true, execute := false, user := true,
          cacheable := true } (cacheState [(SeLe4n.Slot.ofNat 0, vspCap)]) with
    | .error _ => assertBool "the live scenario maps the page" false
    | .ok ((), stLive) =>
      assertBool "the live `.vspaceUnifyInstruction` dispatch succeeds with a write cap"
        (match SeLe4n.Kernel.dispatchSyscall unifyDecoded udCaller stLive with
          | .ok _ => true | .error _ => false)
    match vspaceMapPageWithFlush asid5 vaddrPage paddrPage
        { read := true, write := true, execute := false, user := true,
          cacheable := true } (cacheState [(SeLe4n.Slot.ofNat 0, roCap)]) with
    | .error _ => assertBool "the read-only scenario maps the page" false
    | .ok ((), stRO) =>
      assertBool "a read-only capability is refused (illegalAuthority)"
        (match SeLe4n.Kernel.dispatchSyscall unifyDecoded udCaller stRO with
          | .error .illegalAuthority => true | _ => false)
    match vspaceMapPageWithFlush asid5 vaddrPage paddrPage
        { read := true, write := true, execute := false, user := true,
          cacheable := true } (cacheState []) with
    | .error _ => assertBool "the no-cap scenario maps the page" false
    | .ok ((), stNoCap) =>
      assertBool "no capability at the slot is refused (invalidCapability)"
        (match SeLe4n.Kernel.dispatchSyscall unifyDecoded udCaller stNoCap with
          | .error .invalidCapability => true | _ => false)

-- ----------------------------------------------------------------------------
-- §3.13  SM7.D — the re-type's clean to the Point of Unification.
--
--   A re-type scrubs the target's backing memory.  Those zeroing stores land in
--   the data cache; instruction fetches read at the Point of Unification, so
--   `IC IALLUIS` on its own would drop the cached instruction lines and then let
--   the very next fetch re-fill from the *pre-scrub* PoU content — the previous
--   owner's code, reachable through any later executable mapping of the frame,
--   in any address space.  The operand must therefore clean the scrubbed extent
--   first.  This group pins that it does, for every allocation size, and pins
--   the exclusion (`iallu` does NOT discharge the clean) that makes the
--   distinction load-bearing rather than decorative.
-- ----------------------------------------------------------------------------

-- ----------------------------------------------------------------------------
-- §3.14  PR #845 review (P2) — page alignment enforced at the mapping boundary.
--
--   The SM7.D operands name a *page*, and both HAL loops round their operand
--   down to the containing page (`base & !(PAGE_SIZE - 1)`).  A mapping that
--   carried an unaligned physical address would therefore make the model
--   record maintenance against an address the machine never acts on.  The
--   four checked wrappers rejected such a mapping, but `VSpaceRoot.mapPage`
--   and the builder inserted straight into the mapping table and so bypassed
--   them.  This group pins that the guard is now structural — at the
--   constructor itself, where nothing can get around it.
-- ----------------------------------------------------------------------------

private def runMappingAlignmentChecks : IO Unit := do
  IO.println "-- §3.14 PR #845 (P2) page alignment at the mapping boundary"
  let emptyRoot : VSpaceRoot := { asid := asid5, mappings := default }
  let alignedPa := SeLe4n.PAddr.ofNat 0x2000
  let unalignedPa := SeLe4n.PAddr.ofNat 0x2001
  -- The structural guard: the constructor itself refuses the unaligned PA.
  assertBool "the constructor accepts a page-aligned physical address"
    (emptyRoot.mapPage vaddrPage alignedPa permsExec |>.isSome)
  assertBool "the constructor REFUSES an unaligned physical address"
    (emptyRoot.mapPage vaddrPage unalignedPa permsExec |>.isNone)
  -- Every offset inside a page is refused, not just the odd byte.
  assertBool "every non-zero offset within a page is refused"
    ([1, 63, 64, 0x800, 0xFFF].all fun off =>
      (emptyRoot.mapPage vaddrPage (SeLe4n.PAddr.ofNat (0x2000 + off)) permsExec).isNone)
  -- The transition surfaces the honest error code rather than the
  -- `mappingConflict` the constructor's `none` would otherwise produce.
  match vspaceMapPage asid5 vaddrPage unalignedPa permsExec (cacheState []) with
  | .error e =>
      assertBool "the transition reports `alignmentError`, not `mappingConflict`"
        (e == SeLe4n.Model.KernelError.alignmentError)
  | .ok _ => assertBool "an unaligned map must not succeed" false
  -- ... and the aligned map still goes through, so the guard is not vacuous.
  match vspaceMapPage asid5 vaddrPage alignedPa permsExec (cacheState []) with
  | .error _ => assertBool "the aligned map still succeeds (guard not vacuous)" false
  | .ok ((), stOk) =>
      assertBool "the aligned map installs the translation"
        (vspaceHasTranslation stOk asid5 vaddrPage)
  -- The consequence that motivated the guard: any mapping the model holds now
  -- yields a maintenance operand whose address the HAL will not round away.
  match vspaceMapPageWithFlush asid5 vaddrPage alignedPa permsExec (cacheState []) with
  | .error _ => assertBool "the scenario maps the page" false
  | .ok ((), stMapped) =>
      assertBool "the resulting operand names a page-aligned address"
        ((Architecture.ICacheInvalidation.unifyPage alignedPa).toPaddr % 4096 == 0 &&
         stMapped.perCoreICache.size == numCores)

private def runRetypeCleanToPoUChecks : IO Unit := do
  IO.println "-- §3.13 SM7.D re-type clean-to-PoU (scrubbed-extent coverage)"
  -- The operand is derived from the pre-state object, so it matches the extent
  -- `scrubObjectMemory` will zero — for every object type the model allocates.
  let sizes : List (KernelObjectType × Nat) :=
    [(.tcb, 1024), (.endpoint, 64), (.notification, 64), (.cnode, 4096),
     (.vspaceRoot, 4096), (.untyped, 4096), (.schedContext, 256), (.reply, 64)]
  assertBool "the allocation sizes the scrub uses are the ones under test"
    (sizes.all fun (t, n) => objectTypeAllocSize t == n)
  match vspaceMapPageWithFlush asid5 vaddrPage paddrPage permsExec (cacheState []) with
  | .error _ => assertBool "the scenario maps the executable page" false
  | .ok ((), stMapped) => do
    -- The live seam's operand names the target's own extent — read from
    -- `scrubExtent`, the scrub's *own* definition of the range, rather than
    -- recomputed here.  That single source is what makes the clean and the
    -- zeroing incapable of drifting apart.
    let extent := SeLe4n.Kernel.scrubExtent udVsp KernelObjectType.vspaceRoot
    assertBool "the re-type operand cleans exactly the scrubbed extent"
      (SeLe4n.Kernel.retypeIcacheOp udVsp stMapped ==
        ICacheInvalidation.cleanRangeIallu extent.fst extent.snd)
    -- The correspondence, exercised rather than asserted: dirty all of memory,
    -- run the real scrub, and confirm the bytes it zeroed are inside the range
    -- the operand cleans.  This is the check that fails if the two ever drift.
    let stDirty : SystemState :=
      { stMapped with machine := { stMapped.machine with memory := fun _ => 7 } }
    let stScrubbed :=
      SeLe4n.Kernel.scrubObjectMemory stDirty udVsp KernelObjectType.vspaceRoot
    let probes : List Nat :=
      [extent.fst.toNat, extent.fst.toNat + 1, extent.fst.toNat + extent.snd - 1]
    assertBool "every byte the scrub zeroes lies inside the cleaned range"
      (probes.all fun a =>
        stScrubbed.machine.memory (SeLe4n.PAddr.ofNat a) == 0 &&
        byteRangeContains extent.fst extent.snd (SeLe4n.PAddr.ofNat a) 1)
    assertBool "the byte just past the scrubbed extent is untouched (bound exact)"
      (stScrubbed.machine.memory
        (SeLe4n.PAddr.ofNat (extent.fst.toNat + extent.snd)) == 7)
    -- ... and it discharges the `.retypeScrub` clean-to-PoU obligation over
    -- that very range, which `.iallu` provably would not.
    let base := extent.fst
    let size := extent.snd
    assertBool "the emitted operand discharges the scrub's clean-to-PoU obligation"
      (dischargesPoUClean (SeLe4n.Kernel.retypeIcacheOp udVsp stMapped) base size)
    assertBool "the PRE-FIX operand `iallu` does NOT discharge it (the defect)"
      (!(dischargesPoUClean ICacheInvalidation.iallu base size))
    assertBool "discharging the obligation forces a domain-wide invalidate"
      ((SeLe4n.Kernel.retypeIcacheOp udVsp stMapped).isDomainWide)
    -- An empty slot has nothing to scrub, so no clean is owed; the bare
    -- domain-wide invalidate remains.
    assertBool "an absent target owes no clean (bare domain-wide invalidate)"
      (SeLe4n.Kernel.retypeIcacheOp ⟨9999⟩ stMapped == ICacheInvalidation.iallu)
    -- Coverage algebra, on the concrete operands: a wider clean subsumes a
    -- narrower one, `iallu` subsumes neither, and page-granular cleans cannot
    -- stand in for the domain-wide invalidate.
    let wide := ICacheInvalidation.cleanRangeIallu (SeLe4n.PAddr.ofNat 0x1000) 4096
    let narrow := ICacheInvalidation.cleanRangeIallu (SeLe4n.PAddr.ofNat 0x1040) 64
    let outside := ICacheInvalidation.cleanRangeIallu (SeLe4n.PAddr.ofNat 0x9000) 64
    assertBool "a containing range covers a contained one"
      (wide.covers narrow)
    assertBool "a contained range does NOT cover its container"
      (!(narrow.covers wide))
    assertBool "disjoint ranges are incomparable (the ledger must keep both)"
      (!(wide.covers outside) && !(outside.covers wide))
    assertBool "the range operand covers `iallu` and any page invalidate"
      (wide.covers .iallu && wide.covers (.ivauPage paddrPage))
    assertBool "`iallu` covers NEITHER a unifyPage NOR a cleanRangeIallu"
      (!(ICacheInvalidation.iallu.covers (.unifyPage paddrPage)) &&
       !(ICacheInvalidation.iallu.covers narrow))
    assertBool "a page-granular clean does not stand in for the range operand"
      (!((ICacheInvalidation.unifyPage (SeLe4n.PAddr.ofNat 0x1000)).covers wide))
    -- A range clean that contains a page discharges that page's unify.
    assertBool "a range containing a page covers that page's unify"
      (wide.covers (.unifyPage (SeLe4n.PAddr.ofNat 0x1000)))
    -- FFI encoding: tag 3 carries BOTH words.  Dropping `size` would silently
    -- turn the clean into a zero-length no-op.
    assertBool "the range operand encodes to (3, base, size)"
      (wide.toOpTag == 3 && wide.toPaddr == 0x1000 && wide.toSize == 4096)
    assertBool "every non-range operand encodes a zero length"
      ([ICacheInvalidation.iallu, .ivauPage paddrPage, .unifyPage paddrPage].all
        fun op => op.toSize == 0)
    -- Live, end to end: the retype leaves every core's I-cache cold AND the
    -- ledger owing the clean.
    let authCap : Capability :=
      { target := .object udVsp,
        rights := AccessRightSet.ofList [.read, .write, .grant, .retype] }
    match vspaceMapPageWithFlush asid5 vaddrPage paddrPage permsExec
        (cacheState [(SeLe4n.Slot.ofNat 0, authCap)]) with
    | .error _ => assertBool "the CSpaceAddr scenario maps the page" false
    | .ok ((), stWithCap) => do
    let stAll : SystemState :=
      allCores.foldl (fun st c => icFetchOnCore st c lineExec) stWithCap
    match SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdownPerCoreIcache
        core0 { cnode := udCn, slot := SeLe4n.Slot.ofNat 0 } udVsp
        (.untyped { regionBase := SeLe4n.PAddr.ofNat 0, regionSize := 4096 })
        stAll with
    | .error _ => assertBool "the CSpaceAddr retype seam commits" false
    | .ok ((), stPost) => do
      assertBool "the CSpaceAddr seam records the same range operand"
        (stPost.pendingIcacheMaintenance ==
          [ICacheInvalidation.cleanRangeIallu
            (SeLe4n.PAddr.ofNat (udVsp.toNat * 4096)) 4096])
      assertBool "and still leaves every core's instruction cache cold"
        (allCores.all fun c => (icacheOnCore stPost c).lines.isEmpty)
      assertBool "the post-state satisfies the 14th conjunct"
        (icacheCoherentCheck_perCore stPost)

-- ----------------------------------------------------------------------------
-- §3.15  Cross-cluster mock — the instruction-cache half of the portability
--         seam.  `IC IALLUIS` / `IC IVAU` broadcast within the *Inner
--         Shareable* domain only, so on a multi-cluster SoC the reach stops at
--         the cluster boundary and the out-of-domain cores need the SGI-based
--         protocol (the SM7.B shootdown shape) — exactly the narrowing the
--         module docs call for.  `icBroadcastReach` is already a parameter, so
--         a narrowed mock reach is the executable statement of the hazard:
--         with it, `icInvalidateBroadcast_reaches_all_cores`'s coverage
--         hypothesis fails and the remote cluster keeps its lines.
-- ----------------------------------------------------------------------------

/-- Mock cluster A of the two-cluster topology — the issuing PE's cluster, the
only one a single Inner Shareable broadcast reaches on such a SoC. -/
private def mockClusterA : List CoreId := [core0, core1]

/-- Mock cluster B — the cores an Inner Shareable broadcast would miss. -/
private def mockClusterB : List CoreId := [core2, core3]

private def runCrossClusterReachChecks : IO Unit := do
  IO.println "-- §3.15 cross-cluster mock: the I-cache broadcast reach seam"
  -- The mock is a MOCK: on BCM2712 the reach is genuinely every PE.
  assertBool "on this platform the broadcast reach is the whole topology"
    (allCores.all fun c => icBroadcastReach.contains c)
  assertBool "the mock clusters partition the platform's PEs"
    (mockClusterA.length + mockClusterB.length == numCores &&
      allCores.all fun c => mockClusterA.contains c != mockClusterB.contains c)
  -- Every core has fetched the same executable page.
  let stAll : SystemState :=
    allCores.foldl (fun st c => icFetchOnCore st c lineExec) (default : SystemState)
  -- (a) THE HAZARD: a broadcast whose reach stops at the cluster boundary.
  let stNarrow := icInvalidateBroadcast stAll mockClusterA .iallu
  assertBool "a cluster-narrowed broadcast cleans the issuing PE's cluster"
    (mockClusterA.all fun c => (icacheOnCore stNarrow c).lines.isEmpty)
  assertBool "a cluster-narrowed broadcast leaves the REMOTE cluster stale"
    (mockClusterB.all fun c => (icacheOnCore stNarrow c).lines.contains lineExec)
  -- (b) the targeted (by-VA) operand narrows identically — the hazard is the
  -- reach, not the operand kind.
  let stNarrowIvau := icInvalidateBroadcast stAll mockClusterA (.ivauPage paddrPage)
  assertBool "the by-VA operand is bounded by the same reach"
    (mockClusterA.all (fun c => !((icacheOnCore stNarrowIvau c).lines.contains lineExec)) &&
      mockClusterB.all (fun c => (icacheOnCore stNarrowIvau c).lines.contains lineExec))
  -- (c) the code-publication operand too: a writer on cluster A cannot publish
  -- instructions to cluster B without the out-of-domain protocol.
  let stNarrowUnify := icInvalidateBroadcast stAll mockClusterA (.unifyPage paddrPage)
  assertBool "the clean-then-invalidate operand is bounded by the same reach"
    (mockClusterB.all fun c => (icacheOnCore stNarrowUnify c).lines.contains lineExec)
  -- (d) the closure: composing the per-cluster broadcasts (what an SGI-based
  -- out-of-domain protocol would realise) reaches every PE again — the same
  -- shape SM7.B's explicit-ack round gives the TLB.
  let stBoth := icInvalidateBroadcast stNarrow mockClusterB .iallu
  assertBool "per-cluster broadcasts composed reach every PE of both clusters"
    (allCores.all fun c => (icacheOnCore stBoth c).lines.isEmpty)
  assertBool "the composed result equals the single full-reach broadcast"
    (allCores.all fun c =>
      (icacheOnCore stBoth c).lines ==
        (icacheOnCore (icInvalidateBroadcast stAll icBroadcastReach .iallu) c).lines)
  assertBool "the composed cross-cluster maintenance keeps the 14th conjunct green"
    (icacheCoherentCheck_perCore stBoth)

def runSmpCacheMaintenanceChecks : IO Unit := do
  IO.println "===================================================="
  IO.println "WS-SM SM7.D — cache maintenance broadcast suite"
  IO.println "===================================================="
  runOperandChecks
  runAccessorChecks
  runBroadcastReachChecks
  runDCachePoCChecks
  runDmaScopeChecks
  runInvariantChecks
  runLiveUnmapChecks
  runLiveRetypeChecks
  runSeamConformanceChecks
  runLedgerChecks
  runCodeWriteObligationChecks
  runUnifyInstructionChecks
  runRetypeCleanToPoUChecks
  runMappingAlignmentChecks
  runCrossClusterReachChecks
  IO.println "===================================================="
  IO.println "All SM7.D cache maintenance broadcast checks PASS."

end SeLe4n.Testing.SmpCacheMaintenance

def main : IO Unit :=
  SeLe4n.Testing.SmpCacheMaintenance.runSmpCacheMaintenanceChecks
