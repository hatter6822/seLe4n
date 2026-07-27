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
  system-wide, with no target set to get wrong.
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

-- SM7.D.1 typed operand + FFI encoding:
#check @ICacheInvalidation
#check @ICacheInvalidation.toOpTag
#check @ICacheInvalidation.toPaddr
#check @ICacheInvalidation.toOpTag_in_range
#check @ICacheInvalidation.toOpTag_distinct_constructors
#check @ICacheInvalidation.iallu_opTag
#check @ICacheInvalidation.ivau_opTag
#check @ICacheInvalidation.iallu_zero_operand
#check @ICacheInvalidation.ivau_toPaddr

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
#check @icacheLineMatches_ivau
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
#check @SeLe4n.Kernel.retypeIcacheOperand
#check @SeLe4n.Kernel.retypeIcacheOperand_eq
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
#check @SeLe4n.Platform.FFI.icMaintenanceBroadcast_ivau_encoding
#check @SeLe4n.Kernel.completeIcacheMaintenance
#check @SeLe4n.Kernel.completeIcacheMaintenance_nil
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
example : (ICacheInvalidation.ivau (SeLe4n.PAddr.ofNat 0x3000)).toOpTag = 1 := by decide
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
    ((ICacheInvalidation.ivau paddrPage).toOpTag == 1 &&
     (ICacheInvalidation.ivau paddrPage).toPaddr == UInt64.ofNat paddrPage.toNat)
  assertBool "the two op tags are distinct (Rust match arms cannot overlap)"
    (ICacheInvalidation.iallu.toOpTag != (ICacheInvalidation.ivau paddrPage).toOpTag)
  assertBool "every op tag is in [0, 2) (the Rust decoder's range)"
    ([ICacheInvalidation.iallu, .ivau paddrPage].all fun op => op.toOpTag.toNat < 2)
  -- Effect algebra on a two-line cache.
  let ic : ICacheState := { lines := [lineExec, lineOther] }
  assertBool "iallu empties the view"
    ((applyICacheInvalidation ic .iallu).lines.isEmpty)
  assertBool "ivau removes exactly the lines tagged with its address"
    (!((applyICacheInvalidation ic (.ivau paddrPage)).lines.contains lineExec))
  assertBool "ivau leaves other physical pages cached (selectivity)"
    ((applyICacheInvalidation ic (.ivau paddrPage)).lines.contains lineOther)
  assertBool "invalidation is idempotent"
    (applyICacheInvalidation (applyICacheInvalidation ic (.ivau paddrPage))
      (.ivau paddrPage) == applyICacheInvalidation ic (.ivau paddrPage))
  assertBool "invalidation never adds lines"
    ((applyICacheInvalidation ic (.ivau paddrPage)).lines.all fun l => ic.lines.contains l)

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
  let stIvau := icInvalidateBroadcast stMixed icBroadcastReach (.ivau paddrPage)
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
      let stClean := icInvalidateBroadcast stStale icBroadcastReach (.ivau paddrPage)
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
      (unmapIcacheOperand stAll asid5 vaddrPage == some (.ivau paddrPage))
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
  assertBool "the FFI wrapper emits (1, paddr) for the targeted invalidate"
    ((ICacheInvalidation.ivau paddrPage).toOpTag == 1 &&
     (ICacheInvalidation.ivau paddrPage).toPaddr == 0x2000)
  -- The information-flow projection cannot see the instruction caches (no
  -- covert timing channel), so the maintenance is trace-invisible.
  let st0 : SystemState := default
  let stW := icFetchOnCore st0 core0 lineExec
  assertBool "an instruction-cache write leaves the object store untouched"
    (stW.objectIndex == st0.objectIndex)

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
  IO.println "===================================================="
  IO.println "All SM7.D cache maintenance broadcast checks PASS."

end SeLe4n.Testing.SmpCacheMaintenance

def main : IO Unit :=
  SeLe4n.Testing.SmpCacheMaintenance.runSmpCacheMaintenanceChecks
