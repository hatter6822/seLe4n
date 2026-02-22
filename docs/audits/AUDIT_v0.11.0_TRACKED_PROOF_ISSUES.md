# AUDIT v0.11.0 — Tracked Proof Issues and Follow-up Obligations

This document tracks proof obligations identified in [`AUDIT_v0.11.0.md`](./AUDIT_v0.11.0.md) and carried forward from the WS-C portfolio.

Status legend:

- `OPEN`: accepted obligation, not yet implemented.
- `IN PROGRESS`: implementation/proof branch exists.
- `CLOSED`: theorem is implemented in Lean and covered by tiered tests/anchors.

---

## Issue TPI-D01 (CLOSED) — Non-interference preservation for scheduler operations

- **Audit mapping:** `AUDIT_v0.11.0.md` F-05 (High), recommendation 9.2 #4.
- **Workstream:** WS-D2.
- **Resolution:** Implemented `chooseThread_preserves_lowEquivalent` in `SeLe4n/Kernel/InformationFlow/Invariant.lean`. The proof shows that `chooseThread` does not modify system state, so low-equivalence is trivially preserved. No `sorry` debt.

Closed theorem:

```lean
theorem chooseThread_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂) :
    ∀ (tid₁ : ThreadId) (st₁' : SystemState)
      (tid₂ : ThreadId) (st₂' : SystemState),
      chooseThread s₁ = .ok (tid₁, st₁') →
      chooseThread s₂ = .ok (tid₂, st₂') →
      lowEquivalent ctx observer st₁' st₂'
```

---

## Issue TPI-D02 (CLOSED) — Non-interference preservation for capability operations

- **Audit mapping:** `AUDIT_v0.11.0.md` F-05 (High), recommendation 9.2 #4.
- **Workstream:** WS-D2.
- **Resolution:** Implemented `cspaceMint_preserves_lowEquivalent` and `cspaceRevoke_preserves_lowEquivalent` in `SeLe4n/Kernel/InformationFlow/Invariant.lean`. The mint proof decomposes through `cspaceInsertSlot` preservation helpers; the revoke proof uses `clearCapabilityRefsState` preservation lemmas. No `sorry` debt.

Closed theorem obligations:

```lean
theorem cspaceMint_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (src dst : CSpaceAddr) (rights : List AccessRight)
    (badge : Option Badge) (s₁ s₂ : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hObs : ¬ objectObservable ctx observer src.cnode)
    -- ... (proves low-equivalence preserved when mint acts on unobservable CNode)

theorem cspaceRevoke_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (addr : CSpaceAddr) (s₁ s₂ : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hObs : ¬ objectObservable ctx observer addr.cnode)
    -- ... (proves low-equivalence preserved when revoke acts on unobservable CNode)
```

---

## Issue TPI-D03 (CLOSED) — Non-interference preservation for lifecycle operations

- **Audit mapping:** `AUDIT_v0.11.0.md` F-05 (High), recommendation 9.2 #4.
- **Workstream:** WS-D2.
- **Resolution:** Implemented `lifecycleRetypeObject_preserves_lowEquivalent` in `SeLe4n/Kernel/InformationFlow/Invariant.lean`. The proof delegates to the shared `storeObject_at_unobservable_preserves_lowEquivalent` infrastructure. No `sorry` debt.

Closed theorem obligation:

```lean
theorem lifecycleRetypeObject_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (srcId newId : ObjId) (newType : KernelObjectType)
    (s₁ s₂ : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hObs : ¬ objectObservable ctx observer newId)
    -- ... (proves low-equivalence preserved when retype stores to unobservable ID)
```

---

## Issue TPI-D04 (CLOSED) — Badge-override safety in cspaceMint

- **Audit mapping:** `AUDIT_v0.11.0.md` F-06 (Medium), recommendation 9.2 #5.
- **Workstream:** WS-D3.
- **Resolution:** Three badge-safety theorems implemented in `SeLe4n/Kernel/Capability/Invariant.lean`.
  The proofs decompose through `mintDerivedCap_attenuates` (the existing attenuation lemma) and
  show that the `badge` parameter in `mintDerivedCap` affects only `.badge` of the child — the
  `rightsSubset` check and `target := parent.target` assignment are badge-independent. No `sorry` debt.

Closed theorem obligations:

```lean
/-- Rights attenuation holds regardless of badge override. -/
theorem mintDerivedCap_rights_attenuated_with_badge_override
    (parent child : Capability)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (hMint : mintDerivedCap parent rights badge = .ok child) :
    ∀ right, right ∈ child.rights → right ∈ parent.rights

/-- Target identity preserved regardless of badge override. -/
theorem mintDerivedCap_target_preserved_with_badge_override
    (parent child : Capability)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (hMint : mintDerivedCap parent rights badge = .ok child) :
    child.target = parent.target

/-- Composed kernel-operation-level safety: badge override cannot escalate privilege. -/
theorem cspaceMint_badge_override_safe
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (hStep : cspaceMint src dst rights badge st = .ok ((), st')) :
    ∃ parent child,
      cspaceLookupSlot src st = .ok (parent, st) ∧
      cspaceLookupSlot dst st' = .ok (child, st') ∧
      child.target = parent.target ∧
      (∀ right, right ∈ child.rights → right ∈ parent.rights)
```

---

## Issue TPI-D05 (CLOSED) — VSpace successful-operation invariant preservation

- **Audit mapping:** `AUDIT_v0.11.0.md` F-08 (Medium), recommendation 9.2 #6.
- **Workstream:** WS-D3.
- **Carries forward:** TPI-001 from `AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`.
- **Resolution:** Two success-path invariant preservation theorems and four round-trip theorems
  implemented in `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean`. Supporting infrastructure:
  `resolveAsidRoot_some_implies` and `resolveAsidRoot_of_unique_root` extraction/characterization
  lemmas in `VSpace.lean`; `storeObject_objectIndex_eq_of_mem` for post-state objectIndex stability;
  seven VSpaceRoot helper theorems in `Object.lean` (`mapPage_asid_eq`, `unmapPage_asid_eq`,
  `lookup_eq_none_not_mem`, `mapPage_noVirtualOverlap`, `unmapPage_noVirtualOverlap`,
  `lookup_mapPage_ne`, `lookup_unmapPage_ne`). No `sorry` debt. TPI-001 fully closed.

Closed theorem obligations:

```lean
/-- Successful vspaceMapPage preserves VSpace invariant bundle. -/
theorem vspaceMapPage_success_preserves_vspaceInvariantBundle
    (st st' : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (hInv : vspaceInvariantBundle st)
    (hStep : vspaceMapPage asid vaddr paddr st = .ok ((), st')) :
    vspaceInvariantBundle st'

/-- Successful vspaceUnmapPage preserves VSpace invariant bundle. -/
theorem vspaceUnmapPage_success_preserves_vspaceInvariantBundle
    (st st' : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (hInv : vspaceInvariantBundle st)
    (hStep : vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    vspaceInvariantBundle st'

/-- TPI-001 #1: map then lookup yields mapped address. -/
theorem vspaceLookup_after_map
    (st st' : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (hInv : vspaceInvariantBundle st)
    (hStep : vspaceMapPage asid vaddr paddr st = .ok ((), st')) :
    vspaceLookup asid vaddr st' = .ok (paddr, st')

/-- TPI-001 #2: map at vaddr does not affect lookup at different vaddr'. -/
theorem vspaceLookup_map_other
    (st st' : SystemState) (asid : SeLe4n.ASID) (vaddr vaddr' : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (hNe : vaddr ≠ vaddr')
    (hInv : vspaceInvariantBundle st)
    (hStep : vspaceMapPage asid vaddr paddr st = .ok ((), st')) :
    (vspaceLookup asid vaddr' st').map Prod.fst = (vspaceLookup asid vaddr' st).map Prod.fst

/-- TPI-001 #3: after unmap, lookup fails with translationFault. -/
theorem vspaceLookup_after_unmap
    (st st' : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (hInv : vspaceInvariantBundle st)
    (hStep : vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    vspaceLookup asid vaddr st' = .error .translationFault

/-- TPI-001 #4: unmap at vaddr does not affect lookup at different vaddr'. -/
theorem vspaceLookup_unmap_other
    (st st' : SystemState) (asid : SeLe4n.ASID) (vaddr vaddr' : SeLe4n.VAddr)
    (hNe : vaddr ≠ vaddr')
    (hInv : vspaceInvariantBundle st)
    (hStep : vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    (vspaceLookup asid vaddr' st').map Prod.fst = (vspaceLookup asid vaddr' st).map Prod.fst
```

---

## Issue TPI-D06 (CLOSED) — Waiting-list uniqueness invariant

- **Audit mapping:** `AUDIT_v0.11.0.md` F-12 (Medium), recommendation 9.3 #8.
- **Workstream:** WS-D4.
- **Resolution:** Double-wait prevention implemented in `notificationWait` via `waiter ∈ ntfn.waitingThreads`
  check (returns `alreadyWaiting` error). `uniqueWaiters` invariant defined and preservation theorem
  proved without `sorry`. Decomposition lemmas (`notificationWait_badge_path_notification`,
  `notificationWait_wait_path_notification`) track the notification object through `storeTcbIpcState`
  and `removeRunnable`. Helper lemmas: `storeTcbIpcState_preserves_objects_ne`,
  `storeTcbIpcState_preserves_notification`, `removeRunnable_preserves_objects`.

Closed theorem obligation:

```lean
theorem notificationWait_preserves_uniqueWaiters
    (waiter : ThreadId) (notifId : ObjId)
    (st st' : SystemState)
    (result : Option Badge)
    (hWait : notificationWait notifId waiter st = .ok (result, st'))
    (hUniq : uniqueWaiters notifId st) :
    uniqueWaiters notifId st'
```

---

## Issue TPI-D07 (IN PROGRESS) — Service dependency acyclicity invariant

- **Audit mapping:** `AUDIT_v0.11.0.md` F-07 (Medium), recommendation 9.3 #7.
- **Workstream:** WS-D4.
- **Risk 0 resolution:** Strategy B adopted. The vacuous BFS-based `serviceDependencyAcyclic` definition
  has been corrected to use declarative non-trivial-path acyclicity. Three Layer 0 definitions added:
  `serviceEdge` (direct dependency edge), `serviceReachable` (reflexive-transitive closure),
  `serviceHasNontrivialPath` (path of length ≥ 1). The preservation theorem's `sorry` now represents
  a genuine (non-vacuous) proof obligation requiring BFS soundness (Layer 2) and edge-insertion analysis
  (Layer 3). See [`05_RISK_REGISTER.md`](./execution_plans/05_RISK_REGISTER.md#risk-0--vacuous-invariant-definition-highest--resolved).
- **Execution plan:** Multi-milestone plan (M0–M5) documented in
  [`docs/audits/execution_plans/`](./execution_plans/00_INDEX.md). M0 (baseline lock) is in progress.
- **Current status:** Cycle detection implemented and operational (`serviceRegisterDependency` rejects
  cyclic edges via `serviceHasPathTo` BFS). Acyclicity invariant corrected to declarative form.
  Preservation theorem statement exists but uses `sorry` for the BFS soundness + edge-insertion
  argument. The operational cycle detection is runtime-correct (validated by executable tests).
  TPI-D07 proof infrastructure plan comment block added to `Invariant.lean`.
- **Remaining obligation:** Replace `sorry` in `serviceRegisterDependency_preserves_acyclicity` with a
  formal proof. Requires:
  1. Layer 1 (M1): Structural lemmas for `serviceEdge`, `serviceReachable`, store-interaction.
  2. Layer 2 (M2): BFS soundness — `serviceHasPathTo` false implies no `serviceReachable` path.
  3. Layer 3 (M3): Edge-insertion analysis — acyclicity preserved when adding `svcId → depId` edge
     given no pre-state path from `depId` to `svcId`.

Partially closed theorem obligation (uses `sorry`):

```lean
-- Corrected invariant (Strategy B — declarative acyclicity)
def serviceDependencyAcyclic (st : SystemState) : Prop :=
  ∀ sid, ¬ serviceHasNontrivialPath st sid sid

theorem serviceRegisterDependency_preserves_acyclicity
    (svcId depId : ServiceId) (st st' : SystemState)
    (hReg : serviceRegisterDependency svcId depId st = .ok ((), st'))
    (hAcyc : serviceDependencyAcyclic st) :
    serviceDependencyAcyclic st' := by
  ...  -- proof structure exists; BFS soundness + edge insertion uses sorry
```

---

## Integration requirements before closure

Each issue closes only when all are true:

1. theorem is implemented without `sorry` in production proof surface,
2. tiered checks (`test_tier3_invariant_surface.sh`, plus relevant tier 2/4 evidence) are updated,
3. `AUDIT_v0.11.0_WORKSTREAM_PLAN.md` status table is updated from planned to completed for the corresponding WS-D objective,
4. claim-evidence index updated to reflect new theorem.

## Cross-reference to WS-C obligations

| WS-C Issue | Status | Carried to WS-D |
|---|---|---|
| TPI-001 (VSpace round-trip theorems) | CLOSED | Resolved by TPI-D05 (four round-trip theorems proved) |
| TPI-002 (IF noninterference seed) | CLOSED | Extended by TPI-D01, TPI-D02, TPI-D03 |
