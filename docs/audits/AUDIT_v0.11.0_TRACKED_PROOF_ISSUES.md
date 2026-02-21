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

## Issue TPI-D06 (OPEN) — Waiting-list uniqueness invariant

- **Audit mapping:** `AUDIT_v0.11.0.md` F-12 (Medium), recommendation 9.3 #8.
- **Workstream:** WS-D4.
- **Current problem:** No double-wait prevention exists. A thread can be added to a notification waiting list multiple times.

Required theorem obligation:

```lean
/-- After notificationWait succeeds, the waiting list contains no
    duplicate thread IDs. -/
theorem notificationWait_preserves_uniqueWaiters
    (tid : ThreadId) (notifId : ObjId)
    (st st' : SystemState)
    (hWait : notificationWait tid notifId st = .ok ((), st'))
    (hUniq : uniqueWaiters notifId st) :
    uniqueWaiters notifId st' := by
  sorry  -- proof obligation
```

---

## Issue TPI-D07 (OPEN) — Service dependency acyclicity invariant

- **Audit mapping:** `AUDIT_v0.11.0.md` F-07 (Medium), recommendation 9.3 #7.
- **Workstream:** WS-D4.
- **Current problem:** Service dependency cycles are not prevented. No cycle detection at registration time.

Required theorem obligation:

```lean
/-- After a successful dependency registration, the dependency graph
    remains acyclic. -/
theorem serviceRegisterDependency_preserves_acyclicity
    (svcId depId : ServiceId) (st st' : SystemState)
    (hReg : serviceRegisterDependency svcId depId st = .ok ((), st'))
    (hAcyc : serviceDependencyAcyclic st) :
    serviceDependencyAcyclic st' := by
  sorry  -- proof obligation
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
