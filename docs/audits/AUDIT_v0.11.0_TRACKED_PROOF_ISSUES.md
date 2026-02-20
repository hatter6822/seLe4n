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
- **Resolution:** Implemented four badge-safety theorems in `SeLe4n/Kernel/Capability/Invariant.lean`. The proof leverages the existing `mintDerivedCap_attenuates` / `cspaceMint_child_attenuates` foundations to show that (1) badge override cannot change the derived capability's target (authority scope), and (2) badge override cannot escalate rights beyond the parent's rights. No `sorry` debt.

Closed theorem obligations:

```lean
/-- mintDerivedCap preserves the parent target regardless of badge override. -/
theorem mintDerivedCap_target_preserved
    (parent child : Capability)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (hMint : mintDerivedCap parent rights badge = .ok child) :
    child.target = parent.target

/-- mintDerivedCap attenuates rights regardless of badge override. -/
theorem mintDerivedCap_rights_attenuated
    (parent child : Capability)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (hMint : mintDerivedCap parent rights badge = .ok child) :
    ∀ right, right ∈ child.rights → right ∈ parent.rights

/-- Badge override in cspaceMint cannot escalate rights. -/
theorem cspaceMint_badge_override_rights_attenuated
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (hStep : cspaceMint src dst rights badge st = .ok ((), st')) :
    ∃ parent child,
      cspaceLookupSlot src st = .ok (parent, st) ∧
      cspaceLookupSlot dst st' = .ok (child, st') ∧
      (∀ right, right ∈ child.rights → right ∈ parent.rights)

/-- Badge override in cspaceMint cannot change the derived target. -/
theorem cspaceMint_badge_override_target_preserved
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (hStep : cspaceMint src dst rights badge st = .ok ((), st')) :
    ∃ parent child,
      cspaceLookupSlot src st = .ok (parent, st) ∧
      cspaceLookupSlot dst st' = .ok (child, st') ∧
      child.target = parent.target
```

---

## Issue TPI-D05 (CLOSED) — VSpace successful-operation invariant preservation

- **Audit mapping:** `AUDIT_v0.11.0.md` F-08 (Medium), recommendation 9.2 #6.
- **Workstream:** WS-D3.
- **Carries forward:** TPI-001 from `AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`.
- **Resolution:** Implemented invariant preservation and round-trip theorems in `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean`, with supporting helper lemmas in `SeLe4n/Model/Object.lean` (VSpaceRoot helpers) and `SeLe4n/Kernel/Architecture/VSpace.lean` (resolveAsidRoot characterization). No `sorry` debt.

Closed invariant preservation obligations:

```lean
/-- A successful vspaceMapPage preserves the VSpace invariant bundle. -/
theorem vspaceMapPage_success_preserves_vspaceInvariantBundle
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (hInv : vspaceInvariantBundle st)
    (hStep : vspaceMapPage asid vaddr paddr st = .ok ((), st')) :
    vspaceInvariantBundle st'

/-- A successful vspaceUnmapPage preserves the VSpace invariant bundle. -/
theorem vspaceUnmapPage_success_preserves_vspaceInvariantBundle
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (hInv : vspaceInvariantBundle st)
    (hStep : vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    vspaceInvariantBundle st'
```

Closed TPI-001 round-trip obligations:

```lean
theorem vspaceLookup_after_map ...   -- map then lookup same vaddr → mapped paddr
theorem vspaceLookup_map_other ...   -- map vaddr does not affect lookup of vaddr' ≠ vaddr
theorem vspaceLookup_after_unmap ... -- unmap then lookup → translationFault
theorem vspaceLookup_unmap_other ... -- unmap vaddr does not affect lookup of vaddr' ≠ vaddr
```

Supporting infrastructure:

```lean
-- VSpaceRoot helpers (Model/Object.lean):
theorem VSpaceRoot.mapPage_asid_eq ...
theorem VSpaceRoot.unmapPage_asid_eq ...
theorem VSpaceRoot.lookup_eq_none_not_mem ...
theorem VSpaceRoot.mapPage_noVirtualOverlap ...
theorem VSpaceRoot.unmapPage_noVirtualOverlap ...
theorem VSpaceRoot.lookup_mapPage_ne ...
theorem VSpaceRoot.lookup_unmapPage_ne ...

-- resolveAsidRoot characterization (Architecture/VSpace.lean):
theorem resolveAsidRoot_some_implies ...
theorem resolveAsidRoot_of_unique_root ...
theorem storeObject_objectIndex_eq_of_mem ...
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
| TPI-001 (VSpace round-trip theorems) | CLOSED | Closed via TPI-D05 |
| TPI-002 (IF noninterference seed) | CLOSED | Extended by TPI-D01, TPI-D02, TPI-D03 |
