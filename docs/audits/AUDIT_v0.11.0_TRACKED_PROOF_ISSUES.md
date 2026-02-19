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
- **Resolution:** Proved as `chooseThread_preserves_lowEquivalent` in `SeLe4n/Kernel/InformationFlow/Invariant.lean`. The proof follows trivially from `chooseThread_preserves_state` (scheduler's `chooseThread` is read-only and does not modify system state). Tier 3 anchor added.

---

## Issue TPI-D02 (CLOSED) — Non-interference preservation for capability operations

- **Audit mapping:** `AUDIT_v0.11.0.md` F-05 (High), recommendation 9.2 #4.
- **Workstream:** WS-D2.
- **Resolution:** `cspaceMint_preserves_lowEquivalent` proved in `SeLe4n/Kernel/InformationFlow/Invariant.lean`. The proof decomposes `cspaceMint` via `cspaceMint_ok_as_insertSlot`, then shows the destination CNode is the only modified object. For observers that cannot see the destination CNode, the projected state is unchanged. `cspaceRevoke` noninterference was not required by the minimum acceptance criteria and remains available for future IF-M3 work. Tier 3 anchor added.

---

## Issue TPI-D03 (CLOSED) — Non-interference preservation for lifecycle operations

- **Audit mapping:** `AUDIT_v0.11.0.md` F-05 (High), recommendation 9.2 #4.
- **Workstream:** WS-D2.
- **Resolution:** `lifecycleRetypeObject_preserves_lowEquivalent` proved in `SeLe4n/Kernel/InformationFlow/Invariant.lean`. The proof uses `lifecycleRetypeObject_ok_as_storeObject` to reduce to the generic `storeObject_preserves_lowEquivalent` unwinding lemma. Additionally, `serviceRestart_preserves_lowEquivalent` was proved (exceeding the minimum requirement), chaining through `serviceStop` + `serviceStart` via `serviceRestart_ok_implies_staged_steps`. Tier 3 anchors added for both.

---

## Issue TPI-D04 (OPEN) — Badge-override safety in cspaceMint

- **Audit mapping:** `AUDIT_v0.11.0.md` F-06 (Medium), recommendation 9.2 #5.
- **Workstream:** WS-D3.
- **Current problem:** `cspaceMint` allows badge override from parent. No proof that this cannot enable privilege escalation.

Required theorem obligations:

```lean
/-- A minted capability's rights are a subset of the parent's rights,
    regardless of badge override. -/
theorem cspaceMint_attenuates_rights
    (authority target : ObjId) (srcSlot destSlot : Slot)
    (newRights : CapRights) (newBadge : Badge)
    (st st' : SystemState)
    (hMint : cspaceMint authority target srcSlot destSlot newRights newBadge st = .ok ((), st'))
    (parentCap : Capability)
    (hSrc : lookupSlot target srcSlot st = some parentCap) :
    newRights.isSubsetOf parentCap.rights = true := by
  sorry  -- proof obligation

/-- Badge override in mint does not grant access to objects
    outside the parent capability's authority scope. -/
theorem cspaceMint_badge_no_escalation
    (authority target : ObjId) (srcSlot destSlot : Slot)
    (newRights : CapRights) (newBadge : Badge)
    (st st' : SystemState)
    (hMint : cspaceMint authority target srcSlot destSlot newRights newBadge st = .ok ((), st'))
    (derivedCap : Capability)
    (hDest : lookupSlot target destSlot st' = some derivedCap) :
    derivedCap.targetId = (lookupSlot target srcSlot st).get!.targetId := by
  sorry  -- proof obligation
```

---

## Issue TPI-D05 (OPEN) — VSpace successful-operation invariant preservation

- **Audit mapping:** `AUDIT_v0.11.0.md` F-08 (Medium), recommendation 9.2 #6.
- **Workstream:** WS-D3.
- **Carries forward:** TPI-001 from `AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`.
- **Current problem:** Only error-case preservation is proven for `vspaceMapPage` and `vspaceUnmapPage`. No theorem proves a *successful* operation preserves the invariant bundle.

Required theorem obligations:

```lean
/-- A successful vspaceMapPage preserves the VSpace invariant bundle. -/
theorem vspaceMapPage_success_preserves_invariantBundle
    (asid : ASID) (vaddr : VAddr) (paddr : PAddr)
    (st st' : SystemState)
    (hMap : vspaceMapPage asid vaddr paddr st = .ok ((), st'))
    (hInv : vspaceInvariantBundle st) :
    vspaceInvariantBundle st' := by
  sorry  -- proof obligation

/-- A successful vspaceUnmapPage preserves the VSpace invariant bundle. -/
theorem vspaceUnmapPage_success_preserves_invariantBundle
    (asid : ASID) (vaddr : VAddr)
    (st st' : SystemState)
    (hUnmap : vspaceUnmapPage asid vaddr st = .ok ((), st'))
    (hInv : vspaceInvariantBundle st) :
    vspaceInvariantBundle st' := by
  sorry  -- proof obligation
```

Additionally, close the TPI-001 round-trip obligations from WS-C:

```lean
/-- Mapping a page and then looking it up yields the mapped address. -/
theorem vspaceLookup_after_map
    (asid : ASID) (vaddr : VAddr) (paddr : PAddr)
    (st st' : SystemState)
    (hMap : vspaceMapPage asid vaddr paddr st = .ok ((), st')) :
    vspaceLookup asid vaddr st' = .ok (paddr, st') := by
  sorry  -- proof obligation

/-- Mapping vaddr does not affect lookup of a different vaddr'. -/
theorem vspaceLookup_map_other
    (asid : ASID) (vaddr vaddr' : VAddr) (paddr : PAddr)
    (st st' : SystemState)
    (hNe : vaddr ≠ vaddr')
    (hMap : vspaceMapPage asid vaddr paddr st = .ok ((), st')) :
    vspaceLookup asid vaddr' st' = vspaceLookup asid vaddr' st := by
  sorry  -- proof obligation

/-- After unmap, lookup fails with translationFault. -/
theorem vspaceLookup_after_unmap
    (asid : ASID) (vaddr : VAddr)
    (st st' : SystemState)
    (hUnmap : vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    vspaceLookup asid vaddr st' = .error .translationFault := by
  sorry  -- proof obligation
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
| TPI-001 (VSpace round-trip theorems) | OPEN | Carried to TPI-D05 |
| TPI-002 (IF noninterference seed) | CLOSED | Extended and closed by TPI-D01, TPI-D02, TPI-D03 (all CLOSED in WS-D2) |
