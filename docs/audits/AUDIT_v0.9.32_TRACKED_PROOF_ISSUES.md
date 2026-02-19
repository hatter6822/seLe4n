# AUDIT v0.9.32 — Tracked Proof Issues and Follow-up Obligations

This document tracks proof obligations intentionally deferred while WS-C1..WS-C8 are executed.

Status legend:

- `OPEN`: accepted obligation, not yet implemented.
- `IN PROGRESS`: implementation/proof branch exists.
- `CLOSED`: theorem is implemented in Lean and covered by tiered tests/anchors.

## Issue TPI-001 (OPEN) — Replace tautological VSpace determinism theorem with round-trip properties

- **Audit mapping:** `AUDIT_v0.9.32.md` Immediate recommendation #4.
- **Current problem:** `vspaceLookup_deterministic` is tautological (`f x = f x`) and does not establish semantic correctness.
- **WS-C3 completion action (implemented):**
  1. removed the tautological `_deterministic` theorem,
  2. added a module docstring in the VSpace proof module explaining that determinism of pure Lean functions is a meta-property and should not be encoded as tautological object-level theorems,
  3. replace with explicit semantic theorems below.

Required theorem obligations to implement:

```lean
/-- Mapping a page and then looking it up yields the mapped address. -/
theorem vspaceLookup_after_map
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (st st' : SystemState)
    (hMap : vspaceMapPage asid vaddr paddr st = .ok ((), st')) :
    vspaceLookup asid vaddr st' = .ok (paddr, st') := by
  sorry  -- actual proof obligation

/-- Mapping vaddr does not affect lookup of a different vaddr'. -/
theorem vspaceLookup_map_other
    (asid : SeLe4n.ASID) (vaddr vaddr' : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (st st' : SystemState)
    (hNe : vaddr ≠ vaddr')
    (hMap : vspaceMapPage asid vaddr paddr st = .ok ((), st')) :
    vspaceLookup asid vaddr' st' = vspaceLookup asid vaddr' st := by
  sorry  -- actual proof obligation

/-- After unmap, lookup fails with translationFault. -/
theorem vspaceLookup_after_unmap
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (st st' : SystemState)
    (hUnmap : vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    vspaceLookup asid vaddr st' = .error .translationFault := by
  sorry  -- actual proof obligation
```

## Issue TPI-002 (CLOSED) — Replace tautological IF projection determinism theorem with noninterference preservation theorem

- **Audit mapping:** `AUDIT_v0.9.32.md` Immediate recommendation #4 and #5.
- **Current problem:** `projectState_deterministic` is tautological and does not prove security preservation.
- **WS-C3/WS-C5 staged action:**
  1. removed the tautological `_deterministic` theorem,
  2. WS-C3 added a module docstring in the InformationFlow projection/proof module clarifying determinism-as-meta-property,
  3. implement operation-level noninterference preservation theorem(s), beginning with endpoint send.

Closure evidence (WS-C5):

- `endpointSend_preserves_lowEquivalent` implemented in `SeLe4n/Kernel/InformationFlow/Invariant.lean` without `sorry`.
- Service projection now filters by observer clearance via `serviceLabelOf` + `serviceObservable`.
- Tier-2 negative suite (`information_flow_suite`) updated to exercise service-visibility filtering and theorem witness.

Required theorem obligation to implement (historical target, now satisfied by the theorem above):

```lean
/-- If two states are indistinguishable to an observer, then running
    a high-domain operation leaves them indistinguishable.
    This is the actual noninterference property. -/
theorem endpointSend_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (tid : SeLe4n.ThreadId) (epId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge)
    (s₁ s₂ : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hHigh : ¬ threadObservable ctx observer tid)  -- sender is above observer
    (hR1 : ∃ r1, endpointSend tid epId badge s₁ = .ok r1)
    (hR2 : ∃ r2, endpointSend tid epId badge s₂ = .ok r2) :
    lowEquivalent ctx observer
      (endpointSend tid epId badge s₁).toOption.get!.2
      (endpointSend tid epId badge s₂).toOption.get!.2 := by
  sorry  -- this is where the real security proof lives
```

## Integration requirements before closure

Each issue closes only when all are true:

1. theorem is implemented without `sorry` in production proof surface,
2. old tautological theorem is removed or explicitly marked historical/deprecated with migration notes,
3. tiered checks (`test_tier3_invariant_surface.sh`, plus relevant tier 2/4 evidence) are updated,
4. `AUDIT_v0.9.32_WORKSTREAM_PLAN.md` status table is updated from planned to completed for the corresponding WS-C objective.
