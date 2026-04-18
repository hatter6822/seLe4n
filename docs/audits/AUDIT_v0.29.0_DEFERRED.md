# AUDIT v0.29.0 Deferred Items — AK7 Cascade Tracking

This document tracks deferred items from the v0.29.0 audit workstream
(WS-AK) that land as baseline in v1.0.0 but require cascading consumer
migration in v1.1.

**Purpose:** The initial WS-AK phases (AK1–AK7) land structural changes
in a minimally-invasive way to keep the proof cascade bounded. Consumer
migration of those structural changes to the hundreds of internal call
sites is a separate, incremental effort that does not block the v1.0.0
release.

---

## AK7 Cascade Items

### AK7-E.cascade — `ValidObjId` / `ValidThreadId` / `ValidSchedContextId` / `ValidCPtr` consumer migration

**Baseline (v0.29.13):** Subtypes defined in `Prelude.lean`:

- `ValidObjId := { o : ObjId // o ≠ ObjId.sentinel }`
- `ValidThreadId := { t : ThreadId // t ≠ ThreadId.sentinel }`
- `ValidSchedContextId := { s : SchedContextId // s ≠ SchedContextId.sentinel }`
- `ValidCPtr := { c : CPtr // c ≠ CPtr.sentinel }`

Plus per-type `toValid`/`ofValid`/`toValid?` conversion API and bridge
theorems (`ObjId.valid_of_ne_sentinel`, `ThreadId.toValid?_isSome_iff`).

**Cascade (v1.1):** Migrate the 10 highest-risk syscall entry points to
accept `Valid*Id` at their signatures:

- `suspendThread` (`Lifecycle/Suspend.lean`)
- `resumeThread` (`Lifecycle/Suspend.lean`)
- `setPriorityOp` (`SchedContext/PriorityManagement.lean`)
- `setMCPriorityOp` (`SchedContext/PriorityManagement.lean`)
- `setIPCBufferOp` (`Architecture/IpcBufferValidation.lean`)
- `schedContextConfigure` (`SchedContext/Operations.lean`)
- `schedContextBind` (`SchedContext/Operations.lean`)
- `schedContextUnbind` (`SchedContext/Operations.lean`)
- `vspaceMapPage` (`API.lean`)
- `vspaceUnmapPage` (`API.lean`)

Plus the remaining ~290 internal call sites that currently use raw
`ObjId.ofNat`-style construction.

**Why deferred:** Full migration cascades through the cross-subsystem
preservation proofs. The 10-handler baseline covers the caller-exposed
attack surface; in-kernel propagation of raw IDs remains safe under
`apiInvariantBundle` (see `AK7-E.1`/`AK7-E.2` rationale in plan §10).

---

### AK7-F.cascade — `KindedObjId` consumer migration

**Baseline (v0.29.13):** `ObjectKind` 9-variant enum + `KindedObjId`
parallel structure defined in `Prelude.lean`:

- `ObjectKind := .unknown | .thread | .schedContext | .endpoint | .notification | .cnode | .vspaceRoot | .untyped | .service`
- `KindedObjId` carries `val : Nat` + `kind : ObjectKind`
- `ThreadId.toKinded` / `SchedContextId.toKinded` tag canonically
- `KindedObjId.ne_of_kind_ne` + `ThreadId.toKinded_ne_schedContext_toKinded`
  witness structural disjointness regardless of numeric value

The base `ObjId` struct is NOT modified in this baseline per the plan's
§Risk-mitigation clause — adding a `kind : ObjectKind` field to `ObjId`
would cascade through ~300 preservation proofs. Consumers that need
disjointness promote via `.toKinded`; existing raw-`ObjId` code continues
to work unchanged.

**Cascade (v1.1):** Replace `objects.get? (obj.toObjId)` patterns with
`objects.getKinded? obj` that verifies the stored object's kind matches
the query's tag. Expected ~300 call sites across `IPC/`, `Scheduler/`,
`Capability/`, `Lifecycle/`, `SchedContext/`.

**Why deferred:** AJ2-D (`typedIdDisjointness`) non-escalation proof
already covers the attack surface at runtime. The baseline disjointness
theorems are sufficient for ad-hoc proof obligations; cascade is a
hygiene pass that does not affect correctness.

---

### AK7-I.cascade — `Capability.requireNotNull` consumer migration [RESOLVED v1.0.0 / WS-AL AL1]

**Baseline (v0.29.13):** Predicate + gate helper defined in
`Model/Object/Types.lean`:

- `Capability.isNull` / `isNotNull` predicates
- `Capability.null` canonical null-cap constant
- `Capability.requireNotNull : Capability → Option Capability`
- Correctness theorems (`requireNotNull_isSome_iff`, `requireNotNull_null`,
  `requireNotNull_some_not_null`)

**Resolution (v1.0.0, WS-AL phase AL1):** Null-cap guard wired at the
three capability-using entry points that previously accepted
`Capability.null` without distinguishing it from a valid non-null cap.

| Entry point | Guard sub-task | Commit |
|-------------|----------------|--------|
| `cspaceMint`   | AL1-A | e03d6d3 |
| `cspaceCopy`   | AL1-B | c4d4462 |
| `cspaceMove`   | AL1-C | ab7dc07 |

**Note on `cspaceInvoke`:** The original DEFERRED listing referenced a
`cspaceInvoke` operation. That operation does not exist in the
codebase; the reference was a design aspiration. The three operations
actually affected are mint/copy/move (all listed above).

**Bridge lemma (AL1-D.1, committed in e03d6d3):**
`Capability.requireNotNull_some_eq` (`Model/Object/Types.lean`) — if
`cap.requireNotNull = some cap'`, then `cap' = cap`. Used by every
downstream preservation proof that unfolds through the new match.

**Preservation proofs patched:**
- `Kernel/Capability/Invariant/Authority.lean` — `cspaceMint_attenuates`,
  `cspaceMint_badge_stored`.
- `Kernel/Capability/Invariant/Preservation.lean` —
  `cspaceMint_preserves_capabilityInvariantBundle`,
  `cspaceMint_preserves_badgeWellFormed`,
  `cspaceMint_preserves_cdtMapsConsistent`,
  `cspaceCopy_preserves_capabilityInvariantBundle`,
  `cspaceMove_preserves_capabilityInvariantBundle`.
- `Kernel/InformationFlow/Invariant/Helpers.lean` —
  `cspaceMint_preserves_lowEquivalent`.
- `Kernel/InformationFlow/Invariant/Operations.lean` —
  `cspaceCopy_preserves_projection`,
  `cspaceMove_preserves_projection`.
- `Kernel/InformationFlow/Invariant/Composition.lean` —
  `niStepInd` cspaceMint arm.

**Regression coverage (AL1-E, commit a6c2dd1):** Three end-to-end
tests in `tests/Ak7RegressionSuite.lean`
(`al1E_01_mint_from_null_rejected`,
`al1E_02_copy_from_null_rejected`,
`al1E_03_move_from_null_rejected`) build a minimal state with
`Capability.null` in slot 0 and assert `.error .invalidCapability` at
each of the three operations. Suite size 38 → 41.

**Gate:** `lake build` (260 jobs) + `ak7_regression_suite` (41 checks)
+ `ak7_cascade_check_monotonic.sh` PASS + zero sorry/axiom.

---

## Non-AK7 Deferred Items

See `AUDIT_v0.29.0_WORKSTREAM_PLAN.md` §14.3 "Escape valves" for
portfolio-wide cascades deferred to WS-V (hardware integration) and
post-1.0 hygiene passes.
