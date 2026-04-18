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

### AK7-I.cascade — `Capability.requireNotNull` consumer migration

**Baseline (v0.29.13):** Predicate + gate helper defined in
`Model/Object/Types.lean`:

- `Capability.isNull` / `isNotNull` predicates
- `Capability.null` canonical null-cap constant
- `Capability.requireNotNull : Capability → Option Capability`
- Correctness theorems (`requireNotNull_isSome_iff`, `requireNotNull_null`,
  `requireNotNull_some_not_null`)

**Cascade (v1.1):** Route capability-using entry points through
`requireNotNull` to reject `seL4_CapNull` sentinel caps at the ABI
boundary:

- `cspaceInvoke` (`Capability/Operations.lean`)
- `cspaceMint` (`Capability/Operations.lean`)
- `cspaceCopy` (`Capability/Operations.lean`)

**Why deferred:** Wiring `requireNotNull` at every entry point cascades
through capability-preservation proofs and alters error-propagation
shapes. The predicate availability is sufficient for incremental
adoption.

---

## Non-AK7 Deferred Items

See `AUDIT_v0.29.0_WORKSTREAM_PLAN.md` §14.3 "Escape valves" for
portfolio-wide cascades deferred to WS-V (hardware integration) and
post-1.0 hygiene passes.
