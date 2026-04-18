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

### AK7-E.cascade — `Valid{Obj,Thread,SchedContext,C}Ptr` consumer migration [RESOLVED v0.29.14 / WS-AL AL7]

**Baseline (v0.29.13):** Subtypes defined in `Prelude.lean`:

- `ValidObjId := { o : ObjId // o ≠ ObjId.sentinel }`
- `ValidThreadId := { t : ThreadId // t ≠ ThreadId.sentinel }`
- `ValidSchedContextId := { s : SchedContextId // s ≠ SchedContextId.sentinel }`
- `ValidCPtr := { c : CPtr // c ≠ CPtr.sentinel }`

Plus per-type `toValid`/`ofValid`/`toValid?` conversion API and bridge
theorems (`ObjId.valid_of_ne_sentinel`, `ThreadId.toValid?_isSome_iff`).

**Resolution (v0.29.14, WS-AL phase AL7, commit c2cc60d):** The caller-exposed
attack surface for sentinel-ID injection is closed at the dispatch
boundary in `SeLe4n/Kernel/API.lean`. Two new private helpers added
near line 432:

- `validateThreadIdArg : ThreadId → Except KernelError ValidThreadId` —
  lifts via `toValid?`; returns `.error .invalidArgument` on sentinel.
- `validateSchedContextIdArg : SchedContextId → Except KernelError ValidSchedContextId` —
  mirror for SchedContextId.

Both are wired at every capability-only dispatch arm that accepts a
ThreadId or SchedContextId argument:

| Dispatch arm              | Sub-task | Guards                      |
|---------------------------|----------|-----------------------------|
| `.tcbSuspend`             | AL7-B    | target tid                  |
| `.tcbResume`              | AL7-C    | target tid                  |
| `.tcbSetPriority`         | AL7-D    | caller tid + target tid     |
| `.tcbSetMCPriority`       | AL7-E    | caller tid + target tid     |
| `.tcbSetIPCBuffer`        | AL7-F    | target tid                  |
| `.schedContextConfigure`  | AL7-G    | target scId                 |
| `.schedContextBind`       | AL7-H    | target scId + decoded tid   |
| `.schedContextUnbind`     | AL7-I    | target scId                 |

Validation fires BEFORE any handler entry, so sentinel IDs never reach
downstream object-store lookups. Defense-in-depth is preserved — the
existing graceful `.objectNotFound` at lookup time still fires for
non-sentinel-but-nonexistent IDs.

**Note on `vspaceMapPage` / `vspaceUnmapPage`:** The original listing
included these as cascade targets. These operations take `ASID` /
`VAddr`, not `ObjId`; neither has a sentinel convention (ASID 0 is the
valid kernel root). They are outside the AK7-E attack surface.

**Handler signature tightening (Lifecycle/SchedContext to `Valid*Id`)**:
Signature changes to `suspendThread`/`resumeThread`/`setPriorityOp`/
`setMCPriorityOp`/`setIPCBufferOp`/`schedContextConfigure`/`Bind`/`Unbind`
would cascade through 300+ call sites and their preservation proofs.
This is HYGIENE, not security — AL7's dispatch guards close the attack
surface. Signature tightening is tracked for post-patch work as
**AK7-E.hygiene** (non-gating).

---

### AK7-F.cascade — `KindedObjId` consumer migration [RESOLVED v0.29.14 / WS-AL AL6]

**Baseline (v0.29.13):** `ObjectKind` 9-variant enum + `KindedObjId`
parallel structure defined in `Prelude.lean`:

- `ObjectKind := .unknown | .thread | .schedContext | .endpoint | .notification | .cnode | .vspaceRoot | .untyped | .service`
- `KindedObjId` carries `val : Nat` + `kind : ObjectKind`
- `ThreadId.toKinded` / `SchedContextId.toKinded` tag canonically
- `KindedObjId.ne_of_kind_ne` + `ThreadId.toKinded_ne_schedContext_toKinded`
  witness structural disjointness regardless of numeric value

**Resolution (v0.29.14, WS-AL phases AL2 + AL6, commits af90780..5287522, 6b44dd5, 4d5cc8b):**
The silent cross-variant overwrite hole is closed at the object-store
level via a kind-checked wrapper, backed by a complete helper layer.

**AL2-A helper layer (SeLe4n/Model/State.lean):** Five per-variant
lookup helpers in the `SystemState` namespace:

- `getTcb?         : ThreadId       → Option TCB`
- `getSchedContext? : SchedContextId → Option SeLe4n.Kernel.SchedContext`
- `getEndpoint?    : ObjId          → Option Endpoint`
- `getNotification? : ObjId         → Option Notification`
- `getUntyped?     : ObjId          → Option UntypedObject`

Plus 23 discrimination lemmas: 10 cross-variant rejection lemmas for
`getTcb?` (exhaustive over all non-TCB variants + absent case), 4 mirror
rejection lemmas for the other helpers, 5 `getX?_eq_some_iff`
bidirectional unfolding lemmas, and `getTcb?_eq_none_iff` complement.

**AL6-A kind-guard (commit 4d5cc8b, SeLe4n/Model/State.lean):**
`storeObjectKindChecked : ObjId → KernelObject → Kernel Unit` added
as a defense-in-depth wrapper over the legacy `storeObject`:

- Fresh id (pre-state `objects[id]? = none`): delegates to `storeObject`.
- Existing id with matching `objectType`: delegates to `storeObject`.
- Existing id with different `objectType`: returns
  `.error .invalidObjectType` WITHOUT state mutation (Except.error is
  stateless by construction).

Three substantive correctness theorems proven without `sorry`:
`_fresh_eq_storeObject`, `_sameKind_eq_storeObject`,
`_crossKind_rejected`.

New `KernelError.invalidObjectType` variant (discriminant 49) added to
Lean and kept in sync with the Rust ABI: `sele4n-types/src/error.rs`
`InvalidObjectType = 49` + `from_u32` arm + `Display` arm; conformance
tests in `sele4n-abi/tests/conformance.rs` extended from the 0..=48
range to 0..=49 (5 tests updated); `sele4n-types` unit tests
(`from_u32_roundtrip`, `from_u32_out_of_range`, `discriminant_ordering`,
`lean_rust_correspondence`, `unknown_kernel_error_sentinel`,
`new_variants_discriminants`) extended accordingly. Cargo workspace
remains at 415 passing tests.

**Regression coverage:** 5 new AL6 runtime tests
(`al6_01..05`) in `tests/Ak7RegressionSuite.lean` cover the four paths
(fresh, same-kind, TCB→SC cross-kind, SC→TCB cross-kind) plus the
rejection-preserves-state property. Plus 8 AL2 helper tests
(`al2C_01..08`) verifying per-variant discrimination and round-trip
stores. Plus 5 AL10 integration tests (`al10_01..05`) exercising the
three cascades end-to-end.

**Consumer migration (AK7-F.hygiene)**: Replacing the 304 raw
`match st.objects[id]? with | some (.variant x) => ...` call sites
with the new typed helpers is a hygiene pass that improves readability
without changing semantics. AL6's kind-guard closes the security hole
at the object-store level; consumer sites remain safe under the
existing `apiInvariantBundle`. The migration is tracked for post-patch
work as **AK7-F.hygiene** (non-gating).

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

## AK7 cascade closure summary (v0.29.14)

All three AK7 cascades are structurally closed at their primary attack
surfaces. The three `AK7-*.cascade` rows above are each marked
**RESOLVED** with commit SHAs.

| Cascade | Resolution phase | Attack surface closed at | Commit(s)             |
|---------|------------------|--------------------------|-----------------------|
| AK7-I   | WS-AL AL1        | cspaceMint/Copy/Move     | e03d6d3, c4d4462, ab7dc07 |
| AK7-F   | WS-AL AL6        | storeObjectKindChecked   | 4d5cc8b               |
| AK7-E   | WS-AL AL7        | dispatchCapabilityOnly   | c2cc60d               |

Four residual hygiene items remain tracked for post-patch work. All
are **non-gating** — the three primary attack surfaces (mint/copy/move
null-cap, object-store cross-variant overwrite, dispatch sentinel IDs)
are already closed by AL1 / AL6 / AL7 structurally.

- **AK7-E.hygiene**: tightening the 5+ Lifecycle / SchedContext /
  IpcBufferValidation handler signatures from raw `ThreadId` /
  `SchedContextId` to the `Valid*Id` subtypes. AL7's dispatch-boundary
  guards close the attack surface independently; handler signature
  tightening is readability hygiene. Cascade size: ~240+ internal
  call sites.

- **AK7-F.reader.hygiene**: migrating the 304 raw
  `match st.objects[id]? with | some (.variant x) => ...` call sites
  to use the AL2-A typed helpers (`getTcb?`, `getSchedContext?`,
  `getEndpoint?`, `getNotification?`, `getUntyped?`). Reader-side
  refactoring for readability. AL6's `storeObjectKindChecked` closes
  the silent overwrite hole at the write-side independently.

- **AK7-F.writer.hygiene** (NEW, surfaced by v0.29.14 post-delivery audit):
  wiring `storeObjectKindChecked` at in-place `storeObject` call sites
  where the caller's precondition guarantees same-kind updates (TCB
  field updates, endpoint queue mutations, SchedContext budget
  refills, etc.). Each wire-in reduces to `storeObject` via the
  `storeObjectKindChecked_sameKind_eq_storeObject` theorem, so the
  cascade is a no-op at proof level — but every preservation proof
  that unfolds through `storeObject` must add the match-layer on the
  wrapper body. Estimated ~50 in-place call sites across Scheduler /
  IPC / SchedContext / Lifecycle. AL6-A's wrapper provides the
  opt-in defense; universal adoption is the hygiene cascade.

- **AL6-C.hygiene** (NEW, surfaced by v0.29.14 post-delivery audit):
  completing the preservation proof for `lifecycleObjectTypeLockstep`
  (in `SeLe4n/Kernel/CrossSubsystem.lean`). The invariant definition
  and the semantic schema are committed; the `default` witness and the
  two preservation theorems (`storeObject_preserves_*`,
  `storeObjectKindChecked_preserves_*`) require threading the
  `objects.invExt` and `lifecycle.objectTypes.invExt` preconditions
  through the RHTable `getElem?_insert_{self,ne}` bridge lemmas.
  Composing with the existing `storeObject` frame lemmas in
  `Model/State.lean` discharges the obligation at ~50 LOC; the full
  extension to `crossSubsystemInvariant` (13 conjuncts currently)
  cascades to all downstream crossSubsystem preservation proofs.

All four hygiene items improve code readability / defense-in-depth /
proof-surface tightness without affecting correctness; they are
tracked for incremental landings after the v0.29.14 release.

---

## Non-AK7 Deferred Items

See `AUDIT_v0.29.0_WORKSTREAM_PLAN.md` §14.3 "Escape valves" for
portfolio-wide cascades deferred to WS-V (hardware integration) and
post-1.0 hygiene passes.
