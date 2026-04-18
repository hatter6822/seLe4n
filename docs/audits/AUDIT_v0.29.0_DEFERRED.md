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

## AK7 cascade closure summary (v0.29.14)

All three AK7 cascades are structurally closed at their primary attack
surfaces. The three `AK7-*.cascade` rows above are each marked
**RESOLVED** with commit SHAs.

| Cascade | Resolution phase | Attack surface closed at | Commit(s)             |
|---------|------------------|--------------------------|-----------------------|
| AK7-I   | WS-AL AL1        | cspaceMint/Copy/Move     | e03d6d3, c4d4462, ab7dc07 |
| AK7-F   | WS-AL AL6        | storeObjectKindChecked   | 4d5cc8b               |
| AK7-E   | WS-AL AL7        | dispatchCapabilityOnly   | c2cc60d               |

Two residual hygiene items remain tracked for post-patch work:

- **AK7-E.hygiene**: tightening the 5+ Lifecycle / SchedContext /
  IpcBufferValidation handler signatures from raw `ThreadId` /
  `SchedContextId` to the `Valid*Id` subtypes. Non-gating: AL7's
  dispatch-boundary guards close the attack surface independently.
- **AK7-F.hygiene**: migrating the 304 raw
  `match st.objects[id]? with | some (.variant x) => ...` call sites
  to use the AL2-A typed helpers. Non-gating: AL6's
  `storeObjectKindChecked` closes the silent cross-variant overwrite
  hole independently.

Both hygiene items improve code readability and reduce long-term
maintenance burden without affecting correctness; they are tracked for
incremental landings after the v0.29.14 release.

---

## Non-AK7 Deferred Items

See `AUDIT_v0.29.0_WORKSTREAM_PLAN.md` §14.3 "Escape valves" for
portfolio-wide cascades deferred to WS-V (hardware integration) and
post-1.0 hygiene passes.
