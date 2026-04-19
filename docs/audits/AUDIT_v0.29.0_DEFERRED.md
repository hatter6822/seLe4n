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

### AK7-E.cascade — `Valid{Obj,Thread,SchedContext,C}Ptr` consumer migration [RESOLVED v0.29.14 / WS-AL AL7+AL8]

**Baseline (v0.29.13):** Subtypes defined in `Prelude.lean`:

- `ValidObjId := { o : ObjId // o ≠ ObjId.sentinel }`
- `ValidThreadId := { t : ThreadId // t ≠ ThreadId.sentinel }`
- `ValidSchedContextId := { s : SchedContextId // s ≠ SchedContextId.sentinel }`
- `ValidCPtr := { c : CPtr // c ≠ CPtr.sentinel }`

Plus per-type `toValid`/`ofValid`/`toValid?` conversion API and bridge
theorems (`ObjId.valid_of_ne_sentinel`, `ThreadId.toValid?_isSome_iff`).

**Resolution (v0.29.14, WS-AL phases AL7 + AL8):** Type-level sentinel-ID
rejection enforced at two layers:

- **AL7 (commit c2cc60d)** — dispatch-boundary RUNTIME validation via
  `validateThreadIdArg`/`validateSchedContextIdArg`/`validateObjIdArg`
  helpers in `SeLe4n/Kernel/API.lean`. Produces `.error .invalidArgument`
  on sentinel before handler entry.
- **AL8 (commit db29d80) — SUPERSEDES AL7's runtime-check-only design**:
  all 8 capability-only handlers now accept `ValidThreadId` / `ValidObjId`
  subtypes DIRECTLY. The Lean type system rejects any attempt to pass a
  raw `ThreadId` / `ObjId` into the handler at compile time. Removing the
  dispatch-boundary validation would produce an immediate type error —
  the discipline is no longer bypassable via proof-author oversight.

Two new private helpers added near `SeLe4n/Kernel/API.lean` line 445:

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

**Handler signature tightening (Lifecycle/SchedContext to `Valid*Id`) — COMPLETED in AL8 (commit db29d80)**:

All 8 capability-only handler signatures now accept `Valid*Id`
subtypes directly:

| Handler                | Signature change                                                                        |
|------------------------|-----------------------------------------------------------------------------------------|
| `suspendThread`        | `SystemState → ThreadId → …` → `SystemState → ValidThreadId → …`                        |
| `resumeThread`         | `SystemState → ThreadId → …` → `SystemState → ValidThreadId → …`                        |
| `setIPCBufferOp`       | `SystemState → ThreadId → VAddr → …` → `SystemState → ValidThreadId → VAddr → …`        |
| `setPriorityOp`        | `ThreadId × ThreadId → …` → `ValidThreadId × ValidThreadId → …`                         |
| `setMCPriorityOp`      | `ThreadId × ThreadId → …` → `ValidThreadId × ValidThreadId → …`                         |
| `schedContextConfigure`| `ObjId → …` → `ValidObjId → …`                                                          |
| `schedContextBind`     | `ObjId × ThreadId → …` → `ValidObjId × ValidThreadId → …`                               |
| `schedContextUnbind`   | `ObjId → …` → `ValidObjId → …`                                                          |

Preservation proofs (8 `*_preserves_projection` theorems in
`InformationFlow/Invariant/Operations.lean` + 3 theorems in
`SchedContext/Invariant/PriorityPreservation.lean` + 9 theorems in
`Architecture/IpcBufferValidation.lean`) updated to the new
signatures. Test suites (`SuspendResumeSuite`, `PriorityManagementSuite`,
`IpcBufferSuite`, `NegativeStateSuite` Z8-L, `MainTraceHarness`)
promote via `⟨tid, by decide⟩` proof-carrying construction.

Outcome: the `AK7-E.hygiene` item that was previously tracked here
is now **RESOLVED**. The WS-AL workstream delivered both the dispatch-
boundary guard (AL7) and the type-level enforcement (AL8) at the
handler signatures themselves.

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
tests in `sele4n-abi/tests/conformance.rs` originally extended from
0..=48 to 0..=49 (5 tests updated); `sele4n-types` unit tests
(`from_u32_roundtrip`, `from_u32_out_of_range`, `discriminant_ordering`,
`lean_rust_correspondence`, `unknown_kernel_error_sentinel`,
`new_variants_discriminants`) extended accordingly. Subsequently
extended to 0..=50 by AL1b (adding `NullCapability` at discriminant
50). Cargo workspace remains at 415 passing tests.

**Regression coverage:** 5 new AL6 runtime tests
(`al6_01..05`) in `tests/Ak7RegressionSuite.lean` cover the four paths
(fresh, same-kind, TCB→SC cross-kind, SC→TCB cross-kind) plus the
rejection-preserves-state property. Plus 8 AL2 helper tests
(`al2C_01..08`) verifying per-variant discrimination and round-trip
stores. Plus 5 AL10 integration tests (`al10_01..05`) exercising the
three cascades end-to-end.

**Consumer migration (AK7-F.reader.hygiene + AK7-F.writer.hygiene)**:
Two separately-tracked hygiene tasks remain (see closure summary
below). Both are non-gating — AL6's `storeObjectKindChecked` closes
the silent cross-variant overwrite hole at the object-store level
independently, and consumer sites remain safe under the existing
`apiInvariantBundle`.

---

### AK7-I.cascade — `Capability.requireNotNull` consumer migration [RESOLVED v0.29.14 / WS-AL AL1b]

**Baseline (v0.29.13):** Predicate + gate helper defined in
`Model/Object/Types.lean`:

- `Capability.isNull` / `isNotNull` predicates
- `Capability.null` canonical null-cap constant
- `Capability.requireNotNull : Capability → Option Capability`
- Correctness theorems (`requireNotNull_isSome_iff`, `requireNotNull_null`,
  `requireNotNull_some_not_null`)

**Note on original AL1 approach (reverted):** A first-pass solution
(AL1, commits e03d6d3..4a27c1c) added runtime `requireNotNull` guards
at `cspaceMint` / `cspaceCopy` / `cspaceMove` that returned
`.error .invalidCapability` on null-cap rejection. This was reverted
(commits 5be46b7, 2034d13, d17b4b1) because it OVERLOADED
`.invalidCapability`, which also means "slot empty" (from
`cspaceLookupSlot` failure) and "cap target is not `.object`" (from
outer dispatch match). External ABI consumers could not distinguish
the three failure modes.

**Resolution (v0.29.14, WS-AL phase AL1b, commit 544a410):** Type-level
discipline that enforces null-cap rejection at the Lean compiler level,
with a distinct error code:

- **New `NonNullCap` subtype** in `Model/Object/Types.lean`:
  `abbrev NonNullCap := { cap : Capability // cap.isNull = false }`
  with conversion API (`Capability.toNonNull`, `toNonNull?`,
  `ofNonNull`) and `CoeHead NonNullCap Capability` instance for
  seamless field access.
- **Tightened `mintDerivedCap` signature** from `Capability → …` to
  `NonNullCap → …`. The Lean type system forbids any caller from
  feeding a null cap. This is the *primary* security surface — every
  capability derivation must go through `mintDerivedCap`, and it
  refuses to accept a null `parent` at compile time.
- **New distinct error code** `KernelError.nullCapability`
  (discriminant 50) added to both Lean (`Model/State.lean`) and the
  Rust ABI (`sele4n-types/src/error.rs` `NullCapability = 50`).
  Range-check tests extended from 0..=49 to 0..=50 across
  `from_u32_roundtrip`, `discriminant_ordering`, `af6a_unknown_*`,
  `aa1h_error_boundary_*`, `u3f_*`, `w1h_*`, `lean_rust_correspondence`,
  `kernel_error_exhaustive_roundtrip`, plus the
  `decode_unknown_error_code` test. Cargo workspace stays at 415 tests.
- **cspaceMint / cspaceCopy / cspaceMove internal tightening** — the
  three cspace operations in `Kernel/Capability/Operations.lean`
  promote the looked-up cap via `cap.toNonNull?` before passing it to
  `mintDerivedCap` / `cspaceInsertSlot`. On `none` (= null cap), they
  emit `.error .nullCapability` distinct from `.invalidCapability`.

**Preservation proof patches (9 theorems):**
- `Capability/Invariant/Authority.lean`: `mintDerivedCap_attenuates`,
  `mintDerivedCap_rights_attenuated_with_badge_override`,
  `mintDerivedCap_target_preserved_with_badge_override`,
  `mintDerivedCap_badge_propagated`, `cspaceMint_child_attenuates`,
  `cspaceMint_badge_stored`.
- `Capability/Invariant/Preservation.lean`:
  `cspaceMint_preserves_capabilityInvariantBundle`,
  `cspaceCopy_preserves_capabilityInvariantBundle`,
  `cspaceMove_preserves_capabilityInvariantBundle`,
  `cspaceMint_preserves_badgeWellFormed`,
  `cspaceMint_preserves_cdtMapsConsistent`.
- `InformationFlow/Invariant/Helpers.lean`:
  `cspaceMint_preserves_lowEquivalent` (both `parent₁`/`parent₂`).
- `InformationFlow/Invariant/Composition.lean`: `niStepInd`
  `.cspaceMint` arm.
- `InformationFlow/Invariant/Operations.lean`:
  `cspaceCopy_preserves_projection`, `cspaceMove_preserves_projection`.

Each proof uses the pattern:
```lean
have hNotNull : cap.isNull = false := by
  by_cases h : cap.isNull
  · exfalso; simp [Capability.toNonNull?, h, hSrc] at hStep
  · exact Bool.not_eq_true _ |>.mp h
have hToNN : cap.toNonNull? = some ⟨cap, hNotNull⟩ :=
  Capability.toNonNull?_of_not_null hNotNull
```
The `exfalso` branch derives a REAL contradiction from the `.ok`
success hypothesis (if `isNull` held, the guard would have fired,
making `hStep` equal `.error .nullCapability`, contradicting `.ok`).

**Regression coverage (7 new tests, `al1b_01..07` in
`tests/Ak7RegressionSuite.lean`)**:

- `al1b_01`: `Capability.null.toNonNull?` = `none`
- `al1b_02`: non-null cap promotes successfully
- `al1b_03`: `NonNullCap → val → toNonNull?` round-trip
- `al1b_04`: `cspaceMint` from null-cap slot returns
  `.error .nullCapability` (end-to-end)
- `al1b_05`: `cspaceCopy` from null-cap slot returns
  `.error .nullCapability`
- `al1b_06`: `cspaceMove` from null-cap slot returns
  `.error .nullCapability`
- `al1b_07`: **direct regression test** — `.nullCapability` ≠
  `.invalidCapability` (guards against future reintroduction of the
  overloading bug).

**Note on `cspaceInvoke`:** The original DEFERRED listing referenced
a `cspaceInvoke` operation that does not exist in the codebase. The
three operations actually affected are `cspaceMint` / `cspaceCopy` /
`cspaceMove`, all of which are now guarded by the `NonNullCap`
discipline.

**Why the type-level approach is superior to runtime-only**:
The type system (not proof-author discipline) enforces the null-cap
check. Removing the `toNonNull?` call in `cspaceMint` is not a local
edit — it would require changing `mintDerivedCap`'s type signature,
which cascades to all theorems and fails compilation immediately.
Future contributors cannot accidentally (or maliciously) reintroduce
the bug.

---

## AK7 cascade closure summary (v0.29.14)

All three AK7 cascades are structurally closed at their primary attack
surfaces, with type-level discipline enforced by the Lean compiler.
The three `AK7-*.cascade` rows above are each marked **RESOLVED**
with commit SHAs.

| Cascade | Resolution phase  | Attack surface closed at              | Primary commit |
|---------|-------------------|---------------------------------------|----------------|
| AK7-I   | WS-AL AL1b        | `NonNullCap` subtype @ `mintDerivedCap` + `cspaceMint/Copy/Move` | 544a410        |
| AK7-F   | WS-AL AL2 + AL6   | AL2-A `getX?` helpers + AL6 `storeObjectKindChecked` wrapper + `.invalidObjectType` error code | 4d5cc8b        |
| AK7-E   | WS-AL AL7 + AL8   | dispatch `validate*IdArg` helpers + handler signatures take `Valid*Id` | db29d80        |

**Reverted (not in final history as RESOLVED):** The initial AL1 approach
(commits e03d6d3, c4d4462, ab7dc07, a6c2dd1, 4a27c1c) added runtime
`requireNotNull` guards but overloaded `.invalidCapability`. Reverted
via 5be46b7, 2034d13, d17b4b1 and superseded by AL1b's type-level
design (see AK7-I.cascade section above for full detail).

Three residual hygiene items remain tracked for post-patch work. All
are **non-gating** — the three primary attack surfaces (mint/copy/move
null-cap, object-store cross-variant overwrite, dispatch sentinel IDs)
are already closed by AL1b / AL6 / AL8 structurally at the type level.

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

All three hygiene items improve code readability / defense-in-depth /
proof-surface tightness without affecting correctness; they are
tracked for incremental landings after the v0.29.14 release.

### Hygiene item closed by WS-AL (for historical reference)

- **AK7-E.hygiene** — *no longer tracked as deferred*. This item
  previously tracked the handler-signature tightening from raw
  `ThreadId` / `SchedContextId` / `ObjId` to `ValidThreadId` /
  `ValidObjId`. **RESOLVED in AL8 (commit db29d80)** for all 8
  capability-only handlers (`suspendThread`, `resumeThread`,
  `setIPCBufferOp`, `setPriorityOp`, `setMCPriorityOp`,
  `schedContextConfigure`, `schedContextBind`, `schedContextUnbind`)
  plus all their NI-preservation theorems and test callers. See the
  AK7-E.cascade section above for the complete signature table and
  the enumerated proof / test files touched.

---

## Non-AK7 Deferred Items

See `AUDIT_v0.29.0_WORKSTREAM_PLAN.md` §14.3 "Escape valves" for
portfolio-wide cascades deferred to WS-V (hardware integration) and
post-1.0 hygiene passes.
