# AUDIT v0.30.6 — Closure-form Discharge Index

**Plan ID:** WS-AN Phase AN12-A (Theme 4.1 deliverable)
**Workstream:** WS-AN — Pre-1.0 Audit Remediation (v0.30.6 → v1.0.0)
**Source audit:** [`AUDIT_v0.30.6_COMPREHENSIVE.md`](AUDIT_v0.30.6_COMPREHENSIVE.md)
**Plan:** [`AUDIT_v0.30.6_WORKSTREAM_PLAN.md`](AUDIT_v0.30.6_WORKSTREAM_PLAN.md) §15.A
**Baseline:** [`AUDIT_v0.30.6_WS_AN_BASELINE.txt`](AUDIT_v0.30.6_WS_AN_BASELINE.txt)
**Author:** WS-AN Phase AN12-A
**Date:** 2026-04-26
**Status:** LANDED at v0.30.11 (WS-AN AN12 closure).

## 1. Methodology

The seLe4n proof surface uses three composition patterns where a per-operation
preservation theorem accepts a "closure-form" hypothesis instead of proving
the post-state property from the pre-state invariant alone. This index is
the canonical map from each closure-form theorem to its discharge mechanism.

### Row format

Every row in §3 carries five fields:

| Field | Meaning |
|-------|---------|
| **Theorem name** | The closure-form theorem in `SeLe4n/Kernel/…/Invariant{,/Operations}.lean`. |
| **File:Line** | Canonical source location at v0.30.11. |
| **Hypothesis names** | The closure-form parameters the theorem accepts (e.g. `hCdtPost`, `hProjEq`, `hSchedProj`, `hServiceProjEq`). |
| **Discharge site** | The companion theorem (or recipe) that produces the closure-form witness for a caller. |
| **Reachability check** | A `#check` expression that elaborates only if the discharge site is correctly named and typed at the post-AN12 state. |

### How to use this index

- **Auditors**: every `_preserves_projection` / `_preserves_capabilityInvariantBundle`
  theorem with a closure-form hypothesis appears in §3 with its discharge
  recipe. To verify there is no orphaned closure-form obligation, grep for
  `hCdtPost`, `hProjEq`, `hSchedProj`, `hServiceProjEq` in the proof surface
  and check every match against §3.
- **Implementers**: when wiring a new dispatch arm, locate the per-operation
  theorem in §3 and use the named **discharge site** to produce the closure-
  form witness. Frame lemmas marked "substantively proven" can be invoked
  directly; frame lemmas marked "recipe" require a per-call composition.
- **Maintainers**: when the proof body of a closure-form theorem changes, the
  row's **Discharge site** field must continue to produce a witness with the
  exact closure signature. The reachability `#check` is the regression guard.

### Companion artifact

A marker theorem `closureForm_discharge_index_documented : True := trivial`
in `SeLe4n/Kernel/CrossSubsystem.lean` cross-references this file. The
companion bridges in §3.A (`{cspaceCopy,cspaceMove,cspaceMintWithCdt,
cspaceMutate,cspaceDeleteSlot,cspaceRevoke}_cdt_hypothesis_discharged_at`)
are already substantively proven in the same module and provide the
post-state CDT discharge witnesses.

## 2. Theme index

| § | Theme | Closure | Owning phase | Audit IDs |
|---|-------|---------|--------------|-----------|
| 3.A | CDT post-state witnesses | `hCdtPost` | AN4-C | H-04 |
| 3.B | Projection closures | `hProjEq` | AN6-A / AK6-F | H-07, AK6F.13–19 |
| 3.C | Schedule / Service closures | `hSchedProj`, `hServiceProjEq` | AN5-D / AK6-F | SC-M02, AK6F.11/12 |

§3.A entries are **fully substantively discharged** — every CDT-modifying
operation has a companion bridge that produces the post-state CDT predicates
unconditionally from the bundle. §3.B entries are **7 closure-form per-op
theorems** that take an `hProjEq` parameter; the rest of the
`_preserves_projection` surface (39 substantive theorems for the simpler
cap arms / IPC arms / scheduler arms) is closure-free and falls outside
this index. §3.C entries are closure-form by design — `schedule` and
`revokeService` both call into kernel-internal sub-machines whose
projection witnesses are caller obligations at composition time.

## 3. Theme index — per-theorem rows

### §3.A — CDT post-state discharge (H-04 / AN4-C)

CDT-modifying capability operations take `cdtCompleteness st' ∧ cdtAcyclicity
st'` as a post-state hypothesis (`hCdtPost`) at their preservation theorems
rather than re-deriving it from the pre-state invariant. The discharge
mechanism: at each composition site the post-state CDT predicates are
extracted from `capabilityInvariantBundle st'` (which the per-operation
`_preserves_capabilityInvariantBundle` theorem already produces). The
companion bridges below are the **substantively proven** witnesses landed
in AN4-C; every row is **DISCHARGED**.

| # | Theorem | File:Line | Hypothesis | Discharge site | Reachability check |
|---|---------|-----------|-----------|---------------|--------------------|
| A.1 | `cspaceCopy_preserves_capabilityInvariantBundle` | `SeLe4n/Kernel/Capability/Invariant/Preservation/CopyMoveMutate.lean:35` | `hCdtPost` | `cspaceCopy_cdt_hypothesis_discharged_at` (`CrossSubsystem.lean:2893`) | `#check @SeLe4n.Kernel.cspaceCopy_cdt_hypothesis_discharged_at` |
| A.2 | `cspaceMove_preserves_capabilityInvariantBundle` | `SeLe4n/Kernel/Capability/Invariant/Preservation/CopyMoveMutate.lean:89` | `hCdtPost` | `cspaceMove_cdt_hypothesis_discharged_at` (`CrossSubsystem.lean:2901`) | `#check @SeLe4n.Kernel.cspaceMove_cdt_hypothesis_discharged_at` |
| A.3 | `cspaceMintWithCdt_preserves_capabilityInvariantBundle` | `SeLe4n/Kernel/Capability/Invariant/Preservation/CopyMoveMutate.lean:174` | `hCdtPost` | `cspaceMintWithCdt_cdt_hypothesis_discharged_at` (`CrossSubsystem.lean:2908`) | `#check @SeLe4n.Kernel.cspaceMintWithCdt_cdt_hypothesis_discharged_at` |
| A.4 | `cspaceMutate_preserves_capabilityInvariantBundle` | `SeLe4n/Kernel/Capability/Invariant/Preservation/CopyMoveMutate.lean:240` | (bundle transfer; no `hCdtPost`) | `cspaceMutate_cdt_hypothesis_discharged_at` (`CrossSubsystem.lean:2917`) — index-completeness | `#check @SeLe4n.Kernel.cspaceMutate_cdt_hypothesis_discharged_at` |
| A.5 | `cspaceDeleteSlot_preserves_capabilityInvariantBundle` | `SeLe4n/Kernel/Capability/Invariant/Preservation/Delete.lean:128` | (bundle transfer; no `hCdtPost`) | `cspaceDeleteSlot_cdt_hypothesis_discharged_at` (`CrossSubsystem.lean:2925`) — index-completeness | `#check @SeLe4n.Kernel.cspaceDeleteSlot_cdt_hypothesis_discharged_at` |
| A.6 | `cspaceRevoke_preserves_capabilityInvariantBundle` | `SeLe4n/Kernel/Capability/Invariant/Preservation/Delete.lean:192` | (bundle transfer; no `hCdtPost`) | `cspaceRevoke_cdt_hypothesis_discharged_at` (`CrossSubsystem.lean:2934`) — index-completeness | `#check @SeLe4n.Kernel.cspaceRevoke_cdt_hypothesis_discharged_at` |

**Notes for §3.A**

- All six bridge theorems share the same body shape: project the
  `capabilityInvariantBundle` 7-conjunct (or named field on the
  `CapabilityInvariantBundle` structure once AN4-F.5's primary-form swap
  lands) to the `(cdtCompleteness, cdtAcyclicity)` pair. The proofs are
  one-liners (`⟨hBundle.2.2.2.1, hBundle.2.2.2.2.1⟩`) and machine-checked at
  every commit.
- A.4 / A.5 / A.6 are present even though the underlying preservation
  theorem does not take `hCdtPost`: bundle-transfer-style operations carry
  the CDT predicates implicitly through `_preserves_capabilityInvariantBundle`.
  The companion theorems are listed for **index completeness** so future
  Theme 4.1 extensions can be added uniformly without a special-case gap.
- **Scope note**: four IPC-side cap-transfer preservation theorems
  (`ipcTransferSingleCap_preserves_capabilityInvariantBundle` at
  `BadgeIpcCapsAndCdtMaps.lean:230`,
  `ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle` at `:293`,
  `ipcUnwrapCaps_preserves_capabilityInvariantBundle_grant` at `:355`,
  `ipcUnwrapCaps_preserves_capabilityInvariantBundle` at `:410`) plus the
  parametric helper `cdtExpandingOp_preserves_bundle_with_hypothesis` at
  `:610` also accept `hCdtPost`-shaped hypotheses. They are
  CDT-expanding ops that route through `cspaceCopy`/`cspaceMintWithCdt`
  internally and inherit the §3.A discharge bridges via composition; they
  are not listed as separate rows because they share the same six
  underlying `_cdt_hypothesis_discharged_at` companions.

### §3.B — Projection closures (H-07 / AN6-A / AK6F.13–19)

Per-operation NI preservation theorems in
`SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` come in two
shapes: **substantive** (proves projection from observability hypotheses
alone) and **closure-form** (accepts an `hProjEq` closure that says "if the
internal step succeeded, projection is preserved"). The closure-form
theorems are dispatched per-arm at the call site by composing the named
**frame lemmas** listed below.

**Inventory (verified at v0.30.11)**: the file contains **46 total
`_preserves_projection` theorems**. Of those, **7 take `hProjEq`** and are
listed below; **2 take `hSchedProj`** (`setPriorityOp`, `setMCPriorityOp`
— routed in §3.C); **1 takes `hServiceProjEq`** (`revokeService` — routed
in §3.C); the remaining **36 are fully substantive** (prove projection from
observability hypotheses alone) and fall outside the closure-form index by
construction.

The closure pattern was chosen for the 7 below — rather than substantive
discharge — because Lean 4.28.0's `split` / `split_ifs` tactic interacts
poorly with `Except.ok`-wrapped deeply-nested match conditions; named
frame lemmas (themselves substantively proven) compose to ≈25–100 LOC per
caller arm.

| # | Theorem | File:Line | Hypothesis | Discharge recipe (frame lemmas) | Reachability check |
|---|---------|-----------|-----------|---------------------------------|--------------------|
| B.1 | `schedContextConfigure_preserves_projection` | `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean:3627` | `hProjEq` | `objects_insert_preserves_projection_high` × 2 (SC + bound TCB) + `migrateRunQueueBucket_preserves_projection` + `schedContextBind_frame_runQueue_rebucket` | `#check @SeLe4n.Kernel.InformationFlow.schedContextConfigure_preserves_projection` |
| B.2 | `schedContextBind_preserves_projection` | `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean:3667` | `hProjEq` | `objects_insert_preserves_projection_high` × 2 + `schedContextBind_frame_runQueue_rebucket` + `projectState_scThreadIndex_eq` | `#check @SeLe4n.Kernel.InformationFlow.schedContextBind_preserves_projection` |
| B.3 | `schedContextUnbind_preserves_projection` | `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean:3693` | `hProjEq` | `projectState_scheduler_current_cleared_when_high` + `removeRunnable_preserves_projection` + `objects_insert_preserves_projection_high` × 2 + `projectState_replenishQueue_eq` + `projectState_scThreadIndex_eq` | `#check @SeLe4n.Kernel.InformationFlow.schedContextUnbind_preserves_projection` |
| B.4 | `lifecycleRetypeDirectWithCleanup_preserves_projection` | `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean:3723` | `hProjEq` | `lifecyclePreRetypeCleanup` field-frame lemmas + `scrubObjectMemory_preserves_projection` (memory-ownership-`none` arm) + `storeObject_preserves_projection` | `#check @SeLe4n.Kernel.InformationFlow.lifecycleRetypeDirectWithCleanup_preserves_projection` |
| B.5 | `cancelDonation_preserves_projection` | `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean:3751` | `hProjEq` | 3-arm split (`.unbound` `rfl` / `.bound` SC unbind / `.donated` returnDonation); donor-high derivable from `donationOwnerValid` | `#check @SeLe4n.Kernel.InformationFlow.cancelDonation_preserves_projection` |
| B.6 | `suspendThread_preserves_projection` | `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean:3788` | `hProjEq` | 9-phase recipe in theorem docstring (G1 lookup → G9 schedule); composes `revertPriorityInheritance` chain + `removeRunnable_preserves_projection` + `cancelDonation_preserves_projection` (B.5 helper) + `storeObject_preserves_projection` × 2 | `#check @SeLe4n.Kernel.InformationFlow.suspendThread_preserves_projection` |
| B.7 | `resumeThread_preserves_projection` | `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean:3846` | `hProjEq` | `resumeThread_frame_insert` (substantive, exposed at module scope) + `resumeThread_frame_ensureRunnable` (substantive) | `#check @SeLe4n.Kernel.InformationFlow.resumeThread_preserves_projection` |

**Notes for §3.B**

- B.5 (`cancelDonation`) is a sub-helper consumed by B.6 (`suspendThread`)
  G5; it is listed as its own row because it is exposed at module scope and
  a caller may invoke it directly when composing the lifecycle path.
- B.6 is the longest recipe (≈100 LOC) because `suspendThread` is the most
  multi-phase operation in the lifecycle subsystem (9 sequential phases).
- The `_frame_insert` and `_frame_ensureRunnable` substantive lemmas (B.7)
  are exposed at module scope precisely so a caller can invoke them
  without pulling them out of `private`.

### §3.C — Schedule / Service closures (SC-M02 / AN5-D / AK6F.11–12)

Two operations emit closure-form hypotheses that bridge the proof layer to
an externally-supplied projection witness for sub-machines whose internal
state does not factor through the per-operation invariant:

- **`hSchedProj`** — the optional preemption-schedule arm in
  `setPriorityOp` and `setMCPriorityOp` calls into `schedule`, which is
  itself an invariant-preserving but not-projection-stripping operation.
  The closure is discharged at composition time by the kernel-API layer
  (`syscallDispatch`) where the dispatched operation either:
  (a) does not invoke `schedule` (closure unused), or
  (b) invokes `schedule` against a state observably equal to the call-
      site state, in which case the closure is discharged by
      `schedule_preserves_projection` directly.

- **`hServiceProjEq`** — `revokeService` walks the service registry via a
  RHTable fold; the per-step witness that each fold step preserves
  projection is supplied by the caller, again because the registry's
  internal hashing structure is not part of the per-operation Prop-level
  invariant. The closure is discharged at composition time by induction
  on the registry's fold ordering.

| # | Theorem | File:Line | Hypothesis | Discharge site | Reachability check |
|---|---------|-----------|-----------|---------------|--------------------|
| C.1 | `setPriorityOp_preserves_projection` | `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean:3357` | `hSchedProj` | `schedule_preserves_projection` (`Operations.lean:679`) composed at API dispatch | `#check @SeLe4n.Kernel.InformationFlow.setPriorityOp_preserves_projection` |
| C.2 | `setMCPriorityOp_preserves_projection` | `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean:3435` | `hSchedProj` | `schedule_preserves_projection` (`Operations.lean:679`) composed at API dispatch | `#check @SeLe4n.Kernel.InformationFlow.setMCPriorityOp_preserves_projection` |
| C.3 | `schedContextBind_preserves_projection` (schedule arm) | `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean:3667` | inside `hProjEq` (B.2) | covered by §3.B B.2 recipe; the schedule arm is captured inside the closure body | `#check @SeLe4n.Kernel.InformationFlow.schedContextBind_preserves_projection` |
| C.4 | `schedContextConfigure_preserves_projection` (schedule arm) | `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean:3627` | inside `hProjEq` (B.1) | covered by §3.B B.1 recipe | `#check @SeLe4n.Kernel.InformationFlow.schedContextConfigure_preserves_projection` |
| C.5 | `revokeService_preserves_projection` | `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean:3573` | `hServiceProjEq` | RHTable fold induction at composition time; see the theorem docstring "Design note on hypothesis `hServiceProjEq`" | `#check @SeLe4n.Kernel.InformationFlow.revokeService_preserves_projection` |

**Notes for §3.C**

- C.3 and C.4 are listed for completeness because their closure-form
  `hProjEq` body internally uses the schedule arm. The §3.B recipes for
  B.1 and B.2 already capture how to discharge the schedule call there;
  this section cross-references them.
- C.5 is the only entry that takes a non-`hSchedProj` external closure
  (`hServiceProjEq`); the design rationale is documented inline at the
  theorem's docstring.

## 4. Reachability gate

A marker theorem in `SeLe4n/Kernel/CrossSubsystem.lean` —
`closureForm_discharge_index_documented : True := trivial` — anchors the
post-AN12 state. The reachability `#check` expressions in §3 are exercised
by the existing tier-3 invariant-surface gate (`scripts/test_tier3_invariant_surface.sh`):
the gate searches for the canonical theorem names and fails if any name
disappears or moves to a substantively different signature.

If a future refactor renames or moves any of the listed theorems, this index
must be updated in the same PR. The website link manifest registers this
file so `scripts/check_website_links.sh` enforces its presence.

## 5. Closure summary

- **§3.A — 6 of 6 rows DISCHARGED** with substantively proven companion
  bridges (`*_cdt_hypothesis_discharged_at` in
  `SeLe4n/Kernel/CrossSubsystem.lean`).
- **§3.B — 7 closure-form rows** (every `_preserves_projection` theorem in
  the proof surface that takes `hProjEq`); each row has a named
  discharge recipe via pre-proven frame lemmas. The remaining 36
  `_preserves_projection` theorems are closure-free / substantive and
  fall outside this index.
- **§3.C — 5 rows** (2 substantive `hSchedProj` callers + 1 substantive
  `hServiceProjEq` caller + 2 schedule-arm cross-references covered by
  §3.B); each row has a named composition recipe at the API dispatch
  boundary.

No closure-form obligation is orphaned at v0.30.11: every `hCdtPost`,
`hProjEq`, `hSchedProj`, `hServiceProjEq` parameter in the proof surface
either has a substantively proven discharge bridge (§3.A) or a documented
discharge recipe via named frame lemmas (§3.B / §3.C).
