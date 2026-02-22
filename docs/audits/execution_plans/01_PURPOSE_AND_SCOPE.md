# 01 — Purpose and Scope

## 1. Objective

Close tracked proof issue **TPI-D07** by replacing the `sorry` in `serviceRegisterDependency_preserves_acyclicity` with a complete, machine-checked formal proof.

> **Current status (post-implementation):** The preservation theorem (line 591) is sorry-free. The original `sorry` was eliminated via Strategy B (Risk 0 — declarative invariant + 4-layer proof infrastructure). The sole remaining `sorry` is on `bfs_complete_for_nontrivialPath` (line 531, annotated TPI-D07-BRIDGE), a focused BFS completeness bridge operationally validated by executable tests.

## 2. Success criteria (summary)

1. The theorem `serviceRegisterDependency_preserves_acyclicity` compiles with **zero `sorry` markers**.
2. All intermediate lemmas compile without `sorry`.
3. No operational definitions in `Operations.lean` are changed — no new error variants, no fuel changes, no BFS algorithm changes.
4. The runtime test suite (`NegativeStateSuite.lean`) is expanded with deeper graph topologies.
5. All four documentation files referencing TPI-D07 status are updated to `CLOSED`.
6. The full tiered validation gate (`test_full.sh`) passes cleanly.

## 3. Non-goals

The following are explicitly **out of scope** for this execution plan:

| Non-goal | Rationale |
|---|---|
| Changing the BFS algorithm or fuel computation in `serviceHasPathTo` | Proof-only closure; operational behavior is frozen |
| Refactoring `ServiceGraphEntry`, `ServiceId`, or `storeServiceState` data structures | No data model changes needed |
| Addressing findings outside F-07 (F-11 and F-12 are already closed under WS-D4) | Separate tracked issues, already resolved |
| Introducing BFS completeness proofs (true-return → path exists) | Only soundness (false → no path) is required for the `sorry` elimination; completeness is a nice-to-have but not blocking |
| Migrating from `List`-based to `Finset`-based dependency storage | Out of scope unless list reasoning becomes intractable (see [Risk Register R2](./05_RISK_REGISTER.md#risk-2)) |
| Proving fuel adequacy unconditionally across all possible `SystemState` values | If unconditional fuel adequacy requires cross-subsystem invariant work, a preconditioned approach is acceptable (see [Risk Register R1](./05_RISK_REGISTER.md#risk-1)) |

## 4. Constraint: proof-only closure

This is a **proof-only** change. The constraint is enforced as follows:

- **`SeLe4n/Kernel/Service/Operations.lean`** — zero modifications. The file hash must be unchanged after TPI-D07 closure.
- **`SeLe4n/Model/State.lean`** — zero modifications to definitions. New lemmas may be added if needed, but no existing definition signatures change.
- **`SeLe4n/Model/Object.lean`** — zero modifications.
- **`SeLe4n/Prelude.lean`** — zero modifications.
- **`SeLe4n/Kernel/Service/Invariant.lean`** — the only file with substantive proof changes. New definitions (`serviceEdge`, `serviceReachable`) and lemmas are added. The `sorry` is replaced with a complete proof. No operational definitions change.
- **`tests/NegativeStateSuite.lean`** — new test cases are added; no existing test expectations change.

## 5. Methodology

This execution plan is derived from **direct code inspection** of live repository artifacts, not documentation-only assumptions. Every claim about code behavior is verified against the actual source.

### 5.1 Source artifact inventory

| Artifact | Path | Role in TPI-D07 |
|---|---|---|
| BFS + registration logic | `SeLe4n/Kernel/Service/Operations.lean:96–160` | Operational definitions under proof |
| Acyclicity invariant + proof | `SeLe4n/Kernel/Service/Invariant.lean:381–637` | Layers 0-4 proof infrastructure; preservation theorem at 591; BFS bridge `sorry` at 531 |
| Service graph data model | `SeLe4n/Model/Object.lean:6–26` | `ServiceGraphEntry`, `ServiceStatus`, dependency lists |
| Service ID type | `SeLe4n/Prelude.lean:112–114` | `structure ServiceId` (typed `Nat` wrapper) |
| System state + store lemmas | `SeLe4n/Model/State.lean:45–193` | `storeServiceState`, `lookupService`, `_eq`/`_ne` lemmas |
| Kernel monad | `SeLe4n/Prelude.lean:259` | `KernelM` (state/error monad) |
| Store entry helper | `SeLe4n/Kernel/Service/Operations.lean:11–12` | `storeServiceEntry` wraps `storeServiceState` in kernel monad |
| Negative test suite | `tests/NegativeStateSuite.lean:319–367` | Runtime validation of cycle detection |
| Tracked proof issues | `docs/audits/AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md:214` | TPI-D07 status: CLOSED (Risk 0 resolved) |
| Workstream plan | `docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md:336–343` | WS-D4 completion evidence |
| Claim-evidence index | `docs/CLAIM_EVIDENCE_INDEX.md:37` | TPI-D07 listed as CLOSED |
| Proof and invariant map | `docs/gitbook/12-proof-and-invariant-map.md:195–269` | F-07 theorem catalog + §14 proof infrastructure |

### 5.2 Verification method

Each milestone specifies:

1. **Precise goal states** — the exact Lean 4 proof state after case-splitting, derived from reading the actual code.
2. **Lemma signatures** — written in valid Lean 4 syntax against the actual type definitions.
3. **Tactic suggestions** — concrete Lean 4 tactic sequences, not abstract proof sketches.
4. **Exit criteria** — testable conditions (specific `lake build` or `rg` commands).
5. **Artifacts modified** — exact file paths with anticipated change regions.

### 5.3 Upstream documentation alignment

The following documents must be updated synchronously with the proof closure to maintain documentation-to-code consistency:

| Document | Pre-implementation status | Post-implementation status |
|---|---|---|
| `docs/audits/AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md` | IN PROGRESS | **CLOSED** (updated) |
| `docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md` | `sorry` tracked | **Updated**: Risk 0 resolved, TPI-D07 closed (lines 336-343, 478) |
| `docs/CLAIM_EVIDENCE_INDEX.md` | IN PROGRESS | **CLOSED** (updated: BFS bridge `sorry` tracked as TPI-D07-BRIDGE) |
| `docs/gitbook/12-proof-and-invariant-map.md` | Uses `sorry`; tracked as TPI-D07 | **Updated**: preservation theorem `(no sorry)`; §14 documents 4-layer infrastructure |

All updates are detailed in [M5: Closure Synchronization](./milestones/M5_CLOSURE_SYNC.md).
