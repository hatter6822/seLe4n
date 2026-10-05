# Development History Archive

This directory contains documentation retained **only for historical traceability**.
Nothing here drives active development, planning, or execution.

## Contents

### Milestone closeouts

| File | Description |
|---|---|
| `M7_CLOSEOUT_PACKET.md` | M7 remediation closeout (WS-A1..WS-A8, completed 2026-02-17) |
| `IF_M1_BASELINE_PACKAGE.md` | IF-M1 information-flow baseline deliverable (WS-B7, completed) |

### Historical audits (`audits/`)

| File | Description |
|---|---|
| `AUDIT_CODEBASE_v0.11.6.md` | v0.11.6 codebase audit (WS-E, completed) |
| `AUDIT_v0.11.6_WORKSTREAM_PLAN.md` | WS-E execution portfolio (completed) |
| `AUDIT_v0.11.0.md` | v0.11.0 repository audit (WS-D, completed) |
| `AUDIT_v0.11.0_WORKSTREAM_PLAN.md` | WS-D execution portfolio (completed) |
| `AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md` | WS-D tracked proof obligations (all closed) |
| `AUDIT_PR179_M2_BFS_SOUNDNESS.md` | BFS soundness audit (completed) |
| `execution_plans/` | TPI-D07 BFS soundness proof execution plan (completed) |
| `AUDIT_v0.8.0.md` | Initial repository audit baseline |
| `AUDIT_v0.9.0.md` | Comprehensive audit (WS-B scope) |
| `AUDIT_v0.9.0_WORKSTREAM_PLAN.md` | WS-B execution portfolio (completed) |
| `AUDIT_v0.9.32.md` | Independent audit (WS-C scope) |
| `AUDIT_v0.9.32_WORKSTREAM_PLAN.md` | WS-C execution portfolio (completed) |
| `AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md` | WS-C theorem obligations (closed) |
| `AUDIT_CODEBASE_v0.12.2_v1.md` | v0.12.2 executive summary audit (WS-F scope, completed) |
| `AUDIT_CODEBASE_v0.12.2_v2.md` | v0.12.2 end-to-end detailed audit (WS-F scope, completed) |
| `AUDIT_v0.12.2_WORKSTREAM_PLAN.md` | WS-F execution portfolio (completed, 33/33 findings closed) |
| `AUDIT_CODEBASE_v0.12.15_v1.md` | v0.12.15 executive summary audit (WS-H scope, completed) |
| `AUDIT_CODEBASE_v0.12.15_v2.md` | v0.12.15 end-to-end detailed audit (WS-H scope, completed) |
| `AUDIT_v0.12.15_WORKSTREAM_PLAN.md` | WS-H execution portfolio (completed, H1–H16) |
| `KERNEL_PERFORMANCE_AUDIT_v0.12.5.md` | v0.12.5 performance audit (WS-G, all 14 findings closed) |
| `KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md` | WS-G execution portfolio (completed, 9 workstreams) |
| `AUDIT_CODEBASE_v0.13.6.md` | v0.13.6 end-to-end codebase audit (completed) |
| `AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md` | WS-I portfolio (completed, I1–I4; I5 superseded by WS-L) |
| `AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md` | WS-J1 register namespace migration (completed, J1-A through J1-F) |
| `AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md` | WS-K full syscall dispatch (completed, K-A through K-H) |

### Historical GitBook chapters (`gitbook/`)

| File | Description |
|---|---|
| `08-completed-slice-m4a.md` | M4-A slice closeout |
| `09-m5-closeout-snapshot.md` | M5 closeout snapshot |
| `13-future-slices-and-delivery-plan.md` | Legacy delivery plan |
| `14-m4b-execution-playbook.md` | M4-B execution playbook |
| `15-m5-development-blueprint.md` | M5 development blueprint |
| `16-completed-slice-m4b.md` | M4-B slice closeout |
| `18-m6-execution-plan-and-workstreams.md` | M6 execution plan (closed) |
| `20-repository-audit-remediation-workstreams.md` | WS-A remediation portfolio |
| `21-m7-current-slice-outcomes-and-workstreams.md` | M7 outcomes and workstreams |
| `23-m7-remediation-closeout-packet.md` | M7 remediation closeout mirror |
| `32-v0.11.0-audit-workstream-planning.md` | WS-D/WS-E audit workstream planning |
| `06-development-workflow.md` | Development workflow (superseded by `docs/DEVELOPMENT.md`) |
| `19-end-to-end-audit-and-quality-gates.md` | End-to-end audit and quality gates (v0.12.2 baseline) |
| `22-next-slice-development-path.md` | Next development path (v0.14.10 baseline, superseded) |
| `24-comprehensive-audit-2026-workstream-planning.md` | WS-F audit remediation planning (completed) |

### Retired workstream plans (`planning/`)

Plans move here when their workstream closes.  Kernel source, tests and Rust
must not reference `docs/dev_history/` (Tier 0 enforces it), so they cite an
archived plan by its stable workstream or phase ID (`WS-SM SM6.C`, `WS-RA`,
`WS-RR RR8.12`), and the ID-to-plan table in
[`docs/agent_guide/WORKSTREAM_CONTEXT.md`](../agent_guide/WORKSTREAM_CONTEXT.md)
resolves each ID to its file here.  Before a plan moves, every obligation it
still holds open is lifted into an active row of
[`docs/REGISTERED_DEBT.md`](../REGISTERED_DEBT.md) or a live plan.

**Status lines in these files are the status at the time of archiving, not the
current status.**  Some were stale even then (a `PLANNED` or `IN FLIGHT` header
on a closed workstream).  The authoritative status of every workstream is
[`docs/REGISTERED_DEBT.md`](../REGISTERED_DEBT.md)'s workstream registry, with
the phase table in `docs/agent_guide/WORKSTREAM_CONTEXT.md`.

| File | Description |
|---|---|
| `CLOSED_WORKSTREAM_CONTEXT.md` | Status sections of closed workstreams (WS-RA, WS-OD, WS-RM, WS-HP, WS-LC), formerly in `CLAUDE.md`'s "Active workstream context" |
| `DONATION_POP_TRIGGER_PLAN.md` | WS-HP head-driven donation pop (complete) |
| `REPLY_FRAME_REMOVAL_PLAN.md` | WS-RM `reply_remove` on the reply path (complete, v0.35.6) |
| `REPLY_OBJECTS_COMPLETION_PLAN.md` | Reply-object completeness items (complete, v0.31.155) |
| `SCHEDCONTEXT_DONATION_CHAIN_PLAN.md` | WS-OD SchedContext donation chains (complete, v0.35.2) |
| `SMP_FOUNDATIONS_PLAN.md` | WS-SM SM0 foundations (closed, v0.31.3) |
| `SMP_RUST_HAL_PLAN.md` | WS-SM SM1 Rust HAL (landed, v0.31.3 → v0.31.8) |
| `SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md` | WS-SM SM2.C-defer, the deferred verified-RwLock completion (complete, v0.34.50, closed by WS-RR RR6) |
| `SMP_PER_OBJECT_LOCKS_PLAN.md` | WS-SM SM3 per-object locks (closed, v0.31.9) |
| `SMP_PER_CORE_STATE_PLAN.md` | WS-SM SM4 per-core state (landed, v0.31.37) |
| `SMP_PER_CORE_SCHEDULER_PLAN.md` | WS-SM SM5 per-core scheduler (landed, v0.31.38 → v0.31.64) |
| `SMP_CROSS_CORE_IPC_PLAN.md` | WS-SM SM6 cross-core IPC (landed, v0.31.65 → v0.32.68) |
| `SMP_TLB_SHOOTDOWN_PLAN.md` | WS-SM SM7 TLB shootdown and cache maintenance (landed, v0.32.72 → v0.32.151) |
| `SMP_INFORMATION_FLOW_PLAN.md` | WS-SM SM8 information flow under SMP (closed, v0.33.23) |
| `SMP_DECLASSIFICATION_COMPLETION_PLAN.md` | WS-SM SM9 declassification completion (closed, v0.33.100) |
| `SYSCALL_RETURN_ABI_PLAN.md` | WS-RA syscall return ABI (complete, v0.33.38) |
| `SMP_RELEASE_READINESS_PLAN.md` | WS-RR pre-SM10 release readiness (complete, v0.35.203) |
| `SMP_LOCK_DATATYPE_COMPLETION_PLAN.md` | WS-LC lock datatype completion (complete, v0.34.55) |
| `SMP_PANIC_HANG_REMEDIATION_PLAN.md` | WS-SM SM2.E panic/hang remediation (landed) |
| `SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md` | WS-SM SM2 verified lock primitives (landed, v0.31.9) |
| `WS_RC_R4_TYPE_LEVEL_PROMOTION_PLAN.md` | WS-RC R4 type-level promotion (complete) |
| `IPC_INVARIANT_DETHREADING_PLAN.md`, `V3B_LOAD_FACTOR_BOUNDED_MIGRATION_PLAN.md`, `V3E_IPC_UNWRAP_CAPS_LOOP_COMPOSITION_PLAN.md`, `V3_PROOF_CHAIN_HARDENING_E_G6_PLAN.md`, `WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md`, `WS_V_KERNEL_STARVATION_PREVENTION_PLAN.md`, `WS_X_LEAN_ETHEREUM_FORMALIZATION_PLAN.md`, `WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md` | Plans archived before this index existed; each file's status line is its status when archived, and `docs/REGISTERED_DEBT.md` is authoritative |

### Licensing research (`licensing_research/`)

| File | Description |
|---|---|
| `LICENSE_REVIEW.md` | Pre-adoption MIT license review |
| `LICENSE_REVIEW_UPDATED.md` | Updated license review |

## Audit lineage

The **active** audit baseline is `docs/audits/AUDIT_v0.30.11_*`, and the
pre-SM10 completeness audit is `docs/planning/UNFINISHED_SMP_WORK.md`.
Workstream status and history are in `docs/REGISTERED_DEBT.md` and
`CHANGELOG.md`. The files here provide the predecessor audit chain for
traceability only.
