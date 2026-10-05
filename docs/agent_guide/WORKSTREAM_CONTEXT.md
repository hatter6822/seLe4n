# Workstream context (agent reference)

> Status of the active workstreams and the standing constraints new code must
> assume.  Moved verbatim from `CLAUDE.md` (and its former `AGENTS.md` mirror) so the
> auto-loaded agent guidance stays small; only relative link targets were
> rewritten.  The sections for **closed** workstreams (WS-RA, WS-OD, WS-RM,
> WS-HP, WS-LC) are archived verbatim in
> [`docs/dev_history/planning/CLOSED_WORKSTREAM_CONTEXT.md`](../dev_history/planning/CLOSED_WORKSTREAM_CONTEXT.md).
> Workstream status is canonical in
> [`docs/REGISTERED_DEBT.md`](../REGISTERED_DEBT.md); per-version detail is in
> [`CHANGELOG.md`](../../CHANGELOG.md).

## Active workstream context

**This section is a status index, not a history.**  It says what is in flight,
what each phase covers in one line, and where the detail lives.  Per-sub-task
landing notes, audit-pass refinements, review-cut narratives and closeout
details belong in the canonical sources and must not be restated here:

- [`docs/REGISTERED_DEBT.md`](../../docs/REGISTERED_DEBT.md) — the workstream
  *index*: current status, the open phases' obligations, and the project's
  single debt register.  Not the narrative.
- [`CHANGELOG.md`](../../CHANGELOG.md) — the per-version narrative, one entry per PR.
- `docs/planning/SMP_*.md` — the per-phase plans, linked from the table below.

When a cut lands, update the row's status/version here and write the detail in
`CHANGELOG.md` and `docs/REGISTERED_DEBT.md`.  A row that grows past one line
of summary is a sign the narrative belongs in those files instead.

### WS-CB Hierarchical constant-bandwidth servers — PLANNED (registered v0.34.49)

A `SchedContext` will be able to contain other scheduling contexts: a *server*
holds members instead of a thread, is charged whenever a thread in its subtree
runs, and admits its members against its own budget, so a component's threads
share one reservation and nothing outside the component is delayed by more than
that reservation.  The root scheduler becomes **EDF-first** (maintainer's
decision at planning time): deadlines are kernel-owned CBS deadlines, priority
is the tie-break for deadline-bearing threads and the order of the legacy
unbound class, and priority inheritance becomes deadline inheritance for the
EDF class — a change to the flat model that CB1 lands as three switch cuts,
each with its proofs and its fixture refresh, before any server exists.  Servers are core-homed, members
share the server's security label, and every generalising cut after CB1
carries the theorem that the model is unchanged on states without servers.
No sub-task has started.  The plan also records three pre-existing findings it
closes first: `schedContextConfigure` applies priority, domain and a
caller-supplied deadline to the bound thread under the SchedContext write right
alone, with no caller-MCP check (CB0.3, CB1.6); and the live tick's exhaustion
arm schedules a refill of at most one tick, so a bound thread receives about one
tick per period after its first window (CB1.6, which moves the engine to
per-window refills).  Thirteen review rounds on the planning PR reshaped the design
before any code exists — a transitive tie-break, a key-worsening reschedule
seam, reconfiguration that never mints budget, every reservation move
re-admitted per core, label uniformity over bindings, inheritance for bound
blockers only, the guarantee scoped to roots — and the plan's §14 records each
finding against its fix, and its §14 names the five classes the findings
fell into with the rule that closes each.

Plan: [`docs/planning/HIERARCHICAL_CBS_PLAN.md`](../../docs/planning/HIERARCHICAL_CBS_PLAN.md).

### WS-SM SMP multi-core completion — IN FLIGHT (v0.31.2 → v1.0.0)

Unified workstream merging WS-RC's remaining R6..R14 phases with the SMP-specific
SM-phases (SM0..SM10).  Closes at v1.0.0 with a bootable verified SMP microkernel
on Raspberry Pi 5.

**Binding decisions**: per-object RW fine locks; path-a `Vector` state
replacement; hierarchical-by-kind lock order (`LockKind` levels 0..9 from SM0.I);
SMP enabled by default at v1.0.0; `numCores` via `PlatformBinding.coreCount`
(RPi5 = 4); verified `TicketLock` + `RwLock` with formal mutex/fairness theorems;
SGI INTID 0..4 reserved for kernel SMP coordination (SM0.H).

| Phase | Status | Version | Scope (one line — detail in the canonical sources) |
|-------|--------|---------|----------------------------------------------------|
| SM0 | CLOSED | v0.31.3 | Foundational types, honesty patches, lock hierarchy |
| SM1 | CLOSED | v0.31.8 | Rust HAL: PSCI, per-CPU, secondary init, TLBI, SGI, QEMU |
| SM2 | LANDED | v0.31.9; SM2.C-defer closed v0.34.50 | Memory model, TicketLock, RwLock, FFI bridge, refinement (WS-RR RR6 closed the deferred completion: the deployed lock is `QueuedRwLock` and refines the FIFO spec) |
| SM3 | CLOSED | v0.31.9 | Per-object locks, lock sets, 2PL, deadlock-freedom, serializability |
| SM4 | LANDED | v0.31.37 | Per-core Vector state, SchedulerState, register banks, invariant migration, idle bootstrap |
| SM5.A–H | LANDED | v0.31.38–62 | Per-core scheduler: selection, switch, wake, timer, idle, PIP, domain, CBS |
| SM5.I | LANDED | v0.31.61; entry lock v0.32.142 | Per-core invariant suite + register banks; the global kernel-entry ticket lock (see the standing constraint below — the table read v0.31.38–62, which the constraint contradicted) |
| SM5.J | LANDED | v0.31.63→64 | WCRT under fine locks; per-core eventually-scheduled liveness |
| SM5.K | LANDED | v0.31.63→64 | Scheduler tests + fixtures: 4-thread/4-core aggregate suite, WCRT suite, golden trace |
| SM6.A | LANDED | v0.31.65→67 | Endpoint call across cores, live `.call` dispatch + SGI-firing seam |
| SM6.B | LANDED | v0.31.68→76 | Notification across cores + bound notifications, live |
| SM6.C | LANDED | v0.31.77 | Reply path across cores + live `.reply` / `.replyRecv` dispatch |
| SM6.D | LANDED | v0.32.58→59 | IPC across-core invariant bundle (`ipcInvariantFull_perCore`) |
| SM6.E | LANDED | v0.32.60→66 | Cancellation across cores; live `.tcbSuspend` cross-core dispatch |
| SM6.F | LANDED | v0.32.67→68 | SM6 closure: IPC + notification suites, 4-core golden fixture |
| SM7.A | LANDED | v0.32.72→75 | TLB shootdown descriptor + per-core pending/ack state |
| SM7.B | LANDED | v0.32.76→79 | Shootdown protocol, complete and live (Theorem 3.3.1, round lock, bounded wait) |
| SM7.C | LANDED | v0.32.80→83 | Per-core TLB model, mounted and wired to the shootdown protocol |
| SM7.D | CLOSED (model level) | v0.32.94→102 | Cache maintenance broadcast — the instruction-cache half of SMP-C4 |
| SM7.E | LANDED | v0.32.103 | SM7 closure: shootdown storm, cross-cluster mock, golden fixture |
| SM7.F | LANDED | v0.32.84→105; F.5 v0.32.150–151 | Operative per-core TLB fills; round-generation-tagged descriptors |
| SM8.A | LANDED | v0.33.2→4 | Per-core observable state — the SMP information-flow observer |
| SM8.B | LANDED | v0.33.5 | Per-core non-interference — the SMP lift of the whole NI surface |
| SM8.C | LANDED | v0.33.7→8 | Per-core declassification audit + the producer that did not exist |
| SM8.D | LANDED | v0.33.9→22 | Information flow under fine locks; CC-5 contention channel bounded |
| SM8.E | LANDED | v0.33.23 | SM8 closure: surface anchors, observer golden fixture |
| SM9.A | LANDED | v0.33.42→50 | Audit-trail reader + drain — the 256-entry fail-closed cliff, closed |
| SM9.B | LANDED | v0.33.51 | Refusal auditing — the trail's blind spot (refused downgrades), closed |
| SM9.C | LANDED | v0.33.52 | Data-carrying declassification — the first deliberately visible flow |
| SM9.D | LANDED | v0.33.53→56 | Causal declassification provenance — the laundering detector stops guessing |
| SM9.E | LANDED | v0.33.100 | Tests + closure: acceptance scenarios run live and pinned as golden fixtures; seam boundary coverage of both declassifying syscalls; the epoch exercised with survivors |
| SM9 | CLOSED | v0.33.100 | Declassification completion — reader, refusal auditing, data-carrying signal, causal provenance, acceptance fixtures |
| SM5 runtime seams | LANDED | v0.34.1 | The three seams SM5's docstrings promised between the verified per-core scheduler and the hardware IRQ path — IRQ vector redirect, `.reschedule` SGI receiver, secondary bring-up entry — all dormant behind the per-core `lean_ready` gate until SM10.1 |
| WS-RR | **COMPLETE** | v0.34.26–v0.35.203 (RR0 v0.34.26; RR1 v0.34.41; RR2 v0.34.42; RR3 v0.34.43; RR4 v0.34.44; RR5 v0.34.48; RR6 v0.34.50; RR7 v0.34.47 → v0.34.92; RR8 v0.35.55 → v0.35.203, RR8 having grown 5 → 16 rows at v0.35.56) | Pre-SM10 remediation: the audit's 3 blockers, 11 security findings, fault IPC, de-threading closure, lock completion (**198** subs across RR0..RR8 — the figure the plan declares and the gate holds it to; this cell read 187 until v0.35.203) |
| SM10 | **UNBLOCKED v0.35.203** | — | Release closure (→ v1.0.0); SM10.1's content is **WS-BP** (see above), which opens first |

**Plans**: master overview at
[`docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md`](../../docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md);
per-phase plans at `docs/planning/SMP_*.md` while a phase is open.  A closed
phase's plan is archived in `docs/dev_history/planning/` and is named in the
lookup table below, beginning with
[`SMP_FOUNDATIONS_PLAN.md`](../dev_history/planning/SMP_FOUNDATIONS_PLAN.md) (SM0), which
no canonical index named until WS-RR RR7.32 made that checkable.

#### Archived plans by ID

Source, tests and Rust cite a closed plan by its **workstream or phase ID**, not
by path.  Review holds source to that rule; no gate checks it.  This table
resolves an ID to its plan.  A sub-task ID after the workstream
(`WS-SM SM3.A.10`, `WS-RA RA.B.5b`, `WS-RR RR8.12`) is a row in that plan; a
`§` after a phase ID (`WS-SM SM6 §3.1`) is a section of it.
Each plan's status line is its status when archived; current status is the
phase table above and `docs/REGISTERED_DEBT.md`.

Write a citation in one form, `WS-<FAMILY> <PHASE>[.<SUB>…]`
(`WS-SM SM5.H.4`): the phase follows the workstream after a single space, on
the same line.  A phase parted from its workstream by punctuation or the word
"phase" (`(WS-SM, SM5.H.4)`, `WS-Z/Z6`, `WS-SM (SM0.C …)`) reads as the bare
workstream.  When you archive a plan that source still cites, add its row here
in the same change.

| ID | Archived plan | Closed |
|----|---------------|--------|
| WS-SM SM0 | [`SMP_FOUNDATIONS_PLAN.md`](../dev_history/planning/SMP_FOUNDATIONS_PLAN.md) | v0.31.3 |
| WS-SM SM1 | [`SMP_RUST_HAL_PLAN.md`](../dev_history/planning/SMP_RUST_HAL_PLAN.md) | v0.31.8 |
| WS-SM SM2 | [`SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](../dev_history/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md) | v0.31.9 |
| WS-SM SM2.C-defer | [`SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md`](../dev_history/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md) | v0.34.50 (by WS-RR RR6) |
| WS-SM SM2.E | [`SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](../dev_history/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md) §5.5 defines the phase; its queued-lock panic and hang remediation is [`SMP_PANIC_HANG_REMEDIATION_PLAN.md`](../dev_history/planning/SMP_PANIC_HANG_REMEDIATION_PLAN.md) | v0.32.148 |
| WS-SM SM3 | [`SMP_PER_OBJECT_LOCKS_PLAN.md`](../dev_history/planning/SMP_PER_OBJECT_LOCKS_PLAN.md) | v0.31.9 |
| WS-SM SM4 | [`SMP_PER_CORE_STATE_PLAN.md`](../dev_history/planning/SMP_PER_CORE_STATE_PLAN.md) | v0.31.37 |
| WS-SM SM4.G | [`SMP_PER_CORE_STATE_PLAN.md`](../dev_history/planning/SMP_PER_CORE_STATE_PLAN.md) names the idle-thread cut only in its status notes; the [`CHANGELOG.md`](../../CHANGELOG.md) v0.31.36 entry defines it | v0.31.36 |
| WS-SM SM5 | [`SMP_PER_CORE_SCHEDULER_PLAN.md`](../dev_history/planning/SMP_PER_CORE_SCHEDULER_PLAN.md) | v0.31.64 |
| WS-SM SM6 | [`SMP_CROSS_CORE_IPC_PLAN.md`](../dev_history/planning/SMP_CROSS_CORE_IPC_PLAN.md) | v0.32.68 |
| WS-SM SM7 | [`SMP_TLB_SHOOTDOWN_PLAN.md`](../dev_history/planning/SMP_TLB_SHOOTDOWN_PLAN.md) | v0.32.151 |
| WS-SM SM7.F.5 | [`SMP_TLB_SHOOTDOWN_PLAN.md`](../dev_history/planning/SMP_TLB_SHOOTDOWN_PLAN.md) names the access-time TLB fill only in its status line; the [`CHANGELOG.md`](../../CHANGELOG.md) v0.32.150 entry defines it | v0.32.151 |
| WS-SM SM8 | [`SMP_INFORMATION_FLOW_PLAN.md`](../dev_history/planning/SMP_INFORMATION_FLOW_PLAN.md) | v0.33.23 |
| WS-SM SM9 | [`SMP_DECLASSIFICATION_COMPLETION_PLAN.md`](../dev_history/planning/SMP_DECLASSIFICATION_COMPLETION_PLAN.md) | v0.33.100 |
| WS-RA | [`SYSCALL_RETURN_ABI_PLAN.md`](../dev_history/planning/SYSCALL_RETURN_ABI_PLAN.md) | v0.33.38 |
| WS-RR | [`SMP_RELEASE_READINESS_PLAN.md`](../dev_history/planning/SMP_RELEASE_READINESS_PLAN.md) | v0.35.203 |
| WS-RC R4 | [`WS_RC_R4_TYPE_LEVEL_PROMOTION_PLAN.md`](../dev_history/planning/WS_RC_R4_TYPE_LEVEL_PROMOTION_PLAN.md) (R4.A, R4.C) and [`WS_RC_R4_CLOSEOUT_PLAN.md`](../dev_history/audits/WS_RC_R4_CLOSEOUT_PLAN.md) | v0.31.0 |
| WS-RC R5 | [`WS_RC_R5_DEFERRED_COMPLETION_PLAN.md`](../dev_history/audits/WS_RC_R5_DEFERRED_COMPLETION_PLAN.md) | v0.31.2 |
| WS-DT | [`IPC_INVARIANT_DETHREADING_PLAN.md`](../dev_history/planning/IPC_INVARIANT_DETHREADING_PLAN.md) | v0.34.43 |
| WS-LC | [`SMP_LOCK_DATATYPE_COMPLETION_PLAN.md`](../dev_history/planning/SMP_LOCK_DATATYPE_COMPLETION_PLAN.md) | v0.34.56 |
| WS-OD | [`SCHEDCONTEXT_DONATION_CHAIN_PLAN.md`](../dev_history/planning/SCHEDCONTEXT_DONATION_CHAIN_PLAN.md) | v0.35.2 |
| WS-RM | [`REPLY_FRAME_REMOVAL_PLAN.md`](../dev_history/planning/REPLY_FRAME_REMOVAL_PLAN.md) | v0.35.6 |
| WS-HP | [`DONATION_POP_TRIGGER_PLAN.md`](../dev_history/planning/DONATION_POP_TRIGGER_PLAN.md) | v0.35.54 |

WS-SM's open phase, SM10, keeps its plan under `docs/planning/` (see
**Plans** above).  WS-RC's other phases are in the live
[`AUDIT_v0.30.11_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md).

What these plans still held open is a row in `docs/REGISTERED_DEBT.md`, not
an obligation of the archived file: SM6's `withLockSet` bundle carriage
(fine-lock Track D), SM7.D items 2 and 5, WS-RA's application IPC label
(owner WS-CB, with both candidate designs stated in the row), and WS-RC R4's
two follow-on promotions.

##### Audit-era workstreams

Each workstream before WS-RC was planned in one audit workstream plan, archived
under `docs/dev_history/`.  Its sub-IDs (`WS-H12b`, `WS-K-F5`, `WS-J1-D`,
`WS-Q1-D`) are sections of that plan, and its version range is its row in the
workstream registry of `docs/REGISTERED_DEBT.md`.  Only workstreams that code
still cites are listed.  The milestone era reused the `WS-M` prefix: `WS-M5`
alone is WS-M's phase 5, while `WS-M5-C` and `WS-M6-A`–`C` are milestone
workstreams with rows of their own.

| ID | Archived plan |
|----|---------------|
| WS-A | phases A1–A8: [`20-repository-audit-remediation-workstreams.md`](../dev_history/gitbook/20-repository-audit-remediation-workstreams.md), closed by [`M7_CLOSEOUT_PACKET.md`](../dev_history/M7_CLOSEOUT_PACKET.md) |
| WS-B | [`AUDIT_v0.9.0_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.9.0_WORKSTREAM_PLAN.md) |
| WS-C | [`AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md) |
| WS-D | [`AUDIT_v0.11.0_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md) |
| WS-E | [`AUDIT_v0.11.6_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md) |
| WS-F | [`AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md) |
| WS-G | [`KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md`](../dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md) |
| WS-H | [`AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md) |
| WS-I | [`AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md) |
| WS-J1 | [`AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md) |
| WS-K | [`AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md) |
| WS-L | [`AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md) |
| WS-M | [`AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md) |
| WS-M5-C | Milestone M5's policy-surface workstream: [`15-m5-development-blueprint.md`](../dev_history/gitbook/15-m5-development-blueprint.md) |
| WS-M6 | Milestone M6's workstreams A–C: [`18-m6-execution-plan-and-workstreams.md`](../dev_history/gitbook/18-m6-execution-plan-and-workstreams.md) |
| WS-N | [`AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md) |
| WS-Q | [`MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md`](../dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md) |
| WS-R | [`AUDIT_v0.17.14_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md) |
| WS-T | [`AUDIT_v0.19.6_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.19.6_WORKSTREAM_PLAN.md) |
| WS-U | [`AUDIT_v0.20.7_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md) |
| WS-V | [`AUDIT_v0.21.7_WORKSTREAM_PLAN.md`](../dev_history/AUDIT_v0.21.7_WORKSTREAM_PLAN.md); phase V3's detail plans are [`V3B_LOAD_FACTOR_BOUNDED_MIGRATION_PLAN.md`](../dev_history/planning/V3B_LOAD_FACTOR_BOUNDED_MIGRATION_PLAN.md), [`V3E_IPC_UNWRAP_CAPS_LOOP_COMPOSITION_PLAN.md`](../dev_history/planning/V3E_IPC_UNWRAP_CAPS_LOOP_COMPOSITION_PLAN.md) and [`V3_PROOF_CHAIN_HARDENING_E_G6_PLAN.md`](../dev_history/planning/V3_PROOF_CHAIN_HARDENING_E_G6_PLAN.md).  [`WS_V_KERNEL_STARVATION_PREVENTION_PLAN.md`](../dev_history/planning/WS_V_KERNEL_STARVATION_PREVENTION_PLAN.md) is a separate plan under the same name. |
| WS-W | [`AUDIT_v0.22.10_WORKSTREAM_PLAN.md`](../dev_history/AUDIT_v0.22.10_WORKSTREAM_PLAN.md) |
| WS-Z | [`WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md`](../dev_history/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md) |
| WS-AB | [`WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md`](../dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md) |
| WS-AC | [`AUDIT_v0.25.3_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.25.3_WORKSTREAM_PLAN.md) |
| WS-AD | [`AUDIT_v0.25.10_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.25.10_WORKSTREAM_PLAN.md) |
| WS-AG | [`AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md) |
| WS-AK | [`AUDIT_v0.29.0_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md) |
| WS-AL, WS-AM | No plan of their own.  Both continue WS-AK's AK7 cascade, which [`AUDIT_v0.29.0_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md) proposes as WS-AL.  Their phases (`AM1`, `AM4`, …) are the `###` headings of the v0.29.13–v0.30.0 entries in [`CHANGELOG.md`](../../CHANGELOG.md). |
| WS-AN | [`AUDIT_v0.30.6_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md) |

### WS-BP The bare-metal boot path — IN FLIGHT (registered v0.34.59; absorbs WS-XV as BP0 at v0.34.124; BP0, BP1, BP2, BP3, BP4, BP5 and BP6 v0.36.2; the v0.36.2 audit added BP7.10 and BP7.11; BP7.10 v0.36.3; BP7.1 slice 1 v0.36.4, slice 2 v0.36.5, slice 3 v0.36.6; frame capabilities own their mappings v0.36.7; slice 4a (child untypeds, subtree resets) v0.36.8; in-place VSpace-root creation refused v0.36.9; slice 4b (VSpace roots carved from untypeds) v0.36.10; a thread runs in a carved address space v0.36.11; intermediate page tables v0.36.12; every configured root owns a table page v0.36.13, completing BP7.1; BP7.2's user window and 16-bit ASIDs v0.36.14; its physical-write ledger and translation install v0.36.15, completing BP7.2; the whole trap frame saved at every entry v0.36.16, BP7.3; each core's resume staged per core v0.36.17, BP7.4; the staged unblock frames delivered v0.36.18, BP7.5; the context restore live v0.36.19, BP7.6; the declassified badge delivered v0.36.20, BP7.7; message registers past the fourth, both directions, v0.36.21, BP7.8; per-thread FP/SIMD state switched lazily v0.36.22, BP7.9; both initial threads started, one per domain, v0.36.23, BP7.11, completing BP7; BP8.1 slice 1, the image built for QEMU's `virt` and booted there at EL1 and EL2, v0.36.24; slice 2, the Lean `virt` binding and its boot entry, v0.36.25; slice 3, the Lean-linked image booted on four PEs to every core's first idle dispatch in CI, v0.36.26, completing BP8.1; BP8.2, the four-PE bring-up gate executed in CI, v0.36.27; BP8.4, the Tier-4 gates executed on the `virt` test image, v0.36.28; BP8.5, the per-core counters read on the booted machine, v0.36.29; the BP2.4, BP2.5 and BP4.2 acceptance boxes decided by QEMU runs, v0.36.31)

SM10.1 is not a release cut's first phase; it is a **bare-metal Lean runtime
port**, and holding the two in one plan produced a phase goal ("all substantive
SMP work is complete") that was false of the phase's own first row.  WS-RR
RR7.5 + RR7.15 split it out: [`docs/planning/SMP_BOOT_PATH_PLAN.md`](../../docs/planning/SMP_BOOT_PATH_PLAN.md)
sequences **50 sub-tasks across 9 phases `BP0..BP8`** in execution order — the
cross-implementation gates, the aarch64 Lean object code, bare-metal runtime
hosting, the RPi5 deployment, the boot seam and its install ordering, the
image, per-core readiness, the context restore, and first boot — with an acceptance gate whose every box is ticked by
an *executed run* rather than by an artefact existing.  **BP0 and BP1 landed at
`v0.36.2`**, and so did **BP2.1** (the Lean heap), **BP2.2** (the kernel's own Lean runtime, in Rust), **BP2.3**/**BP2.4** (the library initializer, failing closed), **BP2.5** (the host witnesses, which landed with the first two) and **BP2.6** (the boot map built from constants), and **BP3** (the RPi5 deployment, which boots, and the proof-layer bundle of the state it installs), and **BP4.1**/**BP4.2** (the `lean_kernel_main` entry, and the install ordered before the secondaries by a type), and **BP4.3**/**BP4.4** (the firmware's device tree reaching Lean, and the entry booting on it), and **BP4.5** (the boot image cleaned to the Point of Unification before any thread can fetch), and **BP4.6** (the verified board's RAM mapped above the guaranteed gigabyte), and **BP4.7** (that RAM handed to the root task as untypeds), and **BP5.1** (the kernel image, a bare-metal binary entered at `_start` under `link.ld`), and **BP5.2** (the Lean kernel linked into that image, under `--gc-sections` from the archive lane's own roots), and **BP5.3** (the firmware's boot files, `kernel8.img` and `config.txt`, cut from that image and checked against it), and **BP5.4** (the image's size and section map published with every CI run), and **BP5.5** (the firmware's EL2 entry dropped to EL1, with the PSCI conduit following the entry level), and **BP6** (every PE marks itself ready after its own per-PE runtime handshake and before it unmasks IRQs, and the boot halts unless every declared PE serves the kernel); and **BP7.10**
landed at `v0.36.3` (the first gigabyte's RAM read off the firmware's account,
and the HAL's constant boot map shrunk to the kernel's reserved extent), and
**BP7.1**'s first slice at `v0.36.4` (frames: memory as authority, closing a
raw-physical-address `.vspaceMap`), its second at `v0.36.5` (the live untyped
carve, `.untypedRetype`, so a frame — and mappable memory — is reachable) and its
third at `v0.36.6` (the untyped reset, `.untypedReset`, so memory returns to the
untyped it was carved from), and at `v0.36.7` the security fix that slice 3
found (a frame capability owns the mapping it made, so destroying it unmaps),
and at `v0.36.8` its slice 4a (an untyped carves child untypeds, and a reset
returns everything carved from it at any depth), and the rest of BP7 through
`v0.36.23` (the paragraphs below); BP8.1 landed in three slices at `v0.36.24`–`v0.36.26` and BP8.2 at `v0.36.27` (the last four paragraphs below).  **WS-BP is unblocked since `v0.35.203`**, WS-RR RR8 having closed.  BP7.8 was added
at that version by RR8.16's hand-off check, which re-homed the registered `MR4`-onward
IPC-buffer write there rather than leaving it owned by a finished phase; BP5.5
(the firmware's EL2 entry) and BP7.9 (per-thread FP/SIMD state) were added at
`v0.36.2` by the FP-free-kernel cut below.

Four things new code must respect.  **WS-BP takes its own prefix and renumbers
nothing**: `SM10.1.1` still means the image *packaging* the release cut
consumes, and `BP5.3` is the sub-task that produces what it packages — the
collision between "numbering is execution order" and "IDs in CHANGELOG entries
are frozen" resolved the way `SMP_RELEASE_CLOSURE_PLAN.md` §1.1 named it.  And
the three `contextRestoreSeamLive` prerequisites were scheduled rather than
only described: `BP7.1`/`BP7.2` (the `VSpaceRoot → TTBR0` binding and its
install), `BP7.3` (the full outgoing-frame save — `writeFfiRegistersToTcb`
spilled only x0–x5 and x7 until it landed), `BP7.4` (per-core staging), with `BP7.6` the
flip they gated — which deleted the flag at `v0.36.19`.

And **the boot map is BP2.6's, not the device tree's** (the maintainer's
correction, recorded as a scheduled row rather than as prose, and landed at
`v0.36.2` — the BP2.6 paragraph below).  `init_mmu` used to parse the firmware
blob *before* translation was enabled, to obtain a RAM *size* the boot map does
not need; the verified Lean parser is now the only reader of the blob's memory,
so the device-tree half of the WS-XV pair stopped existing rather than being
gated — which is what [`docs/REGISTERED_DEBT.md`](../../docs/REGISTERED_DEBT.md)
table C named as that pair's remedy.

And **WS-XV is BP0, not a workstream** (`v0.34.124`).  The cross-implementation
findings registered at `v0.34.114` were never given a plan file, and reading
their five rows back showed why: XV1 was always a WS-BP obligation and became
**BP2.6**; XV2 and XV3 were interim *by their own text* ("only if XV1 is far
off"), and BP2.6 retargeted them onto the half of the pair it kept (the Rust
structure walk the bootargs reader runs); XV4 and XV5 sit on surfaces this plan modifies
— the ABI BP7's context restore delivers, and the boot map BP2.6 rebuilds.
Half of WS-XV is deleted by WS-BP's own work and the other half is a harness
over what WS-BP changes.  BP0 is first because its value decays as the rest
lands, and it is the one phase that may run **in parallel** with any other:
nothing in BP1..BP8 consumes it, and the only coupling was BP2.6 retargeting two
of its rows and updating a third.  `docs/REGISTERED_DEBT.md` keeps the WS-XV
*finding* — the evidence that nominal gates miss behavioural drift — and no
longer a work list.

**BP0 — the three Lean/Rust pairs are driven through shared fixtures** (`v0.36.2`).
Four things new code must respect.  (1) **A question answered on both sides
of the boundary is compared by running both, never by a literal beside a
comment naming the other side.**  The device-tree readers share
`tests/fixtures/dtb/` (hand-written expectations in
`scripts/generate_dtb_corpus.py`, never in the rendered files); the ABI's bit
layout, register assignment and bounds share `tests/fixtures/abi_layout.expected`;
the boot map and the Lean memory map share `tests/fixtures/boot_map.expected`.
Both Lean tables go through `SeLe4n.Testing.checkSharedFixture`, and a new
two-sided table does too.  (2) **A divergence the fixtures expose is fixed on the
side that is wrong, never recorded as an exception**: the first run fixed thirteen
Rust and eight Lean refusals, so both readers now share one rule set — the Rust
walk runs `fdt_structure_check` first, the Lean parser bounds depth
(`fdtMaxDepth`), extent count (`fdtMaxMemoryExtents`) and 64-bit ends, and neither
reads a cell width that is not one `<u32>`.  (3) **A Rust FDT walk's bound is the
structure block's size** (`fdt_token_bound`), never a fixed fuel: 4096 tokens
refused a large well-formed device tree the Lean parser reads whole.  (4) **The
boot map is held to the Lean map**: every address it maps Normal is RAM in every
variant, its device window is exactly the Lean one (the BCM2712's SoC-bus
window, both ends 2 MiB aligned), and on the smallest variant its
RAM is exactly the variant's; `check_physical_address_width.sh` no longer
regex-parses `Board.lean` — the driven test decides it.

**The kernel is FP-free, and FP/SIMD traps at EL1** (`v0.36.2`, found while
scoping BP1).  Rust's `aarch64-unknown-none` enables `neon` and `fp-armv8`, and
the HAL built for it carried 129 FP/SIMD instructions (vector zeroing, `d8`–`d15`
spills) while the trap frame saves general-purpose registers only and nothing
wrote `CPACR_EL1` — so on hardware the first vector instruction either trapped
unhandled or, with FP access left on by firmware, every trap silently overwrote
the interrupted thread's `q0`–`q31`.  Latent (no core runs the Lean runtime
yet) and closed before it could ship.  Four things new code must respect.  (1)
**The HAL's target is `aarch64-unknown-none-softfloat`** — `rust-toolchain.toml`,
the cross gate, CI and every script that names it — so FP-freedom is a property
of code generation, as it is for seL4's kernel; the Lean C is compiled with
`-mgeneral-regs-only` for the same reason (BP1.2).  (2) **Both boot entries write
`msr cpacr_el1, xzr` then `isb` as their first instructions at EL1** — right
after `.L_enter_el1` returns, since at EL2 with `HCR_EL2.E2H` set (UNKNOWN at
reset) that encoding names `CPTR_EL2` (the `v0.36.2` audit reordered the two) —
trapping FP/SIMD/SVE/SME at EL0 and EL1 before anything else runs on the PE at
that level, and `build.rs`'s `scan_fp_trap_prologue`
requires exactly that prologue at `_start` and `secondary_entry` and refuses any
other write to `CPACR_EL1` in either spelling (`S3_0_C1_C0_2` included) in any
`.S` file or `asm!` template — except the lazy FP switch's four pinned routines
in `fp_context.S` since BP7.9 (`FP_CONTEXT_CPACR_WRITERS`, the paragraph on
BP7.9 below).  There is no encoding that traps EL1 alone, so a **user** FP
instruction traps too, and since BP7.9 that trap *is* the lazy switch: the
thread's own context is loaded and the trap lifted for it.  (3)
**`scripts/check_fp_simd_free_objects.py` is the evidence rather than the flag**:
the cross gate's step [5/7] disassembles the release rlib and the assembly
archive and refuses any FP/SIMD/SVE register operand or `FPCR`/`FPSR` access,
reading operands only and refusing input it cannot decide — save for the two
FP routines of `fp_context.S`, exempt by symbol and reconciled both ways since
BP7.9 — and
`check_aarch64_cross_target.py` requires that step — executed, over those two
release objects, not followed by `&&`/`||` (which exempts a command from
`set -e`; that check now covers the cross builds and the lint too).  (4) **It is
conclusive only on the linked image**: the target's own `compiler_builtins` is
*not* FP-free (the complex-arithmetic helpers and `__negsf2`/`__negdf2` use
`d`/`v` registers, and `__negdf2` takes a hard-float `d0` argument no soft-float
caller supplies), so the gate also runs over the linked image, where the link
decides which members are in (BP5.2: none of them is).  And the firmware enters the RPi5 at **EL2**, which
`boot.S` handles since BP5.5 (the paragraph below).

**BP1 — the kernel's Lean object code for the target is built and checked**
(`v0.36.2`, `scripts/build_lean_aarch64_archive.py`, lane
`scripts/test_lean_aarch64_archive.sh`, CI job `Lean aarch64 Archive`).  Five
things new code must respect.  (1) **The image's Lean is the elaborator's
closure of `SeLe4n`**, refused unless it equals Lake's `SeLe4n:modules`, holds
nothing outside `SeLe4n`/`Init`/`Std` and is disjoint from the staged allowlist
and `SeLe4n.Testing` — so importing `Lean.*` from a production module, or a
staged module, fails the lane rather than putting the elaborator in the kernel.
(2) **The allocator is a relation**: every object is compiled against
`rust/sele4n-hal/lean_include/lean/config.h`, the toolchain's with
`LEAN_MIMALLOC` swapped for `LEAN_SMALL_ALLOCATOR` and nothing else, and the
archive must call `lean_alloc_small` and no `mi_*`; the kernel's runtime
(BP2.2) serves the same allocator.  A macro the toolchain adds to its `config.h` stops the
build until it is classified.  (3) **The compile is soft-float and `-Werror`**
(`-mgeneral-regs-only -mabi=aapcs-soft`, the toolchain's own clang), and the
generator's two by-construction diagnostics are classified per instance — an
`x_N` temporary holding a discarded `BaseIO Unit`, an import-less initializer's
`res` — so any other warning, or either kind in another shape, fails.  (4) **The
stdlib C is regenerated, and proved to be the toolchain's**: each of the 609
closure stdlib modules must define exactly the global symbols the toolchain's
own `libInit.a`/`libStd.a` object for it defines — keyed by the member's
initializer, never its name, since `libInit.a` holds two `Grind.o`.  (5)
**Every unresolved symbol is attributed to a provider derived from that
provider's own object code or declarations** — allocator, the HAL (a production
module's `@[extern]`), the kernel's runtime (BP2.2), Rust `compiler_builtins`
for the target, or *unreachable* (an upstream runtime function or stdlib
`@[extern]` the reachable link proves nothing names) — and an unattributed one
stops the build.  Measured: 382 unresolved, **no libc symbol at all**.  And
`check_kernel_entry_exports.py` decides on **both** archives: a requirement is
met where both define it, an exemption stale where either does, and
`--require-cross` makes an absent cross archive a failure.  Since BP2.1 the
lane also holds the HAL-provided classes to the HAL's own object code: every
`allocator`, `hal` and (since BP2.2) `runtime` symbol, and the whole
small-allocator API, must be a global **function** of `sele4n-hal`'s rlib for the
target (193 of 193 at `v0.36.2`).

**BP2.1 — the Lean heap is one arena the linker places** (`v0.36.2`,
`rust/sele4n-hal/src/lean_heap.rs`).  Five things new code must respect.  (1)
**The arena's extent is `link.ld`'s, and nothing else's**: a `NOLOAD`
`.lean_heap` of `LEAN_HEAP_SIZE` (64 MiB) above the image and both stacks, three
`ASSERT`s (whole pages, page-aligned, inside the smallest board's `[0, 1 GiB)`),
each proved live by `scripts/check_link_script.py` — the cross lane's step
[6/7], which links a probe under the script and mutates it until every
assertion fires, because until BP5.1 nothing else linked `link.ld`.  (2) **One
heap, one exhaustion condition**: the HAL exports `lean.h`'s `lean_alloc_small`
/ `lean_free_small` / `lean_small_mem_size` under `hw_target`, and the kernel's
runtime (BP2.2) allocates its big objects and scratch buffers through
`Heap::alloc` / `Heap::free` on the same arena — upstream's `alloc.cpp` is not
linked at all.  (3) **All allocator state is out of band**, so the allocator never
touches the memory it serves, every free is validated in release builds (a
double free is refused, not absorbed), and every operation is bounded; a new
allocator feature must keep its state in the metadata pages, never inside an
object.  (4) **The C entry points halt** on a refusal and on exhaustion, after
releasing the heap's leaf lock — `lean.h`'s inline paths do not test the result,
so there is no error to return.  (5) **The boot map covers the arena, and a
device tree inside the image is refused**: the arena lies in the kernel's
reserved extent, the RAM the constant map covers (BP7.10), and `init_mmu` refuses a device-tree window overlapping
`[_start, __lean_heap_end)` (`mmu::kernel_extent`, `dtb_disjoint_from_image`) — the firmware places the blob by the image *file*'s
size, and everything past it is `NOLOAD`.  Placing the arena also found that no
boot refusal stops an untyped over kernel memory (`bootSafeUntypedCheck` accepts
every region); not attacker-reachable, registered in `docs/REGISTERED_DEBT.md`
table B, owned by BP3.2.

**BP2.2 — the kernel's Lean runtime is its own, in Rust** (`v0.36.2`,
`rust/sele4n-hal/src/lean_runtime/`; maintainer's decision: no C++ in the image).
Upstream's `libleanrt` is C++ over the standard library, threads and an OS; the
kernel provides the part its Lean objects reach.  Seven things new code must
respect.  (1) **The surface is derived**: the archive lane links `libsele4n.a`
with `--gc-sections` rooted at the library initializer — `initialize_seLe4n_SeLe4n`,
package-prefixed; an earlier probe rooted at `initialize_SeLe4n` measured 62
because the root was silently absent — and every production `@[export]`, and
every symbol that link leaves undefined must be a global function of the HAL's
rlib or `compiler_builtins`' (the builder prints how many).  The upstream
functions the runtime omits are *unreachable* by that link, so the image link
(BP5.2) uses `--gc-sections` over the same roots — read from the one file the
builder writes.  (2) **Each symbol is
faithful, environmental or fail-closed, and says which**: faithful ones are
ported from `lean4` at the toolchain's commit; the environmental ones answer for
a machine with no OS (platform queries, `Lean.githash` pinned to
`lean --githash` by the lane, zero-byte entropy, temporary files failing with
`unsupportedOperation`); `Float` formatting, `scaleB` and `pow`/`powf` halt, the
last two overriding `compiler_builtins`' **weak** libm port by the linker's own
rule (the lane refuses a strong one).  (3) **Upstream is the oracle**:
`tests/LeanRuntimeConformanceSuite.lean` runs on upstream's runtime and holds
`tests/fixtures/lean_runtime_conformance.expected` (9 215 results over the
representation edges, signs, zero divisors and every UTF-8 width) to what
upstream computes; `lean_runtime::conformance` recomputes every line with the
kernel's runtime, on both the exclusive and shared paths of each mutating
string operation, checks each result canonical, and ends leak-free.  A
primitive added to the runtime gets fixture lines, or a stated reason it cannot.
(4) **What the environmental answers rest on is proved**:
`SeLe4n/Testing/RuntimeEnvironmentCensus.lean` (Tier 1) walks everything every
production `@[export]` reaches, through bodies **and `implemented_by`** — what
compiled code actually calls — and fails if it meets `IO.stdGenRef` or a
constant implemented by one of the nine unprovided symbols; its list and
`io::UNPROVIDED_SEMANTICS` are held equal by a Rust test.  (5) **The runtime
never calls back into the program it serves**: `build.rs`'s readiness scanner
refused the first draft's call to Lean's exported `IO.Error` builder, so the
constructor is built directly and its tag pinned by the fixture.  (6) **No
object is ever multi-threaded, and no task or promise exists**: nothing marks
one, the kernel's Lean code runs one core at a time under the kernel-entry lock,
and every path that would meet one halts.  `panic!` returns `default` and
reports — that is what the proofs describe, so halting there would make the
kernel diverge from its model on the paths the model covers.  (7) **A function
that dereferences an object pointer it was handed is an `unsafe fn`**, with a
`# Safety` section saying what the pointer must be — private helpers included.
The first cut had fifteen safe helpers (`array`, `string`, `ref_cell`,
`nat_val`, `slots`, `del_core`, …) whose `// SAFETY:` comments read *every
caller passes a live …*: a caller's promise inside a safe signature, which the
compiler then lets any safe caller break, and which no gate sees —
`clippy::not_unsafe_ptr_arg_deref` covers `pub` functions only, and the
justification scanner asks whether a block is *commented*, not whether the
comment discharges anything.  A helper over state it owns (`Building`, the
persistence `WorkStack`, the `apply` argument buffer) stays safe.

**BP2.3/BP2.4 — the library initializer runs first, and the order is a type**
(`v0.36.2`, `rust/sele4n-hal/src/lean_entry.rs`).  Four things new code must
respect.  (1) **`lean_kernel_main` is reachable only through
`enter_lean_kernel`**, which consumes a `LeanLibraryInitialised` token that only
a successful `initialise_with` constructs — private field, neither `Clone` nor
`Copy` — so entering the kernel uninitialised, or twice from one
initialization, does not compile.  A new Lean entry on the primary takes the
token too.  (2) **A second initialization is refused by a guard set before the
initializer runs**, because Lean's generated initializer marks itself done
before it calls anything: a retry after a failure would answer `ok` without
re-running what failed.  (3) **Success is exactly a heap constructor of tag
0**; a scalar or any other tag is *malformed* and refused rather than read as
success, and the result's reference is released on every path.  A failure
halts the **system** (`gic::halt_all`), not the PE: it is the one barrier every
boot-fatal refusal uses, and since BP4.2 it also runs before any secondary is
released, so it costs nothing to use it here too.  (4) **A
HAL-declared `initialize_…` symbol is Lean code** to `build.rs`'s readiness
derivation (`is_hal_declared_lean_symbol`, shared with the `link_name` alias
scan), so the initializer call is one of the two entries in
`LEAN_UPCALLS_OUTSIDE_THE_GATE`, and `check_kernel_entry_exports.py` requires
both archives to define it.  Upstream's `lean_initialize_runtime_module` and
`lean_io_mark_end_initialization` are not called: the kernel's runtime has no
per-thread heap, task manager or initialization flag, and the reachable link
names neither.

**BP2.6 — the boot map is built from constants, and nothing is parsed before
translation is on** (`v0.36.2`, `rust/sele4n-hal/src/mmu.rs`, `link.ld`).  Five
things new code must respect.  (1) **The map is a function of the address and
the image's layout, nothing else** (`boot_mapping_for(addr, layout)`):
`[0, KERNEL_RESERVED_END)` — the kernel's reserved extent — is Normal, the
device window Device, everything else unmapped.  (Until **BP7.10** the Normal
window was `[0, GUARANTEED_RAM_TOP)`, the first gigabyte, "the 1 GiB every
Raspberry Pi 5 has"; no board's firmware reports it whole, so the constant is
retired.)  The driven BP0.4 test requires every Normal address to be RAM in
**every** configuration's Lean map and the Normal window to equal the kernel's
extent the table declares.  Every other byte of RAM — the rest of the first
gigabyte as far as the firmware reports it, and everything above it — is
BP4.6's, mapped after the verified Lean parse (the BP4.6 and BP7.10 paragraphs
below); before that nothing past the extent is Normal and cache maintenance
there fails closed.  (2) **W^X at EL1**: the text `[_start, __text_end)`
is read-only and executable, the read-only data read-only and never executable,
and every writable page never executable.  The retired single Normal descriptor
was writable and PXN-clear while `SCTLR_EL1.WXN` is set — which makes a writable
page execute-never — so the first fetch after `enable_mmu` would have faulted,
invisible only because no image had run.  A new mapping picks one of
`BLOCK_KERNEL_TEXT` / `BLOCK_KERNEL_RODATA` / `BLOCK_NORMAL` by what it maps;
`no_page_is_writable_and_executable_and_the_text_executes` walks every page.
(3) **The section boundaries are `link.ld`'s, assigned inside the sections they
bound**: `lld` attaches a location-counter change written *between* sections to
the section that follows, so a boundary written there moves with the gap it
exists to detect.  `__rodata_start == __text_end` is an `ASSERT`, so no orphan
section can land between them and be mapped executable, and
`scripts/check_link_script.py` proves each boundary `ASSERT` live by mutation.
`link.ld`'s RAM region ends at `KERNEL_RESERVED_END` (an `ASSERT` since BP7.10),
so the linker cannot place the image where the map does not reach.  (4) **`init_mmu` reads nothing of the
blob** (a Tier 3 negative refuses any `cmdline` call in its body).  It only
checks that `dtb_window` — `MAX_DTB_SIZE` from the pointer, the bound every
reader enforces before forming a slice — lies in the kernel's reserved extent
and outside `[_start, __lean_heap_end)`, and refuses otherwise; BP5.3's `config.txt` pins
the placement to `link.ld`'s `.dtb_window`.  (5) **The bootargs reader stays, in Rust, with translation on**:
it is a Rust-only question with no Lean counterpart, and the QEMU lanes use it.
So "is this structure block readable" is still two-sided, and the shared corpus
was **retargeted rather than retired**: its manifest carries a hand-written
`structure` verdict both suites drive, and its `regions` column is the Lean
parser's alone.  Retired with a Tier 3 negative each: `ram_top_from_dtb`, the
`/memory` walk, fold and contiguity machinery, `clamp_ram_top`, `boot_ram_top`,
`dtb_dereferenced_range`, `boot_ranges_mapped_under`, `boot_critical_ranges_mapped`
and the RAM-top constants.

**BP3 — the RPi5 deployment boots, proved by evaluation** (`v0.36.2`,
`SeLe4n/Platform/RPi5/Deployment.lean`, in the library root).
The deployment (`rpi5PlatformConfigFor`, over a board account) has two domains as `confinedDeploymentLabeling` declares
them. The root task sits at the lower witness `2`, with its CNode, a VSpace on
ASID 1, the notification every SPI signals, and untypeds over the board's RAM
outside the kernel's extent (`[256 MiB, 1 GiB)` until BP7.10, which cut them to
the firmware's account). The untrusted initial thread sits at the upper witness
`0x10_0000`, with its own CNode and VSpace on ASID 2. No capability crosses the
boundary. Six things new code must respect.

(1) **The boot admits a configured VSpace root, and installs every object one
way.** `createBootObject` is `createObject` plus the ASID registration the
runtime store performs (`bootEntryAsidTable`), and both `foldObjects` and
`installBootVSpaceRoot` are it. The retired `noVSpaceRootsInInitialObjects`
refused every configured root because the builder omitted that write — a refusal
standing in for a missing write. Its replacement at the same cascade position is
`bootVSpaceAsidsDistinct`, since a registration is an insert. A new boot install
path goes through `createBootObject`.

(2) **A configured root is a thread's, never the kernel's.**
`bootSafeObjectCheck`'s `.vspaceRoot` arm is `bootSafeUserVSpaceRootCheck`: a
user ASID and **no mappings**, because a configured mapping would name physical
memory no boot check places. The binding's root keeps `bootSafeVSpaceRootCheck`,
and `bootSafeObjectCheck_refuses_rpi5BootVSpaceRoot` pins that the two cannot
stand in for each other. A later cut that maps a root task image widens the user
check with a placement check for its frames, never by reusing the kernel's.

(3) **A boot untyped describes only memory it may.** `untypedPlacementRespected`
is `wellFormed`'s seventh conjunct: every untyped lies inside one declared region
of its own kind, clear of `MachineConfig.kernelReserved`, and disjoint from every
other boot untyped. It also discharges the proof bridge's `untypedRegionsDisjoint`
(`PlatformConfig.wellFormed_untypedRegionsDisjoint`). A projection path into
`wellFormed` must use the named accessors, which absorbed the new conjunct
without moving.

(4) **The reserved extent is one number in three places, held by a shared
fixture.** The three are `rpi5KernelReservedEnd`, `link.ld`'s
`KERNEL_RESERVED_END` and `mmu::KERNEL_RESERVED_END`. The Lean suite writes the
value into `tests/fixtures/boot_map.expected`, and the HAL test and
`scripts/check_link_script.py` read it back. The image must end inside the
extent, which a live-by-mutation `ASSERT` checks. The device-tree window must too
(`dtb_window_admissible`), so no untyped can describe the blob. Growing the image
past 256 MiB means moving all three together.

(5) **A concrete configuration's gates are decided, never asserted.** The boot's
duplicate checks run an opaque hash set, so `irqsUnique_eq_transparent` and
`objectIdsUnique_eq_transparent` rewrite them to the transparent forms, and
everything after that is `decide`. No `native_decide` anywhere.
`bootFromPlatformChecked_ok_objects_of_mem` — every configured object is in a
successful boot's state, at its own id — is how a deployment's threads are read
off the configuration rather than evaluated out of the boot. `BaseIO` has no
`LawfulMonad` instance in this toolchain, so an IO equation closes by `rfl`
(`bootAndInitialiseRPi5OrHalt_rpi5PlatformConfigFor`), not by rewriting.

(6) **The state the hardware boot installs satisfies the proof-layer bundle,
and there is one argument for it** (BP3.5).
`bootFromPlatformCheckedWithIdleThreadsFor_proofLayerInvariantBundle` covers the
checked, idle-enqueued boot of every configuration the checked boot accepts,
`bootToRuntime_invariantBridge_checked` adds the freeze, and
`rpi5DeploymentBootStateAt_invariantBridge` is the deployment's instance. Both
boots, checked and unchecked, are instances of
`proofLayerInvariantBundle_of_bootShape`: every object is `bootObjectShape`,
the quiescent fields are defaults, the ASID table is consistent, and the
scheduler supplies its run-queue facts. A new boot install step must keep all
four, or say which it breaks. And **a runtime check must decide every clause
the Prop-level predicate states**: `bootSafeCnodeCheck` looked at a CNode's
shape and not at its slots, so a reply capability or an out-of-range badge
booted, and the soundness bridge was partial under a docstring saying the
clauses were checked elsewhere. `bootSafeCapCheck` refuses both, and
`bootSafeObjectCheck_sound` concludes all of `bootSafeObject`.

**BP4.1/BP4.2 — the entry exists, and the install precedes the secondaries by a
type** (`v0.36.2`).  Four things new code must respect.  (1) **The hardware boot
entry is `SeLe4n.Platform.RPi5.kernelMain`** (`SeLe4n/Platform/RPi5/KernelMain.lean`,
in the library root): `@[export lean_kernel_main]`, exactly
`Platform.FFI.bootAndInitialiseRPi5FromDtbOrHalt dtb rpi5IrqTable rpi5InitialObjectsFor none`
since BP4.4 (the item after this block), and `kernelMain_installs` states the
program it is.  `BootEntryContract.lean` now
**refuses** an environment with no entry, so a second one, a moved one or a
deleted one fails Tier 1.  (2) **`EXPECTED_UNRESOLVED` is empty**: every HAL
`extern "C"` declaration is a requirement both archives must meet, and a seam
declared before its provider goes there with its reason.  (3) **Releasing a
secondary consumes a `lean_entry::SecondaryReleasePermit`**, which
`smp::bring_up_secondaries_inner` — the one function every bring-up path reaches
— takes by value.  On an image that links the kernel (`hw_target`) the only
permit is what `enter_lean_kernel` returns after the install;
`SecondaryReleasePermit::no_lean_kernel` exists only without `hw_target` (and in
tests).  So `rust_boot_main` installs in Phase 5, releases in Phase 6 and refuses
a PE-topology mismatch in Phase 7, and a reordering that releases first does not
compile.  (4) **The install is the eighth committing seam, recorded unbracketed**
in `ExportCommitDisciplineCensus` with that ordering as its reason, and the
reachability census's pin shrank by the nineteen boot-path transformers it now
reaches.  A new step the boot entry reaches is therefore *live*, not pinned.
(5) **A Lean function crossing the C boundary returns its VALUE, and each side
must declare exactly the C the Lean compiler generated.**  Lean 4.28 passes no
world argument and wraps no `IO` result: a `BaseIO Unit` export returns
`lean_box(0)`, a `BaseIO UInt64` one a `uint64_t`, and only a module
**initializer** (`initialize_*`) returns an `IO` result constructor.  So a HAL
declaration of a `BaseIO Unit` export returns `lean_runtime::LeanBaseIoUnit`
and its caller hands it to `lean_runtime::discharge_base_io`, which accepts
`lean_box(0)` and halts on anything else; the initializer's is
`lean_runtime::LeanIoResult`, classified by `consume_io_result`.  Both wrappers
are `#[must_use]` and `#[repr(transparent)]`.  In the other direction, a HAL
**definition** of an `@[extern]` binding returns what the generated C declares
— a `BaseIO Unit` binding is `lean_object* f(…)`, so it returns
`lean_runtime::base_io_unit()`: a definition returning nothing leaves whatever
was in `x0` to be read as an object reference.  **The linker checks names,
never types**, so `check_kernel_entry_exports.py` holds every HAL foreign
declaration of a Lean-generated symbol **and** every HAL definition the
generated C calls to the prototype the Lean compiler wrote under
`.lake/build/ir`, and `ExportCommitDisciplineCensus` proves every `@[export]`
returns `Unit` or a C scalar — which is what makes "a boxed export result is
`lean_box(0)`" sound.  (BP4.1 first read the export results as `IO`
constructors, so the discharge refused `lean_box(0)` and the first tick on a
ready core would have halted it; and thirty-three HAL bindings returned
nothing.  The post-BP4.5 ABI audit fixed both.)

**BP4.3/BP4.4 — the device tree reaches Lean, and the entry boots on it**
(`v0.36.2`).  Four things new code must respect.  (1) **The entry takes the
firmware's blob, not its pointer**: `kernelMain (dtb : ByteArray)` is
`bootAndInitialiseRPi5FromDtbOrHalt dtb rpi5IrqTable rpi5InitialObjectsFor none`,
and `BootEntryContract.lean`'s `approvedBootCall` is that wrapper, with the
blob required to be the entry's **own parameter** — a fixed blob, an edited
copy, and the retired `bootAndInitialiseRPi5OrHalt` call are refused witnesses.
(2) **The HAL copies, and does not decide**: `lean_entry::enter_lean_kernel`
reads the blob through `cmdline::dtb_blob_from_ptr` inside the window `init_mmu`
admitted and copies it onto the kernel's Lean heap
(`lean_runtime::array::byte_array_of`); a pointer that yields no blob is handed
over as the **empty** array, which the verified parser refuses
(`kernelMain_refuses`), so whether this board may boot has one owner.  (3) **The
deployment is proved on every board, not one**: `rpi5PlatformConfigFor board`
and `rpi5BoundPlatformConfigAt v` replace the smallest-board
`rpi5PlatformConfig` (retired, with a Tier 3 negative), every gate is decided on
each of the five variants, and `bootAndInitialiseRPi5_rpi5PlatformConfigFor`
holds for every account because `rpi5VariantFor` always names a member.  A
deployment change that breaks the boot on any variant fails to elaborate.  (4)
**What the bridge accepts is the deployment**:
`rpi5PlatformConfigFromDtb_ok_eq_fromDeviceTree` says an accepted result is the
parsed tree's account around the caller's half, so `kernelMain_installs` names
the state it installs — the variant the device tree selected — without
re-running the parse, and `tests/Ak9PlatformSuite.lean` runs that decision on
1, 2, 3, 4 and 8 GiB boards.

**BP4.5 — the boot image is cleaned to the Point of Unification before any
thread can fetch** (`v0.36.2`, closing SM7.D's deferred item 4).  Four things
new code must respect.  (1) **Both kernel code-write sites emit**:
`kernelCodeWriteEmitted .bootImageLoad` is `true`, and
`kernelCodeWriteSites_all_emitted` replaces `kernelCodeWriteSites_emission_pending`
(retired, with a Tier 3 negative), so a site added to `KernelCodeWriteSite`
must emit or the `decide` fails.  (2) **The extent is the image's loaded
bytes**, `link.ld`'s `[_start, __image_load_end)` — text, read-only data and
initialised data, the only memory the boot makes present that a thread could be
handed as code.  Everything else it writes (the Lean heap, `.bss`, the stacks,
the boot tables) is in `MachineConfig.kernelReserved`, which no boot untyped
describes and no boot VSpace maps, and memory a thread receives otherwise comes
through a re-type, which cleans it itself.  `__image_load_end` sits between
`__rodata_end` and `__bss_start` by a live-by-mutation `ASSERT`.  (3) **The
operand is the model's**: `cache::boot_image_icache_operand` is
`CleanRangeIallu` over that extent — op tag 3, `Architecture.bootImageIcacheOp`,
which `bootImageIcacheOp_discharges_obligation` proves discharges the
obligation and which a bare `IC IALLUIS` would not.  (4) **The permit certifies
it**: `lean_entry::enter_lean_kernel` runs `cache::clean_boot_image_to_pou`
after the install and immediately before it mints the `SecondaryReleasePermit`,
so no secondary is released, and the boot core reaches no scheduling point,
before the clean; a Tier 3 anchor holds the order, and a clean moved after the
permit or commented out fails it.  The clean executes on every PR since BP8.1 (`v0.36.26`, on QEMU);
observing it on the board is BP8.3's.

**BP4.6 — the verified board's RAM outside the kernel's extent is mapped, and
the boot map is sealed before a secondary exists** (`v0.36.2`; its lower bound
moved from the first gigabyte to the kernel's extent at BP7.10).  Five things
new code must respect.  (1) **Lean decides the extent, and derives it**: the
device-tree wrapper's accepting arm runs `extendBootRamMap
(rpi5BootRamExtensionsFor config.machineConfig)` before the install, and
`bootRamExtensionsOf` is every RAM region of the *bound* configuration's map
past `rpi5KernelReservedEnd`, clipped to it (`bootRamExtensionOf?`) — `mem_bootRamExtensionsOf` and
`bootRamExtensionsOf_covers` prove it is exactly that RAM in both directions, so
the RAM the HAL maps and the RAM the installed state's machine configuration
declares are one variant's.  A new variant changes its memory map, never a list.
(2) **The HAL writes only invalid entries, and decides every refusal first**:
`mmu::extend_boot_tables` is two passes over one per-gigabyte walk — validate,
then write — so a refused range (`RamExtensionRefusal`) leaves the tables
byte-identical; it writes 1 GiB level-1 blocks, and 2 MiB blocks in a
gigabyte that has a level-2 table (`level2_table`: the first gigabyte since
BP7.10, and the device window's), all Normal, writable and never executable.  Never rewriting a valid descriptor is what makes the change
safe with no break-before-make and no TLB invalidation (a faulting translation
is never cached); the table extent is cleaned to the PoC, as `enable_mmu` does, so a
secondary enabling translation with its cache off reads it, then one `DSB ISH` + `ISB`; a partial gigabyte outside
those two is refused rather than given a table.  (3) **The cacheable
window moves with the tables, by one call**: `extend_boot_ram_map` records each
region after the barrier and `is_boot_cacheable_range` is the union
`ram_range_covered` over the kernel's extent and the record — no longer a `const fn`.
(4) **The boot map is sealed before the permit**: `enter_lean_kernel` calls
`mmu::seal_boot_map` immediately before it mints the `SecondaryReleasePermit`,
and every later extension is refused `Sealed`, so the tables have one writer;
a refusal of any kind halts the system (`ffi_extend_boot_ram_map` →
`gic::halt_all`).  (5) **It is driven, not mirrored**:
`tests/fixtures/boot_map.expected` carries each configuration's `extend` lines,
and the HAL test applies them and requires the extended Normal window to be
**exactly** that configuration's RAM on every configuration — the firmware-cut
ones included, whose withheld top of the gigabyte stays unmapped.  What BP4.6 does *not* do is hand the RAM to
anyone; that is BP4.7's (the paragraph below).

**BP4.7 — the RAM the boot maps is the RAM the root task owns** (`v0.36.2`).
Four things new code must respect.  (1) **A deployment's objects are a function
of the variant**: `rpi5PlatformConfigFromDtb` and the device-tree wrapper take
`initialObjectsFor : BCM2712Config → List ObjectEntry` and apply it to
`rpi5VariantFor dt.machineConfig`, the variant the board check just read, and
the RPi5 deployment's is `rpi5InitialObjectsFor v`; a caller whose objects do
not depend on the board passes a constant function.  The variant-independent
`rpi5InitialObjects` and `rpi5RootTaskCNode` are retired, with a Tier 3
negative.  (2) **The untypeds are derived from the extensions, never listed**:
`rpi5RootTaskUntypeds v` is one normal-memory untyped per
`rpi5BootRamExtensions v` entry, at id `6 + i` and root-CNode slot `5 + i`
(since BP7.10, which retired the two fixed first-gigabyte untypeds and the
`RamUntyped` names), and `rpi5RootTaskUntypeds_regions` states its regions
**are** the RAM BP4.6 maps.
(3) **The boot bounds a CNode's slot count, not its indices**, so
`rpi5RootTaskCNodeFor_slotsAddressable` decides per variant that every root-CNode
slot is below sixteen; eleven extensions fit, and a variant needing more must
widen the root CNode's radix.  (4) **The coverage is the direction the placement
conjunct cannot state**: `untypedPlacementRespected` bounds the untypeds from
above, and `rpi5InitialObjectsFor_covers_ram` says every RAM address outside the
kernel's reserved extent lies in some root-task untyped, on every board, with
`rpi5DeploymentBootStateAt_untypedInstalled` that the boot installs each.
`BootEntryContract.lean`'s `approvedBootCall` did not move; the object function
is data like the rest of the wrapper's arguments.

**BP5.1 — the kernel is one bare-metal binary, and it is checked as an image**
(`v0.36.2`).  Four things new code must respect.  (1) **`sele4n-kernel` is the
tree's only final binary** (`rust/sele4n-hal/src/bin/sele4n_kernel.rs`,
`no_std` / `no_main`), so image-wide decisions live there and nowhere else.  It
requires the `kernel_image` feature, and the HAL's build script passes
`-T link.ld` to that binary's link alone and only when `target_os = "none"`.
A new binary target gets its own `[[bin]]`, since declaring one disables
auto-discovery.  (2) **A panic halts the system**: the `#[panic_handler]` is
`gic::halt_all`, not the per-PE `cpu::fatal_halt`, and prints nothing because
the UART writer takes a lock the panicking core may hold.  A Tier 3 anchor pins
that body.  (3) **The image is checked as an image**, not as objects:
`scripts/check_kernel_image.py` (the cross lane's step [7/7], required by
`check_aarch64_cross_target.py`) refuses an entry other than `_start` at
`link.ld`'s `ORIGIN`, any undefined symbol (weak ones too, which a static link
resolves to `0`), and any allocated section `link.ld` does not name or places
out of order.  It also refuses a `NOLOAD` section with file bytes and a loaded
section outside `[_start, __image_load_end)`.  The allowed sections are derived
from `link.ld` itself, so an orphan placed by the linker fails the lane.  The
FP/SIMD gate reads the linked image too.  (4) **The cross lane's image is the
HAL half**: it builds without `hw_target`, because with it `build.rs` links the
Lean archive, which that lane does not build; that image boots the Rust half
(`SecondaryReleasePermit::no_lean_kernel`).  The cross clippy lane builds with
`hw_target,kernel_image --lib --bins`, so the panic handler — compiled for the
bare-metal target only — is linted.

**BP5.2 — the image carries the Lean kernel, linked from the roots the proof is
about** (`v0.36.2`).  Four things new code must respect.  (1) **One roots file,
two links**: `scripts/build_lean_aarch64_archive.py` writes
`libsele4n.roots.ld` beside the archive — `EXTERN(...)` naming the library
initializer, then every production `@[export]` — and both its reachable link
and the image's link read that file, so the runtime-surface proof and the image
cannot be taken over different root sets.  A new kernel entry is a new
`@[export]`, and it reaches both links by construction.  (2) **`build.rs` links
it under `hw_target` on a bare-metal target only**, with `--gc-sections`, by
path: a missing archive or roots file stops the link naming the file, never a
kernel linked without its Lean half.  The three paths are constants the
builder's self-test holds equal to its own `OUT_DIR`, `ARCHIVE` and
`ROOTS_SCRIPT`.  (3) **The Lean archive lane owns the kernel image**: step
[4/6] of `scripts/test_lean_aarch64_archive.sh` removes the stale image,
builds it release with `hw_target,kernel_image` after the archive, runs
`check_kernel_image.py --lean-kernel` over it (the roots begin with the
initializer, name `lean_kernel_main`, and are all the image's text), then the
FP/SIMD gate — and `check_aarch64_cross_target.py` holds those four relations
(both features on one release build, after the archive build, each check after
the image build, none exempted from `set -e`).  (4) **The FP/SIMD gate is
conclusive here**: none of `compiler_builtins`' FP-using members is in the
linked image, so a change that pulls one in fails the lane.  The cross gate's
shell expander now resolves a variable whose value names another
(`ARCHIVE_DIR="${PROJECT_ROOT}/.lake/build/${CROSS_TARGET}"`) to a fixpoint;
one pass in length order left it half-substituted.

**BP5.3 — the firmware's boot files are cut from the image and checked against
it** (`v0.36.2`).  Four things new code must respect.  (1) **The device tree's
window is `link.ld`'s**: a `NOLOAD` `.dtb_window` of `DTB_WINDOW_SIZE` after the
Lean heap, with `ASSERT`s (each proved live by `check_link_script.py`) that it
is that size on a page, after `__lean_heap_end` and inside
`KERNEL_RESERVED_END` — the two conditions `mmu::dtb_window_admissible`
refuses without, and since `v0.36.35` it also refuses a window reaching the
boot table pool, which the boot zeroes and hands out as tables — and `DTB_WINDOW_SIZE` equals `cmdline::MAX_DTB_SIZE` by the
HAL's test.  A section added after `.lean_heap` goes before `.dtb_window` or
moves it, never between it and the reserved extent's end unchecked.  (2)
**`config.txt` is generated, and a key it does not set is refused**:
`scripts/rpi5_boot_files.py` writes exactly `arm_64bit`, `kernel`,
`kernel_address` (the image's entry, `_start` and `ORIGIN`),
`device_tree_address` and `device_tree_end` (the linker's window), and its
check refuses an unknown key, a repeated or missing one, and a conditional
`[...]` section, since each could move the load or the blob where the check did
not look.  A new firmware option is added to `CONFIG_KEYS` with the relation
it must hold, never by hand to the file.  (3) **`kernel8.img` has two
readings that must agree**: `llvm-objcopy -O binary` cuts it, and the check
rebuilds `[_start, __image_load_end)` from the section headers
(`check_kernel_image.Section.offset`) and requires byte identity.  (4)
**Packaging is the Lean-linked image's**: `scripts/build_rpi5_image.sh` runs
`check_kernel_image.py --lean-kernel` first, `package` always ends in `check`,
and the archive lane runs the script as step [5/6] over the image it linked,
which `check_aarch64_cross_target.py` holds (after the image build, not
exempted from `set -e`).

**BP5.4 — the image's size and section map are published with every run**
(`v0.36.2`).  `scripts/kernel_image_report.py` is `build_rpi5_image.sh`'s last
step, so the archive lane's job reports on each run the size of `kernel8.img`,
the loaded, text, padding and `NOLOAD` bytes, the share of the reserved extent
used, and every section's extent — in the step summary, and as
`kernel-image-report.json`, uploaded with the image and its boot files as the
`rpi5-kernel-image` artifact.  Two things new code must respect.  (1) **The
size is read from the file and held to the image**: a `kernel8.img` that is not
`[_start, __image_load_end)` is refused rather than reported, because a figure
the report could not establish would be a guess published as a measurement.
(2) **The summary is appended to**, never overwritten, since other steps write
to the same file.


**BP5.5 — every boot entry reaches EL1, and the PSCI conduit follows the level
it came from** (`v0.36.2`).  Four things new code must respect.  (1) **Both
entries call `.L_enter_el1` as their first item, ahead of the FP prologue**
(the `v0.36.2` audit's order — the prologue is written once the PE is at EL1),
and the routine is `build.rs`'s `EL1_ENTRY_ROUTINE` item for item.  It returns at EL1
and halts at any level but EL1 or EL2.  At EL2 it `eret`s to EL1h with DAIF
masked, after writing `HCR_EL2 = RW`, `CPTR_EL2` with `TFP = 0` (the
`CPACR_EL1` trap is the one that fires), the timer controls,
`VPIDR_EL2`/`VMPIDR_EL2` (an EL1 MPIDR read returns the latter, reset UNKNOWN),
an untrapping `MDCR_EL2` and a known MMU-off `SCTLR_EL1`.  Changing the routine
means changing the table, and `scan_el1_entry` refuses a write to any EL2
register — by name or by an `S3_4_…` encoding — anywhere else in assembly or
Rust.  (2) **The routine uses no stack and keeps `x0`**: the DTB pointer and
the PSCI context id cross the drop, and it returns the entry level in `x9`,
which `_start` hands to `rust_boot_main` as `entry_el`.  (3) **A PSCI call goes
through `psci::psci_call`, never an `hvc` or `smc` of its own**.  Every wrapper
used to hard-code `hvc #0`.  That could never have reached the RPi5 firmware:
the firmware hands EL2 to the kernel, so an `hvc` was taken at EL2 through a
vector table nothing had installed.  `select_conduit` picks `smc` after an EL2
entry and keeps `hvc` after an EL1 one, and a call before the selection halts.
A Tier 3 negative refuses the retired inline template.  (4) **Reading the
conduit from the device tree's `/psci` `method` on an EL1 entry is registered
debt**; `scripts/test_qemu.sh` has executed the EL2 path under QEMU since
BP8.1 (`virtualization=on`), with the HAL alone and with the Lean kernel.

**BP6 — every PE marks itself ready, and a boot one PE cannot serve halts**
(`v0.36.2`).  The five gated seams went live: the IRQ redirect, the `.reschedule`
SGI receiver, the secondary bring-up entry, the SVC dispatch and the classifier
now run their Lean halves on the image.  Five things new code must respect.
(1) **A core is marked ready by `lean_ready::become_ready_or_halt` and nothing
else**: it runs the per-PE handshake (`initialise_core_runtime`) and hands its
token to `mark_lean_ready`, which is **safe** and consumes a
`LeanRuntimeReadyOnCore` — the old `unsafe fn mark_lean_ready(core_id)`, whose
safety contract *was* the readiness promise, is retired, and the one way to
assert readiness without a handshake is `LeanRuntimeReadyOnCore::assume_initialised`,
which is `unsafe` and exists for host tests.  (2) **Per-PE means the PE's own
posture, because the kernel's runtime has no per-thread state**: the library
initializer and the install are per-image and ran once on the boot core, and
`enter_lean_kernel` publishes that (`Release`) before it mints the release
permit.  The handshake then decides, in order: the call runs on the core it
names, once; the install happened-before (`Acquire`); the PE translates
(`SCTLR_EL1.M` — the heap lock is an exclusive-monitor atomic); it runs on its
**own** stack slot (`own_stack_extent`, the boot stack or the `c`-th 64 KiB
slot below `__smp_secondary_stack_top`); and the kernel heap serves an
allocation and a free from it.  (3) **Every PE marks itself before it unmasks
IRQs** — the boot core's `enable_irq` moved from Phase 4 to after its own mark,
which follows the Phase 5 install, so no PE takes an interrupt in the degraded
Rust-only mode once the kernel exists; `build.rs`'s
`readiness_publication_status` holds each mark as a hardware-only top-level
statement after its dependencies and before its PE's one `enable_irq`, and
derives that nothing else calls `mark_lean_ready` or `become_ready_or_halt`.
(4) **A refusal is a halt, and the halt is the pin**: the boot core halts the
system (`gic::halt_all`, nothing released yet), a secondary parks itself
(`cpu::fatal_halt`), and the boot core's Phase-7 wait counts it short.  (5)
**The wait counts cores that serve the kernel** — `smp::core_serves`, IRQ-ready
**and** Lean-ready, through `serving_core_count_within`; the retired
`irq_ready_core_count_within` counted the IRQ flag alone, which a PE with every
seam dormant satisfies.  What BP6 does not do is return anyone to EL0: the
fault and cap-fault halts became **reachable** here, and stayed the seam's
occupant until the context restore (BP7.6, `v0.36.19`) installed a successor.

**The `v0.36.2` audit of BP0–BP6** — what a re-read of the landed code against
its own prose found, in the order a boot meets it, and what new code must
respect because of it.  (1) **The FP-trap prologue is written at EL1, after
`.L_enter_el1` returns.**  It ran first, and at EL2 with `HCR_EL2.E2H` set —
UNKNOWN at reset — a `cpacr_el1` write names `CPTR_EL2`, so on the firmware's
EL2 entry `CPACR_EL1` stayed UNKNOWN and the trap the FP-free argument rests
on was never written.  `fp_trap_prologue_status` and `el1_entry_status` refuse
the old order.  (2) **The boot console bypasses its ticket lock while the
executing PE does not translate** (`uart::with_boot_uart`,
`ticket_lock_usable` from `SCTLR_EL1.M`): the lock's `fetch_add` is an
`LDAXR`/`STXR` loop on the LSE-less softfloat target, and an exclusive access
to Device memory with translation off never succeeds on the BCM271x, so the
first `kprintln!` before `enable_mmu` could spin forever.  The readiness
handshake asks translation before it touches its once-per-core guard, so a
PE refused there can retry.  (3) **A runtime `fatal` and a heap exhaustion
halt the system** (`gic::halt_all`), never one PE.  (4) **Every PE unmasks
SError after installing its vectors** and `handle_serror` reports through the
unlocked console writer; and every PE reads `CTR_EL0` and halts if either
cache's minimum line is smaller than the maintenance stride
(`cache::verify_cache_line_stride_or_halt`).  (5) **The Phase-7 window is one
second, derived** from what a secondary does before it publishes, and the
refusal names each short PE and the half it lacks; `core_serves_in` carries
its own witness.  (6) **The ShareCommon pass compares big naturals by their
limbs**, never by reserved capacity, and `alloc_ctor` zeroes the trailing pad
word; every C-ABI export that dereferences a pointer is `unsafe extern "C"`
with a `# Safety` section; the release profile keeps `overflow-checks`.  (7)
**The UART window is the device tree's `0x200` block** (`mmioRegions`): the
board check requires the board's block to contain the window, so the `0x1000`
window refused every real board and the boot halted — invisible because every
fixture built its UART node from the binding's constant.  (8) **A boot
untyped is pristine** — `bootSafeUntypedCheck` was `true` and `bootSafeObject`
had no untyped clause; both, and the soundness bridge, now require
`watermark = 0`, `children = []`, `parent = none`.  (9) **A fuel-starved
`ranges` walk refuses** rather than answering its prefix (the default fuel's
`+ 1` is the unit spent observing the end).  (10) **Two findings are
registered with their evidence and scheduled**: a real Raspberry Pi 5 firmware
memory account — `[0, 0x80000)`, `[0x80000, 0x3FC00000)`, `[0x40000000, top)`,
the top of the first gigabyte withheld by a board-dependent amount — covers
no `[0, ramSize)` variant, so the bridge refuses every real board and the
boot halts; the corpus carries the account (`eight_gib_rpi5_firmware`), and
**BP7.10** (`v0.36.3`, the paragraph below) derives the deployment's
first-gigabyte RAM from it — `realFirmwareAccountBindsTheReportedRam` is the
flipped witness.  And nothing starts the root task or the
untrusted witness (**BP7.11** — decided at the audit's review: the boot starts
both, one per domain, so no capability crosses the confinement boundary).
(11) **Gates**: `check_link_script.py`
witnesses name whole `ASSERT` messages, one per conjunct;
`check_dtb_corpus_consumers.py` pins the comparison rather than the call;
`build_lean_aarch64_archive.py` reads the reachable link's exit status;
`check_fp_simd_free_objects.py` refuses an `<unknown>` mnemonic and knows the
SVE predicate registers; `test_qemu.sh` builds the real image and SKIPs
unless `QEMU_MACHINE` names a machine, since QEMU models no BCM2712 — and on
the Lean-linked image `smp_enabled=false` or `smp_max_cores` below four halts
at Phase 7 rather than booting fewer PEs.  (12) **The physical address width
is the Cortex-A76's 40 bits, and `TCR_EL1.IPS` is derived from the PE**
(the audit's review): `rpi5MachineConfig.physicalAddressWidth` read `44` —
the bound on every physical address the model admits (`addrInRange`, the
checked VSpace map decode, `MachineConfig.wellFormed`) — and the HAL
programmed a constant 44-bit `IPS` under a comment claiming that matched the
BCM2712, while the Cortex-A76's `ID_AA64MMFR0_EL1.PARange` (bits [3:0]) is
`0b0010`, 40 bits (TRM r4p1 §B2.58): the model admitted mappings in
`[2^40, 2^44)` that the PE answers with an Address size fault, and an `IPS`
wider than the implemented size is treated as the implemented size, which is
why nothing broke.  `Board.lean` declares 40, `check_physical_address_width.sh`
holds it there, `enable_mmu` reads the register on the executing PE
(`mmu::physical_address_size_of`, a `const fn` over the raw value with the
architecture's whole table, capped at the 48 bits an ARMv8.0 descriptor can
name) and refuses a reserved encoding or a PE narrower than the tables'
reach (`BOOT_TABLE_PA_BITS_REQUIRED`, 39 bits) before programming
`tcr_el1_value(pa.ips)`, and the two sides are held together by running both:
the Lean suite writes `physicalAddressWidth` into
`tests/fixtures/boot_map.expected` and the HAL's
`the_lean_physical_address_width_is_the_pe_the_hal_programs_for` holds it to
the PE it derives `IPS` for.  (13) **The handoff's declared PE count is the
binding's `coreCount`, read from the same fixture** (`declaredCores`) rather
than a literal `4` beside a comment naming it.

**BP7.10 — the first gigabyte's RAM is read off the firmware's account, and
the constant boot map is the kernel's extent alone** (`v0.36.3`).  Six things
new code must respect.  (1) **A configuration carries its first-gigabyte top**:
`BCM2712Config.lowRamTop` (default `rpi5FirstGigabyteTop`, so every member of
`rpi5Variants` is the uncut form it was) ends the first RAM region
`rpi5MemoryMapForConfig` declares, and `rpi5VariantFor` binds the covered member
cut to `rpi5LowRamTopFor board` — the account's RAM reach from the image
origin (`ramReachFrom board rpi5RamOrigin`, the union reading's own cursor;
from `0` until `v0.36.36`, below), capped at the gigabyte and
rounded **down** to the 2 MiB granule, or the floor when it reaches less.  The
real Pi 5 8 GiB account binds `{8 GiB, 0x3FC00000}`; a CM5's rounds to
`0x3FA00000`; an account reporting less than the floor (the kernel's extent plus
one granule) is refused.  (2) **A theorem about a deployed configuration is
stated over `v.Admissible`**, never `v ∈ rpi5Variants` — the uncut form a member,
the top admissible (`rpi5VariantFor_admissible`, which replaces
`rpi5VariantFor_mem`).  (3) **A gate `decide` cannot reach is factored, not
enumerated**: every well-formedness conjunct but the untyped placement is
invariant under `PlatformConfig.withoutExtents` (extent erasure), so it is
decided once on the uncut member; the placement is proved symbolically and the
machine config's well-formedness by `MachineConfig.wellFormed_of_within`.  (4)
**The HAL maps nothing past the kernel's extent from constants**:
`GUARANTEED_RAM_TOP` is retired (a Tier 3 negative refuses it), the constant
Normal window is `[IMAGE_ORIGIN, KERNEL_RESERVED_END)` (from `0` until
`v0.36.36`), `link.ld`'s RAM region ends there
(`ASSERT`), and an extension may not start inside it
(`RamExtensionRefusal::InsideKernelReserved`).  The first gigabyte's reported
part is an extension like any other, written in 2 MiB blocks into `l2_ram`.  (5)
**What is mapped, declared and owned is one list**: `bootRamExtensionsOf`
clips at the extent, and the root task holds one untyped per extension — so the
firmware's withheld top of the gigabyte is neither in the model, the boot map,
the cacheable window nor any untyped.  (6) **The shared fixture carries cut
configurations**: `tests/fixtures/boot_map.expected` has the five variants and
three firmware-cut configurations, each line `variant <ramSize> lowRamTop <t>`,
and the HAL test requires the constant window to be the extent and each
extended window to be exactly its configuration's RAM.

**...and a Raspberry Pi 5's RAM begins at the image origin** (`v0.36.36`, the
post-landing audit's finding F1, confirmed against `bcm2712.dtsi` at
`raspberrypi/linux` `rpi-6.6.y`).  The tree reserves the secure monitor's
`[0, 0x80000)` as `reserved-memory/atf@0` with `no-map`, the parser subtracts
every reservation, so no parsed account of a real board reached past `0`: the
BP7.10 derivation fell to the floor and the bridge refused **every** real Pi 5 —
and the HAL mapped that secure memory Normal-cacheable, where a speculative
fetch can raise an external abort.  Four things new code must respect.  (1)
**Declared RAM begins at the image origin on every board**: `rpi5RamOrigin` and
`qemuVirtRamOrigin` (the RAM base plus `0x80000`, `link.ld`'s `ORIGIN`) start
the first RAM region, the first gigabyte's top is measured from there
(`Boot.ramReachFrom`, which replaces `ramPrefixTop`), and the reserved extent
still starts at the RAM base, so the hole is reserved from every untyped and is
neither RAM nor mapped.  (2) **The boot map, the cacheable window and the
device tree's window ask one predicate**, `mmu::in_kernel_memory_window`
(`[IMAGE_ORIGIN, KERNEL_RESERVED_END)`), and `IMAGE_ORIGIN` is a boundary
forcing page granularity on its block (`IMAGE_BOUNDARY_COUNT` is four, one more
4 KiB boot table).  (3) **A symbolic `x - 0x80000` is a kernel hazard**: the
kernel's `Nat.sub` unfolds once per unit of its literal second argument, so a
proof must not let the kernel evaluate a configuration's extension list over a
symbolic top — state the fact over the list or the extension
(`untypedsOver_regions`, `extension_placed` in `Deployment.lean`).  (4) **The
witnesses use the real tree**: the Ak9 firmware test and the shared corpus's
`eight_gib_rpi5_firmware` carry `atf@0` exactly as `bcm2712.dtsi` declares it
(two address cells, one size cell, `ranges`, `no-map`), and
`rpi5VariantFor_rpi5_parsed_account` binds the subtracted account.

**The RPi5 binding is the BCM2712's address map** (`v0.36.2`, found while
scoping BP5.4).  Until then the model and the HAL both carried the **BCM2711**'s
(Raspberry Pi 4) map — UART `0xFE20_1000` at 48 MHz, GIC-400 `0xFF84_1000` /
`0xFF84_2000`, a device window `[0xFE00_0000, 0xFF85_0000)`, RAM capped at
`0xFC00_0000` — all of it DRAM on the BCM2712, and `Board.lean`'s checklist
marked every one **Validated**.  Four things new code must respect.  (1) **The
map follows `bcm2712.dtsi`**: DRAM contiguous from 0 (`[0, ramSize)`, one RAM
region per variant, one boot extension above the gigabyte), the SoC-bus window
`[0x10_7C00_0000, +64 MiB)` as the one device region (`socPeripheralBase`,
`mmu::DEVICE_WINDOW_BASE`), UART10 at `0x10_7D00_1000` clocked at 9.216 MHz,
GIC-400 at `0x10_7FFF_9000` / `0x10_7FFF_A000`; `peripheralBaseLow` is retired,
and a Tier 3 negative refuses any BCM2711 address returning as a live constant.
(2) **A driver's base is compared with the Lean one by running both**: the Lean
suite writes `mmio uart|gicd|gicc` lines into `tests/fixtures/boot_map.expected`
from `mmioRegions`, and the HAL's UART and GIC tests read them
(`mmu::lean_mmio_window`) — the literal-beside-a-comment tests those replace are
how both sides agreed on the wrong board.  (3) **The window is block aligned**,
so the boot map's device-tail L3 table is deleted and a Tier 3 negative refuses
it returning.  (4) **Cross-checked is not validated**: the constants are the
device-tree source's (`raspberrypi/linux` `rpi-6.6.y`, read 2026-09-25), and
what a real board's firmware reports is BP8.3's readback to confirm.

**BP7.1, slice 1 — memory is authority, and `.vspaceMap` maps only a frame the
caller holds** (`v0.36.4`).  A table base a PE can be told to use is a page the
kernel owns, so BP7.1 opens with seL4's memory-as-authority model: `FrameObject`
(`base`, `isDevice`, its lock) is the ninth kernel-object kind
(`KernelObjectType.frame`, retype tag `8`), locked at `LockKind.page`, now a
modelled kind.  Scoping it found a **High**-severity vulnerability, reported
before the fix: `.vspaceMap` read MR2 as a raw physical address, so one
VSpace-root capability was authority over every page of physical memory, the
kernel image included.  Five things new code must respect.  (1) **No physical
address crosses the ABI**: MR2 is a frame-capability address in the caller's
CSpace (`VSpaceMapArgs.frame`), resolved with `.read` by `resolveVSpaceMapFrame`,
and the page installed is the frame's own `base`; `vspaceMapFromFrameCap` is the
one definition the arm and its theorems read, and `vspaceMapFromFrameCap_ok` its
decomposition.  (2) **The frame capability bounds the mapping**
(`frameMappingAdmissible`): a writable mapping needs `.write` on it
(`.illegalAuthority`, refused rather than silently narrowed), a device frame
maps neither executable nor cacheable, and — since `v0.36.32` — a RAM frame maps
cacheable or not at all (`.policyDenied`; `frameMappingAdmissible_cacheable_iff_ram`):
the kernel writes RAM through its cacheable identity map, so an uncached user
alias is a mismatched-attribute alias (ARM ARM B2.8) through which the carve's
zeroes can arrive late and the previous owner's bytes early.  (3) **Nothing mints
memory authority except an untyped**: an in-place retype refuses a
memory-backed replacement (`KernelObjectType.memoryBacked`,
`retypeReplacementAdmissible`'s third conjunct, `.illegalState`), the boot
refuses a configured frame (`bootSafeObjectCheck`'s `.frame` arm,
`bootSafeObject`'s last conjunct), and the pre-retype cleanup refuses to destroy
one in place (`.revocationRequired`) — permanently since slice 3, which returns
a frame's memory through its untyped instead.  At this slice **no
reachable state held a frame and `.vspaceMap` succeeded on none** — the
fail-closed cost, registered and closed by slice 2's live untyped carve (the
next paragraph).  (4) **`decodeVSpaceMapArgsChecked`
is retired** with the operand it bounded; the PA-width bound on the frame's
`base` is `vspaceMapPageCheckedWithFlushFromState`'s, and W^X is refused at the
decode (`PagePermissions.ofNat?`).  (5) **The retired reading lives in the
witness**: `tests/VSpaceCapabilityBindingSuite.lean` §5c drives a raw-address
MR2 beside the live arm, and a frame held without address-space authority is
still refused.

**BP7.1, slice 2 — memory reaches a thread only by a carve** (`v0.36.5`).
`SyscallId.untypedRetype` (discriminant **36**, count 37) is seL4's
`seL4_Untyped_Retype` at the frame type, and the only path by which a frame comes
to exist on a live state.  Six things new code must respect.  (1) **The carve is
`untypedRetypeObject` at `.frame` (`untypedRetypeFrame` until `v0.36.8`, when
slice 4a generalised it), and its guards are the primitive's**: it is
`retypeFromUntyped` at `untypedNextFrame ut` — the page at the untyped's
watermark, of the untyped's memory kind — and one page, so authority
(`lifecycleRetypeAuthority`: the capability names the untyped and carries
`.retype`), capacity, fresh id, alignment and the watermark advance are not a
second copy; `untypedRetypeObject_ok_decompose` is its one case analysis and
`untypedRetypeObject_ok_frame` / `untypedNextFrame_of_retype_ok` its payoff — the
frame's page lies inside the untyped's region, is page-aligned, and carries the
untyped's device flag.  (2) **A device untyped backs exactly the memory-backed
kinds**: `retypeFromUntyped`'s device rule is `!objectType.memoryBacked` (a child
untyped or a frame), where it read `!= .untyped` while no frame existed.  (3) **A
RAM page is zeroed before any capability to it exists** (`carveZeroFrame`), and a
device page is not — a store to MMIO is a command, not a scrub.  (4) **The new
capability is a CDT child of the untyped capability** (`DerivationOp.retype`), so
revoking the untyped capability reaches it; its rights are read, write and grant
(`frameCapability`).  (5) **The arm resolves two slots through the caller's own
CSpace** (`resolveUntypedRetype`): the source is the invoked capability's own
slot, the destination CNode needs `.write`, and the destination slot must be
empty and addressable (`cspaceInsertSlot`); the child id is a raw operand and
passes `validateObjIdArg`.  Only `.frame` was carved at this slice — any other
tag was `.invalidArgument`, kernel objects being the in-place retype's; slice 4a
adds `.untyped` (below).  (6) **It writes
no scheduler slot**, so both lock domains place it rather than declare it
dynamically: a static object footprint (`lockSet_untypedRetype`, six members,
the new frame's key at the now-used `LockKind.page`), and the scheduler domain's
`none` group.  `ipcInvariantFull` is preserved
(`untypedRetypeObject_preserves_ipcInvariantFull`, over
`storeObject_inertNonCNode_preserves_ipcInvariantFull` and
`ipcReadViewAgreement.of_fresh_inert_write`), and `ipcReadInert` now counts a
frame as inert.  The witness is `tests/VSpaceCapabilityBindingSuite.lean` §5d:
carve, scrub, map the carved page, and every refusal the carve owns.

**BP7.1, slice 3 — memory returns to its untyped** (`v0.36.6`).
`SyscallId.untypedReset` (discriminant **37**, count 38) is seL4's
`resetUntypedCap`, invoked on an untyped capability carrying `.retype`, with no
message registers.  Six things new code must respect.  (1) **"No child survives"
is decided over the whole store, not the invoked slot.**  seL4 keeps a free index
per capability, so `ensureNoChildren` on the invoked slot is enough there; this
model keeps the watermark on the untyped *object*, shared by every copy of its
capability, so a derivation-free sibling copy would pass a per-slot test while
frames carved through the original are still named.  `carvedSubtreeUnreferenced`
(`untypedChildrenUnreferenced` until slice 4a) folds over the object table and
asks every CNode slot and every blocked sender's parked message, and
`carvedSubtreeRetirable` requires every carved object to be a frame or, since
slice 4a, an untyped — a kernel object has no operation here that returns its
memory; both refuse `.revocationRequired`.  (2) **The reset finalises the frames.**  A mapping
records a physical address, not an object, so revoking a frame's last capability
leaves every mapping of it in place: the reset removes each mapping of a page
meeting the region through the `.vspaceUnmap` arm's own verified transition
(page-table erase, local flush, shootdown round, initiator drain,
instruction-cache broadcast), collected from the pre-state and **checked**
afterwards (`untypedRegionUnmapped`; `.illegalState` otherwise), so a mapping the
collection missed refuses the reset rather than surviving it.  (3) **Carved
frames are erased, not left capless.**  `retireCarvedObject` (`retireFrame` until
slice 4a) is the one primitive that erases an object — a no-op at any key holding
neither a frame nor an untyped, so no other kind can be erased through it — and
is registered in `WRITE_PRIMITIVE_BODIES`.  Leaving
dead frames in the store would be unreachable but would consume an object-store
slot per carve, so a holder of one small untyped could exhaust the global store
by carving and resetting in a loop.  (4) **The reset zeroes nothing**: the carve
zeroes a RAM page before any capability to it exists, so a page is scrubbed
exactly when it is handed out, whatever happened to it in between.  (5) **The
payoff is four theorems**: `untypedReset_ok_unmapped` (no VSpace root maps a page
of the region), `untypedReset_ok_unreferenced` (no CNode slot or parked message
names a former child), `untypedReset_ok_subtree_absent` (`_children_absent`
until slice 4a) and
`untypedReset_ok_untyped` (watermark `0`, no children) — together, a page the
reset hands back is reachable by no thread until the next carve hands it out,
zeroed.  `untypedReset_preserves_ipcInvariantFull` is the bundle, over the new
`ipcReadViewAgreement.of_inertOrAbsentWrites` (a key may go from inert to
**absent**).  (6) **It declares no static lock footprint**, for `.cspaceRevoke`'s
reason — the VSpace roots it writes are state-discovered and unbounded — so
`declaresStaticLockFootprint_false_iff` names two arms, and it sits in the
scheduler domain's `none` group (`untypedReset_ok_frame`: the scheduler is
unchanged).  It is a live arm of the cross-core inventory
(`CrossCoreTransition.untypedResetDispatch`) with an **empty** write set
(`untypedReset_confinedToCores`) and a delegation proof
(`syscallDelegates_untypedReset`) — the `.vspaceUnmap` arm's shape, since its
unmap pass is that arm's transition.  **An in-place retype of a frame stays refused, and that is final**:
memory returns through its untyped, as in seL4.  What this slice did not give was
seL4's *immediate* unmap on revocation — revoking the untyped capability removed
the frame capabilities while their mappings persisted until the reset, so a
thread kept reading and writing memory whose every capability had been revoked.
That is closed at `v0.36.7` (the next paragraph).  The witness is
`tests/VSpaceCapabilityBindingSuite.lean` §5e, whose decisive case is the sibling
copy.

**A frame capability owns the mapping it made, so destroying it unmaps**
(`v0.36.7`, the security fix slice 3 found).  Until this cut a mapping recorded a
physical address and nothing else, so no capability operation could know which
mapping was its own, and a revoked or deleted frame capability left its mapping
in place until the untyped was reset.  The remedy is seL4's own, not a pool of
page tables.  Six things new code must respect.  (1) **The record lives on the
capability**: `Capability.mapping : Option FrameMapping` (seL4's
`capFMappedASID` / `capFMappedAddress`), written only by `.vspaceMap` on the
capability that made the mapping (`cspaceRecordFrameMapping`, in that
capability's own slot), and a capability whose recorded mapping is still live
cannot map again (`capabilityMappingLive`, `.invalidCapability` — seL4's
`seL4_ARM_Page_Map` on a mapped capability).  Mapping a frame twice takes a
copy.  (2) **A derivation carries no record**: a copy and an IPC transfer insert
`cap.withoutMapping` (seL4's `deriveCap`), while a move and a mutate keep it,
because the capability they leave is the one that made the mapping.  A new
capability-creating path strips the record or states why it keeps it.  (3)
**The destroying arms finalise**: the live `.cspaceDelete` and `.cspaceRevoke`
arms run `cspaceDeleteSlotFinalising` / `cspaceRevokeCdtFinalising`, which
remove every mapping a destroyed capability recorded through the `.vspaceUnmap`
arm's own transition (`unmapLivePages`, in `Architecture/PageTeardown.lean`,
shared with the untyped reset) and **decide** the result (`livePagesCleared`,
`.illegalState` otherwise).  The revocation reports exactly the pages its
traversal destroyed — `cspaceRevokeCdt` returns them, its fold reading each page
from the slot it deletes (`revokeCdtFoldBody_records`) — and the payoffs are
`cspaceDeleteSlotFinalising_ok_unmapped` and
`cspaceRevokeCdtFinalising_ok_unmapped`.  There is **one** revocation traversal:
a first draft added a reporting one beside the state-only one, the reachability
census reported the state-only one as executed by nothing, and it was deleted
rather than pinned.  The bare `cspaceDeleteSlot` / `cspaceRevokeCdt` stay as
the steps the finalising arms compose.  (4) **A stale record removes nothing**: `.vspaceUnmap`
works through a VSpace capability, so a record can outlive its mapping, and each
teardown step re-checks that the recorded address still maps the frame's own
page (`mappedPageLive` — seL4's `unmapPage` paddr comparison), so a different
frame mapped there since survives.  What remains is seL4's own residue: a copy of
the *same* frame remapped at that address is removed by the stale record's
deletion, exactly as upstream.  (5) **Nothing else may drop a recording
capability**: a CNode holding one is not retyped in place
(`CNode.holdsFrameMappingRecord`, `.revocationRequired`), the boot admits no
configured record (`bootSafeCapCheck`, with `bootSafeCnodeCheck_caps`
concluding it), and the frozen delete — which has no unmap — refuses what it
cannot finalise.  (6) **The footprints name what the teardown writes**:
`lockSet_cspaceDelete` takes the unmapped VSpace root as an optional write
member, `lockSet_vspaceMap` the frame capability's CNode (write, for the record)
and the frame (read), and `permittedKinds` admits `.vspaceRoot` for the delete
and the revocation and `.page` for the map.  Both destroying arms are live,
delegation-backed entries of the cross-core inventory with an **empty** write
set, and capability-only entries of the enforcement boundary (canonical 49,
per-core 64).  The witness is `tests/VSpaceCapabilityBindingSuite.lean` §5f,
with the retired non-finalising delete and revocation computed beside the live
arms.

**BP7.1, slice 4a — child untypeds, and a reset that returns the whole subtree**
(`v0.36.8`).  seL4 hands on *part* of a memory grant by carving a smaller
untyped, which the recipient carves in turn; this model can now do that.  Five
things new code must respect.  (1) **The size rides in MR0.**  `.untypedRetype`'s
MR0 is the type tag in bits `[0, 8)` and the object's size as a power of two in
bits `[8, 64)` (seL4's `size_bits`), because all four argument registers are
taken; a frame's MR0 is its tag alone, as before.  `carveRequestOf?` is the one
reading: `.frame` at size `0`, `.untyped` at `[minUntypedSizeBits,
maxUntypedSizeBits] = [12, 47]` (one page, so every carve keeps the parent's
next base page-aligned — `requiresPageAlignment .untyped` is `true`; and seL4's
`seL4_MaxUntypedBits`), anything else `.invalidArgument`.  (2) **There is one
carve.**  `untypedRetypeObject src childId dst req` takes a `CarveRequest`, which
supplies the object, its size, its capability and its memory write; a new
carvable kind is a constructor there, never a second carve beside it.  A child
untyped is `untypedNextChild` — the parent's watermark region, of its kind,
**parent stamped** (the AN6-C.2 contract `retypeFromUntyped` states, first
honoured here) — handed back with read/write/retype (`untypedCapability`) and
**not written**: each frame carve zeroes its own page.  The footprint names the
new key under the kind it will hold (`carvedObjectLock`).  (3) **An untyped is
never destroyed in place.**  `lifecyclePreRetypeCleanup` refuses an `.untyped`
target (`.revocationRequired`), as it refuses a frame: replacing one orphans
everything carved from it, and for a child untyped leaves the parent's child
list naming a kernel object no reset can retire.  (4) **The reset retires the
carved SUBTREE, and it has to.**  `untypedCarvedSubtree` is a bounded worklist
walk over the child lists, proved to contain every child and to be closed
(`untypedCarvedSubtree_spec`); a walk that runs out of fuel is a refusal, never a
smaller subtree.  Every member must be a frame or an untyped, no capability may
name one (decided over the whole store, as before), and every frame must lie in
the region (`carvedSubtreeFramesInRegion` — true of every reachable state, and
decided because it is what lets the region-wide unmap reach a frame at any
depth).  Retiring the whole subtree is forced, not chosen: revoking the parent
capability destroys the child's capabilities too, so a reset requiring each child
to be reset first could never run.  (5) **The payoffs** are
`untypedReset_ok_subtree_absent` (every member gone, the subtree holding every
child and closed) and `untypedReset_ok_retired_pages_unmapped` (no retired
frame's page mapped anywhere, whatever depth it was carved at), beside
`untypedReset_ok_unmapped`, `_unreferenced` and `_untyped`.  The witness is
`tests/VSpaceCapabilityBindingSuite.lean` §5g, with the retired frames-only guard
spelled in the suite and computed beside the live reset on the state it would
have refused forever.  **Page-table objects are slice 4b**, the base BP7.2
installs; `carveRequestOf?` still refuses them.

**A VSpace root is memory, and is never created in place** (`v0.36.9`,
found while scoping slice 4b and reported before the fix).  The in-place retype
built a root at ASID `0` — the boot VSpace root's — and nothing checked the ASID
was free, so `storeObject` moved the ASID table's entry to the caller's root
while the owner's was still stored: `vspaceAsidRootsUnique` and
`asidTableConsistent` false on a reachable state, and every root so made sharing
one TLB tag.  Three things new code must respect.  (1) **`memoryBacked` holds of
`.vspaceRoot`**, so `retypeReplacementAdmissible` refuses it, as seL4 creates a
VSpace only from an untyped.  (2) **Which kinds a device untyped backs is
`deviceBackable`** (untypeds and frames), a separate question from
`memoryBacked`, because a table must be RAM — a table walk reading a device
reads a register.  (3) **No runtime path creates an address space** until slice
4b carves a root from a RAM untyped with a physical table base and an ASID the
kernel checks is free; the cost is registered.  The witness is
`tests/VSpaceCapabilityBindingSuite.lean` §5h, with the retired guard computed
beside the live one.

**...nor destroyed in place** (`v0.36.35`, the post-landing audit, reported
before the fix).  The creation half left the other direction open:
`lifecyclePreRetypeCleanup` was the **identity** on a VSpace-root target, so a
`.retype`-bearing capability to a live root replaced it with any kernel object
while its page tables kept their pages — live leaf descriptors included — and
no ASID invalidation was recorded.  `pageTableMap` reinstalls a stale table
without zeroing it, so the holder could let the frames those tables translate
be reset and recarved to another thread, carve a new root and reinstall the old
table: a writable hardware walk to that thread's page with nothing mapped in
the model.  Latent — a carved root's capability carries no `.retype`, so only a
configured capability reaches it — and High if one does.  Three things new code
must respect.  (1) **The cleanup's `.vspaceRoot` arm is `.revocationRequired`**,
beside the frame, page-table and untyped arms: memory is returned through the
untyped it was carved from, whose reset finalises a root (refuses while a thread
runs in it, unmaps everything, releases its ASID).  (2) **The retype's shootdown
layer is now vacuous** — both of its ASID sources (a destroyed root and an
installed one) are refused before it runs — and it is kept as a defensive layer
rather than retired in this cut; the SM7.F.4(b)(iii) VSpace-root-target TLB
theorems were statements about a refused input and are deleted with a tombstone
in `RetypeWrappers.lean`, replaced by `…_refuses_vspaceRoot` for every wrapper
the live arm composes.  (3) **The witness is §5h again**: the owner's own root,
retyped into an endpoint, is refused, and an endpoint beside it, through the
same arm, is retyped.

**BP7.1, slice 4b — an address space is carved memory** (`v0.36.10`).
`.untypedRetype` at the VSpace-root tag carves a root on one zeroed RAM page of
its untyped, which is its top-level table (`VSpaceRoot.tableBase`), under the
least free non-zero ASID.  Four things new code must respect.  (1) **The carve
checks its own precondition**: `CarveRequest.admissible` re-decides that the
ASID is non-zero, in range and free before anything is written, because
`storeObject` registers a root's ASID unconditionally — the arm choosing one
(`freshAsid?`) is not what makes it safe.  (2) **`tableBase` is `some` exactly
for a carved root**; a boot-configured root has none and cannot be installed
until the boot places a page for it.  (3) **Retiring a root is finalising it**:
the reset refuses while a thread's `vspaceRoot` names one (a reference no
capability carries), removes every mapping it holds through the verified unmap
and checks it empty, and erases its ASID entry, deciding afterwards that no
entry names a retired object (`untypedReset_ok_asids_released`).  **And every
PE leaves a retired root before the reset returns** (`v0.36.37`): the live arm is
`untypedResetWithShootdown`, which posts one acknowledged `.aside1` round per
retired ASID (`untypedResetShootdownAsids_mem`), and a PE servicing an `.aside1`
round installs the kernel's boot tables in `TTBR0_EL1` if it still runs under
that ASID (`shootdown::evict_retired_translation`) before it acknowledges.  The
ledger's broadcast `TLBI ASIDE1IS` empties TLBs and leaves every `TTBR0_EL1`
alone, so a PE lagging behind a remote deschedule kept the retired root's table
page — which the next carve may hand out as a frame — as its walk base.  Every
`.aside1` round in the tree names an ASID no thread may run under, so the
eviction never takes a live thread out of its address space.  (4) **The
carve lock is keyed on the carved kind** (`carvedObjectLock`), so a kind the
carve gains names its own lock.  What is still owed before BP7.2: a table
page for each configured root, and intermediate page-table objects —
registered.  The witness is `tests/VSpaceCapabilityBindingSuite.lean` §5i.

**A thread runs in a carved address space** (`v0.36.11`).  `.tcbSetSpace`
(syscall **38**, count 39) is seL4's `TCB_SetSpace`: invoked on the target TCB
capability with `.write`, MR0/MR1 the addresses in the **caller's** CSpace of
capabilities to the new CSpace root and VSpace root.  Four things new code must
respect.  (1) **The CSpace root needs `.grant` and `.write`**
(`resolveSetSpace`): making a CNode a thread's root hands the thread every
capability it holds and the right to change them, which is the authority
`.cspaceMint` gates on — a read-only or grant-less capability is refused.  The
VSpace root needs `.write`, as `.vspaceMap` does.  (2) **Suspended means the
state says so, not the flag alone**: `setThreadSpace` refuses unless the stored
flag is `.Inactive` *and* `inferThreadState` classifies the thread so (placed on
no core, blocked on nothing), so a stale flag cannot admit a running thread —
§5j's decisive case is the running owner, whose stored flag is the default
`.Inactive`.  (3) **The write is one in-place TCB rewrite** under the lookup's
own witness, reaching `ipcInvariantFull` through the one-field transport
`setThreadFaultHandlerOp` uses.  (4) **It declares a static footprint**
(`lockSet_tcbSetSpace`: the caller and its CNode root read, the target written,
the two new roots read), and `resolveCallerCapObject` is the caller-CSpace
resolution the arm's two operands share — a new arm resolving a capability
operand reaches for it rather than spelling the gate again.  The payoff §5j
measures: the reset refuses while a thread runs in a carved root, and succeeds
once the thread is moved back.

**Intermediate page tables** (`v0.36.12`).  A page table (`KernelObject.pageTable`,
retype tag **9**, `LockKind.page` beside frames) is carved like a frame — one
zeroed RAM page — and installed by `.pageTableMap` (syscall **39**, seL4's
`seL4_ARM_PageTable_Map`; `.pageTableUnmap` is **40**, count 41).  Five things new
code must respect.  (1) **A table installs at the shallowest level the walk to its
address is missing** (`VSpaceRoot.missingLevel?`), so levels arrive in order and
none sits beneath an absent one; a fourth is `.mappingConflict`.  (2) **Both sides
of an install are written together** — the table's `installedIn` and the root's
`tables` slot — and a table installs in one place at a time.  (3) **A carved root
maps a frame only where its walk is complete** (`Architecture.asidTranslationReady`,
read by `vspaceMapFromFrameCap`; `.translationFault` otherwise); a boot-configured
root has no table page and is exempt until the boot places one.  (4) **A table is
not unmapped while anything translates through it** (`pageTableInUse`: a mapping,
or a deeper table), because seL4's tear-out would leave frame capabilities
recording translations the root no longer holds.  (5) **The reset retires tables
with their subtree and refuses an install crossing its boundary**
(`carvedSubtreeInstallsClosed`) — the two sides name each other, so retiring one
leaves the survivor naming an id the next carve reuses.  `LockId.lookup` at `.page`
reads `getPageObject?` (a frame or a table); a new page-backed kind joins it there.
**Destroying a table's last capability takes it out of its address space**
(`finaliseDestroyedCapabilities`, seL4's `finaliseCap` → `unmapPageTable`), with
every mapping and every table beneath it, so revoking memory authority revokes the
translations built on it: the finalising delete and revocation find the tables
some CNode slot named before and none names after (`pageTablesOrphaned` over
`cnodeSlotsUnreferenced`, `v0.36.38` — a copy parked in a blocked sender's message
is dropped by a cancellation that finalises nothing, so it must not keep a table
installed), and the retype of a CNode holding such a capability is refused.  **The root is the truth
and a table's `installedIn` a pointer** (`pageTableInstallLive`): the detach
writes only roots, so the tables it takes out keep a stale record, which reads as
installed nowhere — `.pageTableMap` installs it again, `.pageTableUnmap` clears it,
and the reset does not refuse it.  `tests/VSpaceCapabilityBindingSuite.lean` §5k is
the witness.

**Every configured address space owns a table page** (`v0.36.13`, completing
BP7.1).  Three things new code must respect.  (1) **A root with no table page
maps nothing**: `VSpaceRoot.translationReady` is `tableBase.isSome &&
walkComplete`, so the kernel's own boot root — the one root without a page —
takes no mapping, and a test fixture that means to exercise a map starts from
`Testing.fixtureMappableRoot`.  (2) **A configured root's page comes from the
binding's pool** (`MachineConfig.bootTablePool`): `bootRootTablesPlaced`,
`PlatformConfig.wellFormed`'s eighth conjunct, requires every configured root to
name a distinct pool page and every pool page to lie page-aligned inside the
kernel's reserved extent, so no untyped describes it; a configured root also
holds no intermediate table (`bootSafeUserVSpaceRootCheck`).  (3) **The pool is
one pool in three places**: `rpi5BootTablePool*`, `link.ld`'s
`.boot_table_pool` (the last sixteen pages of the reserved extent, `ASSERT`ed
live by `scripts/check_link_script.py`) and `mmu::BOOT_TABLE_POOL_*`, held
together by `tests/fixtures/boot_map.expected`'s `tablePool` line; the HAL zeroes
it (`mmu::zero_boot_table_pool`) before the Lean kernel is entered.

**A thread maps only inside the user window, under a 16-bit hardware ASID**
(`v0.36.14`, BP7.2's first cut).  Three things new code must respect.  (1)
**Level-0 entry 0 of every user root is the kernel's**: a thread's root is
installed in `TTBR0_EL1` beside the kernel's own window rather than the kernel
moving to `TTBR1_EL1`, so `.vspaceMap` refuses an address below
`VAddr.userWindowBase` (`2^39`) and `.pageTableMap` installs no table there
(`pageTableAddressable` is `VAddr.inUserWindow`); a fixture addresses a mapping
with `Testing.fixtureUserVAddr`.  (2) **A mapping's virtual address is
page-aligned**, as its physical address is: `VSpaceRoot.mapPage` refuses both
(`mapPage_vaddrAligned`), and `vspaceMapPage` answers `.alignmentError` through
`pageMappingAligned` — two keys inside one page would be two mappings in the
model and one translation on the machine.  (3) **The model's ASID space is the
hardware's tag**: `TCR_EL1.AS` selects 16-bit ASIDs, a PE implementing fewer
halts before it is written (`mmu::asid_bits_of_this_pe_or_halt`), and
`tests/fixtures/boot_map.expected`'s `asidSpace` line holds `maxASID` to it —
with `AS` clear two address spaces whose ASIDs agree in their low byte would
share TLB entries.

**Physical memory is made to agree with the model, and a thread's translation is
installed with the kernel window** (`v0.36.15`, completing BP7.2).  Five things
new code must respect.  (1) **A transition that changes an address space
records what it owes physical memory**, at the one place it changes the model,
in `SystemState.pendingPhysicalWrites` (`Architecture.PhysicalWrite`: zero a
page, store a descriptor, invalidate an ASID) — a mapping or an unmap its
level-3 entry (`mappingStore?`), a table install or unmap the parent entry
(`slotStore?`), a finalising detach the parent clear, a zeroing of every table
page it takes out and an ASID invalidation (`detachWrites`), every carve's scrub
its zeroing, a reset's retired root its ASID.  A new writer of `mappings` or
`tables`, or a new scrub, records too; the model's `machine.memory` is not the
machine's.  (2) **The ledger is drained by every state-committing entry**, read and
cleared in the atomic step (`syscallDispatchCrossCoreStep_drains_physicalWrites`
at the syscall seam) and performed **first** — before the SGIs, the shootdown
round and the restore (`completePhysicalWrites`) — so no core refills a TLB
entry from a descriptor already cleared.  The fault seams, the timer tick, the
`.reschedule` receiver (and so the secondary bring-up entry) and the cross-core
suspend all drain it the same way since `v0.36.39`, each pinned by a Tier 3
anchor: until then only the syscall and fault seams did, under a sentence saying
no other entry reached a recording transition — a claim nothing checked, and one
a new recording step inside a tick or a suspend would have falsified silently,
leaving its writes owed to RAM until an unrelated syscall drained them.  The
instruction-cache operand ledger (`pendingIcacheMaintenance`) is drained at the
same entries in the same step, emitted after the SGIs and before the restore,
through `Platform.FFI.completeIcacheMaintenance` (moved there from
`SyscallDispatchEntry` so the other entries can reach it).  A new
state-committing entry drains both ledgers in its atomic step.  (3) **The HAL validates, then writes, and halts on
a refusal**: a page is a pool page or covered RAM past `KERNEL_RESERVED_END`,
never the kernel's own (`user_translation::decode_physical_write`), because the
Lean kernel names only pages it owns and a refused operand is a defect.  (4)
**Level-0 entry 0 of a user root is written by the install, not the model**
(`ffi::mmu_install_translation`): the boot tables' own entry 0 with UXNTable and
APTable = no-EL0, which makes the window's EL0 denial a property of one entry
rather than of every descriptor beneath it (each of those carries UXN and no
EL0 access today; a boot-map descriptor that lost either would not reach EL0) —
and
`TTBR0_EL1` takes the root's page with the ASID in bits [63:48], with no TLB
invalidation (thread translations are nG, the kernel's are global).  (5) **What
a thread installs is `Architecture.threadTranslationOperands`**: its root's page
and ASID, or `(0, 0)` for the kernel's translation when the root owns no page;
BP7.6's context restore hands them to `Platform.FFI.ffiRestoreCommit`, which
installs them only once the frame is replaced (`v0.36.41`, below).

**Every trap entry saves the whole frame the thread trapped with** (`v0.36.16`,
BP7.3).  Four things new code must respect.  (1) **`RegisterFile` carries
`pstate`** (`SPSR_EL1` — the flags, the mode and the masks), compared by its
`BEq` and required by `RegisterFile.ext`; a context without it resumes a thread
preempted between a compare and its branch with the wrong condition.  (2) **The
HAL publishes the in-flight frame** for a handler's duration
(`trap::InFlightFrame`, withdrawn on drop, a nested handler restoring the one it
displaced), and the Lean entry reads it whole, in one call, before its atomic step
(`Platform.FFI.captureTrapFrame` over `ffiTrapContext`, `trap::TRAP_FRAME_CONTEXT_WORDS`: `x0`–`x30`,
`SP_EL0`, `ELR_EL1`, `SPSR_EL1`, and since v0.36.30 `TPIDR_EL0`, which EL0
writes with no trap — until then a thread read the previous thread's value).  (3) **Every state-committing trap entry saves
it** — the syscall seam, the fault and unknown-syscall entries, the timer tick
and the `.reschedule` receiver — into **both** the executing core's bank and the
current thread's `registerContext` (`Architecture.saveTrapFrameOnCore`), so
`contextMatchesCurrentOnCore` holds on the state the transition runs on
(`saveTrapFrameOnCore_contextMatchesCurrentOnCore`) and a switch saves every
register rather than the syscall window.  A new state-committing trap entry
captures and saves the same way.  (4) **Only a frame taken from EL0 is a
thread's** (`trapFromEl0`, `SPSR_EL1.M[3:0] = 0`): a tick taken while an idle
core waits at EL1 carries the kernel's registers and saves nothing.

**Each core's resume is staged from the committed state** (`v0.36.17`, BP7.4).
Four things new code must respect.  (1) **A syscall's result is in the caller's
saved context before any local reschedule** (`Architecture.stageCallerReturn`,
run before `scheduleLocalSuccessorLive`): the restore resumes a thread *from*
its context, so a result staged only in the HAL mailbox would be replaced by the
arguments a same-entry switch saved.  A path that answers a syscall with a frame
— the refusal in `syscallBracketRefusalResult` included — stages it the same
way.  (2) **Every state-committing entry names what its core resumes**
(`Architecture.restoreTargetOnCore` on the committed state: a user thread's
context and translation, `.idle` for an idle thread, `.none` for an empty core)
and hands it to `Platform.FFI.restoreTrapFrameLive` last, after every memory and
TLB effect the commit owed; a new entry does too.  (3) **The HAL sanitises a
user resume's `SPSR_EL1` to its condition flags** (`trap::sanitise_user_spsr`),
because a thread's saved `pstate` is state the thread influences, and an idle
resume enters `trap::kernel_idle_loop` at EL1h — the only EL1-origin frame a
restore ever replaces, since every other kernel path runs with IRQs masked.
(4) **The restore was gated on `contextRestoreSeamLive` at this cut**, and
BP7.6 deleted the gate — the paragraph after next.

**A staged unblock frame is what the thread resumes with** (`v0.36.18`, BP7.5).
Delivery is one relation, not a mechanism per path:
`switchToThreadOnCore_delivers_readReturnFrame` says a switch resumes the
incoming thread with the frame its TCB holds, because the switch's only object
write is the *outgoing* thread's context save; the two unblock paths then state
what that frame is (`restoreToReadyCancelled_readReturnFrame`,
`abortPendingIpcOnEndpoint_readReturnFrame`) and the two corollaries compose
them.  Two things new code must respect.  (1) **The delivered frame has one
reading**, `Architecture.RestoreTarget.deliveredFrame?` (`x0`–`x5` of a user
target, none for idle or an empty core), beside the restore target in
`Scheduler/Operations/ResumeDelivery.lean`; a witness that decodes a target's
context itself is a second reading, and a Tier 3 negative refuses the one the
cancellation suite had.  (2) **What is not claimed**: that nothing between the
unblock and the switch rewrites the frame.  A `.ready` thread on no IPC queue is
targeted by no delivery and the trap-frame save writes only a core's *current*
thread, but that is a property of every transition, not of this relation; the
executed witnesses (`tests/SmpCancellationSuite.lean` §3.19b,
`tests/SmpTimerSuite.lean` §3.15b) drive the live unblock and the live switch
end to end, each with a CONTROL that switches before the unblock and resumes the
stale window.

**The context restore is live, and its gate is deleted rather than flipped**
(`v0.36.19`, BP7.6).  `contextRestoreSeamLive`, its module
`Concurrency/ContextRestoreSeam.lean`, `scheduleLocalSuccessorLive`, the
`…Live` / `…EnqueueOnly` pairs of `.tcbResume` and of the priority preemption,
`restoreTrapFrameLive` and the context-switch-site register are gone, each with a
tombstone and a Tier 3 negative; every entry runs `scheduleLocalSuccessor` and
hands `Platform.FFI.restoreTrapFrame` the target BP7.4 stages.  Four things new
code must respect.  (1) **A trap arm returns through the restore first**: the SVC
arm, `deliver_fault` and `deliver_unknown_syscall` open with
`if crate::trap::take_restored() { return; }` ahead of any mailbox write, poison
or halt, and `build.rs` holds it there as a top-level statement
(`is_restored_frame_return`); publishing a mailbox frame clears the core's
`RESTORED` flag, so a stale restore cannot survive into the next trap.  The
sentinel and the two halts remain, and mean only *no restore was staged on this
core*.  (2) **A caller its own syscall switched out keeps its result**: an inline
`.tcbResume` or a priority preemption can switch the caller out before the
result is staged, so `stageCallerReturn` writes the frame into the caller's TCB
always and into the core bank only while the caller is still current
(`stageCallerReturn_stages_switched_out`) — the bank then belongs to the
successor.  (3) **The fault progress theorem sees through the successor**, and
what that needs is the executing core's queue well-formed where the successor is
chosen (`handleRescheduleSgiOnCore_preserves_not_dispatchable`).  It is taken of
the **pre**-state (`runQueuesWellFormed`, every core) and carried across the
spill and the delivery by `faultDeliverOnCoreChecked_preserves_runQueuesWellFormed`,
never stated of the delivered state, which no caller holds.  (4) **One path,
not two**: with the gate gone there is no inert arm for a theorem to be stated
over, so a result about an entry is a result about the program the hardware
runs; a new entry does not grow a `…Live` twin.

**The declassified badge is delivered, not only staged** (`v0.36.20`, BP7.7).
SM9.C's data-carrying declassification is the one flow the kernel makes visible
on purpose, and in the wait-before-signal ordering its badge reaches the waiter
only through the return frame.  `tests/SyscallReturnAbiSuite.lean` §11 runs the
whole path through the live bracketed entry step: the waiter's
`.notificationWait` blocks on the boot core, a `kernelTrusted` signaller's
`.declassifySignal` from core 1 — a downgrade the base lattice refuses and the
policy authorizes — returns the unit frame, posts one `.reschedule` and writes
one trail record, and the waiter's core, taking that `.reschedule`, stages a
restore whose `x0` is the badge.  Two things new code must respect.  (1) **A
witness of delivery reads the RESTORE TARGET**, `restoreTargetAt … |>.deliveredFrame?`,
never the TCB's register context alone: the context is what the switch reads,
the target is what the hardware receives, and only the second is the claim.
(2) **Its control is the deny-all policy**, under which the signal is refused
and the waiter's core resumes nothing — so the positive run is a statement about
the policy rather than about the fixture.  Executing it on the image is BP8's.


**Message registers past the fourth cross the kernel in both directions**
(`v0.36.21`, BP7.8).  Both were owed and one was registered: the decode read a
sender's `MR4` onward from `machine.memory` — the model's memory, which holds no
thread's writes — and no delivery wrote a receiver's.  Four things new code must
respect.  (1) **One resolver, both directions**:
`IpcBufferRead.ipcBufferSlotPAddr?` (the slot's page through the thread's own
VSpace, eight-byte aligned, declared RAM, and writable when `needWrite`) is what
the seam reads and what a delivery writes; a new path touching a thread's buffer
asks it, never `root.lookup` directly.  (2) **The model holds no thread's memory,
so a read of it is synced first**: the syscall seam reads the caller's words from
RAM (`readCallerOverflowWords`, `ffi_read_user_word`) and writes them in with
`syncUserWords` in the atomic step before the decode — `ipcBufferReadMr_syncUserWord`
is the relation, over `writeUInt64` and `readUInt64_writeUInt64`.  A new kernel
read of user memory is synced the same way.  (3) **A write to a thread's memory is
owed to RAM, not to the model**: `stageDeliveredMessage` records
`PhysicalWrite.storeUserWord` (tag 3) on the ledger, as a descriptor store is, and
`returnMessageInfo`'s `overflow` makes the frame's length count exactly what was
written — a prefix, stopping at the first slot the resolver refuses.  The HAL
admits a user word only in RAM past the kernel's extent and never in the table
pool, so a message register cannot become a descriptor.  (4) **Every entry whose
commit can deliver a message drains the ledger** through
`Platform.FFI.completePhysicalWrites`, the fault seams included, since a
thirteen-word fault message is delivered to a handler waiting in receive.

**Each thread has an FP/SIMD context, switched lazily** (`v0.36.22`, BP7.9).
`TCB.fpContext` (`v0`–`v31`, `FPCR`, `FPSR`; erased by `projectKernelObject`)
and `MachineState.fpOwner` (whose values each core's registers hold); the
transitions are `Architecture.fpAccessOnCore` (EC `0x07` from EL0, entered by
`lean_handle_fp_access`) and `Architecture.fpReleaseOnCore`.  Six things new code
must respect.  (1) **The load is always the trapping thread's own saved
context** (`fpAccessOnCore_load_eq_own_context`), and captured live values are
written into the recorded owner and no other thread
(`fpAccessOnCore_saves_owner`, `fpReleaseOnCore_saves_owner`) — the property that
keeps one thread's FP state out of another's reach.  (2) **The release happens at
the entry that switches the owner out**, not when the next thread traps as in
seL4: this kernel's placement is not fixed by affinity, so pure per-core laziness
would need seL4's cross-core release IPI on every move.  Every entry that
restores a context runs `Concurrency.releaseSwitchedFpOwner` between its commit
and its restore — a second commit under the same entry lock — and a new such
entry does too; its `_def` marker pins it.  (3) **A thread owned on another core
retries** (`fpAccessOnCore_retry_of_owned_elsewhere`): the trap stays armed and
the instruction re-executes until that core's next entry releases it, which the
SGI its `current`-slot change sent guarantees; loading the stale TCB copy instead
would lose the thread's work.  (4) **The trap follows the restore**:
`RestoreTarget.user`'s `fpLive` (`fpLiveFor`) is restore kind `2`, which lifts the
trap; kinds `0` and `1` arm it.  So the trap is lifted exactly while a core runs
its owner, which is what makes the kernel's own FP-freedom (the gate above) the
only thing standing between kernel code and an owner's registers at EL1.  (5)
**`fp_context.S` is the only kernel code that names an FP/SIMD register or writes
`CPACR_EL1` outside the boot prologues**: `sele4n_fp_save_context` (lift, store,
re-arm), `sele4n_fp_load_context` (lift, load everything, `FPCR`/`FPSR`
included), `sele4n_fp_trap_lift`, `sele4n_fp_trap_arm`, in
`.text.sele4n_fp_context`, writing `FPEN = 0b11` alone so SVE and SME stay
trapped.  `build.rs` pins each routine's writes (`FP_CONTEXT_CPACR_WRITERS`) and
the disassembly gate exempts the two FP routines **by symbol**, reconciled both
ways.  (6) **A thread a core's registers still hold is not destroyed**
(`threadHeldOnSomeCore`, `.revocationRequired`): the release would otherwise
write a destroyed thread's values into whatever TCB the retype creates under its
id.  `retypeTargetDetached` carries `tcbFpReleased` for the payoff.  Executing
the switch on the image is BP8's.

**The boot starts both initial threads, one per domain** (`v0.36.23`, BP7.11).
Until then every configured thread was installed `.Inactive` and nothing ever
resumed one, so the labeling guard was decided on a separation between two
threads that could never run.  Five things new code must respect.  (1) **The
start is the kernel model's**: `Kernel.startInitialThreadOnCore`
(`Scheduler/Operations/InitialThreadStart.lean`) is `enqueueRunnableOnCore`
preceded by the flag write it does not do, and it dispatches nothing — every
current slot stays `none`, so each core's first scheduling point selects.  A
second body in the boot would be a second answer to "what makes a thread
runnable", the reason `enqueueIdleThread` is the kernel model's too.  (2)
**`bootSafeTcbCheck` still requires `.Inactive` of every configured thread**;
the start writes `.Ready`, and `initialThreadStartable` (stored, `.Inactive`,
unqueued, positive time slice, no inherited boost) is the one place the started
set is admitted — a name it refuses refuses the boot
(`unstartableInitialThreadBootError`), never a skip.  (3) **A binding's started
threads are derived from its labeling**: `PlatformBinding.initialThreads` is the
two separation witnesses, and `bindPlatformConfig` installs it as it installs the
boot root, so the threads the guard is decided on and the threads that run are
one list; a direct-entry caller names its own through
`PlatformConfig.initialThreads` (default `[]`, where the stage is the idle boot,
`bootFromPlatformCheckedStartedFor_of_nil`).  (4) **One bundle argument for
every boot**: `bootStartShape` names what the proof-layer bundle reads of a boot
state, `proofLayerInvariantBundle_of_bootStartShape` is the argument, and a new
boot stage proves that it keeps the shape (`startInitialThread_preserves_bootStartShape`)
rather than re-running the argument.  (5) **Concrete boot states are proved by
rewriting, never by unfolding a bind against them**: the deployment's proofs go
through `bootFromPlatformCheckedStartedFor_of_idle`, stated over variables,
because a defeq check that reaches `startInitialThreads` of a concrete list
evaluates `initialThreadStartable` against the whole boot state and times out.

**The image runs under QEMU, on `virt`** (`v0.36.24`, BP8.1 slice 1).  QEMU
ships no BCM2712, and `virt` is its one machine carrying PSCI, a GICv2 and a
PL011, so BP8.1's answer is a QEMU device map from a platform binding.  Six
things new code must respect.  (1) **The board is a build-time choice with one
home**: `rust/sele4n-hal/src/board.rs`'s `BoardMap` holds every board-dependent
constant the boot path reads — RAM base, reserved extent, device window, PL011
base and clock, GIC bases — `RPI5` by default and `QEMU_VIRT` under
`board_qemu_virt`, and `mmu`, `uart` and `gic` read them off `BOARD`.  A new
board is one more `BoardMap`; its shape is decided by a `const` assertion on
every board, so a malformed one fails every build.  (2) **The reserved extent
is `[KERNEL_RESERVED_BASE, KERNEL_RESERVED_END)`**, at the base of a
gigabyte-aligned RAM: membership is `mmu::in_kernel_reserved_extent` (offset
form, since `0 <= x` is an absurd comparison clippy refuses on the RPi5), and
the boot tables put `l2_ram` at the RAM's gigabyte (`RAM_GIB`), never at index
0.  (3) **`link.ld` is the RPi5's and the `virt` script is derived from it**:
`build.rs`'s `board_link_script` rewrites exactly the three board lines
(`RAM_BASE`, `KERNEL_RESERVED_END`, `MEMORY`'s `ORIGIN`) from `board.rs` and
nothing else, and refuses to build either image if `link.ld`'s three do not
state `RPI5`'s.  The image loads 512 KiB above RAM on both boards, which a
`link.ld` `ASSERT` holds.  (4) **`_start` begins with the arm64 Image header**
(a branch past it, then `text_offset`, `image_size` = `__kernel_image_size`,
flags and the magic): QEMU passes the device tree in `x0` only to an image
carrying it, and hands a headerless ELF nothing.  `build.rs` pins it word for
word (`IMAGE_HEADER`, `entry_body_index`), the prologue scanners start after it,
and the FP/SIMD gate reads its data words as data, admitted only in `_start`'s
first 64 bytes.  (5) **A uniprocessor GIC reads its targets as zero**: the
distributor self-check expected `0x0101_0101` from ITARGETSR unconditionally and
halted the first run, since `GICD_TYPER.CPUNumber = 0` makes the field RAZ/WI;
it reads `TYPER` now (`self_check_expected`).  (6) **`scripts/test_qemu.sh` is a
live gate**: it builds the `virt` image, cuts the raw binary, boots it at EL1
and with `virtualization=on` at EL2, and requires `qemu_boot_expected.txt`'s
fragments **in order** plus each run's own entry level and PSCI conduit.  The
fixture has a `.sha256` companion the lane verifies itself.  What slice 1 does
**not** do is run Lean: the Lean `virt` binding and its fixture are slice 2, and
the Lean-linked boot to the first idle dispatch is slice 3.  The HAL's `virt`
constants were held to nothing on the Lean side until slice 2 (the next
paragraph).

**The Lean kernel has a `virt` binding and a `virt` boot entry** (`v0.36.25`,
BP8.1 slice 2; `SeLe4n/Platform/QemuVirt/`, in the library root).  Five things
new code must respect.  (1) **A board is a binding plus an entry**: the
`virt` image calls `lean_kernel_main_qemu_virt` (`QemuVirt.kernelMain`) where
the RPi5's calls `lean_kernel_main`, both exported from every archive, and
`lean_entry::enter_lean_kernel` selects by `cfg` — two extern items, two
cfg-gated `let`s, one occurrence each in `LEAN_UPCALLS_OUTSIDE_THE_GATE`.  A new
board adds a row, never a runtime switch.  (2) **The boot-entry contract is a
table** (`BootEntryContract.bootEntries`, `BootEntrySpec`): each exported symbol
is held to its own approved call, and the cross-wired witnesses — each board's
shape refused under the other's row — are what make it decide *which* board an
entry boots.  (3) **The board check is one question**: `virt`'s bridge
(`qemuVirtPlatformConfigFromDtb`) accepts through the RPi5 bridge's own
`Boot.deviceTreeCoversMachineConfig` and `Boot.deviceTreeCoversMmioRegions`,
asked of this binding's machine configuration and windows; only the binding
differs.  Board-free pieces are shared, not copied — the runtime contract, the
kernel boot root's builder (`VSpaceBoot.insertIdentity`) and the deployment's
object builders — and a piece is board-free only if it reads no board
constant.  (4) **`virt` is one fixed configuration**: RAM `[0x4000_0000,
0x8000_0000)`, extent `[0x4000_0000, 0x5000_0000)`, four PEs, the RPi5
deployment's layout on it, every boot gate `decide`d
(`qemuVirtBoundPlatformConfig_*`), the started boot proved on every account
(`bootAndInitialiseQemuVirt_qemuVirtPlatformConfigFor`).  (5) **Each board's
HAL is held to its own binding by running both**: the Lean suite writes
`tests/fixtures/boot_map_qemu_virt.expected`, the HAL reads it under
`board_qemu_virt` through the same readers the RPi5 uses (`mmu::LEAN_BOOT_MAP`,
`mmu::BOARD_LINK_SCRIPT` — the derived script, written on every build), and
`scripts/test_rust.sh` runs that lane (step 4) and lints the RPi5 HAL apart
(step 7), since `--all-features` selects `virt`.  A HAL test that names a
board's address is a board's test: it reads `board::BOARD`, or it carries a
twin for the other board.  QEMU's own device tree is a fixture
(`tests/fixtures/qemu_virt_dtb.hex`, `scripts/qemu_virt_dtb_fixture.py`) that
both bridges are run on.

**The Lean kernel runs, on every PR** (`v0.36.26`, BP8.1 slice 3).
`scripts/test_qemu.sh --lean-kernel` boots the Lean-linked `virt` image on four
PEs at EL1 and EL2 to every core's first idle dispatch, as the archive lane's
sixth step, with `REQUIRE_QEMU=1`.  Its first execution found three defects no
host test could, and each is a rule now.  (1) **A Lean byte read on the boot
path is `bytes[i]?`, never `bytes.data[i]?`**: in compiled code `ByteArray.data`
copies the whole array boxed, so a per-byte `.data` read is quadratic in the
blob — the device-tree parse never finished on QEMU's 1 MiB tree, and a Tier 3
negative refuses the spelling in `DeviceTree.lean`.  (2) **A restore replaces
an EL1-origin frame only after its core has handed itself to the idle wait**
(`trap::IdleHandoffFlags`): every core's bring-up tail runs with IRQs unmasked,
so a tick there would otherwise resume the idle loop over the bring-up and
abandon it — the secondaries' IRQ-readiness publication, the boot core's
topology refusal.  A bring-up ends in `trap::enter_idle_wait`, never in a loop
of its own.  (3) **Every core runs a first reschedule** (`smp::first_reschedule`),
the boot core's between its readiness and its unmask as a secondary's is: a
booted state has no current thread, and a tick on such a core dispatches
nothing.  The lane runs QEMU under `-icount shift=0,sleep=off` because under
multi-threaded TCG one emulated Lean tick outlasts the 1 ms period and four
PEs saturate the kernel-entry lock; the clock is counted in instructions, which
is not a longer tick.  The fixture is
`tests/fixtures/qemu_lean_boot_expected.txt`; the log's
`[sched] core N: first idle dispatch` is printed after the IRQ handler releases
its kernel-entry bracket, the one place a print cannot deadlock against a core
still printing its bring-up.

**The four-PE bring-up is executed, and a console line is a line** (`v0.36.27`,
BP8.2).  `scripts/test_qemu_smp_bringup.sh` boots the HAL-only and the
Lean-linked `virt` images on four PEs at EL1 and EL2 in the archive lane, holds
every secondary's per-core init in order to
`tests/fixtures/qemu_smp_bringup_expected.txt`, and ticks the two SM1.H boxes
WS-RR RR7.16 unchecked.  Four things new code must respect.  (1) **A banner is
matched as a whole line**: no console tag may appear anywhere but at a line's
start, because a substring search passed the first four-PE boot, whose log was
torn.  (2) **A PE prints nothing before its own MMU is on**, the invalid-context
refusal excepted: with translation off the console bypasses its ticket lock
(`uart::ticket_lock_usable`), which is sound only while no other PE prints, and
each secondary's first banner tore against the others'.  (3) **A console line
is one lock acquisition**: `kprintln!` took it twice (body, then newline), the
defect `kprintln_core!` fixed at SM1.G and nothing swept onto its sibling;
`uart::tests::a_printed_line_takes_the_console_lock_once` counts the lock's
tickets.  (4) **A QEMU lane builds and boots through `scripts/qemu_boot_lib.sh`**,
never its own copy, and a `virt` image builds under `rust/target/qemu-virt*`:
the archive lane uploads `rust/target/<target>/release/sele4n-kernel` as the
Raspberry Pi 5 image, and a `virt` build there would ship in its place.

**The Tier-4 gates execute on the `virt` test image, and the shootdown box is
decided by a run** (`v0.36.28`, BP8.4).  The four gates that need no user
program — the SGI round trip (SM1.H.5), the console stress (SM1.G.3), the TLB
shootdown round trip (SM7.E.2) and the shootdown stress (SM7.E.3) — are
in-image drivers (`rust/sele4n-hal/src/smp_exercisers.rs`, feature
`smp_exercisers`) the boot core runs before it hands itself to the idle wait,
and `scripts/test_qemu_smp_minimal.sh` boots two PEs where the kernel declares
four; every gate reports a result on both `virt` images, and the eight that
drive kernel transitions from user space report NOT RUN naming why.  Five
things new code must respect.  (1) **The exerciser feature never reaches a
release image**: it builds into `rust/target/qemu-virt*-exercisers`, the
archive lane's image build is refused if it names it
(`check_aarch64_cross_target.py`, which also refuses it on any image build
without the board selector), and the cross lane builds the test image last,
after both images it checks.  (2) **A round is the kernel's round**:
`run_round_in` acquires the round lock (self-servicing a round in flight while
it waits, under the seam's own fuel `ROUND_LOCK_ACQUIRE_FUEL`, which is
`shootdownRoundLockAcquireFuel`), allocates the generation, publishes the
operand, requests every online target, broadcasts the invalidation and waits
bounded for the acknowledgments — `completeShootdownRounds`' order, with
`tlbi_local` nowhere in the module — and a timed-out round halts the system,
because a round left open is a round lock the next kernel entry halts on.
The three mutations that decide it are recorded in the plan: a local
invalidation leaves core 1's translation stale, a round that sends no request
times out, and two initiators without the lock are reported inside one
critical section.  (3) **The window is global and hangs off the boot L1
table** (`mmu::install_exerciser_window`, entry 511, `0x7F_C000_0000`), so a
probe translates under every thread's `TTBR0` and survives the idle restore;
the install is refused unsealed, unaligned, outside the kernel's extent or at
an entry in use, and the HAL-only image seals the map where the Lean image
does.  (4) **A driver prints whole lines and the checker reads relations**
(`scripts/qemu_exerciser_lib.sh`): acknowledged generations at or past the
round's, each core's stress lines exactly the iterations 0..31, 32 rounds
under 32 distinct generations, and no stale probe.  (5) **A gate that cannot
run says why**: the PE-withheld Lean run admits a serving secondary's idle
dispatch and refuses the boot core's, and the eight user-program gates exit 77
through `exerciser_user_program_gate`, never by searching an image with
`strings`.

**The per-core counters are read on the booted machine** (`v0.36.29`,
BP8.5).  `Concurrency.perCoreStats` and `perCoreStatsPlausible` — WS-RR
RR7.33's reader and its containment, proved and runtime-checked and until now
executed on no machine — run on the Lean-linked `virt` image on every PR,
through one selector-driven seam.  Four things new code must respect.  (1)
**The seam answers one word per call**: `lean_per_core_stats_component(core,
selector)` is `perCoreStatsComponentExport`, `BaseIO UInt64` so it crosses as a
`uint64_t`; `perCoreStatsSelect`'s arms are the four counters in the snapshot's
own order (`0..3`) and the verdict (`4`, as `1`/`0`), and every other selector,
or a core the model lacks, is refused with every bit set (`perCoreStatsRefused`),
which no counter reaches and neither verdict is.  The Rust side mirrors the
selectors as `STATS_*` constants, pinned to the arms by Tier 3.  (2) **It is a
Lean upcall like every other**: declared and called inside the readiness
guard's true branch in `smp_exercisers::lean_stats_component`, a
`LEAN_READY_GATED_SEAMS` entry — and **it runs with IRQs masked, under the
kernel-entry lock**.  It commits nothing, and that was the wrong question: the
kernel's Lean runtime runs one core at a time (non-atomic reference counts, one
heap behind a leaf lock that does not mask IRQs), and the first cut called it
bare from the boot core in thread context, so a tick preempting it inside the
heap lock wedged the kernel-entry lock on every core (Lean Action CI run
36499869963, `v0.36.34`).  `build.rs` now derives that every Lean upcall sits
inside `crate::kernel_entry::with_kernel_entry(…)` or is registered, by
occurrence and with its reason, in `LEAN_UPCALLS_OUTSIDE_THE_ENTRY_LOCK` (the
boot install, the library initializer, and the exception classifier, which runs
with IRQs masked and touches no non-persistent shared object), and holds each
thread-context seam (`LEAN_UPCALLS_IN_THREAD_CONTEXT`) to masking IRQs before
the bracket and restoring the value it saved after.  (3)
**The driver's evidence is the bracket, and the bracket needs the slots told
apart.**  Each core's words are read between two Rust reads of the same slot,
in the reader's own order (subtypes, total, syscalls; the verdict last, of a
snapshot of its own), so a word outside `[before, after]` was read off another
slot; and since the four cores tick at one rate from nearly one instant, the
driver first drives each secondary's SGI count `STATS_SGI_SPREAD` past the
core before it with agent commands, reading the count live so the chain holds
whatever the earlier drivers left in each slot — a fixed spread would have
depended on those priors.  (4) **The gate re-derives the relations from the
printed words** (`scripts/qemu_exerciser_lib.sh`), never from the driver's own
verdict: a verdict `1` beside words that refute it is a seam answering `1`
unconditionally, which the driver alone could not see.  The gate
(`scripts/test_qemu_smp_per_core_stats.sh`) is Lean-image only and reports NOT
RUN otherwise (`gate_lean_only` in the runner), the all-driver tally is five on
the Lean image and four on the HAL-only one, and the verdict on a core
(`stats_verdict`) is pure and host-tested.

**Three acceptance boxes are decided by runs on the target** (`v0.36.31`).
Three things new code must respect.  (1) **A refused Lean initialization is
reported and halted on in one function**, `lean_entry::initialise_or_halt`, and
the refusal probe (`lean_init_refusal_probe`, a `virt` test image) drives all
three refusals through it, so what `scripts/test_qemu_lean_init_refusal.sh`
executes is the code a real refusal runs; a second report-and-halt path beside
it would make the gate a statement about a copy.  (2) **A test image's feature
is in `TEST_IMAGE_FEATURES`** (`scripts/check_aarch64_cross_target.py`), which
refuses it on a board image and on the release image; a new test-image feature
joins that tuple on the day it is added.  (3) **The boot reports a heap census on
each side of the install and a line at the release**, and `scripts/test_qemu.sh
--lean-kernel` reads them as relations (the install allocated with the heap's
invariants intact; install, then release, then any secondary).  The release
line is printed before the first `CPU_ON`, so moving it after one breaks the
BP4.2 evidence.

**PR #904's review, and the rows this PR had registered, are fixed rather than
registered** (`v0.36.41`).  Seven things new code must respect.  (1) **A core
records the thread its registers hold at EL0** (`MachineState.resident`,
written by `PriorityInheritance.settleResidencyOnCore`, the last step of every
state-committing entry's atomic commit): a remote deschedule empties a core's
`current` slot while the thread still runs there, and the next EL0 exception on
that core now saves its frame into the resident thread
(`Architecture.saveVacatedFrameOnCore`) — rewound to the `SVC` on the syscall
and unknown-syscall entries (`saveCapturedSyscallFrame`), so the interrupted
syscall is re-issued — where it used to be dropped — and a thread some core still holds as its
resident is not destroyed (`threadHeldOnSomeCore` reads
`MachineState.residentOnSomeCore`; `retypeTargetDetached.tcbResidencyReleased`),
since that save would otherwise land in the TCB retyped under its id.  (2) **No thread is resumed
on two cores**: the settle step switches a core to its idle thread rather than
resume a thread another core is still resident in
(`deferResidentElsewhere_current_not_elsewhere`); the thread stays queued and is
selected once that core has saved it.  (3) **A frame capability's mapping record
names a mapping epoch** (`FrameMapping.epoch`, drawn from the frame's own
`FrameObject.mapEpoch` and stored in the root's `mappingEpochs`,
`tagFrameMapping`), so a record whose ASID and address were reused by a later
mapping of the same frame is stale (`mappedPageLive`), and the frame is a
**write** member of `lockSet_vspaceMap`.  (4) **`freshAsid?` scans without
materialising the ASID space** (`freshAsidFrom`, fuel-bounded).  (5) **The HAL
validates what a descriptor says, not only where it lands**: `PhysicalWrite`
separates a level-3 page (`storeDescriptor`, tag 1) from a table
(`storeTableDescriptor`, tag 4), because the walker reads `0b11` by level, and
`user_translation::page_descriptor_admissible` / `table_descriptor_admissible`
refuse a page naming the kernel, a table page or uncached RAM, and a table naming
anything but a thread table page.  (6) **A restore installs the translation and
lifts the FP trap only once the frame is replaced**: the translation rides with
`ffiRestoreCommit`, and `fp_context::load_commit` re-arms the trap for the
commit to lift.  (7) **Every kernel stack has an unmapped guard page below it**
(`link.ld`, `ImageLayout::stack_guards`; secondary slots are 128 KiB with the
guard at their base), and an EL1-origin synchronous exception or SError runs on a
per-PE fault stack (`vectors.S` `msr spsel, #0`; SP_EL0 holds the fault stack's
top whenever a PE runs at EL1 — `boot.S`, `trap.S`'s `set_fault_stack`, the idle
restore's `IdleResume`), so an overflow faults and halts rather than corrupting
`.bss` or re-faulting on the stack that overflowed.  And the boot-entry contract
refuses a configuration argument whose project closure reaches an
`@[implemented_by]`, `@[extern]` or `unsafe` constant
(`compiledEffectConstant`), since a term with the type of data can still run
effects in the compiled image.

Plan: [`docs/planning/SMP_BOOT_PATH_PLAN.md`](../../docs/planning/SMP_BOOT_PATH_PLAN.md).

### Standing constraints and registered debt

These are *current facts about the tree*, not history — they change what new
code may assume:

- **Kernel entry is serialised by one global ticket lock** (SM5.I, v0.32.142,
  `rust/sele4n-hal/src/kernel_entry.rs`), acquired outside
  `SHOOTDOWN_ROUND_LOCK` and self-servicing pending shootdowns while spinning.
  It brackets all five state-committing entries (syscall dispatch, per-core
  timer tick, `.reschedule` SGI receiver, secondary bring-up entry, cross-core
  suspend); the primary's `lean_kernel_main` boot install remains outside, and
  needs no bracket because it runs before any secondary is released — a
  bring-up consumes the `SecondaryReleasePermit` only the install returns
  (WS-BP BP4.2; see kernel_entry.rs module docs).
  The lock-order tripwire asks **ownership**, not held-ness (PR #889 review):
  the round lock records its holder (`round_lock_held_by`, owner word
  `core + 1`, `0` free), so a core entering while *another* core's shootdown
  holds the round lock waits and self-services its acknowledgment, and only
  the holder itself re-entering halts — a held/free flag halted every innocent
  core for the length of every shootdown, in release builds.  The two
  release-surviving tripwires — this one and the VBAR alignment check — are
  pinned in `build.rs` together with the operation each protects
  (`RELEASE_SURVIVING_TRIPWIRES`), and the scanner requires the tripwire
  among the statements **dominating** every occurrence of that operation
  (`tripwire_dominates_protected_operation`, PR #889 review round 6): a
  branch that halts but is no longer reached before the acquire or the VBAR
  write is refused, and (round 7) the branch must end in `fatal_halt` itself
  (`statement_halts`) — a `return` diverges from the helper, not the core.
  The branch must be a top-level statement of the helper, or sit under a
  block that executes unconditionally on the image — a bare or `unsafe`
  block, or one under exactly `#[cfg(target_arch = "aarch64")]` (round 8,
  `tripwire_branch_halts` / `unconditional_block_interior`): an
  exact-condition `if` nested under a further condition halted only when
  that condition held, and the dominance check, which asks whether the
  *helper* is called, could not see it.  Nothing may **leave** the helper
  before that branch either (round 9, `statement_may_exit`): an
  `if <the same condition> { return; }` above it returns exactly when the
  failure condition holds, so an earlier statement carrying a `return` or a
  panicking macro refuses the tripwire.
  Live WCRT is therefore weaker
  than `PerCoreWcrt.lean`'s fine-lock bound, which remains a statement about the
  intended discipline.  **And that bound carries no number** (WS-RR RR7.31): it is
  `maxLockSetSize · (numCores − 1) · tCs`, and `tCs` — a per-object critical
  section on a Cortex-A76 — is measured nowhere in this tree, so the whole surface
  is parametric in it.  The master plan's §7.2 used to instantiate it as
  `4 × 3 × 60 µs ≈ 720 µs`, "comfortably within the 1 ms timer tick"; the first
  factor was a *typical* footprint size rather than `maxLockSetSize` (11 since
  WS-OD OD3.5, 9 since RR7.11, and 8 before that), and at 60 µs the tick admits
  **five** locks and
  refuses six.  What the tree states instead is the budget condition solved for the
  measurable factor: `admissibleCriticalSection budget` is the largest per-lock cost
  a budget admits at the declared ceiling, with
  `WCRT_lockSet_le_budget_of_admissible` the payoff and
  `rpi5Tick_refuses_sixty_micro_sections` the `decide`-checked negative.  At
  HEAD, the declared lock-set ceiling is **24**, the RPi5 tick admits **13 µs** per lock, and the uniform 60 µs envelope is **4320 µs**.
  Those three figures are **derived** from the constants and the formula in
  `LockSet.lean`, `Types.lean` and `PerCoreWcrt.lean`; no gate checks prose copies
  of them, so quote the theorem (`admissibleCriticalSection_rpi5Tick`) rather than
  restating a figure, and update any live copy in the cut that raises the
  ceiling.  Narrative may name an old value freely
  (`OD3.5 raised the ceiling to 11`).  New code
  must not quote a numeric syscall WCRT for this kernel; measuring `tCs` on the
  target is an acceptance criterion of RR7.39–RR7.41 and fine-lock Track D.
- **The syscall seam brackets; the scheduler entries do not** (WS-RR RR7.12,
  v0.34.65).  `syscallDispatchCrossCoreEntry` runs its atomic step inside the
  footprint `lockSetForSyscall` declares for the operation its own registers
  decode to — resolve, acquire, **re-resolve at the state the growing phase
  ended in**, refuse on change, unwind — via
  `syscallDispatchCrossCoreBracketedStep`
  (`SeLe4n/Kernel/SyscallLockBracket.lean` holds the mechanism).  Four things
  new code must respect.  (1) **The fallback is exactly the pre-RR7.12 seam**
  (`syscallDispatchCrossCoreBracketedStep_undeclared`, definitional), which is
  what makes bracketing safe while twenty-seven arms are still undeclared:
  falling back is always sound, claiming a footprint that does not cover a write
  never is.  (2) **The operands come from the entry's own decode**, tied by
  `abiEntryPlan_dispatches` — a footprint resolved from a decode the dispatch
  does not use is a footprint for a different operation.  (3) **A multi-level
  CSpace resolution declares nothing**: the footprint's only CNode member is the
  caller's root, a `LockSet` is capped at `maxLockSetSize` and a CSpace path is
  not, so a deeper walk selects the target through CNodes no declared lock
  covers and the resolver refuses.  (4) **A refusal returns `.illegalState` and
  commits nothing but the unwinding**
  (`syscallDispatchCrossCoreBracketedStep_refused`); it is unreachable today,
  since `modifyGetKernelState` is one global read-modify-write and the growing
  phase writes nothing the resolver reads, and a dedicated `.lockContention`
  becomes worth its ABI cost when the commit is partitioned.  The per-core scheduler path
  brackets too since **WS-RR RR7.39** (v0.34.89), which gave `SchedLockId` the
  state words it never had (`SystemState.schedulerLocks`) and made the
  revalidating bracket shared — `Concurrency.runBracketed`, of which RR7.12's
  `runUnderDeclaredLockSet` is now definitionally the object-domain instance.  So
  the timer tick, the `.reschedule` SGI receiver and the secondary bring-up entry
  run inside the footprints SM5.B–G declared for them, with the write set proved
  inside the footprint on both steps (`perCoreRescheduleStep_coversWrites`,
  `perCoreTimerTickStep_coversWrites`).  Two things new code must respect.  (1)
  **The tick's footprint names every core's run-queue write lock**, not the boot
  core's and its own: the replenish drain and the bound-exhausted timeout both
  wake via `determineTargetCore`, so the two-lock segment was a *false* footprint
  from SM5.F onward, and RR7.39 fixed it — the widening is free, because every
  tick footprint already holds the object-store *table* lock
  (`timerTickOnCoreCompleteLockSet_serialises_pairwise`), and `maxLockSetSize`
  does not move.  (2) **The scheduler domain is not fully covered**: what remains
  is the *syscall* seam's scheduler writes — an `endpointSend`'s receiver wake —
  because `lockSetForSyscall` returns a `LockSet` whose `LockId` cannot name a
  run-queue lock at all.  That was `UncoveredLockDomain.syscallSeamSchedulerDomain`,
  owner RR8, and it needed per-arm resolved wake targets rather than the free
  over-approximation.  **Closed at WS-RR RR8.12 Cut C6h (`v0.35.181`)**: the seam
  brackets on `schedulerLockBracketDomain` over one unified footprint, and its own
  stated reason — that the object-domain footprints hold `stateLevelLock` *"rather
  than the table lock"* — was **false**, the two being one word
  (`schedAcquireLock_objStore_congr`), which is why the cut unifies rather than
  nests.  Live WCRT is still the global lock's for the arms neither domain
  declares, and `PerCoreWcrt.lean` says which half acquires.
  **How much of the kernel that is, is measured rather than asserted** (RR7.13,
  v0.34.66): `SeLe4n/Testing/ExportCommitDisciplineCensus.lean` derives the
  state-committing `@[export]` set from the elaborated environment — transitive
  `getUsedConstants` reachability to a `kernelStateRef` write — and reconciles it
  against a registry in **both** directions, so an unclassified committing seam
  and a stale entry are each a build failure.  **Seven seams commit; five
  bracket** (WS-RR RR7.39 — the two syscall seams and, since it gave the
  scheduler domain a runtime, the three per-core scheduler entries; two before
  it).  A body recorded `bracketed` must reach `runUnderDeclaredLockSet` or
  `Concurrency.withLockSet`; one recorded `unbracketed` must carry a reason.  New
  code adding an `@[export]` that commits kernel state must classify it there —
  that is where the project's coverage figure is read off, and the two
  fault-delivery seams (`lean_handle_fault`, `lean_handle_unknown_syscall`) are
  recorded unbracketed because a fault is not a syscall and `lockSetForSyscall`
  declares no footprint for one.
- **SM3.C.9's `@[export]` body migration is otherwise deferred**: outside the
  syscall seam and the raw `suspend_thread_cross_core` entry, the bodies are not
  wrapped in `withLockSet`, so the per-object fine locks remain a model-level
  discipline there.  **Eight of the
  thirty-five arms are declared** since WS-RR RR7.11 (v0.34.64) — that suspend
  plus the seven IPC hot-path arms `.send`, `.receive`, `.call`, `.reply`,
  `.replyRecv`, `.notificationSignal` and `.notificationWait` — and twenty-seven
  answer `none`, which `declaredFootprintSyscall` names and
  `lockSetForSyscall_undeclared_none` enforces.  Declaring is not bracketing, and RR7.12
  (v0.34.65) closed the gap at the syscall seam: the eight declared arms now run
  inside their footprints there, the twenty-seven undeclared ones run exactly as
  before, and the per-core scheduler entries still bracket nothing.  Three things new code must respect.  (1) `.send` and `.call` answer
  `none` without a **message**: whether the footprint includes the receiver's
  CSpace root and the state-level lock is a property of what the message carries,
  so defaulting to the capless shape would declare a footprint that omits the two
  members the caps path writes.  (2) The **receive** side writes the CDT too —
  `ipcTransferSingleCap` is one function, so a receive that dequeues a
  caps-bearing sender mints a derivation node and adds an edge exactly as a send
  does; RR7.7 declared that on the two sending arms and RR7.11 on the two
  receiving ones, and `capsCarryingIpcArms_footprints_share_serialization` is the
  statement that no two of the four are ever disjoint.  (3) **`maxLockSetSize` is
  21** (PR #894's review; 16 at `v0.35.4`, 14 at OD3.13, 13 at OD3.7, 11 at OD3.5,
  9 at RR7.11, 8 before that): the widest declared
  footprint is a `.replyRecv` that returns a donation, re-donates, installs
  capabilities, was answered through a *delegated* reply capability, reads the
  two objects below its reply-stack head, names the head its pop clears and the
  old head its push rewrites, and declares the five objects the **invoking**
  receiver's own pre-receive return touches.  The WCRT headline
  `maxLockSetSize · (numCores − 1) · tCs` is
  parametric in it — `admissibleCriticalSection` reads **15 µs** off it for the
  1 ms tick, down from 20 — and a theorem named `_size_le_maxLockSetSize` must
  state the
  constant, never the numeral — five in the scheduler pinned `≤ 8` literally,
  which is why the constant now lives in `Locks/LockSet.lean` where every
  footprint-declaring module can name it.  (4) **`.replyRecv` declares for the
  recorded server too, and for the second hand-off** (WS-OD OD3.5).  PR #892
  review round 6 made the arm *refuse* a delegated reply — one answered by a
  thread other than the one the Reply records — because
  `replyRecvReturnDonation` writes that server's TCB and there was no room for
  its lock.  OD3.5 found that the same function performs a **second**
  SchedContext hand-off the footprint named nowhere:
  `applyCallDonationOnCore nextThread tid` runs whenever the receive leg dequeues
  a queued `Call`, and `donateSchedContext` writes the new caller's context —
  provably not the returned one, and the passive-server steady state rather than
  an edge case, since the receiver is `.unbound` at that point *because* the
  return just made it so.  So the arm was writing a kernel object under no
  declared lock on the tree's most-travelled IPC path, and a `.replyRecv` on one
  core and a `.tcbSuspend` of that queued caller on another had provably
  disjoint footprints while both writing it.  Both members are declared now
  (`receiveRendezvousDonatedSc?`, `recordedReplyServer?`, both threaded through
  `lockSet_endpointReplyRecvOnCore`), the delegated case declares
  (`lockSetForSyscall_replyRecv_delegated_declares`) rather than falling back to
  the coarse serialisation, and `lockSetForSyscall_replyRecv_delegated` — which
  concluded `none` — is retired.  New code must not read that refusal as live.
  The
  migration plus commit partitioning is planned in
  [`docs/planning/SMP_FINE_LOCK_MIGRATION_PLAN.md`](../../docs/planning/SMP_FINE_LOCK_MIGRATION_PLAN.md),
  whose High-severity revocation-precision finding is **closed** at v0.33.88
  (§3.1).  It took five cuts because the first three patched the operation that
  destroyed the slot — synthetic source (v0.33.59→60), delete guard
  (v0.33.62), CNode retype and the revoke sweep (v0.33.64) — and the set of
  slot-destroying operations is open-ended.  The guarantee sits in two halves,
  neither implying the other: the single creator of an `.ipcTransfer` edge
  declines (`CapTransferResult.sourceRevoked`) when the **source** node has no
  live slot, which holds against destroyers not yet written; and revocation
  consumes the derivations still parked in senders' `pendingMessage`
  (`revokePendingTransfersFrom`, v0.33.88), because revoking a derived subtree
  leaves the source slot live and so never trips the creator's check.  New code
  must not assume a carried `TransferCap` will install.
- **A footprint's same-kind core segment is `schedCoreSegment`, over a core
  *set*** (WS-RR RR8.12, `v0.35.87`).  A cross-domain footprint that names
  several cores' run queues or replenish queues declares them through
  `schedCoreSegment (f : CoreId → SchedLockId) (cs : List CoreId)`
  (`Scheduler/Operations/PerCoreChooseThread.lean`), whose canonical form is
  `Concurrency.canonicalCores` — `allCores.filter (· ∈ cs)`, so ascending,
  duplicate-free and bounded by `numCores` because `allCores` is.  Three things
  new code must respect.  (1) **The arity is an argument, not a definition.**
  `sortedSchedCorePair` and `sortedSchedCoreTriple` were this question at two
  arities and are **deleted**, with a Tier 3 negative refusing each tree-wide;
  a footprint needing four cores passes a four-element list, and a footprint
  resolved from a *walk* passes whatever the walk found
  (`pipChainSchedFootprint` does).  (2) **A hand-inlined `if`-chain over two
  cores is the same defect**: `cancelDonatedDonationOnCoreSchedLockSet` carried
  one for eleven cuts, forty lines below a comment asserting the shared
  definition was used everywhere below it, and its uniqueness and ordering
  proofs were 30 and 35 lines of branch analysis for a fact the shared lemmas
  state once.  (3) **`allCores`'s ordering is `allCores_pairwise_le`, never a
  `decide`**: a `decide` at the literal `numCores` stops reducing the moment a
  multi-platform build parameterises it by `PlatformBinding.coreCount`, which is
  what `allCores_nodup`'s own docstring says and what one chain-footprint proof
  had done anyway.

- **...and a whole operation's footprint is `schedFootprintOfCores`, over two
  core sets** (WS-RR RR8.12 sixth cut, `v0.35.94`).  The segment above is one
  kind; a footprint of a whole kernel operation is the three-domain ladder
  `(object, .write) :: runSegment ++ replenishSegment`, and that was spelled at
  **seven** definitions with **four** byte-identical twenty-five-line
  `_pairwise_le` proofs — one question with four answers, about to become nine
  as the remaining syscall arms are declared.  `schedFootprintOfCores (runCores
  replenishCores : List CoreId)` is the one answer, with `_pairwise_le`,
  `_write_only`, `_keys_nodup`, `_length_le`, `_subset` and the single
  characterisation `mem_schedFootprintOfCores_iff` its consumers read instead of
  each running the same three-way case analysis.  Four things new code must
  respect.  (1) **The criterion is the *shape of the argument*, not a list of
  names**: a footprint whose cores form a set — two or more of a kind, an
  `Option` joined with another, a segment resolved from a walk — is this
  constructor; one at a fixed single core of each kind
  (`wakeThreadLockSet`, `descheduleThreadLockSet`,
  `cancelBoundDonationOnCoreSchedLockSet`) is a literal, because there is
  nothing to sort and nothing to merge and its ladder is a two-element `simp`.
  A literal that gains a second core of a kind becomes this constructor in the
  same cut.  (2) **"The argument is a set" is a theorem, not a claim**:
  `Concurrency.canonicalCores_congr` and `schedFootprintOfCores_congr` say two
  resolvers that discover the same cores declare the same footprint, and
  `canonicalCores_singleton` is the `Option CoreId` arm.  That is what retired
  `cancelIpcBlockingOnCoreSchedLockSet`'s hand-written deduplication — `if
  placed = some c then … else … ++ [(runQueue ⟨c⟩, .write)]`, a question about a
  set answered by an `if`-chain over its two possible elements, which is item
  (2) above one level up and which RR8.12's first cut did not sweep onto its own
  sibling.  With the branch gone,
  `cancelIpcBlockingOnCoreSchedLockSet_contains_wake_runQueue_write`
  (`…_contains_holder_runQueue_write` since `v0.35.158`) is
  **unconditional**, where it used to need `placed ≠ some c`.  (3) **A composite
  covers a component by `schedFootprintOfCores_subset`**, not by a second
  member-by-member case analysis; over-declaring is the safe direction and the
  lemma is stated that way round.  (4) **`Scheduler/PriorityInheritance/
  ChainFootprint.lean` is deliberately not this shape**: its object segment is a
  *per-thread* TCB lock per chain member rather than the single table lock, so
  its ladder is a different proposition and it keeps its own — which is why the
  Tier 3 negative that refuses a re-inlined `runQueue_lt_replenishQueue` is
  scoped to `SeLe4n/Kernel/IPC/` and `SeLe4n/Kernel/Lifecycle/` rather than
  tree-wide.

- **...and the first three syscall arms declare one** (WS-RR RR8.12 seventh cut,
  `v0.35.95`).  `UncoveredLockDomain.syscallSeamSchedulerDomain` recorded that
  `lockSetForSyscall` returns a `LockSet` whose `LockId` cannot name a run-queue
  lock at all, so an `endpointSend`'s receiver wake was outside the footprint the
  RR7.12 seam acquired (that entry is retired at Cut C6h, `v0.35.181`).  `.notificationSignal` (through the **bound** arm the
  live dispatch routes to), `.notificationWait` and `.send` now have one —
  `schedLockSet_notificationSignalBoundOnCore`,
  `schedLockSet_notificationSignalOnCore`,
  `schedLockSet_notificationWaitOnCore`, `schedLockSet_endpointSendOnCore`, all
  **inert** until the bracket cut.  Four things new code must respect.  (1) **A
  footprint is `schedFootprintOfCores` of the arm's SM8.B write set**, never of a
  second resolution of the same cores: `notificationSignalOnCore_confinedToCores`
  is *stated at* `notificationSignalWriteSet` and the footprint is that list, so a
  footprint and a confinement claim naming different cores is unstateable rather
  than merely refuted.  (2) **The write sets moved to production for that
  reason.**  `notificationSignalWriteSet`, `notificationSignalBoundWriteSet` and
  `endpointSendWriteSet` were declared in
  `InformationFlow/NonInterferenceCrossCore.lean`, which is staged and imports
  `Kernel.API`, so the production footprint could not read them; they now sit
  beside the transitions they describe and the confinement theorems that consume
  them stay staged.  `wakeThread_replenishQueueOnCore` moved the same way, out of
  the staged `PerCoreCbs.lean` where its `_local` suffix was the signal.  (3) **An
  empty replenish segment is a theorem, not a reading of the body**: these three
  arms move no scheduling context — only `.call`, `.receive` and `.replyRecv`
  donate — and `notificationSignalOnCore_replenishQueueOnCore`,
  `notificationWaitOnCore_replenishQueueOnCore`,
  `notificationSignalBoundOnCore_replenishQueueOnCore` and
  `endpointSendCrossCoreDispatchChecked_replenishQueueOnCore` say so, because a
  footprint that omits a written lock is false and `observableSlotsConfinedToCores`
  covers six per-core slots of which the replenish queue is **not** one.  (4)
  **`.receive` and `.replyRecv` are deliberately still undeclared at this cut**:
  both donate, so their replenish segments are non-empty and their cores come from
  the migration rather than from a confinement write set, and `.receive`'s chain
  leg is not pre-state computable at all (`receiveRendezvousHandoffWriteSet` takes
  the post-donation state) — those cores are declared through the dynamic chain
  extension, as the object domain declares them.  `.receive` is declared at Cut
  8a-ii (`v0.35.107`, the bullet below), `.replyRecv` at Cut C2 (`v0.35.162`, the bullet after that), `.call` and `.reply` at Cut C3a (`v0.35.163`, the bullet after those), and the three TCB-control arms at Cut C3b-i (`v0.35.167`, the bullet after that).  **And that sentence named two arms where the
  derivation gives many more** (`v0.35.104`, found by running the sweep on this
  note rather than by a review): four arms declare a scheduler footprint and the
  staged non-interference module holds **24** per-core write sets, so `.call`,
  `.tcbSuspend`, `.tcbResume`, the three SchedContext arms, `.tcbSetPriority`,
  `.tcbSetAffinity` and the retype are undeclared too and were in neither list.
  *A recognised set is not a derived set*, in the note written one cut earlier to
  record which arms remain — read the `schedLockSet_` inventory and
  `schedLockSetForSyscall`'s own `match`, never this paragraph, for what is left.
  (`UncoveredLockDomain.syscallSeamSchedulerDomain` was the register entry until
  Cut C6h retired it; the inventory is the derivation that outlives it.)

- **...and the first DONATING arm declares one, so the first with a non-empty
  replenish segment** (WS-RR RR8.12 Cut 8a-ii, `v0.35.107`).
  `schedLockSet_endpointReceiveOnCore` is the live `.receive` arm's
  scheduler-domain footprint — the object-store table write lock, the run-queue
  write lock of the one core the receive leg moves, and the replenish-queue write
  locks of the two endpoints WS-OD OD3.6's donation migrates between — **inert**
  until the bracket cut.  Seven things new code must respect.  (1) **Every core is
  DERIVED; nothing is a parameter — and the first shape of this cut got that
  wrong.**  The run segment is `schedFootprintOfCores` of the arm's SM8.B write
  set, as Cut 7 requires.  The replenish segment has no write set to take —
  `observableSlotsConfinedToCores` does not read the replenish queue at all — and
  the first shape therefore took the donation's two cores as **parameters**, on the
  reasoning that `applyRendezvousCallDonation` resolves them at the *post*-receive-leg
  state, so a pre-state reading would answer the question at a state the migration
  does not run at.  Three things were wrong with that.  It breaks this file's own
  rule that **a parameter is a place for a caller to be wrong** (PR #895 round 10:
  the fix is not a better argument but *no* argument), since a caller could declare
  locks for a migration between two cores the transition never touches.  A bracket
  resolves a footprint **before** the transition runs, so Cut 9 could not have
  supplied them at all and the form would have had to be rewritten anyway.  And it
  left three frames Cut 8a had promoted *for this footprint* with no consumer, which
  is the measurement that said so: a frame nobody asks for is a question nobody
  asked.  The replenish segment is `endpointReceiveHandoffReplenishCores`, read on
  the **pre**-state, licensed by
  `endpointReceiveDualWithCapsOnCore_determineTargetCore_eq_of_rendezvous` — *the
  receive leg moves no thread's home core*, because `determineTargetCore` reads
  `cpuAffinity` and only `.tcbSetAffinity` writes it — and
  `endpointReceiveHandoffReplenishCores_of_donating_call_rendezvous` (the
  `_of_call_rendezvous` of this cut, re-keyed at Cut C1) states that the pre-state
  list **equals** the pair the donation resolves, not that it agrees with or
  over-approximates it.  So this *closes*, for `.receive`, the
  footprint/transition resolution asymmetry WS-HP HP10.8 registered for the reply
  arm's origin member rather than adding a second instance of it.  A Tier 3 positive
  pins both segments in one anchor, a second pins the equality, and a negative
  refuses the parameter names coming back; each is mutation-tested by keeping every
  other token.  (2) **The declaration is TRUE by theorem, not by reading the body**:
  `schedLockSet_endpointReceiveOnCore_covers_donation` covers
  `applyCallDonationOnCoreSchedLockSet` member for member, hence — through
  `applyCallDonationOnCoreSchedLockSet_covers_migration` — the SM5.H migration's
  two slots; and in the other direction
  `endpointReceiveDualOnCore_replenishQueueOnCore_of_rendezvous` and its WithCaps
  sibling say the receive **leg** writes no replenish queue on a rendezvous, so
  every core in that segment comes from the donation and none from the leg.  On
  the block path the segment is `[]` for a receiver holding no loan
  (`schedLockSet_endpointReceiveOnCore_no_replenishQueue_of_blocked`, conditioned
  on `endpointReplyDonation?` answering `none` since `v0.35.161`): a receive that
  parks itself donates nothing, and over-declaring is not free — lock contention
  is an observable channel (SM8.D's CC-5), which is why OD3.5 *narrowed* a
  footprint for the same reason.  A receiver that parks holding a **loan** is the
  other case, and until `v0.35.161` it was wrong on both sides: the block arm's
  pre-receive return rebound the context to its owner across cores and migrated
  nothing, and the whole-leg frame that pinned *the leg writes no replenish queue
  on either path* was true only because the transition omitted the write.  The arm
  runs `cleanupPreReceiveDonationMigrated` now, the segment names the receiver's
  home and the owner's through `receivePreReturn?`
  (`endpointReceiveHandoffReplenishCores_of_blocked_returning`, with
  `…_eq_migration` the licence that the pre-state pair **is** the migration's),
  and the whole-leg frame is retired for per-path ones — see the standing
  constraint on the pre-receive return below.  (3) **The chain walk is declared
  dynamically, not statically.**  The arm also runs `applyReceiverPipHandoff`,
  whose cores are state-discovered; `PriorityInheritance.pipChainSchedFootprint`
  declares them per walked member and `pipChainStart_endpointReceive` is the SM3.C
  obligation that ties the walk to it.  A static footprint that tried to
  enumerate them would be a footprint over an unbounded set.  (4) **Two more
  production relocations, for the reason `v0.35.59` states.**
  `endpointReceiveDualWriteSet` and
  `endpointReceiveDualWithCapsOnCore_scheduler_eq` were declared in the staged
  `InformationFlow/NonInterferenceCrossCore.lean`, which imports `Kernel.API`, so
  the production footprint and its replenish frame could not read them; a frame
  lemma about a production transition belongs beside that transition, not in the
  staged surface that first happened to need it.  Both are refused there by a
  Tier 3 negative.  Two more of the same class surfaced from the **build** rather
  than from reading, and both are the shape `v0.35.59` names — *when a question has
  one owner and an asker that cannot see it, the owner is in the wrong layer*:
  `storeTcbIpcStateAndMessage_determineTargetCore_eq` is a frame over an IPC
  *primitive* and sat in a cross-core *arm* module the receive leg's own frame does
  not import, while `endpointReceiveDualOnCore_preserves_objects_invExt` is a frame
  over a transition and sat **downstream** of the module that declares it.  Four
  relocations in one cut is the signal that the class is a layering convention, not
  four accidents.  (5) **The frames the licence needed, and where they live.**  The
  `*_determineTargetCore_eq` family gained `linkCallerReply_…` (a Reply store then
  a TCB store, `cpuAffinity`-`rfl` on both) and `ipcUnwrapCaps_…` (whose own TCB
  frame holds at every key in *both* directions, so the whole `getTcb?` projection
  is fixed — strictly stronger than the affinity the licence needs, which is why no
  per-field argument appears in it).  Both sit in the family's home module, not
  beside their operations, because that is where every other member lives.  The
  composite is stated on the **rendezvous** branch, and that is the claim's own
  subject rather than an economy: the segment is `[]` on the block path, so there is
  no core there for a pre-state reading to get wrong.  (6) **The one missing frame is a corollary, not a second case
  analysis**: `cleanupPreReceiveDonationChecked_scheduler_eq` goes through
  `cleanupPreReceiveDonationChecked_ok_eq_cleanup`, the bridge that already
  settles that the checked and defensive variants agree on `.ok` — re-deriving it
  from the checked body would let the two disagree about a branch.  And the
  layering worry that deferred this cut was unfounded: `IPC.Invariant.Defs` *is*
  reachable from `IPC/CrossCore/EndpointReply.lean`, through
  `Scheduler.Operations.PerCoreWake → IPC.Invariant.PerCore`; the grep that
  suggested otherwise measured which cross-core module happens to cite those
  frames, not which can.  (7) **The scheduler-footprint family has no census, and
  the measurement is what says so.**  A footprint's `_write_only` / `_pairwise_le`
  are `schedFootprintOfCores`' own lemmas at that footprint's arguments, so
  restating them per footprint is a delegation with no content — Cut 7's four arms
  omit them and this one does too, with the reason stated where a reader looks for
  them.  What is **not** a delegation is a run-segment coverage lemma, and asking
  the whole family who consumes those found **33 of its 47 theorems with neither a
  consumer nor a Tier 3 anchor** — every RR2.4 / RR2.10 / RR8.12 footprint property,
  silently deletable.  Their consumer is the bracket cut, which is the ordering the
  numbering rule requires, so the answer is not to delete them; it is that the
  scheduler domain has no `LockFootprintBoundCensus`, which the object domain has
  had since RR7.18 for exactly this reason.  Deriving one is Cut 8c; the eight hand
  anchors this cut adds are the stopgap, and a hand-written list is what that census
  retires.

- **`ipcInvariantFull` has its dispatch payoff, under stated packs and
  confinements** (WS-RR RR3.15–RR3.26, `v0.34.43`; compressed here at RR8.14,
  `v0.35.88`).  The bundle family is de-threaded end to end and
  `scripts/check_ipc_invariant_dethreading.py` (Tier 0) keeps it so; the family
  size quoted in prose is not gated (run the script's `--report` to measure it),
  and the figure and the narrative of how it drifted live in
  `docs/spec/SELE4N_SPEC.md` and `CHANGELOG.md`, not here.  Four things new code must respect.  (1) **Cite the
  right tier.**  `dispatchCapabilityOnly_preserves_ipcInvariantFull`
  (`SeLe4n/Kernel/API.lean`) is **production** and covers every capability-gated
  arm; `dispatchWithCap_preserves_ipcInvariantFull`,
  `dispatchSyscall_preserves_ipcInvariantFull` and their two `…Checked` twins
  (`SeLe4n/Kernel/IPC/Invariant/DispatchPayoff.lean`) are **staged**, because the
  `.call` arm composes the staged `EndpointCallInvariant` surface, and production
  code must not cite them; they relocate when that surface promotes.  (2) **The
  payoff holds *under the packs***: every field of
  `capabilityDispatchQuiescence` / `syscallDispatchQuiescence` /
  `checkedSyscallDispatchQuiescence` is a pre-state fact, with the state-shaped
  ones collected as `ipcReachable`
  (`SeLe4n/Kernel/IPC/Invariant/Reachability.lean`, boot-inhabited by
  `ipcReachable_default`), so a caller supplies the pack rather than citing the
  theorem bare.  (3) **The packs are inhabited, per arm** — an unsatisfiable
  field cannot hide behind a vacuous witness (`DispatchPayoff` §7b); the two
  interiors beyond the retype and binding levers' reach are registered debt.
  (4) **The confinements are stated, not implied**: `.notificationSignal` is
  covered on the unbound-delivery path only, the `.replyRecv` composite excludes
  a live donation edge naming the woken caller, and the retype and suspend arms
  demand `retypeTargetDetached` / `threadIpcFieldsQuiescent` — revoke, suspend,
  cancel and (`tcbNotBound`, since `v0.35.164`) unbind *before* retype or
  suspend; the arm the retype's cleanup runs is what makes a violation of the
  last one safe rather than what the pack rules out.
- **A cancelled caller gets its donated SchedContext back** (WS-RR RR7.22
  residual remediation, v0.34.97).  `cancelIpcBlocking`'s `.blockedOnReply` arm
  is `consumeReplyLink (restoreToReadyCancelled (spliceThreadReplyFrameOut
  (returnDonationToCancelledCaller st tid tcb) tcb) tid) tid tcb` — seL4-MCS's
  `reply_remove` (the splice joined the chain at `v0.35.4`; this sentence
  omitted it for fifty-nine cuts).  Before it, the server
  kept `.donated scId caller` while the caller left `.blockedOnReply`, which
  `donationOwnerValid` forbids and which permanently transferred the caller's CBS
  reservation.  Four things new code must respect.  (1) **The return runs before
  the restore**, because it reads the `.blockedOnReply` state the restore clears;
  a Tier 3 negative refuses the old order.  (2) **The holder is the thread the
  caller's own reply frame's head context is bound to** (`cancelledCallerDonation?`;
  it was the caller's *recorded reply target* until WS-HP HP5.1 re-keyed the
  resolver), and that no invariant entails — `donationOwnerValid` relates a donation
  to no reply object and `donationChainWellFormed` carries no binding clause — so
  `donatedContextIsOwnerFrameHead` states it, having replaced
  `donationHolderIsReplyTarget` at HP5.3; the *behaviour* needs no hypothesis, only
  the payoff `cancelIpcBlocking_reply_no_donation_to_victim` does.  (3) **The SM5.H
  replenishment migration is at the cross-core layer** (`cancelIpcBlockingMigrated`),
  where this tree resolves home cores for every donation-carrying path, which is
  what keeps `cancelIpcBlocking` an objects-only write; that it *establishes*
  `replenishQueueAffinityConsistent_smp` is proved at WS-RR RR8.11 (`v0.35.86`,
  `cancelIpcBlockingMigrated_establishes_replenishQueueAffinityConsistent_smp` and its
  cross-core lift), which also moved the migration's **destination** onto the bound
  thread's post-teardown home — see the hand-off constraint below for why the
  victim's pre-state home was wrong.  (4) **The return
  is invisible to every observer, not merely a high one**: `projectKernelObject`
  strips `schedContextBinding` and `boundThread`, so writing a possibly-low
  server's TCB on a high caller's cancellation leaks nothing
  (`returnDonationToCancelledCaller_preserves_projection`).  `cancelIpcBlocking_lifecycle_eq`
  was made conditional on there being no donation, because `storeObject` maintains
  bookkeeping the arm's other writes bypassed — and it is **deleted** at WS-RR
  RR8.5 (`v0.35.63`), when the teardown started writing through `storeObject`
  too: the definitional lifecycle frame would then need `tcb.replyObject = none`,
  which no reachable `.blockedOnReply` state satisfies, and nothing consumed it.
- **...and the reclaim ends the holder's outstanding send or call first**
  (WS-OD OD1.4, v0.34.104).  The hand-back is
  `returnDonatedSchedContext (abortHolderPendingIpc st holder) holder scId tid`.
  Without the prefix the reclaim leaves the holder `.unbound` while it is still
  `.blockedOnCall` — reachable at depth 1 with no chain, when the server Calls an
  endpoint with no receiver waiting — which `passiveServerIdle` forbids.
  Semantically it is what a timeout is in MCS: the budget the operation was
  issued on has been revoked, so the operation fails with `.ipcTimeout`.  Five
  things new code must respect.  (1) **The abort runs before the hand-back**, for
  the reason the hand-back runs before the restore, one level down: with the
  return first the intermediate state *is* the violation being closed, and a
  Tier 3 negative refuses the swapped order.  (2) **The prefix is
  `abortPendingIpcOnEndpoint`, not `timeoutThread`** — the timeout's objects-only
  half, without the wake and the priority-inheritance revert — because
  `cancelIpcBlocking_scheduler_eq` has four cross-core consumers and must stay
  true.  (3) **The reclaim is all-or-nothing**: a refused return discards the
  abort, since `cancelledCallerDonation?` resolves through the *holder* and can
  answer `some` for a caller with no TCB; committing the abort there would end a
  live server's IPC for a reclaim that did not happen and would falsify
  `returnDonationToCancelledCaller_eq_self_of_getTcb?_none`.  A Tier 3 negative
  refuses the committing error arm.  (4) **Every fact the hand-back reads
  survives the abort**, which is why the donation is resolved once, on the
  pre-state: the abort writes no `schedContextBinding`
  (`abortHolderPendingIpc_binding_backward` / `_forward`) and no SchedContext
  (`abortPendingIpcOnEndpoint_schedContext_forward`), so
  `donationOwnerValid` carries across it — given the holder holds a binding,
  which it does, since owners are `.unbound` and the holder is `.donated`
  (`abortHolderPendingIpc_preserves_donationOwnerValid`).  (5) **The abort is
  projection-*visible* and the reply arm's NI result says so.**  It writes the
  holder's endpoint, its queue neighbours and its own `ipcState` / queue links —
  none of which `projectKernelObject` erases — so
  `returnDonationToCancelledCaller_preserves_projection` and
  `cancelIpcBlocking_blockedOnReply_preserves_projection` now carry
  `abortHolderProjectionStable`.  That is the endpoint-queue label-uniformity gap
  the three *queue* arms already carry, reaching the reply arm through the holder
  rather than the victim; it is discharged outright wherever the abort is inert
  (`abortHolderProjectionStable_of_allowed`, from
  `abortHolderPendingIpc_eq_self_of_allowed` — the abort is the identity unless
  the holder is blocked sending or calling), so no result that held before the
  remediation is weakened on the states it held for, and the general discharge is
  registered WS-OD debt.  New code must not read either projection theorem as
  unconditional.
- **...and the holder the reclaim UNBINDS is descheduled, not woken**
  (`v0.35.158`; WS-OD OD1.7's wake of it from v0.34.108 until then).
  `cancelIpcBlockingOnCore`'s state is `descheduleAtPlacement
  (cancelIpcBlockingReclaimed victim tcb st) victim`, and the reclaim-complete
  teardown is the migration followed by `descheduleUnboundHolder` — the holder
  the pop unbound, taken off the scheduler slot the post-teardown state places
  it on.  OD1.7 had placed that holder on its home core's run queue, on the
  reasoning that an unbound thread is fully schedulable in this model; it is,
  **at its legacy TCB band charged to no reservation**, refilled by
  `timerTickBudgetOnCore`'s `.unbound` arm forever — which PR #897's review
  measured on the live `suspendThreadOnCore`: a server that Called onward and
  blocked, plus an ordinary `.tcbSuspend` of its *client*, left the server
  runnable and unbudgeted, outside CBS admission entirely.  The premise the wake
  rested on read `.unbound` as *legacy time-sliced* where the passive-server
  pattern reads it as *MCS-passive*, and every other donation pop in the tree
  takes the second reading (`applyReplyDonation`, `applyReplyDonationOnCore`,
  `replyRecvHolderDeschedule`, and seL4-MCS's `schedContext_donate`, which
  dequeues the previous holder); the reclaim was the one deliberate outlier.
  Six things new code must respect.  (1) **The trigger reads the POP's two
  writes off the post-teardown state** (`cancelUnboundHolder?`): the holder's
  binding cleared and the victim's installed, which is exactly the pop having
  landed and distinguishes it from a refused, all-or-nothing reclaim.  It reads
  no `ipcState`, so it fires on a blocked holder and on a queued one alike —
  the wake's `.ready`-gated trigger was silent on exactly the queued server this
  cut is about.  (2) **`holder ≠ victim` is structural**
  (`cancelUnboundHolder?_ne_victim`): one thread cannot answer both conjuncts,
  so the composite's own deschedule of the victim is stated with no case on the
  holder (`cancelIpcBlockingReclaimed_placedCoreOf?_victim` is an equation where
  the wake left a disjunction over a degenerate self-insert no state reached).
  (3) **The step is `descheduleAtPlacement`**, the one removal every other pop
  performs: the identity on a holder placed nowhere — every holder the abort
  unblocked, and every holder blocked in receive — and a removal from the
  holder's own placement otherwise.  A scheduler-only write, so
  `cancelIpcBlockingOnCore_objects_eq` and the whole `CancellationNI` surface
  hold verbatim; no SGI is surfaced, because both `.tcbSuspend` entry paths
  derive their pokes from the committed pre/post diff, whose
  `currentSlotChangeSgis` rule reaches a holder taken off a remote current slot.
  (4) **What the holder is left with**: `.ready`, `.unbound`, on no slot, with
  the `.ipcTimeout` frame the abort staged (WS-RR RR7.14) still in its register
  context — delivered the first time it is dispatched, which is the first time
  it holds a reservation.  Its own manager recovers it: a `.tcbSuspend` then a
  `.tcbResume`, or a `schedContextBind` once that arm places a parked thread
  (seL4-MCS's `schedContext_bindTCB` ends in `SCHED_ENQUEUE`; this kernel's bind
  re-buckets only an already-queued thread — the divergence
  `docs/REGISTERED_DEBT.md` table C keeps, owner WS-CB).  What no ordinary
  client suspension can do any more is hand a server the CPU on nobody's
  budget.  (5) **The declared scheduler footprint names the holder's PLACED
  core**: `cancelIpcBlockingOnCoreSchedLockSet` takes a `holderPlaced : Option
  CoreId`, resolved by `cancelUnboundHolderCore?` through the same
  `placedCoreOf?` the step reads (the wake's member was the holder's *home*),
  and `…_covers_holder_deschedule` is the relation; a footprint naming only the
  victim's core would be *false* of the transition.  (6) **The per-core locality
  clause excludes that core on BOTH halves**: `cancellation_cross_core_correct`'s
  run-queue and current-slot halves are conditioned on
  `cancelUnboundHolderCore?`, where the wake's insert had needed the exclusion
  on the run-queue half alone.  The bundle frame the removal owes — an insert
  owed none — is discharged from the abort that runs first
  (`cancelIpcBlocking_unboundHolder_binding_or_allowed`, under the reply arm's
  own `owed` premise), and the information-flow obligation is
  `descheduledHolderHigh`, `abortHolderWakeHigh`'s successor with the same
  discharge (`descheduledHolderHigh_of_donationOwnerFlowsToHolder`): a removal
  is filtered by the removed thread's own observability exactly as an insert is.
- **...and the live `.tcbSuspend` performs that step — since `v0.35.90`, and not
  before** (WS-RR RR8.12, second cut; the step was OD1.7's wake until
  `v0.35.158`).  OD1.7's wake and WS-RR RR7.22/RR8.11's
  replenishment migration were both added to `cancelIpcBlockingOnCore`, a
  composite **no production path calls**: the live arm and the
  `suspend_thread_cross_core` seam run `Lifecycle.Suspend.suspendThreadOnCore`,
  whose G4 performs its own placement removal and whose G2 therefore reached for
  the *bare* teardown.  So on the only path a syscall takes, neither fix was
  present — measured on the live transition, an aborted donation holder ended
  `.ready` and `.unbound` on **no** run queue on any core (the strand OD1.7
  describes, reachable from an ordinary `.tcbSuspend` on a thread in one's own
  call chain), and the reclaimed reservation's replenishment stayed on the
  holder's home core while the `.bound` arm purged the victim's, leaving an entry
  naming a deactivated SchedContext.  Five things new code must respect.  (1)
  **The shared step is the composite's PREFIX, and it has a name**:
  `cancelIpcBlockingReclaimed` is the teardown with its migration and its holder
  deschedule, `cancelIpcBlockingOnCore` is that plus the victim's deschedule
  (`cancelIpcBlockingOnCore_eq_reclaimed_deschedule`, `rfl`), and G2 is the
  prefix — so every object-level, bundle and information-flow result about the
  composite's teardown half reaches the live path with no second statement.  (2)
  **A step added to the cancellation *teardown* goes in the prefix**; only a step
  about the victim's own placement belongs to the composite.  A composite whose
  prefix a second consumer needs is a shared answer that consumer cannot reach,
  which is how two cuts each believed they had closed this.  (3) **The state pair
  is `(st, cancelIpcBlockingMigrated … st)`** — `descheduleUnboundHolder` reads
  the pre-state to resolve the holder and the post-teardown state to check the
  pop landed and to place the removal, and handing it a state further down the
  pipeline is a different predicate.  (4) **Both declarations grew by the
  holder's core**: `suspendThreadOnCoreSchedLockSet` takes a `holderPlaced :
  Option CoreId` (the run-queue segment is the placed and executing cores *plus*
  it; it was the wake's home core until `v0.35.158`) and
  `suspendThreadOnCoreWriteSet`'s first entry is no longer `[]` — a write set that
  omits a written core is as false as a footprint that does, and both were silent
  because the pipeline performed no such step.  `maxLockSetSize` does not move:
  a `SchedLockSet` carries no cardinality bound.  (5) **The guarantee is proved of
  the whole pipeline, not only measured** (`v0.35.92`, RR8.12's fourth cut;
  inverted at `v0.35.158`): `suspendThreadOnCore_holder_unplaced` lifts the
  reclaim's payoff through the six stages after G2 — the chain reversion, the
  donation arm, the placement deschedule, the pending-state clear, the
  `.Inactive` store and the G7 scheduling point — and
  `tests/SmpCancellationSuite.lean` §3.26 exhibits its premises and its
  conclusion on a state the live operations reach, computing the retired wake
  beside the live deschedule on the blocked, the queued and the running holder,
  because a hypothesis nothing exhibits is indistinguishable from one that cannot
  hold.  (Until `v0.35.158` the theorem was `suspendThreadOnCore_holder_still_placed`,
  the opposite fact about the wake, retired with it.)  Three things new code must
  respect.  **`holder ≠ victim` is derived, not assumed**:
  `cancelUnboundHolder?_ne_victim` reads it off the trigger's own two conjuncts,
  which ask the holder's binding to be `.unbound` and the victim's not to be —
  it had been a sentence in the G4-precapture comment, and a sentence is not a
  licence.  **Single placement is a hypothesis, not a bundle**: one removal is a
  removal from every core only if the holder sat on at most one, which the
  scheduler maintains by construction, and the statement takes that fact so a
  caller holding only the scheduler invariant can discharge it.  And
  **well-formedness travels to the scheduling point where resolvability used
  to**: a scheduling point places a thread only by dispatching it, and the
  dispatched thread is one the chooser took out of the executing core's run
  queue (`chooseThreadEffectiveOnCore_some_mem_runQueueOnCore`, stated under that
  queue's well-formedness), so every stage carries `wellFormed` forward
  (`handleRescheduleSgiOnCore_preserves_unplaced`,
  `switchToThreadOnCore_preserves_unplaced`) and the holder's TCB is never
  consulted; the placed direction's resolvability chain
  (`propagatePipChainCrossCore_getTcb?_isSome` and its siblings) went with it.
  The chain walk's run-queue and `current` frames
  moved to `Scheduler/PriorityInheritance/Propagate.lean` for the reason the second
  cut named a prefix — `IPC/Invariant/FaultProgress.lean`, where they sat, imports
  `IPC.CrossCore.Fault`, which imports `Cancellation` — and its three
  `_not_mem_of_not_mem` forms were retired with them, the biconditional being the
  answer.  **And the single-core reference path reads it too, since `v0.35.93`**
  (RR8.12's fifth cut): `cancelIpcBlockingReclaimed` and the wake family (the
  holder-deschedule family since `v0.35.158`) were
  declared in `IPC/CrossCore/Cancellation.lean`, which *imports*
  `Lifecycle/Suspend.lean`, so `Lifecycle.Suspend.suspendThread`'s G2 could not see
  them and the same strand was reachable on it.  They are declared beside the
  teardown they complete now — *when a question has one owner and an asker that
  cannot see it, the owner is in the wrong layer* — keeping the `SeLe4n.Kernel`
  namespace they were declared in, so the move renames nothing.
- **...and its replenish segment follows the donation's own guard, not "is the send
  queue non-empty"** (PR #897 Codex review, `v0.35.112`).  Cut 8a-ii's own docstring
  rejected over-declaration in as many words — *a segment naming two cores would be
  a footprint wider than its operation, and lock contention is an observable channel
  (SM8.D's CC-5)* — and applied that to the **block** path only.  The segment keyed
  on `receiveRendezvousSender?` while WS-OD OD3.6's donation fires only on a dequeued
  **`Call`**, so **every ordinary `seL4_Send` rendezvous declared two
  replenish-queue write locks for a migration that provably does not happen**: the
  defect the paragraph above it rejects, on the more common path, which is this
  file's own *a fix applied at one site and not its siblings*.  Seven things new code
  must respect.

  (1) **The pre-state guard and the post-state guard are two spellings of one
  question and both must exist.**  `rendezvousSenderIsCall` is
  `rendezvousDequeuedCall`'s pre-state sibling, clause for clause, because a dequeued
  `Call` sender is `.blockedOnCall` *before* the receive leg and `.blockedOnReply`
  *after* it.  Asking for the post-state constructor at the pre-state answers `false`
  for exactly the sender that *will* donate, so a footprint derived from it would
  **omit** a lock the transition writes — and a footprint that omits a written lock
  is false, where one wider than its operation is merely expensive.  That asymmetry
  is the whole reason the narrowing is safe in one direction and not the other.

  (2) **It reads the leg's OWN branch condition.**
  `endpointReceiveDualOnCore` branches on the TCB `endpointQueuePopHead` *returns*,
  which no consumer could name until
  `endpointQueuePopHead_popped_tcb_eq_lookup` — the twin of WS-RR RR2.6's
  `endpointQueuePopHead_popped_eq_head` — said that record **is**
  `lookupTcb st head`.  Without it a pre-state resolver is a *second* reading of the
  same question, which is the shape this file spends its length retiring.

  (3) **The licence is unconditional in the result, and that is why it names
  `.blockedOnSend` rather than "not a `Call`".**  On the refusal branches the leg
  returns the *pre*-state, where a sender already `.blockedOnReply` would satisfy the
  weaker hypothesis and refute the conclusion; `ipcStateQueueMembershipConsistent` is
  what says `.blockedOnSend` is the reachable non-`Call` shape on a send queue.  The
  proof needs **no** distinctness between sender and receiver, because the last write
  at the sender's key is `.ready` either way.

  (4) **The rename is the claim.**  `_of_rendezvous` asserted the
  segment/migration equality for *every* rendezvous, which on a plain `Send` is now
  false (the segment is `[]`), so it became `_of_call_rendezvous` with the hypothesis
  the name promises, and a Tier 3 negative refuses the retired spelling — and Cut C1
  re-keyed it once more, to `_of_donating_call_rendezvous`, see (5).  Its four
  citations were swept, and the two positive anchors **failed loudly** at the rename —
  which is *sweep what was pinning the thing you deleted* working in the direction it
  is meant to.

  (5) **The residual was a LAYERING defect, registered rather than glossed — and
  CLOSED at `v0.35.160` (WS-RR RR8.12 Cut C1, register row 55).**  A dequeued `Call`
  whose donation prerequisites fail migrates nothing either, and the transition's
  guard for that is `callDonationSchedContext?`; transporting its pre-state answer
  across the receive leg is the backward `sameSchedContextBindings` frame.  Two
  things stood in the way, and each was a rule this file already carries.  **The
  frame was declared where the resolver could not see it**:
  `IPC/Operations/Donation.lean`'s closure contained neither
  `IPC/Invariant/Defs.lean` nor the reverse, so the bridge had no home beside the
  resolver — *a shared answer must be reachable from every asker* (`v0.35.59`),
  remedied the same way, the owner moved down.  The predicate and its `refl` /
  `trans` / `of_objects_eq` live in `IPC/Operations/Endpoint.lean` now, beside the
  two primitives that write the field they frame; the two invariant consumers stay
  in `Defs.lean`, and the `SeLe4n.Kernel` namespace is kept so nothing was renamed.
  **And the receive leg had no frame at all**: the two theorems that needed one
  (`endpointReceiveDual_preserves_donationBudgetTransfer`,
  `…_donationOwnerUnique`) each inlined the whole rendezvous composition, so it was
  extracted — `endpointReceiveDual_sameSchedContextBindings_of_rendezvous`, and
  `…_of_blocked` from the state the pre-receive cleanup leaves — and both became one
  case split over the frames, the de-duplication that is the evidence the frame was
  missing rather than merely unnamed.  (This item first said the per-primitive
  frames were unreachable from the footprint's module; they were, through a
  nine-edge production path, and *a module's layer is a fact about the import
  closure*.)  Six things new code must respect.  (a) **The segment keys on
  `receiveRendezvousDonatingSender?`**: the `Call`-narrowed resolver narrowed once
  more by `callDonationSchedContext?`, asked of the same two threads the transition
  asks it of, on the pre-state.  (b) **The bridge is one direction, and it is the
  right one**: `callDonationSchedContext?_some_of_sameSchedContextBindings` pulls a
  post-state `some` back to a pre-state `some`, which is exactly *the transition
  migrates ⟹ the footprint declares*; the forward direction is neither given by the
  backward frame nor needed, since declaring on a `some` the transition then
  declines is merely wide.  (c) **The licence is the leg's binding frame** —
  `endpointReceiveDualOnCore_sameSchedContextBindings_of_rendezvous` and its
  WithCaps twin, composed from the per-primitive frames and the pointwise
  `sameSchedContextBindings.of_objects_getElem_eq` for the wake of a `.ready`
  thread — so a pre-state `none` is the post-state's answer
  (`endpointReceiveDualWithCapsOnCore_callDonationSchedContext?_none_of_none`).
  (d) **Three payoffs, at three units**: the donation step is the identity
  (`applyReceiveRendezvousDonation_eq_self_of_no_donation`, over the general
  `applyReceiveRendezvousDonation_of_no_donation` in `Donation.lean`), the arm's
  whole hand-off writes no replenish queue
  (`applyReceiveRendezvousHandoff_replenishQueueOnCore_of_no_donation` — not the
  identity, since the chain walk still runs), and the footprint declares no
  replenish lock
  (`schedLockSet_endpointReceiveOnCore_no_replenishQueue_of_no_donation`).
  (e) **The coverage claim is stated at the donation's OWN resolver on its OWN
  state**: `schedLockSet_endpointReceiveOnCore_covers_donation`'s `hDon` is the
  post-receive-leg resolver, the guard `applyCallDonationOnCore` migrates on, bridged
  back to the pre-state reading the segment keys on — hypothesised on the
  footprint's own reading it would be the footprint vouching for itself.  The
  licence theorem is `endpointReceiveHandoffReplenishCores_of_donating_call_rendezvous`
  now, with the pre-state `some` as a hypothesis, and `_of_call_rendezvous` is
  refused tree-wide for the reason `_of_rendezvous` was.  (f) **The object-domain
  members were not narrowed in this cut and are since `v0.35.189`** — the bullet
  below; until then `receiveRendezvousDonatedSc?` and `endpointCallDonatedSc?`
  declared a SchedContext write lock for a donation the resolver declines.

  (6) **The claim is made about the step the ARM runs, not only about the donation.**
  `API.lean`'s `.receive` arm calls `applyReceiveRendezvousHandoff`, which is the
  donation **and** WS-OD OD3.14's priority-inheritance walk under one guard, so
  `applyReceiveRendezvousHandoff_eq_self_of_blockedOnSend` sits beside the
  donation-level fact — *a proxy is not the fact*, and a consumer reaching for the
  component would be reasoning about a sub-step of the transition it brackets.  The
  walk writes run queues rather than replenish queues (declared dynamically through
  `pipChainSchedFootprint`), so the replenish segment's own licence is still the
  donation half; both exist so neither can be read as the other.

  (7) **The witness computes the retired readings beside the live one.**
  `tests/SmpIpcSuite.lean` §3.26 drives three shapes through the live operations —
  a `Call` to a passive server (both cores declared, and the donation hands the
  context over at the state it runs on), a plain `Send` (the sender-keyed reading
  declares two cores, the live one none) and, since Cut C1, a `Call` to an
  **active** server (the `Call`-keyed reading declares two cores, the live one
  none) — with both retired segments computed as `private def`s beside the live
  one, so every assertion is known to discriminate.  Each empty segment is asserted
  against the donation step moving no replenishment, on the replenish *entries*
  rather than on state equality, because that is the proposition the footprint is
  about — `SystemState` has no `DecidableEq`, and reaching for one would have been
  a claim about the wrong thing.

- **...and the OBJECT-domain donation members follow the same guard** (WS-RR
  RR8.16, `v0.35.189`; register row 56).  Cut C1 narrowed the *replenish* segment
  and recorded that the two object-domain members had the same gaps one lock
  domain over: `endpointCallDonatedSc?` read the caller's own effective context
  with no test that a receiver was waiting or that it was passive, and
  `receiveRendezvousDonatedSc?` read the queued sender's through it — so a plain
  `Send`, and a `Call` to a receiver that already holds a reservation, each
  declared a SchedContext **write** lock (and a donation-old-head reply lock) for
  a migration that provably does not happen.  Sound, and not free: lock
  contention is an observable channel (SM8.D's CC-5), which is WS-OD OD3.5's own
  reason for narrowing a footprint.  Five things new code must respect.

  (1) **Each member resolves the OTHER party and asks the transition's own guard
  of the pair**: `endpointCallDonatedSc? st endpointId caller` is
  `(endpointCallReceiver? st endpointId).bind fun receiver =>
  callDonationSchedContext? st caller receiver`, and
  `receiveRendezvousDonatedSc? st endpointObjId receiver` is
  `(receiveRendezvousCallSender? st endpointObjId).bind fun sender =>
  callDonationSchedContext? st sender receiver`.  A member that inlines a binding
  read is the defect returning, and a Tier 3 negative refuses one at each.

  (2) **The owner moved DOWN, and the layering was measured rather than read off
  module paths.**  `IPC/CrossCore/EndpointCall.lean` and
  `IPC/Operations/Donation.lean` are **incomparable** — neither is in the other's
  import closure — and both reach `IPC/Operations/Endpoint.lean`, so
  `callDonationSchedContext?` and its four lemmas live at the join, with a
  tombstone at the old home (`v0.35.59`: *when a question has one owner and an
  asker that cannot see it, the owner is in the wrong layer*).  The same rule
  moved three binding frames out of the **staged** `EndpointCallInvariant.lean`
  into production — `endpointCallOnCore_preserves_objects_invExt`,
  `wakeThread_sameSchedContextBindings_of_ready`,
  `endpointCallOnCore_sameSchedContextBindings` — since the footprint and the
  licence are production and could not read a frame declared in the staged
  surface.  The first attempt wrote a *second* copy of the third and the build
  refused it as already declared: *before writing a helper, find the one this tree
  already has*, caught by the elaborator rather than by a review.

  (3) **Soundness is a proved relation in ONE direction, and that is the
  direction a footprint needs.**  A footprint that omits a written lock is false,
  so a narrowing owes *the transition migrates ⟹ the footprint declares* — and
  because the footprint resolves on the state the bracket acquires at while the
  donation branches at the state its leg leaves, that is **post `some` ⟹ pre
  `some`**: `endpointCallDonatedSc?_some_of_post` and
  `receiveRendezvousDonatedSc?_some_of_post`, each through Cut C1's backward
  binding frame (`callDonationSchedContext?_some_of_sameSchedContextBindings`)
  over the arm's own leg, with `endpointCallWithCapsOnCore_sameSchedContextBindings`
  the sending side's new whole-leg frame.  The forward direction is neither given
  by a backward frame nor needed: a footprint that declares on a pre-state `some`
  the transition then declines is *wider* than its operation, which is sound.

  (4) **The two lock domains ask ONE question, and that is stated.**
  `receiveRendezvousDonatedSc?_isSome_iff_donatingSender` says the object member
  and Cut C1's scheduler segment declare on exactly the same rendezvous, both
  composing `receiveRendezvousCallSender?` with `callDonationSchedContext?` at the
  same two threads — a shared *spelling* is not that fact.  The object member
  deliberately does **not** route through `receiveRendezvousDonatingSender?`,
  which already asks the guard to decide its own answer, so composing through it
  would ask the same question twice and leave two places for the answer to be
  read.  The `.call` arm has no such equality **by design**: its scheduler segment
  resolves at the WithCaps *post*-state and its object member on the pre-state,
  which is exactly what the `_some_of_post` licence is for.

  (5) **The narrowing is measured, not only proved, and it costs nothing.**
  `tests/SmpIpcSuite.lean` §3.36 drives five shapes through the live operations —
  a passive receiver (CONTROL), a bound receiver (the `.call` defect), a queued
  `Call` from a bound client (CONTROL), a queued plain `Send` and a queued `Call`
  to a bound receiver (the two receive-side defects) — with **both** retired
  readings spelled as `private def`s in the suite and nowhere else and computed
  beside the live resolver on every shape, each wrong on exactly one of them; a
  tree-wide negative refuses either escaping the witness.  `maxLockSetSize` is
  unmoved, both reachable `.replyRecv` bounds are unchanged (a narrowing can only
  lower a bound) and the golden trace is byte-identical.  Two things the cut
  records about its own register row, rather than quietly satisfying them: the
  blast radius was **35 call sites across six files**, not the registered 55
  across nine (that figure counted every occurrence of the two names, the
  hypotheses of theorems *about* them included), and it did **not** ride Cut C4,
  which restated each arm's members without touching these two — so it is a cut of
  its own after Cut C4 rather than inside it.
- **...and `seL4_CNode_Revoke` has an arm** (WS-RR RR8.16, `v0.35.190`).  The
  revocation family was verified machinery with **no ABI path**: `API.lean` had
  no revocation arm at all, so no capability a thread could present revoked
  anything — the register row RR8.12's reachability census opened on its first
  run, closed the way this project's implement-the-improvement rule says to close
  one.  `SyscallId.cspaceRevoke` (discriminant 35) is the arm.  Seven things new
  code must respect.

  (1) **It dispatches `cspaceRevokeCdt`, and that is its whole security
  content.**  The local `cspaceRevoke` reaches only the *containing* CNode, so a
  derived capability copied into any other CSpace survives it; the CDT walk
  follows the derivation tree across arbitrary CNodes.
  `tests/SyscallDispatchSuite.lean` SD-059 computes the local-only reading beside
  the live arm on a state whose derivation lives in a **second** CNode — spelled
  in the suite and nowhere else — so its assertions are known to discriminate,
  and a mutation of the arm to the local variant fails exactly the one that names
  the claim.  **And since `v0.36.1` no entry point opens with that local sweep**
  (PR #900 review).  It matches on the **target**, so as `revokeCdtScaffold`'s
  prologue it destroyed an independently rooted capability to the same object
  and the source's own parent in the same CNode, and left their CDT nodes mapped
  to emptied slots — which made *their* derivations unrevocable by anyone, since
  every revocation begins with a lookup of its slot.  The prologue is a read of
  the source slot now (`cspaceLookupSlot`: the same refusal set, no writes), so
  every entry point destroys exactly the source's CDT descendants, in every
  CNode, which is seL4's `cteRevoke` (read at `13.0.0`).  Every live install path
  records its edge, which is what makes dropping the sweep safe in the direction
  that matters: SD-059 asserts a same-CNode derivation is still destroyed and an
  independent sibling is not, and `tests/OperationChainSuite.lean`'s
  `revokeLeavesIndependentSibling` is PR #873 round 18's scenario inverted, at
  all four entry points, with the retired sweep computed beside it.  The local
  `cspaceRevoke` stays an operation — `lifecycleRevokeDeleteRetype` runs it and
  the non-interference catalogue carries it — and is recorded in the
  reachability census as reaching no syscall.

  (2) **The source slot survives, and that is what makes the delete's refusal
  dischargeable.**  Revocation destroys a capability's derivations, not the
  capability, so `cspaceDeleteSlot`'s `.revocationRequired` is answered by
  *revoke, then delete* — both halves run in the witness.  The arm takes the
  delete's one-register ABI (`decodeCSpaceDeleteArgs`), since both name one slot
  of the invoked CNode, and requires `.write`: `.grant` authorises **creating** a
  derivation (mint/copy/move), and destroying one is not that authority.

  (3) **A `donationReadAgreement` no longer demands `pendingMessage`
  EQUALITY.**  `revokePendingTransfersFrom` — the in-flight sweep the scaffold
  ends with — is the one transition in the tree that rewrites a
  `TCB.pendingMessage` to a *different* value while the thread stays blocked, and
  every bundle transport demanded the field be unchanged.  Equality was strictly
  more than the bundle reads: only `allPendingMessagesBounded` and
  `blockedThreadsPendingMessageConsistent` read it, the first needs the payload
  still bounded and the second needs a blocked sender still to *have* one.  So
  the relation is `pendingMessageReadAgrees` (presence agrees; boundedness
  transfers), the sweep's write is a **drop** (`TCB.pendingCapsDropped`: every
  other field equal, registers kept, capability array shorter), and a drop
  satisfies both.  A new transition that shortens a parked message reaches for
  those two; one that rewrites the field arbitrarily still has no transport, and
  that is correct.

  (4) **The scaffold's case analysis and the traversal's induction are
  predicate-free and live beside their definitions.**
  `revokeCdtScaffold_ok_decompose` says what a successful revocation *consists
  of* (the source slot resolves, then the traversal and the sweep, or the state
  unchanged), and `revokeCdtFold_induct` / `revokeCdtMaterializedTraversal_ok_induct`
  carry any `P` through the fold — so the capability bundle's argument and the
  IPC bundle's are **one** answer.  Each was the capability bundle's alone,
  spelled inside its preservation module; a second copy per predicate is the
  duplication this file spends its length retiring.  `revokeCdtFoldBody` moved to
  `Capability/Operations.lean` with them and `revokeCdtMaterializedTraversal` is
  *defined* through it — keeping the fold body in an invariant module is what had
  forced that traversal's proof to `change` its way into an inlined lambda.

  (5) **`.cspaceRevoke` declares NO static lock footprint, and that is a
  decision.**  The CDT walk's CNode set is state-discovered and unbounded while a
  `LockSet` is capped at `maxLockSetSize`, so a footprint naming only the source
  CNode would be **false** of the transition — which this project rates worse
  than no footprint at all.  `permittedKinds .cspaceRevoke` says which kinds a
  future declaration may contain, in the shape the PIP chain walk's
  `pipChainStart_<τ>` markers take for the same reason.  The inventory's coverage
  claim is therefore stated over `declaresStaticLockFootprint` — a total
  classification with its own `_false_iff` pin — rather than against
  `SyscallId.count`, because demanding an entry for this arm would force a
  footprint to exist in order to satisfy a number.

  (6) **`SyscallId.count` became 36, and the exhaustive tables moved with it**
  (37 since WS-BP BP7.1 added `.untypedRetype` at `v0.36.5`): the
  ABI mirrors in `sele4n-types` and the HAL, the return-shape table on both sides
  of the ABI (`.unit`, with `tests/fixtures/syscall_return_shape.expected`
  regenerated deliberately), `refusalSeamClass` (`.exempt`),
  `capFaultReceivePhase?` (`some false` — a send-phase capability fault),
  `frozenOpCoverage` (`false`: the per-node step ends in `cdt.removeNode`, a key
  *removal*, and the frozen CDT is four `FrozenMap`s with no `erase` — the same
  reason `lifecycleRetype` and the two service ops give), the enforcement
  boundary (`capabilityOnly "cspaceRevokeCdt"` — the composite a capability
  reaches, never the inner local step), and a `sele4n-sys` wrapper
  (`cspace::cspace_revoke`) so the conformance sweep can drive it.

  (7) **What the reachability census still lists is a narrower claim.**  The
  three *reporting* variants (`cspaceRevokeCdtStrict`, `…Streaming`,
  `…Transactional`) with their traversals, the streaming BFS and the reporting
  fold step remain outside the live closure: each is the same scaffold at a
  different traversal, offered to **in-kernel** callers that want a structured
  failure report or an `O(branching-factor)` walk, and the syscall dispatches the
  materialized one because a userspace invocation has no channel to receive a
  report through.  A variant with no in-kernel caller either gains one or is
  retired.
- **A capability is installed only at a slot the target CNode can address**
  (WS-RR RR8.16, `v0.35.201`).  `CNode.resolveSlot` extracts a slot by masking
  with `2 ^ radixWidth`, so an index at or above `slotCount` can be **stored**
  and can never be **reached**; `cspaceInsertSlot` — the one primitive every
  capability install passes through — asks `CNode.slotAddressable` before it
  asks about occupancy, and refuses with `.invalidArgument`.  Before it, a
  `seL4_CNode_Copy` whose `dstSlot` came verbatim from a message register grew a
  fixed-size kernel object without bound and falsified `cspaceSlotCountBounded`,
  a conjunct of `capabilityInvariantBundle`, on a state one ordinary syscall
  reaches.  Six things new code must respect.

  (1) **The chokepoint is the primitive, not the four arms.**  `cspaceCopy`,
  `cspaceMint`, `cspaceMove` and the IPC capability transfer all reach
  `cspaceInsertSlot`, so the range check is stated once — the *creator is exactly
  one function* principle `ipcTransferSingleCap`'s own comment already invokes
  for the revocation window.  A new install path inherits it by calling the
  primitive; one that writes a CNode directly is the defect returning.

  (2) **The transfer path answers `.noSlot`, it does not refuse.**
  `ipcTransferSingleCap` scans with `findFirstEmptySlotChecked`, so a receiver
  CNode with no free in-range slot yields an outcome the transfer summary already
  models rather than an error — and `findFirstEmptySlotChecked_slotAddressable`
  is what makes its `.ok` provably not the guard's refusal.  Its sibling
  `resolveSlot_slotAddressable` is the other half of the claim: the guard refuses
  exactly the slots no CPtr can name.

  (3) **A helper written for a hazard and never wired is the hazard, unfixed.**
  `findFirstEmptySlotChecked` was written by AK8-F for *precisely* this, proved
  `findFirstEmptySlotChecked_within_radix`, said in its own docstring that the
  zero-width window ensures no out-of-range slot is ever produced — and had **no
  production consumer at all**, in the whole of this repository's visible
  history, which begins at `v0.32.69` and in which the checked variant is
  present from the first commit, while `findFirstEmptySlot` sat on the live
  transfer path.  The tree held the fix and
  the defect at once.  *A helper whose docstring names the hazard it prevents is
  a claim that the hazard is prevented; check who calls it.*

  (4) **A fixture built on the defect makes the defect invisible to every test,
  and landing the guard is what finds it.**  Six fixture CNodes were malformed,
  the trace harness's own **bootstrap root CSpace** among them: CNode ⟨10⟩
  declared `radixWidth := 0` — *one* slot — while holding capabilities at 0, 5
  and 6, so `cspaceSlotCountBounded` was **false** of the state every trace
  scenario starts from and every capability but slot 0's was unreachable.  No
  audit of the guard's *call sites* could have shown that; the diff after
  landing it did, in one run.  Two of the six carried a **comment naming the
  radix the code did not have** (`S2-G-05`: *"Build a CNode with radixWidth=2 …
  fill slots 0-3"* over `radixWidth := 0`) — a defect report nobody read.  *A
  fixture comment that names a parameter the code does not have is a finding.*

  (5) **An invariant no runtime check asserts is one a fixture can violate
  silently** — which is *why* (4) could persist for as long as those fixtures
  have existed: `slotCountBounded` appeared nowhere under `SeLe4n/Testing/`.
  `cspaceSlotAddressableChecks` is part of `stateInvariantChecksFor` now, and it
  asserts the **structural** property rather than the cardinality: slot keys are
  unique, so *every occupied index is below `slotCount`* entails the count bound
  and, unlike it, names the offending slot.  This is RR8.3's *the conjunct is
  checked at runtime, not only proved* rule meeting a conjunct that predates
  this repository's visible history and had been checked never.  What the boot still
  bounds is the **count** and not the **indices**, so a `PlatformConfig` CNode
  may hold four capabilities at slots 0, 9, 17 and 33 in four addressable slots;
  that is registered rather than assumed away.

  (6) **A scanner for this class must resolve indirection, and the runtime check
  is the authority.**  The static sweep written to size the damage read slot
  indices out of CNode literals and **missed** `strictSeed`, whose slots are
  spelled `strictRootSlot.slot` — *a helper the scanner cannot see is a spelling
  that evades the metric*, arriving inside the measurement written to size the
  class.  The runtime check named it in one run.  And a guard forces a sweep of
  every **re-derivation** of the operation it guards: a successful insert's
  decomposition was re-derived inline at **eight** sites and the guard broke all
  eight, so they read `cspaceInsertSlot_ok_decompose` now and three frames moved
  beside the primitive (`_cdt_eq` relocated out of a preservation module,
  `_cdtNodeSlot_eq` and `_objects_eq` new, the last replacing a `private` copy).
  With the fixtures repaired the golden trace is **byte-identical** but for the
  post-dispatch check count the new runtime check moves (29 → 32), which is the
  measurement that the guard refuses only what was already unreachable.
- **A definition that transforms kernel state is wired or recorded** (WS-RR
  RR8.12 third cut, `v0.35.91`).
  `SeLe4n/Testing/KernelTransitionReachabilityCensus.lean` (Tier 1) derives every
  project `def` whose **result type** mentions `SystemState` — 528 of them —
  partitions that domain by whether one of the 7 committing `@[export]`s can
  reach it (288 do), and reconciles the other 240 against a pin in **both**
  directions: a new non-executed transformer fails, and so does an entry that
  has become live.  New code adding a state transformer that no seam runs must
  either wire it or record it there.

  Four things it decides and one it does not.  (1) **The commit predicate and
  the auxiliary filter are imported, not restated** —
  `ExportCommitDisciplineCensus.commitsState` and
  `ReplyStackWriteCensus.isAuxiliary` — so the three censuses cannot disagree
  about what installs kernel state or about what the compiler generated; the
  three generated shapes the second does not reach are named with the
  measurement that found them.  (2) **The domain over-approximates on purpose**:
  an `Option SystemState` resolver qualifies, which is the safe direction, since
  a member wrongly included must be explained and a member wrongly excluded is
  never looked at.  (3) **The 240 carry no per-entry prose**, deliberately —
  that many shallow reasons read as justification while asserting nothing — so
  the obligation falls on whoever adds the next entry.  (4) **The known residue is
  named in the pin's docstring rather than left to read as unexamined**: four
  transformers consumed by nothing, which carry a register row because each needs the
  wire-or-retire judgement `v0.35.78` made for the capability-reference table.

  **What it does not decide, and this corrects the row that asked for it**:
  reachability sees a *new* non-executed transition and **cannot** see a step
  added inside an already-registered one — which is the defect that motivated
  it, since `cancelIpcBlockingOnCore` already existed and was already
  unreachable.  The register row claiming the census "would have failed on the
  day" that step was added was wrong and is corrected.  What sees it is
  `standsBesideLive`: a row names the non-executed surface, the live definition
  that re-composes it, and a **pin theorem** that RELATES them, so a step added to
  one side alone fails the build — measured by inserting one into
  `cancelIpcBlockingOnCore` and watching
  `cancelIpcBlockingOnCore_eq_reclaimed_deschedule` stop elaborating.  *Relates*,
  not *mentions* (PR #897 review, `v0.35.96`): the check asked whether the
  statement named both programs, which a conjunction of reflexive equations
  satisfies while relating nothing — this file's oldest rule failing inside the
  gate written to enforce a different one.  `pinRelatesPrograms` requires an `Eq`
  or `Iff` conclusion with **each program on exactly one side, on opposite
  sides**, so one side is built from the surface without naming the counterpart
  and the other from the counterpart without naming the surface; three witness
  theorems carry the shapes the superseded check accepted and the census asserts
  all three are refused, because a check that cannot fire on this tree is
  indistinguishable from one that is wrong.  Two rows are pinned today; a
  registered surface with no pin makes **no** agreement claim, and extending the
  pinned set is what closes the class rather than the instance.
- **An endpoint queue's membership lives in its members' TCBs, and those members'
  labels differ** (WS-RR RR8.8, `v0.35.83`).  Three facts new code must respect,
  and the first is the one that decides the other two.  (1) **The admission gate
  is an order, not an equality**: the live send / call gate is
  `endpointFlowGate ctx ep (threadLabelOf sender) (endpointLabelOf ep)` and the
  receive gate its mirror, so a *lower*-labelled and a *higher*-labelled sender
  are both admitted onto one higher-labelled endpoint —
  `publicLabel → kernelTrusted` being the flow
  `securityFlowsTo_prevents_label_escalation` documents as intended.
  `endpointAdmissionAdmitsMixedObservability`
  (`InformationFlow/Projection.lean`) is that admission as a `decide`-checked
  theorem, with an observer that sees exactly one of the two.  So **an
  endpoint/notification queue label-uniformity invariant is unestablishable**, not
  merely absent; it was the registered closure for `abortHolderProjectionStable`,
  `abortHolderWakeHigh` (`descheduledHolderHigh` since `v0.35.158`) and the three
  queue arms' `hTeardownProj`, and it is retracted.  A proof that reaches for it is asking for a premise the gate
  refutes.  (2) **What the gate gives is the other direction, and with one
  added conjunct it is enough for everything but the neighbours.**  Every
  waiter's label flows to its endpoint's **flow** label
  (`endpointFlowGate_implies_securityFlowsTo`, no hypothesis) — but
  `objectObservable` decides visibility from `objectLabelOf`, and
  `LabelingContext` carried `endpointLabelOf` and `objectLabelOf` as
  *independent* fields with nothing relating them, so "the endpoint object is
  non-observable whenever a waiter is" was **not derivable** and `v0.35.83`
  asserted it anyway.  `LabelingContextValid.endpointObjectCoherence`
  (`v0.35.84`) is the missing conjunct — an endpoint's flow label flows to its
  own object's label, so the object is at least as sensitive as the flows the
  endpoint admits — discharged structurally for every constructed context from
  `DeploymentLabeling.hEndpointObjectCoherence`, which the one base constructor
  meets by reflexivity.  A new `DeploymentLabeling` must supply it; a new
  labelling *question* about an endpoint must say which of the two fields it is
  about.  With it, `endpointObjectHigh_of_admittedThreadHigh` covers the
  endpoint's own queue boundaries and `donationHolderHigh_of_donorHigh` covers
  the aborted holder's TCB, through `donationOwnerFlowsToHolder` — the state
  form of `label victim ⊑ label endpoint ⊑ label holder`, established where a
  donation is minted because the state records no trace of the two gates that
  licensed it.  The **queue neighbours** are covered by nothing: their labels are
  constrained only against the endpoint's.  So `abortHolderWakeHigh` is
  **reduced to that fact** (`abortHolderWakeHigh_of_donationOwnerFlowsToHolder`,
  `v0.35.84`; `descheduledHolderHigh_of_donationOwnerFlowsToHolder` since
  `v0.35.158`, a removal being filtered by the removed thread's own
  observability exactly as an insert is) — it is a single `threadObservable` of
  the holder and needed no queue reasoning at all — while
  `abortHolderProjectionStable` and
  `hTeardownProj` reduce to the neighbour class and no further
  (`abortHolderSpliceHigh_of_victimHigh`, over the shared
  `endpointSpliceHigh`).  **Read that as a reduction, not a closure**: `v0.35.84`
  called it *discharged*, which is what it would be if the fact it reduces to were
  a fact about reachable states, and for two cuts it was a `Prop` nothing
  established — see item (4).  **And a reduction to a predicate is not a
  connection to the OPERATION** (`v0.35.193`): for nine cuts
  `abortHolderProjectionStable` went on carrying its *whole* obligation as a
  hypothesis, because the reduction stopped at `endpointSpliceHigh` and nothing
  related that predicate to `abortHolderPendingIpc` — the prefix runs the
  **single** `endpointQueueRemove`, and only the **dual** removal had a projection
  lemma (RR7.22).  The labelling layer was proved and the wire was missing, which
  in a bundle search reads exactly like a closed obligation.  The single removal
  has one now (`endpointQueueRemove_preserves_projection{,_and_invExt}`, beside
  `endpointSpliceHigh` in `InformationFlow/Invariant/Operations.lean`, built from
  raw-insert frames because the removal's four writes are `RHTable.insert`s in one
  record update rather than four store primitives), and with it
  `abortHolderPendingIpc_preserves_projection` and the discharges
  `abortHolderProjectionStable_of_{spliceHigh,neighbourHigh}` — so what a caller
  supplies is the neighbour clause and nothing else.  The one mismatch that
  crossing needed is a mismatch of *spelling*: `endpointSpliceHigh` names the
  predecessor through `queuePPrev` and the single removal reads `queuePrev`, and
  RR8.3's `TCB.queuePPrevAgreesWithPrev` is exactly the statement that those are
  one thread (`endpointSpliceHigh_queuePrev_high`), read at a thread through
  `queuePPrevAgreesWithPrev_lookupTcb` rather than by re-opening the
  `getTcb?` / `objects[…]?` bridge at each consumer.  **When a reduction stops at
  a predicate, ask what still connects that predicate to the transition**; a
  hypothesis and its labelling layer can both be right while nothing joins them.
  (3) **The residue is
  representational and the remedy is forced**: `queuePrev` / `queuePPrev` /
  `queueNext` survive `projectKernelObject`, so an observable thread's projection
  already names a non-observable one's identity with no operation having run —
  the same class as the `replyObject` erasure SM6.D landed — and a splice then
  rewrites an observable field.  *Stripping* the links is **unsound** rather than
  coarse: the projection would stop determining the next dequeue, so two
  low-equivalent states would step to states differing in the endpoint's own
  visible `head` and the step-level NI theorems would become false.  A queue's
  content must live in an object whose label **dominates** every member's, which
  the endpoint is and a member's own TCB is not — so the closure is non-intrusive
  endpoint queues, registered in `docs/REGISTERED_DEBT.md` table C with its
  measurement.  Until it lands, **v1.0.0 must not claim that a low observer
  cannot learn a high thread's identity from endpoint queue state.**  (4) **A
  predicate only consumed as a hypothesis is an assumption wearing a definition's
  name** (WS-RR RR8.16, `v0.35.126`, PR #897 review).  `v0.35.83` and `v0.35.84`
  introduced `blockedSenderFlowsToEndpoint` and `donationOwnerFlowsToHolder`, argued
  from the *gates* in their docstrings — which is the right argument — and then
  consumed both as hypotheses and nothing else: no theorem established either where
  the fact is created, none transported it across a step, and no state inhabited
  either.  So the reduction above was not composable for a live state, and the word
  *discharged* was reading a reduction as a closure.  Four things new code must
  respect.  **Only ONE of the two needs a story**: `donationFlowFromBlockedDonor`
  derives `donationOwnerFlowsToHolder`'s conclusion from its sibling plus the
  *receiving* gate — `label owner ⊑ label ep ⊑ label holder` — because a
  `.donated scId owner` binding is minted only through a `Call` rendezvous in which
  the donor is `.blockedOnCall` on that endpoint.  **Transport is weaker than a
  frame, deliberately**: `blockedSenderShrinks` (with `.refl`, `.trans` and
  `blockedSenderShrinks_of_ipcStateFrame`) says a step introduces no blocked sender
  *on the same endpoint* it did not already have — a send rendezvous writes the
  receiver `.ready` and a wake writes a runnable state, so neither frames every
  `ipcState` while both shrink the set, and a step moving a thread from
  `.blockedOnSend ep₁` to `.blockedOnCall ep₂` would satisfy a set-shaped relation
  and break the predicate.  The donation fact's counterpart is
  `donationOwnerFlowsToHolder_of_sameSchedContextBindings`, over the frame family
  the tree already has for every transition that mints no donation.
  **Establishment is stated at the one WRITE, not per transition**: every
  production path that blocks a sender or a caller goes through
  `storeTcbIpcStateAndMessage` with the endpoint as an explicit argument, so
  `storeTcbIpcStateAndMessage_preserves_blockedSenderFlowsToEndpoint` takes the gate
  as an argument (a transition-time check the store records no trace of) and a
  transition inherits the fact by exhibiting its own decomposition.  Landing it
  moved `storeTcbIpcStateAndMessage_tcb_backward_fields` out of
  `IPC/CrossCore/EndpointReplyInvariant.lean` and beside the primitive it frames,
  which is `v0.35.59`'s rule — *when a question has one owner and an asker that
  cannot see it, the owner is in the wrong layer* — and put it next to the two
  siblings RR3.5 had already relocated for the same reason.  And **the boot state
  inhabits both, for every labelling context**
  (`bootFromPlatformCheckedWithIdleThreads_flowGateFacts`): `bootSafeTcbCheck`
  refuses a blocked or bound config TCB and the idle fold installs neither, so both
  antecedents are *empty* rather than their conclusions cheap.  That measurement
  generalised `bootFromPlatformChecked_ok_tcb_inactive` — which concluded two of the
  ten fields its own object-reachability argument establishes, so the other eight
  needed a second copy of that argument — into
  `bootFromPlatformChecked_ok_tcb_bootSafeFields`, with the old name its two-field
  corollary.  **And the per-transition lift landed at `v0.35.191`**
  (`SeLe4n/Kernel/IPC/Invariant/BlockedSenderPreservation.lean`): both
  `endpointSendCrossCoreDispatchChecked` and `endpointCallCrossCoreDispatchChecked`
  carry the fact, each under the `endpointFlowGate` its own branch condition
  supplies.  **The per-TCB dichotomy this paragraph predicted was not needed**, and
  that correction is the cut's own finding: every step of both composites falls
  into one of three classes rather than needing a pullback — it preserves every
  `ipcState` (the queue splice, the capability transfer, the reply link, the
  SchedContext donation, the priority-inheritance walk, the run-queue removal, each
  getting `ipcStateFrame`, the relation `QueueSplicePreservation.lean` already owned
  for this question), it writes `.ready` (`storeTcbReceiveComplete` and the wake's
  `enqueueRunnableOnCore`, which *shrink* the blocked-sender set and are therefore
  `blockedSenderShrinks` rather than a frame — a Tier 3 negative refuses the
  stronger claim, which is false of both), or it **is** the blocking store, which
  the `v0.35.126` establishment already covered.  A donation's frame is read off its
  own `donationReadAgreement`, whose `tcbBwd` clause states the conjunct outright,
  so a widening of the donation inherits it.  Two things new code must respect.
  **The lift is a theorem about the CHECKED arm and is false of the unchecked one**:
  what discharges the blocking store's obligation is the gate the dispatch
  evaluates, so the unchecked composites take it as an argument and only the checked
  ones discharge it.  And **both arms carry `donationOwnerFlowsToHolder` too, by
  two different routes**: the send over its own `sameSchedContextBindings` frame
  (`endpointSendCrossCoreDispatchChecked_preserves_donationOwnerFlowsToHolder`,
  `v0.35.191`), which the `.call` chain has had since RR2 and the send did not,
  and the call — the one transition that **mints** a donation, so no binding frame
  can carry it — over the *receiving* gate, which `v0.35.196` made a state
  predicate.  See the next bullet.
- **...and the RECEIVING side of the endpoint gate is a state predicate too, so
  the arm that mints a donation carries the flow fact** (WS-RR RR8.16,
  `v0.35.196`, closing register row 183).  `blockedSenderFlowsToEndpoint` records
  what the *sending* gate checked; nothing recorded what the *receiving* gate
  checked, so `donationFlowFromBlockedDonor` had to take that half as an argument
  (`hReceiveGate`) and no dispatch could discharge it.  Six things new code must
  respect.  (1) **The direction IS the predicate.**
  `blockedReceiverFlowsFromEndpoint` reads `endpoint ⊑ thread` where its sibling
  reads `thread ⊑ endpoint`, so a spelling that swaps the two arguments is the
  sibling's reading and the transitivity in `donationFlowToBlockedReceiver` stops
  composing; a Tier 3 anchor pins the direction inside the declaration.  (2) **It
  is established at the SAME write**, `storeTcbIpcStateAndMessage`, from the
  receive arm's own `endpointFlowGate` — a second establishment site would be a
  second answer to one question — and transported by a `blockedReceiverShrinks`
  twin, which is weaker than `ipcStateFrame` for the reason its sibling is.  (3)
  **The derivation reads the receive half OFF THE STATE**, which is the whole
  content: `donationFlowToBlockedReceiver` takes
  `blockedReceiverFlowsFromEndpoint` where `donationFlowFromBlockedDonor` takes a
  gate, and a mutation that restores the argument shape keeps every token and
  reopens the row.  (4) **The extra `ipcInvariantFull` conjunct is the RESOLUTION
  of the receiver, not an extra assumption.**  The `.call` lift takes
  `queueHeadBlockedConsistent` where the send's lift takes none, and that
  difference is structural: the sending gate is evaluated on the *invoking*
  thread, whose identity the transition holds, while the receiving gate is
  evaluated on a thread the rendezvous **finds** on a queue — so the conjunct is
  what says *which* thread the receiver is.  `rendezvousReceiverFlow` is where the
  two meet.  (5) **The donation's own step is gated on its own resolver**:
  `applyCallDonationOnCore_preserves_donationOwnerFlowsToHolder` keys its flow
  hypothesis on `callDonationSchedContext?` rather than on the two threads'
  identities, so a widening of the donation guard cannot leave it behind.  (6)
  **The labelled reachable pack is OPT-IN**: `ipcReachableUnder ctx` is
  `ipcReachable` and the three flow facts, `ipcReachable` is unchanged and
  `.reachable` projects out of it, so no existing consumer carries a `ctx` it does
  not read, and `ipcReachableUnder_default` inhabits it for *every* labelling.
  Neither pack is claimed preserved along a trace — that is `ipcReachable`'s own
  shape as a pre-state pack the dispatch payoff consumes, so the labelled
  extension is exactly as strong as the thing it extends.  The witness is
  `tests/SmpInformationFlowSuite.lean` §15 and its decisive case is the one where
  the caller's gate **passes** and the donation **is** minted while the
  receiver-side fact is false; its fixture is built by the **live** receive,
  because a hand-built blocked server carries no Reply object, `donationPushFrame?`
  then refuses, and every outcome assertion passes vacuously.
- **The two cross-subsystem invariant bundles have FRAMES, so a step that writes
  nothing they read costs one application** (WS-RR RR8.16, `v0.35.197`, register
  row 85's first half).  Before this cut neither `schedulerInvariantBase_smp` nor
  `capabilityInvariantBundle` had one: twelve per-conjunct lemmas existed across
  the *scheduler* transitions and **none** for an objects-only step, and the only
  reusable capability shape was one operation's forty-line argument — so each IPC
  step's lift would have been a fresh case analysis over predicates it does not
  touch.  Six things new code must respect.  (1) **The scheduler frame takes TCB
  SURVIVAL, not store equality.**  A step that rewrites the current thread's own
  TCB — the reply leg's `ipcState` write, the donation's binding write, the
  walk's `pipBoost` write — is the common case, and equality would refuse exactly
  the steps the frame exists for; a Tier 3 negative refuses that hypothesis
  coming back.  (2) **The narrower frame is at the fields the invariant reads**:
  `SchedulerState` has nine and the base invariant reads `current` and
  `runQueue`, so a step that writes `replenishQueue` alone (the SM5.H migration)
  satisfies `_of_schedulerFields` and *not* whole-scheduler equality — demanding
  the latter would refuse a step the invariant provably does not see.  (3) **The
  capability frame states the DIRECTION each conjunct transports in**, which is
  its whole content: three conjuncts read CNodes and go **backward** (a post-state
  CNode must be a pre-state CNode — what a store at a TCB key gives), while
  `cdtCompleteness` and the Reply half of `replyCapPointsToValidReply` go
  **forward** (a store removes no key and no Reply).  `cspaceLookupSound` is
  structural and `cdtAcyclicity` reads `st.cdt` alone.  (4) **`cnode` is excluded
  from the pointwise instance, in one direction only**: a CNode *rewrite* keeps
  the key and the kind while changing the slots, and three conjuncts are about
  the **value** — so a genuinely CNode-writing step (`ipcTransferSingleCap`,
  `ipcUnwrapCaps`) takes the general frame and has its own bundle lemma already.
  (5) **`storeObject_preserves_capabilityInvariantBundle_of_kind` is what every
  IPC store chain is built from**: `storeObject` writes no CDT table, so of the
  frame's six hypotheses four are that lemma pair and the `invExt` frame, and
  what is left is the store's own key.  (6) **A lift is not always a frame
  application, and the walk is the example**: `propagatePipChainCrossCore`
  re-buckets, so neither whole-scheduler nor field equality holds of it, and its
  lift composes four facts stated *beside the transition* — the current slot is
  fixed, membership is fixed, the `remove`-then-`insert` keeps `Nodup`, and the
  only object write is a TCB for a TCB.  An instance of a frame lives beside the
  frame; a fact about a transition lives beside the transition; where a
  transition's own module is upstream of the predicate's (which is true of
  `Propagate.lean` and of `Scheduler/Operations/Selection.lean`), the lift goes
  to the predicate's module and says so.
- **...and the relation those frames read has ONE NAME, so the reply chain is
  citations rather than an argument** (WS-RR RR8.16, `v0.35.199`, register row
  85's reply half).  `v0.35.197` stated each frame's pointwise instance as an
  inline condition on the two stores, which is the recognised-set shape one level
  down: a step's lift had to spell it out, and a widening would reach whichever
  consumer a review named.  `kindPreservingWrite st st'` — *at every key the
  object is unchanged, or both sides hold an object of the same non-`cnode` kind*
  — is the one name both bundles' frames take (`_of_kindPreserving` on each), so
  a widening reaches the scheduler bundle and the capability bundle by
  construction.  Five things new code must respect.

  (1) **A store primitive answers this question BESIDE ITSELF.**  The two
  primitives are `storeObject_kindPreservingWrite` and
  `rewriteObject_kindPreservingWrite`, and every composite reaches them through
  `.trans` rather than through a pointwise walk: the consume, the splice, seL4's
  `reply_remove`, the delivery store, the enqueue, the wake and the donation pop
  each carry one, and each is a few lines because the primitive carries the
  content.  A new store-shaped step states its own on the day it is written.

  (2) **The in-place primitive needs NO side condition, and that is not an
  economy.**  A `rewriteObject` carries its own proof that the key holds an
  object of the replacement's kind *and* that the kind is bookkeeping-neutral
  (`rewriteAdmissible`), and `KernelObjectType.rewriteNeutral` is `false` at
  `.cnode` — so **both** of the store lemma's hypotheses are already inside the
  rewrite's proof argument.  A Tier 3 negative refuses a `cnode` side condition
  coming back, because re-adding one reads as caution and is the statement that
  the admissibility argument was not consulted.

  (3) **The two lifts of one transition take DIFFERENT preconditions, and the
  asymmetry is the claim.**  The capability bundle reads the object store and the
  two CDT tables, all of which the reply chain frames or writes
  kind-preservingly, so `endpointReplyOnCore_preserves_capabilityInvariantBundle`
  and the dispatch's are **unconditional**; the scheduler bundle reads
  `currentOnCore`, and the wake's `queueCurrentConsistentOnCore` preservation
  needs the thread it enqueues not to be that core's current thread, so the
  scheduler lifts carry `hNotCur`.  Both directions are pinned — a positive that
  the scheduler lift has it, a negative that the capability lift does not — since
  a mutation either way keeps every other token.

  (4) **`hNotCur` is stated on the PRE-state, which is where a caller can
  discharge it — and it is STATED rather than derived, which is a gap this cut
  names rather than closes.**  The delivery store frames the scheduler and every
  thread's `cpuAffinity`, so the core the wake enqueues on and the slot it reads
  are the pre-state's; a lift that asked for the post-delivery state would be
  asking a caller about a state it does not hold.  What would *derive* it is a
  **per-core** current-thread-IPC-readiness discipline, and this tree states that
  at the boot core only (`currentThreadIpcReady`); `blockedOnReplyNotRunnable` is
  not it, since it says a reply-blocked thread is not in a run **queue**, which
  `queueCurrentConsistentOnCore` makes compatible with being current rather than
  incompatible.  The single-core `endpointReply_preserves_schedulerInvariantBundle`
  has taken the boot-core form since WS-H1 for the same reason.

  (5) **What remained of row 85 was the CALL chain and the fault composition**,
  and `v0.35.200` closed it — see the next bullet.  The scope was a measurement
  rather than an estimate, and the measurement held: `endpointCallOnCore`'s store
  primitives (`endpointQueueEnqueue`, `endpointQueuePopHead`,
  `storeTcbQueueLinks`, `linkCallerReply`, `linkServerStashedReply`, and the
  delivery store this cut already covers) had **no** CDT frames and no
  `kindPreservingWrite` instances, so each owed the pair this cut wrote for the
  reply side; `endpointCallWithCapsOnCore` then takes the *general* capability
  frame, because `ipcUnwrapCaps` writes CNodes and has its own bundle lemma
  (`ipcUnwrapCaps_preserves_capabilityInvariantBundle_grant`).
- **...and the CALL chain and the FAULT composition close it — where the two
  lifts' preconditions come from, and where a frame LIVES** (WS-RR RR8.16,
  `v0.35.200`, register row 85 **CLOSED**).  The row is named for the fault path,
  and the fault path could not compose what its substrate lacked:
  `faultDeliverOnCore` runs the live cross-core `.call` chain and
  `faultReplyOnCore` the live `.reply` chain.  With `v0.35.199`'s relation and
  this cut's call-side instances both transitions carry the base SMP scheduler
  invariant and the capability invariant bundle.  Six things new code must
  respect.

  (1) **The typed read-modify-write is the one owner for "a TCB rewrite keeps
  every key's kind".**  `SystemState.updateTcb_kindPreservingWrite` needs **no**
  side condition, for the reason `rewriteObject`'s does not, and every write on
  the fault path — the fault record, the restart frame, the `.Inactive` store,
  the four register-context writers, the delivered-message staging — is
  `updateTcb`, so each reaches both bundles through it rather than re-deriving
  the rewrite's admissibility at its own site.  Its `_cdt` / `_cdtNodeSlot`
  siblings sit beside it, and a Tier 3 negative refuses a `cnode` side condition
  coming back.

  (2) **The two lifts' preconditions differ for a reason that is a property of
  the CHAIN, not of a level of it.**  The `.reply` chain's capability lift is
  unconditional at every level; the `.call` chain's is unconditional at the bare
  leg and **reduces** to `ipcUnwrapCaps`'s from `endpointCallWithCapsOnCore` up,
  because that is where the one IPC step that writes a CNode *and* mints CDT
  derivations enters, which `kindPreservingWrite` excludes by construction.  So
  **neither** fault transition owes anything: `faultMessage` carries `caps := #[]`
  and the leg short-circuits on `msg.caps.isEmpty` *before* it resolves the
  receiver's CSpace root, so the delivery composes `…_of_no_caps`, and the reply's
  payload is registers.  The scheduler lifts carry `hNotCur` at every level of
  both chains, stated on the pre-state and *stated rather than derived*, for the
  reason `v0.35.199` recorded.

  (3) **A hypothesis you cannot exhibit is a vacuity, so REDUCE rather than
  import.**  The obvious shape here is to take
  `ipcUnwrapCaps_preserves_capabilityInvariantBundle`'s three externalised
  premises.  The first is **refuted**: `hSlotCap` asks that inserting any
  capability at any slot of any CNode of any bundle-satisfying state keep
  `slotCountBounded`, `cspaceSlotCountBounded` is `≤` so a bundle state may hold a
  CNode at capacity, and `CNode.insert` at a fresh slot grows the table.  A lift
  taking it would hold on no state while its name read as coverage — and that
  lemma's having no consumer since it was written is the corroborating
  measurement.  `ipcUnwrapCapsPreservesCapabilityBundle` is the reduction instead:
  a statement about the *operation*, exhibited by `…_of_noGrant`, so the chain's
  content is *everything else is kind-preserving; the bundle reduces to this one
  step*.  **Ask of any hypothesis you add: what discharges it?**  Pulling on that
  question here surfaced a live **High**-severity defect — no CSpace destination
  slot is validated against the target CNode's radix width at *any* of the four
  capability-insert paths, so one `seL4_CNode_Copy` with a raw out-of-range
  `dstSlot` grows a fixed-size kernel object without bound and falsifies
  `cspaceSlotCountBounded` — which is registered with its end-to-end `#eval`
  measurement rather than described.

  (4) **A composition that resolves its own endpoint takes the STATE-level
  `hNotCur`.**  `endpointReceiveHeadsNotCurrent` — *no endpoint's receive-queue
  head is current on the core its own affinity names* — is what the fault
  delivery takes, since its handler endpoint comes from `resolveFaultHandler`;
  `endpointReceiveHeadsNotCurrent_at` projects it at one endpoint, which is the
  form every rendezvous lift keeps, because that is exactly what each lift needs
  and a caller who knows the endpoint can discharge it there.  The per-core
  `currentThreadIpcReady` discipline retires both.

  (5) **A frame that reads no staged surface is PRODUCTION, and eight of them
  were not.**  The four fault-path `_preserves_objects_invExt` frames and the two
  chain-level ones lived in the staged `IPC/Invariant/FaultPreservation.lean`,
  which is staged for the call chain's staged *`ipcInvariantFull`* bundle — so
  each was out of reach of the production consumer that needed it, which is row
  85's own complaint one level up.  They are beside their operations now, and the
  fault path's two cross-subsystem bundles live in the **production**
  `IPC/Invariant/FaultBundlePreservation.lean` rather than beside the staged
  `ipcInvariantFull` surface of the same transitions.  Two more moved for
  `v0.35.59`'s rule: `ipcUnwrapCaps_getTcb?_eq` was `private` in a cross-core
  *reply* module while framing a model-layer primitive the `.call` leg asks the
  same question of, and the two reply-link `invExt` frames sat above the model
  primitives they frame.  A `private` duplicate of `storeTcbIpcStateAndMessage`'s
  CDT frame was **deleted** rather than kept beside the public one.

  (6) **The donation's lifts sit with the call chain, and the asymmetry with the
  reply pop's is the import graph's.**  `returnDonatedSchedContext` is declared in
  `IPC/Operations/Endpoint.lean`, below both bundle modules, so its lifts are
  beside the bundles; `applyCallDonationOnCore` is declared in
  `IPC/Operations/Donation.lean`, which composes the priority-inheritance walk and
  so sits *above* the scheduler-invariant layer — neither bundle module can name
  it.  Its lifts are therefore in `IPC/CrossCore/EndpointCallDispatch.lean` beside
  the chain that composes them, and the docstring says which fact decides that
  rather than leaving a reader to infer a convention.
- **...and `passiveServerIdle` is preserved by `cancelIpcBlocking` on every arm**
  (WS-OD OD1.5, v0.34.105) — the theorem OD1 exists to prove, and one that was
  *false* before the abort prefix: the reply arm's reclaim could leave a holder
  `.unbound` and still `.blockedOnCall`.  Four things new code must respect.
  (1) **The load-bearing fact is the filter, not a pullback**: every thread a
  cancellation rewrites ends in a state `passiveServerIdle` permits, so
  `passiveServerIdleFrame`'s own `¬ passiveServerIdleAllowed` hypothesis
  discharges it and the pullback fires only on threads the transition left
  alone.  That is why the frame primitive
  (`passiveServerIdleFrame_of_backward_of_not_allowed`) hands the backward
  obligation *both* discriminating hypotheses — the donation return needs the
  `.unbound` one for the caller it re-binds and the filter for the holder it
  unbinds.  (2) **`ipcStateQueueMembershipConsistent` is a hypothesis, and a
  substantive one**: it is what makes the abort *succeed*
  (`abortPendingIpcOnEndpoint_ok` — a thread blocked sending or calling names an
  endpoint that exists), and a refused abort leaves the holder exactly where the
  defect left it.  (3) **The footprint gained three members, not one**: the abort
  *splices*, so `lockSet_cancelIpcBlocking` names the holder's endpoint **and its
  two queue neighbours** (`cancelHolderBlockedEndpoint?`,
  `cancelHolderSpliceNeighbors?`, both resolved from `st` because the holder is
  resolved rather than supplied, and both gated on the abort's own guard).
  (4) **The bound is a case analysis, and since WS-OD OD3.5 an arm-selected
  one**: summed, the resolved footprint carries fourteen members (twelve before
  OD3.7's two below-head reads), and it fits because every resolver keys on
  `tcb.ipcState` — including, since OD3.5, the victim's own splice neighbours,
  which were the one member of the family that did not.  The widest arm is the
  reply arm, at **eight** after OD3.5 and **ten** since OD3.7
  (`lockSet_cancelIpcBlockingOnCore_size_le_ten` then; the live bound is
  `lockSet_cancelIpcBlockingOnCore_size_le_thirteen`); the endpoint arm is four and
  the notification arm two.  Before the OD3.5 split the reply arm declared two
  TCB write locks for a splice it does not perform, which also put it at ten —
  the same number for the opposite reason, so read the theorem rather than the
  figure.  New code adding a cancellation member states the arm it belongs to,
  not the sum.
- **The cancellation teardown IS the reply path's consume** (WS-RR RR8.5,
  v0.35.63).  The tree carried two spellings of "tear down the caller↔Reply
  link": the monadic `SystemState.consumeCallerReply` on the reply paths, and a
  pure pair of raw-insert helpers on the cancellation path, written because
  `cancelIpcBlocking` is a pure composition and could not run a `Kernel` step.
  They had parted on write order and on whether the writes went through
  `storeObject`'s bookkeeping, and every fact about one was proved a second time
  about the other.  Five things new code must respect.  (1) **The survivor is the
  monadic step, and its pure form is a projection, not a second body**:
  `SystemState.consumeCallerReplyLink st caller rid` is the one state
  `consumeCallerReply caller rid st` leaves — defined by matching on the step
  with the `.error` arm *eliminated* by `consumeCallerReply_isOk`, never
  defaulted to `st` — and `consumeCallerReply_eq_link` is the bridge.  A pure
  transition that needs the consume calls the projection; one that re-spells the
  two writes is the defect this closed, and Tier 3 refuses the retired names
  (`clearTcbReplyObject`, `clearReplyObjectCaller`) tree-wide.  (2) **Every
  cancellation-side fact is a corollary through the bridge.**
  `consumeReplyLink st tid tcb` is the projection under the victim's own
  `replyObject`, and `consumeReplyLink_preserves_objects_invExt`, `_tcb_lookup`,
  `_other_tcb_eq`, `_preserves_ipcInvariant`, `_sameSchedContextBindings`,
  `_passiveServerIdleFrame`, `_preserves_donationChainWellFormed` and
  `_preserves_projection_high` all keep their statements and are one application
  of the `consumeCallerReply_*` twin each; a new fact about the teardown is proved
  of the monadic step and read across, never of `consumeReplyLink` directly.  The
  two sharp pointwise readings that made this possible are new —
  `consumeCallerReply_tcb_caller` (the caller's key holds the pre-state TCB with
  `replyObject` cleared and nothing else moved) and `consumeCallerReply_tcb_other`
  (every other TCB-holding key is untouched), stated with no `rid`-distinctness
  hypothesis because the distinctness is derived from the store's contents.  (3)
  **The teardown writes through `storeObject` now, so a definitional lifecycle
  frame across the reply arm is false**: `cancelIpcBlocking_lifecycle_eq` and
  `consumeReplyLink_lifecycle_eq` are deleted rather than given a third
  hypothesis, and a caller needing the metadata across a cancellation needs a
  semantic frame, owed once, about `storeObject`.  (4) **The projection theorem
  reads index completeness**, because the reply path's
  `consumeCallerReply_preserves_projection` needs the (already-present) Reply's
  membership — so `consumeReplyLink_preserves_projection_high` takes
  `objectIndexSetComplete` and the reply arm's composite carries it from the
  return through the splice and the restore
  (`restoreToReadyStaging_preserves_objectIndexSetComplete`,
  `spliceThreadReplyFrameOut_preserves_objectIndexSetComplete`).  (5) **The
  census knows both**: `consumeCallerReplyLink` is a `chainWritePrimitives`
  entry — a pure transition reaching for it bare is WS-RM's defect in the other
  calling convention — and `consumeReplyLink` is registered as a site stating its
  chain result.  What the collapse *measured* and did not fix is the drift it is
  one instance of: sixty executable definitions still wrote the object table
  raw beside `storeObject`, registered with the measurement in
  [`docs/REGISTERED_DEBT.md`](../../docs/REGISTERED_DEBT.md) table C rather than
  absorbed into an M-sized row — and migrated from `v0.35.64` on, see the next
  bullet.
- **A kernel object is rewritten in place through `SystemState.rewriteObject`,
  and stored through `storeObject`** (`v0.35.64`, the raw-write migration's
  first cut).  The register's remedy for the raw writers — a pure `storeObject`
  projection — was the wrong primitive for the sites that matter: `storeObject`
  filters every capability reference and re-inserts into two more tables on
  every write, and an `RHTable` re-insert of an existing key is not structurally
  the identity without a no-resize hypothesis, so a scheduler tick spelled
  through it would pay on every quantum and every definitional field frame would
  become a conditional theorem.  `rewriteObject st id new h` takes a proof that
  the key holds an object of the **same, bookkeeping-neutral kind**
  (`rewriteAdmissible`, over `KernelObjectType.rewriteNeutral` — every kind but
  CNode and VSpace root, whose contents *are* bookkeeping, enumerated
  constructor by constructor) and its body is the bare insert; the proof is
  erased, so the executable is one table insert.  Five things new code must
  respect.  (1) **A lookup-then-write site is `updateTcb` /
  `updateSchedContext`** — a plain match on the **witnessed lookup**
  `getTcbWitnessed?` / `getSchedContextWitnessed?` (`v0.35.65`: `getTcb?`
  carrying its own equation, `Option { t // st.getTcb? tid = some t }`, matched
  on the store and erased to the value; `getEndpointWitnessed?` /
  `getNotificationWitnessed?` are the endpoint and notification twins since
  `v0.35.74`) whose witness is the rewrite's proof —
  or that witnessed lookup around `rewriteObject` with `rewriteAdmissible_tcb`
  (one such lemma per neutral kind) when the looked-up value is used for more
  than the write; never a raw `objects.insert`, and never a dependent
  `match h : st.getTcb? tid with`: a dependent matcher's discriminant occurs in
  its own motive, so no consumer proof can rewrite it, and `v0.35.64`'s
  `updateTcb` was spelled that way for exactly one cut.  A Tier 3 negative holds
  the migrated files to it.  (2) **A key that may hold nothing, or a CNode or VSpace
  root, is a store**: `storeObject` in a `Kernel` step, `withObjectStored` in a
  pure transition — the RR8.5 projection with the error arm eliminated by
  `storeObject_isOk`, bridged by `storeObject_eq_withObjectStored`.  (3) **The
  bookkeeping is unchanged by theorem, once**:
  `rewriteObject_preserves_objectIndexSetComplete`,
  `rewriteObject_preserves_objectIndexLive`,
  `rewriteObject_preserves_objectIndexBounded`,
  `rewriteObject_preserves_objectIndexSetSync`,
  `rewriteObject_preserves_objectTypeMetadataConsistent` in `Model/State.lean`,
  `rewriteObject_preserves_asidTableConsistent` in
  `Architecture/VSpaceInvariant.lean`, `rewriteObject_preservesFieldsOutside`
  against the one-field `rewriteObject_modifiedFields` in
  `Kernel/CrossSubsystem.lean`, and `rewriteObject_eq_objects_update` for any
  field with no named frame — each instantiated on `updateTcb` and
  `updateSchedContext`.  A site proof reaches for these rather than re-deriving
  the fact from `RHTable.insert_preserves_invExt`.  (4) **The proof recipe is
  two equations**: `cases hT : st.getTcb? tid`, then `updateTcb_eq_of_some hT`
  or `updateTcb_eq_self_of_none hT`, and the old proof continues verbatim;
  `updateTcb_getTcb?_self` is the read-back.  A site that matches on the
  witnessed lookup itself reduces under `simp only [site,
  getTcbWitnessed?_eq_some hT]` (or `_eq_none`), and after a `split` its arm
  carries **three** inaccessibles — the value, the witness, the match equation —
  so it is `rename_i tcb hTcb _`, never the two-name `next tcb _` of the old arm,
  which binds the witness to the value's name and fails one line later at the
  record update; `rewriteObject_objects` exposes the insert to a proof that
  reads the table directly.  **The case split precedes the unfold**
  (`v0.35.66`): `cases hT : st.getTcb? tid` over a goal that already holds the
  unfolded witnessed match fails to generalise, because the lookup's *type*
  mentions `st.getTcb? tid` — so a proof cases on the typed lookup first, then
  unfolds the site and rewrites with `getTcbWitnessed?_eq_some hT` /
  `_eq_none hT`; a hypothesis `hStep : site st = .ok …` is rewritten the same
  way and then `dsimp only [SystemState.rewriteObject] at hStep` restores the
  literal the old proof read.  (5) **A twin migrates with its
  original.**  `cancelBoundDonationOnCore` is held to `cancelBoundDonation` by a
  `rfl` bridge, so it moved in the same cut; the private copy of
  `restoreToReadyOnCore`'s prefix that `PriorityInheritance/PerCore.lean` pinned
  by `rfl` was deleted instead, and the operation is now *defined* through the
  public `restoreToReadyMidState` — a pin between two spellings of one prefix is
  the signal to make one of them the definition.  The R5.D shim
  `clearTcbIpcFields` and its theorems went in the same cut, having no consumer.
  The same signal closed the single-thread PIP boost update at `v0.35.66`:
  `updatePipBoost` and `updatePipBoostOnCore` were two copies of one body
  differing in the literal core, held together by an `rfl`, so the single-core
  name is now *defined* as the per-core update at `bootCoreId` and
  `updatePipBoost_eq_updatePipBoostOnCore_bootCore` stays as the equation
  consumers rewrite with — definitional, and still the fact that the two cannot
  diverge.  What is still raw is registered with its measurement (65 sites in 52
  executable declarations across 22 files after `v0.35.64`; 60 in 47 across 22
  after `v0.35.65` moved the scheduler's context-save family —
  `saveOutgoingContext`, `saveOutgoingContextChecked`,
  `saveOutgoingContextOnCore`, `preemptCurrentOnCore` — and
  `setThreadCpuAffinity`; **53 in 41 across 20** after `v0.35.66` moved
  `enqueueRunnableOnCore`, `updatePipBoostOnCore`, `timerTick`,
  `refillSchedContext` and `handleYieldWithBudget`; **43 in 37 across 17** after
  `v0.35.67` moved `timerTickBudget`, `timerTickBudgetOnCore`,
  `enqueueIdleThreadOnCore` and the trace model's `stepPost`; unchanged at
  `v0.35.68`, which migrated no site but *derived* the boot's idle install from
  `enqueueIdleThreadOnCore`, so the boot performs no raw write of its own
  through it; **39 in 33 across 15** after `v0.35.69` made the four
  register-context writers — `writeReturnFrameToTcb`, `writeRestartFrameToTcb`,
  `writeFfiRegistersToTcb`, `writeFaultRegistersToTcb` — the `updateTcb` each
  already had the shape of; **32 in 26 across 13** after `v0.35.70` moved the
  fault path's seven — `recordPendingFault`, `applyFaultRestart`, the four
  fail-closed dispositions over their deschedule, and `installFaultHandler`
  taking the store's witness for the TCB it is handed; **19 in 19 across 10**
  after `v0.35.71` moved the SchedContext operations and the priority
  management — `updatePrioritySource`, `setMCPriorityOp`,
  `setMCPriorityOnCore`, `schedContextConfigureBoundPropagate`,
  `schedContextBind`, `schedContextUnbind`, `schedContextYieldTo`; **16 in 16
  across 8** after `v0.35.72` moved the cross-core suspend's G6, the revoke
  sweep's step and the destroy path's origin scrub — `suspendThreadOnCore`,
  `revokePendingTransfersStep`, `clearDonationOriginReferences`; **9 in 9
  across 6** after `v0.35.73` made the seven inhabitation witnesses the
  store on each fresh key and the rewrite on the bind's two in-place writes
  — `witnessSt1`–`witnessSt4`, `chainWitnessSt1`, `chainWitnessSt2`,
  `donationChainWitness`; **5 in 5 across 4** after `v0.35.74` moved the two
  queue sweeps — `removeFromAllEndpointQueues`,
  `removeFromAllNotificationWaitLists` — onto the witnessed lookup around
  `rewriteObject`, and those five are the primitives that should be raw:
  `storeObject`, `rewriteObject`, `Builder.createObject`, `updateObjectAt`
  and the frozen store, so the executable population outside them is
  **zero**; since `v0.35.75` the trace harness's 61 fixture inserts are
  stores too, so over the whole `SeLe4n/` tree the only raw writes in the
  spellings that census recognises are those five and the reply-stack
  census's planted witness — and since `v0.35.76` that is **enforced**:
  `STORE_WRITE_CODE` is a Tier 0 `ZERO_METRICS` entry, those six bodies are
  `WRITE_PRIMITIVE_BODIES` (seven since `v0.36.6`, whose `retireCarvedObject` —
  `retireFrame` until `v0.36.8` — is the one primitive that erases a key), reconciled in both directions, and a raw write
  reappearing in an executable position fails on the day it is written.
  **Six executable writes and four reads are outside those spellings** and
  were outside this ledger until `v0.35.117` measured them: a declaration
  that holds the object table through a binding or a parameter is invisible
  to a pattern keyed on the receiver text `.objects`, and three of them do
  — see *both zeros are over the DIRECT spellings* in the key-conventions
  section above for the population, the floor that now reports it, and the
  named architecture for driving it to zero).  At `v0.35.77` (D2)
  `storeObject`'s capability-reference maintenance became an erase over the
  displaced CNode's populated slots rather than a filter over the whole
  table, and the register row was **closed**; what landing it found — the
  table was read by no executable code, and `capabilityRefMetadataConsistent`,
  the invariant named for it, read the object store instead, so it was
  definitionally true and its `storeObject` preservation proof consumed no
  hypothesis — is closed at `v0.35.78` by **retiring the table** (the
  *capability-reference table* bullet below).  (6) **A transition that rewrites a TCB it is
  handed takes the store's witness for it.**  `timerTickBudget` /
  `timerTickBudgetOnCore` (`v0.35.67`) take `(hTcb : st.getTcb? tid = some tcb)`
  beside the TCB — the proof `rewriteAdmissible_tcb` consumes, erased at runtime —
  so a caller cannot charge a TCB the store does not hold (both suites did, with a
  TCB fabricated at an unstored id, and the tick then wrote it into the store);
  every caller resolves the thread through `getTcbWitnessed?` and hands the
  witness on.  A consumer statement carries it as an implicit
  `{hW : st.getTcb? tid = some tcb}` beside its `hStep` — positional applications
  are unchanged, and a pre-state hypothesis of the same type stays revertible,
  the two being interchangeable by proof irrelevance — an arrow-chain hypothesis
  names its binder (`∀ (hTcb : …), timerTickBudgetOnCore … tcb hTcb = .ok … → …`),
  and a `split` on the witnessed SchedContext match yields three inaccessibles,
  `rename_i sc hSc _`, in the bullet form as well as the bare one.  (7) **A
  dependent match lives in a definition whose state is a parameter, never inline
  under a `let`.**  Lean elaborates a `let` whose body's type does not depend on
  it as a `have`, and a dependent match — one whose alternative's type names the
  scrutinised state, which every witnessed lookup is — under a `have` binder, or
  over a stuck projection, is opaque to definitional unification: two spellings
  of one match tree unify only when the state is a variable.  Measured
  (`v0.35.67`, eleven isolated experiments): with the witnessed lookup inline,
  `timerTickOnCore_eq_prepared`'s `rfl` failed on every restatement but a
  verbatim copy of the body, a phase definition over the prepared triple failed
  the same way, and a `split`-based proof splits the two sides independently.
  `timerTickChargeCurrentOnCore` is the shape — the dependent match over a
  parameter, the tick's own match tree non-dependent, the equation `rfl` — a
  consumer reads through `timerTickChargeCurrentOnCore_eq` / `_none` / `_ok`,
  and Tier 3 refuses any lookup coming back into the tick's body.  (8) **A
  transition that rewrites two objects performs the first under the witness
  its own lookup carries and the second through the typed read-modify-write
  over the rewritten state** (`v0.35.71`).  A witness taken at the pre-state
  does not carry across a rewrite without `invExt`, which executable code has
  no proof of — so `schedContextBind` writes the SchedContext through
  `rewriteObject` under `hSc` and then the TCB through `st1.updateTcb`, and
  the lambda's record is the stored one with its fields moved, which is what
  the raw insert wrote from the pre-state lookup on every state the two
  lookups admit.  The proofs reduce the pair once, from the pre-state's
  witness and `invExt` (`updateTcb_after_rewriteObject_schedContext` and its
  three siblings), on the lemma library that makes the reduction a fact
  rather than a case split: a SchedContext rewrite is invisible to every TCB
  lookup at *every* key (`rewriteObject_schedContext_getTcb?` — at the key
  itself the admissibility witness says it held a SchedContext, so no TCB
  lookup read it), the twin, the typed read-modify-writes inheriting both,
  and the keys of two typed witnesses distinct with no invariant consulted
  (`getTcb?_getSchedContext?_keys_distinct`).  Where the second write sits on
  a state that is a scheduler-only update of the pre-state, the stage is
  spelled `{ st with scheduler := … }` so its object table is the pre-state's
  *definitionally* and the witness needs no transport at all
  (`schedContextUnbind`).  Two things that cut measured.  A `_` field in a
  `{ s with x := _ }` pattern is filled from `s`, not left as a hole, so a
  reduction whose base state must be read off the goal is applied with
  `exact` rather than `rw`.  And a hypothesis a raw insert needed can be one
  the typed rewrite makes false to need:
  `updatePrioritySource_donated_preserves_donor_schedContext` lost
  `tid.toObjId ≠ scId.toObjId`, because the rewrite fires only at a key
  holding a TCB and reaches no SchedContext at any key — the one way that
  security statement could have been vacuous is gone with the hypothesis.
- **There is no capability-reference table** (`v0.35.78`, closing the row
  `v0.35.77` registered).  `LifecycleMetadata` is the object-type table alone,
  `lifecycleInvariantBundle` is `objectTypeMetadataConsistent` under two names
  (`lifecycleIdentityTypeExact`, `lifecycleIdentityAliasingInvariant`),
  `IntermediateState.hLifecycleConsistent` is that predicate of the builder
  state, and a slot's target is read through `lookupSlotCap` — the one
  slot-target reader, `O(1)`, which yields the whole capability.  The register
  row's remedy said *wire or retire, and the rule says wire*; the decision was
  **retire, on measurement**.  `lookupCapabilityRefMeta`, the reader the table
  was named for, had been `(lookupSlotCap st ref).map Capability.target` since
  the repository's root, so no executable code had ever read the table; every
  slot-target query in the tree holds or fetches the CNode already; the one
  consumer the remedy proposed — a revocation sweep over a *target* — is a
  target→slots question a table keyed by slot cannot answer; the boot builder
  installed populated CNodes without ever populating it; the frozen mirror
  never maintained it; and every CNode store paid a fold over the CNode's slots
  for it.  A cache nothing reads is not a cache, and *implement the
  improvement* has no improvement to implement when no reader can be named.
  Four things new code must respect.  (1) **A conjunct whose proof consumes
  no hypothesis is deleted, and so is everything stated over it**:
  `capabilityRefMetadataConsistent`, the bundle-of-one
  `lifecycleMetadataConsistent`, the lifecycle capability-reference and
  stale-reference families (`lifecycleCapabilityRefExact` through
  `lifecycleIdentityStaleReferenceInvariant`), the capability layer's
  `lifecycleCapabilityStaleAuthorityInvariant`, the policy surface's
  owner-authority implication (`policyOwnerAuthorityRefRecorded →
  policyOwnerAuthoritySlotPresent`) and the builders' `withLifecycleCapabilityRef`
  — each an instance of `x = x`, of lookup determinism or of
  `objectTypeMetadataConsistent` — with Tier 3 refusing every name tree-wide.
  (2) **`storeObject`'s lifecycle write is the object-type insert alone**, so
  a CNode store is `O(1)` on the lifecycle side rather than a fold over its
  slots, and `allTablesInvExtK` is **sixteen** conjuncts: the positional
  projections in `Builder.lean`, `Boot.lean`, `FreezeProofs.lean` and
  `IdleEnqueue.lean` shifted by one at every position past the sixth, which
  is the fragility their docstrings already record.  (3) **The capability
  operations store once**: `cspaceInsertSlot`, `cspaceRevoke` and
  `cspaceMutate` end in `storeObject`, `cspaceDeleteSlotCore` in the store
  then `detachSlotFromCdt`; the second writer `storeCapabilityRef` and the
  fused `revokeAndClearRefsState` are gone, and a proof over one of these
  operations is one `storeObject_*` frame lemma rather than a composition of
  two.  (4) **The one substantive fact the layer had restated is owned where
  it always was**: a reply cap is backed iff its Reply resolves, which is the
  capability layer's step-preserved `replyCapPointsToValidReply`, exhibited
  by `replyCapPointsToValidReply_distinguishes_backed_and_dangling`.
- **A state-resolved thread is descheduled where the state PLACES it** (WS-RR
  RR8.6, `v0.35.79`).  `descheduleThread`, `cancelIpcBlockingOnCore` and
  `suspendThreadOnCore`'s G4 removed a victim at `determineTargetCore` — its
  *home*, which is where a wake places a thread and not where a removal finds
  it: `preemptCurrentOnCore` re-enqueues a preempted thread on the core that ran
  it, and an unpinned thread may run on any core, so a `.tcbSuspend` on an
  unpinned thread preempted on a secondary core marked it `.Inactive` and left
  it in that core's run queue.  Five things new code must respect.  (1) **One
  primitive, one resolver**: `descheduleAt st tid placed` removes at a
  pre-resolved placement and `descheduleAtPlacement st tid` *is*
  `descheduleAt st tid (placedCoreOf? st tid)`; a transition that must declare
  its footprint before it runs captures `placedCoreOf?` on the pre-state and
  removes through `descheduleAt` (the suspend), one that acts after other steps
  resolves at the state it acts on through `descheduleAtPlacement` (the reply
  path, the cancellation composite).  Tier 3 refuses `determineTargetCore` and a
  bare `removeRunnableOnCore` inside each of the three declarations.  (2) **The
  poke reads the same placement** (`descheduleSgi?`): the placed core, when the
  thread is current there and it is not the executing core — and no object.
  The wake's ghost-guard is not mirrored, because a removal takes a placed thread
  off its core whether or not a TCB backs it, so a guard on the TCB would clear a
  slot and poke nobody.  (3) **The composite is `descheduleThread` on the
  reclaim's post-state by `rfl`**, and the footprint is declared on the
  pre-state; `cancelIpcBlockingReclaimed_placedCoreOf?_victim` is the relation
  (the victim's post-reclaim placement *is* the pre-state's — an equation since
  `v0.35.158`, where the wake's degenerate self-insert had left it a
  disjunction) and `cancelIpcBlockingOnCoreSchedLockSet_covers_deschedule` is
  its payoff.  (4) **The scheduler footprints take the placement**:
  `descheduleThreadLockSet (placed : Option CoreId)`,
  `cancelIpcBlockingOnCoreSchedLockSet (placed holderPlaced : Option CoreId)`,
  and `suspendThreadOnCoreSchedLockSet (home
  executingCore ownerHome outerHome : CoreId) (placed : Option CoreId)`, whose
  run-queue segment is a *pair* over the placed and executing cores — the home
  stays a replenish member, since the `.bound` arm's purge is keyed on it, and
  the running core needs no member of its own.  (5) **A theorem about a
  deschedule is stated at the placement, never at the home**:
  `descheduleThread_fully_descheduled` takes single placement (which the
  scheduler maintains by construction) where it took the home-placement
  discipline (false of exactly the thread the defect is about), and
  `suspendThreadOnCore_sgi_remote_reschedule` concludes `runningCoreOf? = some c`
  because a victim current nowhere now falls back to the executing core, where
  no SGI can arise.  The retired reading survives in one place,
  `tests/SmpCancellationSuite.lean` §3.24's `retiredHomeAndRunningDeschedule`,
  computed beside the live one on the queued-off-home shape.
- **A donation pop's deschedule names the thread the pop UNBOUND** (PR #897
  review, `v0.35.149`).  Every production pop makes the answered frame's head
  context's own `boundThread` `.unbound`, and the step that follows must be about
  *that* thread: `applyReplyDonation` and `applyReplyDonationOnCore` always were,
  and `replyRecvPostReceiveDonation` was not — it descheduled
  `recordedReplyServer?`, the server the answered caller recorded when it
  *Called*.  WS-HP HP4 (`v0.35.38`) repointed the **trigger** onto the frame and
  left the **deschedule** on the binding-era proxy; HP6.8 (`v0.35.45`) is what
  makes the two disagree, because a spliced middle caller leaves an **orphan
  head** whose context is bound to a thread the caller never recorded.  Measured
  on the live `replyRecvBody`: the holder ended `.unbound` and still queued
  (`hasSufficientBudget` is unconditionally `true` for an unbound thread, so it
  runs at its legacy TCB band charged to no reservation — PR #895 round 8's
  defect on the sibling site that round did not sweep), while a bystander still
  holding its own reservation was taken off its run queue and left `.ready`,
  which WS-OD OD1.7 enumerates as unrecoverable.  Four things new code must
  respect.  (1) **The holder travels inside the arm selector**:
  `replyRecvPopDonation` answers `Option (SchedContextId × ThreadId)`, so a
  consumer cannot hold the context and the holder apart and hand the deschedule a
  different thread; `replyRecvPopDonation_holder_eq_frameHead` is the relation,
  and `replyRecvServerDeschedule` / `replyRecvPoppedContext` are refused
  tree-wide.  (2) **Two threads, two questions**: both deschedule arms name the
  holder and both chain walks keep `recordedServer`, because the walk keys on
  waiters rather than on donations (WS-HP HP7's reason for keeping that
  resolver).  (3) **The idle-state obligation moved with the thread** —
  `hHolderIdleAllowed`, conditioned on the pair the pop returned rather than
  stated unconditionally at a proxy, in the transition's own theorem and in both
  dispatch packs.  (4) **The cancellation reclaim deschedules too, since
  `v0.35.158`** — it was the one pop that ENQUEUED (WS-OD OD1.7), on the
  reasoning that `abortPendingIpcOnEndpoint` stages `Architecture.timeoutFrame`
  into the holder's register context (WS-RR RR7.14) and the kernel owes it a
  delivery it can only observe by running.  It still owes it, and the frame still
  waits in the register context; what changed is *who* pays for the run — the
  holder's next reservation, through its manager's resume or a bind, rather than
  nobody's budget.  All four production pops now take the thread they unbind off
  its placement (`descheduleUnboundHolder`); see the bullet below for what is
  left.
- **A reclaimed holder no longer runs unbudgeted — the reclaim parks it**
  (PR #897 review, `v0.35.149`; the reclaim half **closed at `v0.35.158`**, the
  bind half WS-CB's).  `.unbound` in this kernel means *both* "MCS-passive" and
  "legacy time-sliced at `tcb.priority`": `hasSufficientBudget`'s `.unbound` arm
  is `true` by design, `timerTickBudgetOnCore`'s refills `configDefaultTimeSlice`
  forever, and `schedContextUnbind` deliberately re-buckets an unbound thread.
  So a reclaim that returned the reservation *and* left the holder placed handed
  it the CPU on nobody's budget — measured on the live `suspendThreadOnCore`
  at `v0.35.149`: after a `.tcbSuspend` of a reply-blocked client whose donated
  context was held by a server blocked on a nested call, the server ended
  `.unbound`, `.ready`, **on its home core's run queue**, `hasSufficientBudget =
  true`, at its own TCB band, selected by `chooseThreadOnCore`; and a server
  merely *queued* on the donated context stayed queued, unbound, because OD1.7's
  wake declined a placed thread.  `passiveServerIdle`'s antecedent is *not
  queued*, so a runnable unbound thread satisfied it vacuously — PR #895 round
  8's rule, on the conjunct that rule was written about.  Since `v0.35.158` the
  reclaim takes the holder it unbinds off the scheduler
  (`descheduleUnboundHolder`, the bullet on the reclaim above) and
  `suspendThreadOnCore_holder_unplaced` carries that to the end of the live
  pipeline, so a suspension of the *client* — authority over the client, none
  over the server — no longer puts the server outside CBS admission.  What it
  costs is stated: a passive server whose client is suspended while it services
  the request is parked `.ready`, `.unbound` and unplaced until its own manager
  resumes it or a reservation is bound to it, which is the MCS-passive reading
  and the one every other pop takes.  **And since `v0.35.182` (Cut B2) the bind
  is that manager's recovery**: `schedContextBind` places a parked runnable
  thread on its home core, which is seL4-MCS's `schedContext_bindTCB` tail
  (`if (isSchedulable(tcb)) { SCHED_ENQUEUE(tcb); rescheduleRequired(); }`, read
  at `13.0.0`) and which this kernel did not do — it re-bucketed only a thread
  already queued, so what the reclaim parked stayed parked.  Four things new
  code must respect.  (a) **The guard is `bindPlacesParkedThread`**, four
  conjuncts excluding a placed thread, a thread blocked in IPC, a suspended one
  and — since `v0.36.1`, (d) below — a reservation with no budget left, and its
  third reads the **stored** `threadState` rather than `inferThreadState` —
  which answers `.Inactive` for *any* unplaced, unblocked thread, so the
  inferred reading would refuse exactly the parked shape the guard exists to
  admit.  (b) **The declared footprint did not move**: its run
  segment was already the bound thread's home core, which is the core the
  placement inserts on — a declaration written for the *operation* rather than
  for the branch it happened to take is what makes a behavioural widening free,
  and both that footprint's docstring and its coverage theorem's, which
  predicted a widening, are corrected rather than left standing.  (c) **The
  frozen mirror is swept through a bind-specific writer**
  (`frozenWriteTcbBoundPlaced`), never by widening `frozenWriteTcbRebucketed`:
  that one's other callers are priority writes, and a priority write must not
  make a parked thread schedulable — only a bind, which hands the thread a
  reservation, may.  (d) **A bind places a thread only on a reservation that can
  run it** (PR #900 review, `v0.36.1`).  The fourth conjunct is
  `sc.budgetRemaining.isPositive` of the reservation being bound, which is the
  selector's own reading — `hasSufficientBudget` of a bound thread *is* that
  (`bindPlacesParkedThread_budget_eq_hasSufficientBudget`) — and seL4-MCS's:
  `isSchedulable` requires an active context and `schedContext_resume` postpones
  a thread whose refill is not ready, both read at `13.0.0`.  Without it a
  reservation exhausted mid-period, then unbound — which keeps `budgetRemaining`
  and purges the per-core replenish entry — and rebound to a parked thread put
  that thread on a run queue the selector skips forever, since nothing is left
  to refill it; `budgetPositiveOnCore` was false on the bind's post-state and
  the bind reported success.  With it the thread stays parked
  (`schedContextBind_leaves_unplaced_of_exhausted`), and the frozen mirror
  (`frozenBindPlacesParkedThread`) carries the same conjunct.  **What it does
  not do is postpone**: seL4 re-derives the refill trigger at every
  `schedContext_resume`, and this kernel re-derives it nowhere, so the parked
  thread waits for its manager (unbind, configure, rebind), and the same
  trigger-less state is reachable through the re-bucket arm, a resume of a
  bound thread and a configure that places nothing — all inherited from `main`,
  registered in `docs/REGISTERED_DEBT.md` table C, owner WS-CB.  New code must
  not read a successful bind as evidence that the thread will run.

  **One instance of the class remains**, measured by the post-merge audit
  (`v0.35.156`): a plain-`Send` rendezvous is decided by the two readings on two
  arms — `.replyRecv`'s non-`Call` arm deschedules the holder the pop unbound
  (the MCS-passive reading, so a passive server handed a plain `Send` is parked
  `.ready`, `.unbound` and unplaced), while a `.receive` by an already-unbound
  running thread leaves it current on a plain `Send` (the legacy reading).  That
  is the WS-CB row in `docs/REGISTERED_DEBT.md` table C; it is not a soundness
  gap, and it is not fixed here because it is the passive/legacy split that row
  names rather than a footprint or a placement.  **v1.0.0 may claim, since
  `v0.35.158`, that no client suspension hands a server the CPU on nobody's
  budget, and since `v0.35.182` that a parked passive server is recovered by
  binding it a reservation.**
- **A bare reply's post-state does not satisfy `donationOwnerValid`.**
  `endpointReply` wakes the answered caller `.ready` while the recorded server
  still holds `.donated _ caller`; the donated SchedContext comes back only at
  the next stage, because the server needs that budget *while* it replies (the
  AUD-3 ordering).  The honest statement about that state is
  `ipcInvariantFullExceptDonationOwner st target` — the bundle with
  `donationOwnerValid` relaxed at the woken caller — which
  `endpointReply{,OnCore}_preserves_ipcInvariantFullExceptDonationOwner`
  establishes unconditionally, and which the donation return upgrades back
  (`returnDonatedSchedContext_establishes_donationOwnerValid_of_except`).  The
  composite that covers the whole chain is
  `endpointReplyCrossCoreDispatch_establishes_ipcInvariantFull`.  New code must
  not assume `ipcInvariantFull` of a state between a reply and its donation
  return, and must not add a bundle theorem that threads `donationOwnerValid` on
  such a state: it would be vacuous rather than conditional, which is how the
  nine pre-RR3.12 reply bundles asserted nothing on the ordinary seL4-MCS path.
- **...and the bare reply and the leg the kernel dispatches disagree about
  delegated authority** (PR #895 review round 22).  `endpointReplyOnCore` dropped
  the `replier == expected` gate at PR #822 review 6J-lYm — authority is the
  presented reply capability, which the dispatch resolves, and seL4-MCS reply
  caps are delegatable — while the **bare** `endpointReply`, `endpointReplyRecv`
  and the single-core `endpointReplyWithDonation` that composes the first still
  carry it.  The live `.reply` arm routes through
  `replyTransferOnCoreChecked` → `endpointReplyCrossCoreDispatch`, so **the
  kernel admits a delegated reply-cap holder and the single-core composites
  refuse one**, whatever `endpointReplyOnCore`'s "mirrors the single-core
  `endpointReply`" wording suggests.  Two things new code must respect.  (1) The
  divergence is pinned in both directions —
  `endpointReplyCrossCoreDispatch_independent_of_replier` (every use of `replier`
  is the unused `_replier`, so a delegate gets the non-delegated behaviour) and
  `endpointReplyWithDonation_refuses_delegated_replier` — so a coverage claim, a
  refinement or a mirror must name *which* spelling it is about; `frozenBranchLiveLeg`
  and `frozenBranchLiveOperation` carry the frozen surface's counterparts as data
  for exactly that reason.  (2) The direction is fail-**closed** (legitimate
  authority declined, never illegitimate authority admitted) and the single-core
  composite has no production caller, so this is a divergence to respect rather
  than a hole; giving the question one answer is registered debt.
- **A bare endpoint splice's post-state does not satisfy
  `ipcStateQueueMembershipConsistent`.**  `endpointQueueRemoveDual` takes a
  thread out of its endpoint queue and deliberately does **not** touch that
  thread's `ipcState`; the composites that use it write it in their very next
  step (the bound delivery makes it `.ready`).  So the honest statement about
  that state is `ipcInvariantFullExceptMembership st' tid` — the bundle with the
  membership conjunct relaxed exactly at the removed thread — which
  `endpointQueueRemoveDual_establishes_ipcInvariantFullExceptMembership`
  (`IPC/Invariant/QueueSplicePreservation.lean`) establishes from
  `ipcInvariantFull`.  It stands to the splice as
  `ipcInvariantFullExceptDonationOwner` stands to the bare reply, and new code
  must not state a splice bundle threading the **full** membership conjunct on
  the post-state: that would be vacuous rather than conditional.  Three further
  things the module fixes in place.  (1) **The four-branch case analysis is
  derived once**, as `SpliceShape`: which program `endpointQueueRemoveDual` is
  depends on whether the removed thread is the queue head and whether it has a
  successor, and that is a property of the *operation*, not of the conjunct — a
  new conjunct proof consumes the four branches rather than re-running `unfold`.
  (2) **One conjunct genuinely does not follow from the bundle**:
  `splicePredecessorBlocked`, the fact that a predecessor promoted to tail is
  blocked on that endpoint.  `queueNextTargetBlocked` propagates blockedness
  *forwards*, the head conjunct constrains only the head, and link integrity
  says nothing about `ipcState` — so it is stated, vacuous when the removed
  thread is the head, and discharged from a reachability witness through
  `spliceSideBlocked_along_path` (*every thread reachable from a queue head is
  blocked on that endpoint* — the fact `queueNextTargetBlocked`'s own docstring
  promised and nothing stated).  (3) **`endpointQueueNoDup` is a consequence,
  not an obligation**: `endpointQueueNoDup_of_dualQueue_of_headBlocked` derives
  it from the dual-queue invariant and the head conjunct, so a transition need
  not re-establish it separately.
- **A woken caller's post-state does not satisfy `replyCallerLinkage`, and
  asking for the full bundle *and* the wake is asking for nothing** (WS-RR
  RR8.7, `v0.35.80`).  The third relaxed view, and the one whose absence had
  produced two **vacuous** production theorems.
  `consumeCallerReply_preserves_ipcInvariantFull` and
  `removeCallerReplyFrame_preserves_ipcInvariantFull` each took
  `ipcInvariantFull st` together with "st's answered caller is not
  `.blockedOnReply`", and `replyCallerLinkage`'s second direction refutes that
  pairing outright — a stored Reply naming a caller obliges that caller to be
  reply-blocked, so the bundle *entails* that no woken thread is still named.
  Their premises held on **no state**; they asserted nothing while their names
  read, in a bundle search, exactly like coverage.  Six things new code must
  respect.  (1) **The refutation is pinned, permanently**:
  `replyCallerLinkage_refutes_woken_linked_caller` derives `False` from the two
  premises, is consumed by nothing, and is anchored in Tier 3 for that reason —
  a refutation nothing states is one the next cut re-discovers by shipping the
  defect again.  Two Tier 3 negatives refuse both retired spellings tree-wide,
  each mutation-tested by reintroducing the name as **code** (the tombstones
  mention them in prose, which the code view strips, so the clean tree
  exercises the other direction).  (2) **The relaxation is the narrowest one
  that admits the state.**  `replyCallerLinkageExcept st woken` still requires
  the reciprocal pair to *exist* at the woken thread — the Reply resolves and
  the thread names it back — and drops only the blocking clause, written as a
  **disjunct** (`tid = woken ∨ ∃ ep rt, …`) rather than by excusing the thread
  from the clause.  Excusing it would drop the pair too, and the pair is
  precisely what the teardown reads.  (3) **The unit is the pair, not either
  half.**  `restoreToReadyStaging` wakes the victim and so *breaks*
  reciprocity, leaving `ipcInvariantFullExceptReplyLinkage` and nothing
  stronger; the teardown alone would break the third clause, since it clears
  `replyObject` without unblocking.  Each is the other's repair, so
  `restoredAndConsumed` — the composition the reply arm performs — is what
  carries the full bundle (`restoredAndConsumed_preserves_ipcInvariantFull`), and
  a claim taken at either half is a claim about a state the arm does not rest
  at.  (4) **A relaxed view is registered with the de-threading gate**, in
  `PRE_STATE_PREDICATES`, longest-prefix-first — otherwise the gate reads the
  relaxed bundle's own hypothesis as a threaded post-state conjunct.  (5) **The
  removal's own bundle statement is the *relaxed* one, and since `v0.35.188` it
  exists** (`removeCallerReplyFrame_establishes_ipcInvariantFull_of_exceptReplyLinkage`).
  What it needed was a **unit** at which the relaxation could be transported:
  `replyCallerLinkageExcept` was a flat triple, so no `replyLinkageFrame` could
  carry it and the splice would have had to re-run the full store's case
  analysis.  It is now split exactly as `replyCallerLinkage` is — the reciprocal
  pair (`replyCallerLinkageReciprocalExcept`) and `blockedOnReplyHasReplyObject`
  — so `replyCallerLinkageReciprocalExcept_of_frame` is its full sibling one
  strength down, and the store's own frame member
  (`storeObject_reply_caller_replyLinkageFrame`, which the family lacked because
  its neighbour excludes a Reply on purpose) carries it.  Three things new code
  must respect.  **Everything but the reciprocal pair is proved once**
  (`storeObject_reply_stackLinks_preserves_nonReciprocal`) and assembled twice,
  because the two bundles differ in the pair and nowhere else.  **The splice's
  store chain has one owner** (`spliceReplyFrameOut_transport`, over any
  predicate a caller-preserving Reply store carries): which stores run, in what
  order, with which lookups surviving between them is a fact about the
  *operation*, and a second copy per bundle is how the two would come to disagree
  about it.  And **the composite's hypotheses are all about the state the removal
  runs on** — the answered Reply's survival and the woken caller's TCB's are
  discharged inside it, not pushed onto a caller reasoning about a state the
  operation does not rest at.  Its premises are jointly satisfiable and that is
  *exhibited*: `restoredAndConsumed_preserves_ipcInvariantFull` already supplies
  the relaxed bundle and the caller's non-`.blockedOnReply`-ness at one state,
  which is exactly the pairing the deleted theorem could not have.
  (6) **The class was named at `v0.31.154` and not swept.**
  `REPLY_OBJECTS_COMPLETION_PLAN.md`'s own landed note re-based
  `linkCallerReply_preserves_ipcInvariantFull` because "full `ipcInvariantFull
  st` would be *vacuous* at a link site" — and left the sibling `consumeCallerReply`
  threading the post-state, one clause away, with the same contradiction
  available.  RR8.5 then turned that post-state threading into a *pre*-state
  hypothesis, which moved the vacuity from the conclusion into the premises
  rather than removing it.  **When a cut records that a bundle would be vacuous
  at one site, ask the same question of every operation that writes the same
  field** — and note that de-threading a conjunct can *preserve* a vacuity by
  relocating it.
- **The `.call` chain's IPC bundle is staged; every other live-arm bundle is
  production.**  RR2 (v0.34.42) gave the transitions behind `Kernel/API.lean`'s
  SMP dispatch `_preserves_ipcInvariantFull` theorems, and the RR2 closure audit
  split them by what they actually read: only
  `endpointCallCrossCoreDispatch`'s bundle
  (`SeLe4n/Kernel/IPC/CrossCore/DispatchInvariant.lean`) composes the staged
  `EndpointCallInvariant` surface and is staged with it — CI builds it on every
  PR through `Platform.Staged`; a linked kernel image does not.  The `.reply`
  chain's (`IPC/CrossCore/EndpointReplyDispatchInvariant.lean`), the
  priority-inheritance walk's (`IPC/Invariant/DonationPreservation.lean` §8),
  the send/receive/stash/wait and `replyRecvReturnDonation` bundles are all
  production (`EndpointReplyInvariant` always was — the first staging rationale
  misnamed it).  Production code must not cite the call chain's bundle.  RR3.22 (v0.34.43)
  closed two of the four gaps this bullet used to list: the `replyRecvBody`
  three-stage composite (`replyRecvBody_preserves_ipcInvariantFull`,
  `IPC/Invariant/DispatchPayoff.lean`, staged with the payoff tier) and the
  `Architecture.stage*` return-frame writes
  (`IPC/Invariant/DispatchArmPreservation.lean`, production).  **All three
  `cancelIpcBlocking` arms are covered since RR8.7 (`v0.35.82`)**, each in its own
  production module: the **blocked-on-endpoint** arm at v0.34.95
  (`cancelIpcBlocking_endpointArm_preserves_ipcInvariantFull`,
  `SeLe4n/Kernel/Lifecycle/Invariant/CancellationQueueShape.lean`), the
  **notification** arm at v0.34.96
  (`cancelIpcBlocking_notificationArm_preserves_ipcInvariantFull`,
  `…/CancellationNotificationShape.lean`), and the **reply** arm at `v0.35.82`
  (`cancelIpcBlocking_replyArm_preserves_ipcInvariantFull`,
  `…/CancellationReplyShape.lean`).  **The arm-complete composite and its
  cross-core lift landed at `v0.35.85`** (WS-RR RR8.10,
  `SeLe4n/Kernel/IPC/Invariant/CancellationBundle.lean`, production and in the
  library root): `cancelIpcBlocking_preserves_ipcInvariantFull` over the four
  bodies the six `ipcState` constructors are serviced by, and
  `cancelIpcBlockingOnCore_preserves_ipcInvariantFull` over the transition the
  live `.tcbSuspend` dispatch runs.  Three things new code must respect.  (1)
  **The premises are per-arm**: `cancelIpcBlockingArmPremises` gates each group
  on that arm's own `ipcState` equation — which is the equation each arm theorem
  already takes, so no second reading of "which arm is this" enters the tree —
  and the `.ready` arm owes nothing, because it commits no write.  (2) **The
  cross-core form's premises are the teardown's and nothing more**: the
  migration, the holder wake and the victim's placement removal each frame
  `passiveServerIdle` for a reason that is a property of the *step* — the
  migration writes no run queue and no current slot, an *insert* cannot break a
  conjunct whose antecedent is "not queued", and the removal's one obligation is
  discharged from `cancelIpcBlocking_victim_ready`, the fact that a cancelled
  victim ends `.ready` on every arm.  A hypothesis about any of the three here
  would retract that claim, and a Tier 3 negative refuses one.  (3) **Only
  `passiveServerIdle` reads the scheduler**, which is why the lift is
  `ipcInvariantFull_of_descheduleFrame` and not a second twenty-conjunct
  argument; a proof that unfolds the bundle instead is doing the work RR2.5
  factored away.  "All five arms" is how the register named this row and the
  count is **four bodies over six constructors** — the three endpoint states
  share one.  The sentence here named the notification arm as
  uncovered for eighteen cuts after v0.34.96 covered it, two sentences below its
  own retraction, which is the *status claim a later cut must sweep* shape — so
  read this list as of its stated versions and sweep it, not around it.  Each arm
  needed its own engine, because the first two run a whole-store fold rather than
  RR7.22's splice, and the third is a **four-step composition** — reclaim, splice,
  restore, teardown — in which no two steps carry the bundle for the same reason
  (`cancelIpcBlocking_reply_arm_eq` pins the arm to that composition by `rfl`).
  Two hypotheses beyond the bundle are common to the first two: the
  timeout-budget discipline
  `allTimeoutBudgetsNone` (unavoidable — the conjunct says a budget-carrying
  thread is *blocked*, and both operations make one `.ready`), and a
  queue-coherence fact `ipcInvariantFull` does not entail, because it constrains
  queues only at their boundaries and carries no connectivity:
  `sweptThreadQueueCoherent`'s three clauses for the endpoint arm, and
  `sweptThreadOffQueueChains` for the notification arm, which has no splice to
  repair the swept thread's neighbours.  New code must state those rather than
  assume them.  **The reply arm's set is larger, because its steps are** — read it
  off `cancelIpcBlocking_replyArm_preserves_ipcInvariantFull` rather than off a
  count here.  Those two, and: `donationChainWellFormed`, which is what makes the
  pop's fail-closed head validation *resolve*; `cancelDonationStackValid` for the
  pop's outer caller; `abortHolderQueueCoherent`, the endpoint arm's three clauses
  again but for the *holder* the reclaim aborts and under the arm gate, since a
  caller cannot name that thread to state them of it; and **both directions of one
  local coherence fact** — `replyFrameHeadHolderDonation` at the victim's reply
  object (head → binding, which the pop's carriage is stated over) and
  `donatedContextIsOwnerFrameHead` (binding → head, which the no-donation payoff
  quantifies over).  Neither direction entails the other — a frame head whose
  context is `.bound` to its holder satisfies the second and refutes the first, and
  a binding with no frame satisfies the first vacuously — and `ipcInvariantFull`
  entails neither, which is WS-HP HP7's own reason for keeping the first stated.
  `sweptThreadOffQueueChains` does double duty here: it is also what rules the
  victim out as a queue neighbour of that holder, which is what carries the
  victim's own TCB across the reclaim with only its binding rewritten.  What is **not** a hypothesis is anything the bundle entails:
  `replyObject_none_of_not_blockedOnReply` derives "holds no Reply object" from
  the bundle's own reciprocity, and
  `purgedAndRestored_victim_off_endpoint_boundaries` derives that a
  notification-blocked thread bounds no endpoint queue.  Tier 3 negatives refuse
  either as a premise.  The flow-`Checked` dispatch
  wrappers gained their own payoff tier
  (`dispatchWithCapChecked_preserves_ipcInvariantFull` /
  `dispatchSyscallChecked_preserves_ipcInvariantFull`, staged) in the same
  cut.
- **Every SchedContext hand-off must migrate the replenish queue, and the
  migration's DESTINATION is the bound thread's home rather than the thread the
  hand-off expects to bind** (SM5.H; the destination half is WS-RR RR8.11,
  `v0.35.86`).  The CBS replenishments of a SchedContext live on its *bound
  thread's* home core (`replenishQueueAffinityConsistentOnCore`), so any transition
  that rebinds `boundThread` across cores must call
  `migrateSchedContextReplenishment` or the invariant is false from the instant it
  commits.  Four live paths do (`applyCallDonationOnCore`,
  `applyReplyDonationOnCore`, `.replyRecv`'s pop — `replyRecvPopDonation` since
  WS-RM split the fused `replyRecvReturnDonation`; the paths landed at v0.34.42 —
  and, since `v0.35.161`, the pre-receive donation return
  `cleanupPreReceiveDonationMigrated`), each with a
  `replenishQueueAffinityConsistent_smp` preservation theorem, and
  `PerCoreDonationStep` (`API.lean`) is the relation that names them all.  The
  pre-SM10 audit found only two of the first three, because it enumerated the
  donation *primitives* and `.replyRecv` composes them from the API layer — the
  enumeration-versus-derivation shape the key-conventions section above warns
  about — and this sentence then said **three** from v0.34.42 until `v0.35.160`,
  while the fourth rebound a context across cores and migrated nothing (register
  row 57, found by reading the arm for RR8.12 Cut C2 and closed one cut later).
  Twice is the measurement that a hand-kept list of hand-offs is not a derivation;
  the bullet after this one says what pins the fourth.
  And **one more** migrates with no constructor here and, until `v0.35.164`, no
  theorem anywhere: the suspend pipeline's own G3 donated arm
  (`cancelDonatedDonationOnCore`), which the destroy path runs too since that
  version.  Its theorem is beside the arm
  (`cancelDonatedDonationOnCore_preserves_replenishQueueAffinityConsistent_smp`),
  composed from the same general `_to_home` migration lemma the pre-receive
  return's is, and this relation's docstring names it as the second hand-off of
  the reclaim's shape — one that carries its own theorem rather than a
  constructor.  See the standing constraint on the retype's cleanup below.
  A same-core hand-off is a definitional no-op
  (`migrateSchedContextReplenishment_noop`), so the migration costs nothing where it
  is not needed and there is no reason to omit it.

  **And a caller that can refuse must read the destination off the post-rebind
  state.**  `cancelIpcBlockingMigrated` aimed its migration at
  `determineTargetCore st victim` — the home of the thread the reclaim is *about to*
  bind the context to — and the reclaim's guards are fail-closed (the outer-caller
  check, HP4.6's recipient guard, the head validation), so on a refusal it moved
  `scId`'s replenishments to a core no thread bound to `scId` is homed on, which is
  the invariant's own negation.  Latent rather than live — the refusal needs a state
  violating one of the two *stated* coherence facts, which hold on every reachable
  state — but the migration's soundness rested on an unstated hypothesis, and the
  reply path never had the defect because *its* migration sits in the `.ok`
  continuation of its return: one question, two spellings, and the pure one had it
  wrong.  `replenishHomeOfSchedContext` (`SchedContext/ReplenishAffinity.lean`) is
  the destination now — the home of the thread the context is bound to, read on the
  state the migration runs against — so a refused rebind is a *self*-migration that
  `_noop` collapses to the identity, and
  `migrateSchedContextReplenishment_to_home_preserves_affinityConsistent_smp` gets
  its destination obligation free from `replenishHomeOfSchedContext_spec`.  Three
  things new code must respect.  (1) **Every caller passes the migration's own
  source as the fallback**, so a context that resolves to nothing or is bound to no
  thread is a no-op rather than a pointless move.  (2) **The general lemma requires
  the source to be where the invariant currently puts the context** — spelled as the
  pre-state binding and its home, not as an implication, because a context bound to
  no thread locates no entries a migration could move.  (3) **The footprint does not
  grow**: both cores the destination can name were already declared, and
  `maxLockSetSize` is unmoved.
- **...and the pre-receive donation return migrates too, on the cross-core leg,
  keyed on the pop's own guard** (`v0.35.161`, register row 57).  The block arm
  of `endpointReceiveDualOnCore` — so `.receive`, and `.replyRecv`'s receive leg —
  returns a `.donated` receiver's context to its owner before the receiver parks,
  and it ran that pop bare until this cut: `boundThread` moved to the owner, the
  reservation's replenishments stayed on the receiver's home core, and
  `replenishQueueAffinityConsistent_smp` was false on a state three ordinary
  operations reach (a client `Call`s a passive server homed elsewhere, the
  server's `Recv` takes it and the hand-off migrates, the server abandons the call
  with a plain `Recv`).  No theorem claimed the leg preserved the invariant, so the
  surface was silent rather than wrong.  Five things new code must respect.  (1)
  **The arm runs `cleanupPreReceiveDonationMigrated`** — the checked pop, then
  `preReceiveReturnMigration` — and never the bare
  `cleanupPreReceiveDonationChecked`; a Tier 3 negative refuses the bare match
  inside the definition.  The order is the content: the migration reads the
  *post-pop* binding for its destination (`replenishHomeOfSchedContext`, RR8.11's
  rule above), so a refused pop self-migrates to the identity; and its guard is
  the pop's own — `preReceiveDonation?`, resolved through `lookupTcb` exactly as
  the pop resolves it — never the footprint's `getTcb?` resolver
  `endpointReplyDonation?`, which differs from it only on a reserved id, where the
  footprint over-declares and the transition is inert
  (`preReceiveDonation?_eq_endpointReplyDonation?_of_lookup`).  (2) **The
  single-core `endpointReceiveDual` keeps the bare pop**, because on one core the
  migration is the identity; what that costs is the agreement dichotomy
  `endpointReceiveDualOnCore_post_agrees`, whose block path now runs the two
  spines on two states that agree off the scheduler rather than on one, carried
  by three step congruences the dichotomy lacked
  (`endpointQueueEnqueue_offSchedulerAgrees`,
  `storeTcbQueueLinks_offSchedulerAgrees`,
  `migrateSchedContextReplenishment_offSchedulerAgrees`) — a new object-level step
  in that leg needs its congruence on the day it is written.  (3) **The leg has
  its affinity theorems** (`cleanupPreReceiveDonationMigrated_preserves_…`,
  `endpointReceiveDualOnCore_preserves_…`, `…WithCapsOnCore_preserves_…`), stated
  over every path, and `PerCoreDonationStep.preReceiveReturn` is the catalogue's
  fifth constructor; the whole-leg frame
  `endpointReceiveDualOnCore_replenishQueueOnCore` is retired for per-path ones
  (`_of_rendezvous`, `_of_blocked`, `_of_no_donation`) and refused tree-wide,
  because it was true of the transition only because the transition omitted the
  write.  (4) **The `.receive` footprint's block-path replenish segment is the
  pair `[receiver's home, owner's home]`**, read through `receivePreReturn?` — the
  resolver the object domain already reads this return through, so the two
  domains cannot name different owners — with
  `endpointReceiveHandoffReplenishCores_of_blocked_returning_eq_migration` the
  licence that the pre-state pair **is** the migration's and
  `schedLockSet_endpointReceiveOnCore_covers_preReturnMigration` the coverage;
  `endpointReceiveHandoffReplenishCores_of_blocked` and
  `schedLockSet_endpointReceiveOnCore_no_replenishQueue_of_blocked` are
  conditioned on no loan now, and the `.replyRecv` footprint inherits the pair
  when Cut C2 declares it over the same leg.  (5) **The witness computes the bare
  pop beside the migrated return** on the same reachable state
  (`tests/SmpIpcSuite.lean` §3.28) and asserts the bare one *falsifies* the
  invariant — the bare pop is still a live definition, the migrated return's own
  first half, so the retired reading needs no private copy — with a no-loan
  control and a same-core control, where the two returns agree.
- **A destroyed thread's reservation is ended the way a suspended thread's is**
  (`v0.35.164`, register row 62).  `lifecyclePreRetypeCleanup`'s TCB arm runs
  `cancelDonationArmOnCore` (`Lifecycle/Operations/Cleanup.lean`) — the suspend
  pipeline's G3 three-way binding match, named: `.unbound` is the identity,
  `.bound` is the in-place unbind with the replenish purge on the thread's home
  core (seL4's `finaliseCap` → `unbindFromSc`), `.donated` the return **and** the
  replenishment migration to the owner's home.  Until then the arm was the bare
  `cleanupDonatedSchedContext` — a return that migrates nothing, register row 57's
  class on the destroy path — and a `.bound` thread had only its `scThreadIndex`
  entry removed, leaving the SchedContext bound to a destroyed thread with its
  replenishment stranded on that thread's home core: `schedContextBindingConsistent`
  and `replenishQueueAffinityConsistent_smp` were both false after a successful
  retype, and no theorem claimed either across it.  Five things new code must
  respect.  (1) **The two per-core arms live beside the cleanup they complete**:
  `cancelBoundDonationOnCore` and `cancelDonatedDonationOnCore` moved from
  `IPC/CrossCore/Cancellation.lean` to `Cleanup.lean`, definitions only, keeping
  their namespace — the destroy path's module cannot import the cancellation
  layer, so *when a question has one owner and an asker that cannot see it, the
  owner is in the wrong layer* (`v0.35.59`).  Their `ipcInvariant` theorems, the
  single-core bridges and the suspend footprint stay where they were; the frames
  the destroy path reads are in `CleanupPreservation.lean`.  (2) **One owner, two
  spellings, one of them defined through the other**: `cancelDonationOnCore` (the
  `withLockSet` bracket convention) is one `match` over the arm, and the suspend's
  G3 is pinned to the arm by `rfl` (`suspendDonationArm_eq_cancelDonationArmOnCore`)
  rather than defined through it, because its `home` is read on the **pre**-G2
  state and calling the arm there would owe an affinity frame at the eight proof
  sites that open the pipeline — RR8.12's recorded reason stands.  A step added to
  the arm reaches the destroy path by construction and fails the G3 pin on the
  day it is written.  (3) **The arm has the affinity theorem neither caller had**:
  `cancelDonationArmOnCore_preserves_replenishQueueAffinityConsistent_smp`, over
  `cancelBoundDonationOnCore_preserves_…` (no hypothesis on the purge core — the
  unbound context's obligations are vacuous wherever its entries survive, which is
  the unbind's own argument) and `cancelDonatedDonationOnCore_preserves_…`
  (through the general `migrateSchedContextReplenishment_to_home_preserves_affinityConsistent_smp`,
  the one owner `v0.35.161`'s pre-receive return composes).  The suspend pipeline
  had run both arms since SM6.E.3 with the invariant stated of its G2 teardown and
  of nothing after it.  (4) **`retypeTargetDetached` has `tcbNotBound`**: revoke,
  suspend, cancel *and unbind* before retype, so the dispatch payoff's retype arm
  is stated where the arm is the identity, and the runtime arm is what makes a
  violation safe.  (5) **What is measured, and what is proved**: `tests/SmpIpcSuite.lean`
  §3.31 drives the live wrapper on both binding shapes with the retired cleanup
  computed beside it and an unbound control; the **cleanup**'s own preservation of
  `replenishQueueAffinityConsistent_smp` is proved at `v0.35.166`
  (`lifecyclePreRetypeCleanup_preserves_replenishQueueAffinityConsistent_smp`,
  `Lifecycle/Invariant/RetypeReservation.lean` — see the bullet below for where
  the frames it composes went), and what register row 63 still carries is
  `schedContextBindingConsistent` across either program, plus the retype
  *composite*'s affinity theorem, which is gated on it.

- **...and a destroyed SCHEDULING CONTEXT releases the binding it holds**
  (`v0.35.165`, register row 63's arm half).  `lifecyclePreRetypeCleanup`'s
  `.schedContext` arm refused a context that heads a reply stack
  (`sc.scReply.isSome`) and nothing else, so a context **bound** to a thread
  passed: the retype left that thread `.bound scId` — or `.donated scId owner`,
  the binding a donee holds — naming an object the slot no longer carries, its
  `scThreadIndex` entry in place, and `scId`'s replenish entries queued on its
  home core under an id the slot's next occupant inherits.  `releaseSchedContextBinding`
  (`Lifecycle/Operations/Cleanup.lean`) is seL4's `schedContext_unbindAllTCBs`
  per core.  Four things new code must respect.  (1) **Its three writes are
  `schedContextUnbind`'s own**, composed from the same primitives in the same
  order — the binding cleared through `updateTcb`, the replenishments purged with
  `purgeReplenishmentOnCore` on the bound thread's home core, the index entry
  removed — rather than a second spelling of the queue write; the TCB-absent arm
  sweeps **every** core, for the unbind's own stated reason (a thread gone from
  the store has no `cpuAffinity` left to read).  (2) **It does not rewrite the
  SchedContext record**, because the retype replaces the object, and it writes no
  run queue and no current slot — which is what keeps the destroy path's write
  set empty and its confinement result unchanged
  (`releaseSchedContextBinding_confinedToCores`, over the six slots a replenish
  queue is deliberately not among).  (3) **A donee's context is not
  returned to its owner**: the owner is already `.unbound` and the object it
  would receive no longer exists.  (4) **Its affinity theorem is unconditional,
  and not for the unbind's reason**: the release only ever *removes* replenish
  entries and frames both readings the invariant makes, so an invariant
  quantified over the entries that are present descends to a state with fewer of
  them — where the unbind needs more precisely because it rewrites its context to
  `boundThread := none`.  One consequence for proofs: the arm is **unreachable**
  under `retypeTargetDetached`, whose `notSc` excludes SchedContext targets
  outright, so `lifecyclePreRetypeCleanup_detached_frame` discharges it by
  contradiction rather than by the arm being the identity.
- **...and the CLEANUP has its reservation theorem, because a frame it composes
  moved to the layer that can state it** (`v0.35.166`, register row 63's layering
  half).  `v0.35.164` and `v0.35.165` each gave an *arm* of
  `lifecyclePreRetypeCleanup` its own `replenishQueueAffinityConsistent_smp`
  theorem and neither could state one about the **program** that runs them: the
  `.tcb` arm's reference sweep runs two whole-store folds whose
  `getSchedContext?` and `cpuAffinity` frames WS-RR RR8.11 wrote `private` in
  `IPC/Invariant/CancellationBundle.lean`, which is downstream of both the
  cleanup and the retype wrapper.  So the theorem was **unstateable** rather than
  unproved — `v0.35.59`'s rule (*when a question has one owner and an asker that
  cannot see it, the owner is in the wrong layer*) at the scale of a composite.
  Six things new code must respect.  (1) **Each frame is beside the fact its
  proof rests on, not in one convenience module**: the two generic accessor
  bridges (`SystemState.getSchedContext?_eq_of_kind_iff`,
  `SystemState.map_cpuAffinity_eq_of_refines`) in `Model/State.lean` beside
  `getSchedContext?_eq_some_iff` / `getTcb?_eq_some_iff`; the splice's affinity
  frame in `CleanupPreservation.lean`; each sweep's pair in its own
  `Cancellation*Shape.lean` beside that sweep's `non…` biconditional.  A new
  frame over one of those sweeps goes to the same place.  (2) **The composite
  lives in `Lifecycle/Invariant/RetypeReservation.lean`**, which imports
  `CancellationNotificationShape` — the only layer that sees every frame it
  composes, and imported by nothing that would close a cycle — and which the
  library root imports, since a module outside every root is outside every
  census's derived domain.  (3) **The sweep frames `boundThread`, not
  `getSchedContext?`**: its last step (`clearDonationOriginReferences`) genuinely
  rewrites scheduling contexts, and the invariant reads only the field it leaves
  alone, so `cleanupTcbReferences_boundThread_frame` is the projection and
  `replenishQueueAffinityConsistentOnCore_transfer` is what consumes it.  (4)
  **The composite takes no detachment pack**, so it covers exactly the states on
  which the runtime arms do the work — under `retypeTargetDetached` the whole
  cleanup is the identity (`lifecyclePreRetypeCleanup_detached_frame`), which is
  the posture that pack's own clauses record and the reason a theorem stated
  under it would exercise neither arm.  `hTcb` is the arm's own soundness
  condition, stated where it binds.  (5) **`replenishQueueAffinityConsistent_smp_frame`
  is the shape a step writing no object at all reaches for** — the per-core
  `_frame` at every core, beside `_smp_congr` in `ReplenishAffinity.lean` — and
  the CDT detach, the service-registry revoke and the memory scrub all take it.
  (6) **What row 63 then carried was an effort fact, measured**: there was no
  `preserves_schedContextBindingConsistent` theorem anywhere in the tree, so that
  reciprocity had to be built for eight operations before either program could
  claim it — `v0.35.183` built it, see the bullet below — and the retype
  *composite*'s affinity theorem is gated on the same work rather than on a
  second layering fact, because its `storeObject` at `target` rewrites
  `getSchedContext?` and `determineTargetCore` there and so preserves the
  invariant exactly when no surviving context is bound to the destroyed thread.
  Stating *that* as a hypothesis would be a predicate no transition establishes
  (`v0.35.126`).
- **...and Z4-O crosses that cleanup too — with the SchedContext arm REFUTED
  rather than proved** (`v0.35.183`, register row 63's remaining half).
  `schedContextBindingConsistent` is bidirectional reciprocity between
  `TCB.schedContextBinding` and `SchedContext.boundThread`, and it reads nothing
  else, so `schedContextBindingConsistent_transfer` (beside the predicate) takes
  both projections as `Option.map` frames and carries the invariant whole, with
  `schedContextBindingConsistent_of_objects_eq` the degenerate case.  Five things
  new code must respect.

  (1) **Both frames, never one.**  Framing the binding alone leaves the backward
  clause unsupported — a step that rewrites a `boundThread` and no binding would
  pass it — which is *a presence check is not a relation check* at the level of a
  transfer lemma's own hypotheses.

  (2) **The splice's field frame has one owner.**  `spliceOutMidQueueNode`
  rewrites its neighbours' three link fields and nothing else (WS-OD OD1.1 /
  OD3.9's own subject), so `tcbQueueLinkRewrite` states that as a relation,
  `spliceOutMidQueueNode_tcbField_frame` proves the frame once over an arbitrary
  projection, and `_affinity_frame` and `_binding_frame` are instances.  A new
  projection over the splice is a one-line instance, never a second induction —
  and a whole-record `getTcb?` equality for the splice, or for the sweep built
  over it, is **false** and refused tree-wide.

  (3) **The pop moves one whole reciprocal pair.**
  `returnDonatedSchedContext_preserves_schedContextBindingConsistent` is the
  substantive theorem of the family: the pop clears the holder's binding,
  installs the recipient's and rewrites the context's `boundThread` to name the
  recipient, so both clauses are re-established at the moved pair and transported
  everywhere else — and its uniqueness obligations come from Z4-O itself rather
  than from a fresh argument.  `cancelBoundDonationOnCore`'s unbind *clears* both
  sides of one pair; `cancelDonationArmOnCore` covers all three bindings, so the
  suspend pipeline's G3 inherits it through
  `suspendDonationArm_eq_cancelDonationArmOnCore`.

  (4) **`releaseSchedContextBinding` does NOT preserve it, deliberately**, and
  `releaseSchedContextBinding_refutes_schedContextBindingConsistent` says so: the
  arm clears the bound thread's binding and leaves the destroyed context's
  `boundThread` naming it for the retype's own `storeObject` at that key to
  replace, so the backward clause is false on the arm's post-state and repaired
  one step later.  Writing `boundThread := none` there would add a store to an
  object the very next step replaces, for no property that is not already had.
  `lifecyclePreRetypeCleanup_preserves_schedContextBindingConsistent` therefore
  takes `hNotSc` — free at the live call site, where `retypeTargetDetached`'s
  `notSc` excludes a SchedContext target outright — and the refutation is what
  shows that hypothesis *necessary* rather than convenient, the standing pattern
  WS-RR RR8.7 set with `replyCallerLinkage_refutes_woken_linked_caller`.  A proof
  that wants the preservation is asking for a premise the arm refutes.

  (5) **A retyped SchedContext starts bound to nobody, and that is a runtime
  refusal** (`v0.35.184`).  `KernelObject.wellFormed`'s `.schedContext` arm is
  `sc.boundThread = none`, following the `Reply` clause SM6.D added one field over
  and for the reason SM6.D states in terms: the two retype wrappers check
  `wellFormed` and **nothing else** of the replacement, so an arm reading `True`
  admits a retype installing a context that claims a thread which does not name it
  back — exactly what Z4-O forbids, and a disagreement no operation reconciles.
  Three things new code must respect.  The clause **is** the refusal, because both
  wrappers answer `.illegalState` and commit nothing when `wellFormed` fails; a
  Tier 3 anchor is scoped to **each** wrapper's declaration, since one tree-wide
  pattern is satisfied by whichever of the two still carries the guard.  It costs
  the tree nothing — nothing depended on the arm being `True`, and the live
  dispatch's builder is `objectOfKernelType`, whose `.schedContext` arm is
  `SchedContext.empty` — which is what makes it the difference between an invariant
  maintained by convention and one enforced structurally, true of every *future*
  replacement builder rather than of the one that exists.  And the witness's
  negative is the falsification: `tests/SmpIpcSuite.lean` §3.34 computes the
  retired guard beside the live one, stores the claiming replacement through it and
  asserts Z4-O **false**, against a CONTROL on the pristine replacement where it
  holds — so the claim is about `boundThread` rather than about the retype.

  Register row 63's last half — the retype **composite**'s two theorems — is
  `v0.35.185`, the bullet below.
- **...and the COMPOSITE crosses through one intermediate, carved out of BOTH
  sides, and it is the intermediate BOTH invariants need** (`v0.35.185`,
  register row 63 CLOSED).  `lifecycleRetypeDirectWithCleanup` is the cleanup,
  then `scrubObjectMemory`, then a `storeObject` at `target`, and a composite
  stated as *"Z4-O of the post-cleanup state carries to the post-store state"* is
  a statement about a state the pipeline does not rest at — the `.schedContext`
  arm refutes Z4-O on its own post-state by design (the item above).  Six things
  new code must respect.

  (1) **`schedContextBindingRetypeReady st target` is Z4-O with `target` carved
  out of the SUBJECT and of the OBJECT of both clauses**, and all four carve-outs
  earn their place at the store: the forward clause's `scId.toObjId ≠ target`
  rules out a thread still bound to the *destroyed context* (after the store the
  target holds `newObj`, so it would have no witness), the backward clause's
  `tid.toObjId ≠ target` a surviving context still naming the *destroyed thread*
  (after the store its record is `newObj`'s).  Neither follows from the other, and
  dropping either makes
  `storeObject_establishes_schedContextBindingConsistent` **false** rather than
  unprovable.  It stands to the retype as
  `ipcInvariantFullExceptDonationOwner` stands to the bare reply and
  `replyCallerLinkageExcept` to the woken caller.

  (2) **The SAME predicate carries the replenish half**, which is the measurement
  that it is the destroy path's own fact rather than one proof's scaffolding:
  `storeObject_preserves_replenishQueueAffinityConsistent_smp` consumes it because
  the backward carve-out is exactly what keeps the store from moving a replenish
  entry's home core — the replacement TCB's `cpuAffinity` is its own.  A second,
  private readiness predicate for that half would be *one question, two answers*
  inside the remedy for it.

  (3) **`retypeTargetUnpaired` is the fact each cleanup arm establishes**, stated
  once, and `lifecyclePreRetypeCleanup_targetUnpaired` proves it for five of the
  six arms; `hNotSc` is the sixth, free at the live call site.  The store's two
  remaining conditions are the replacement's: `hScFresh` is a **runtime refusal**
  (`v0.35.184`) read off the wrapper's own guard, and `hTcbFresh` the
  `retypeReplacementFresh` pack the live dispatch already supplies.

  (4) **`hIdentity` — a TCB is stored under its own thread id — is a hypothesis,
  and the reason it is one is a registered gap** (its runtime half closed at
  `v0.35.187`, the item below; the store-level invariant that would retire the
  hypothesis is open).  The `.tcb` arm is handed `tcb`
  and operates on `tcb.tid` while the store is at `target`, so without their
  agreement the cleanup can clear a binding at one key and leave the retype's own
  key paired.  Four measurements place it: `PlatformConfig.wellFormed`'s
  `embeddedIdentitiesMatchSlots` establishes it for every boot object,
  `enqueueIdleThreadOnCore` stores `queuedIdleThread c` at
  `(idleThreadId c).toObjId` carrying that very id, **no transition writes
  `TCB.tid`**, and the one remaining builder (`objectOfKernelType`) sets it to
  `ThreadId.sentinel` but is refused by `KernelObject.wellFormed`, whose `.tcb`
  arm requires the replacement's `cspaceRoot` and `vspaceRoot` to resolve while
  that builder sets both to `ObjId.sentinel`.  **That last refusal is a
  convention, not an invariant** — the H-06/WS-E3 reservation of id 0 is enforced
  at boot for the *boot VSpace root alone* and by no store-level invariant, and no
  conjunct of `PlatformConfig.wellFormed` refuses an `initialObjects` entry at
  slot 0 — so the agreement holds of every reachable state and is stated by
  nothing, a latent false-assurance gap with its own register row whose remedy is
  to **stamp the slot's identity** rather than to weaken the claim.

  (5) **The claim's unit is the PROGRAM THE ARM RUNS.**  The live
  `.lifecycleRetype` dispatch runs
  `lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache`, so both theorems are
  lifted through the three cached-structure layers — Cut C6g's rule, and the lift
  is a citation rather than a second argument because each layer frames `objects`
  and `scheduler` outright.  One shared frame
  (`lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_ok_frame`) says it for
  both, so a fourth layer costs one proof rather than one per consumer.

  (6) **What the composite DID has one owner**, and a `private` frame has none.
  `lifecycleRetypeDirectWithCleanup_ok_decompose` replaced the same twenty-line
  decomposition inlined in both proofs, which were free to disagree about which
  state the cleanup left; and `retypeInitiatorDrain_objects` is public beside its
  `_scheduler` and `_machine` siblings, where it was the `.1` of a `private`
  conjunction whose `.2` duplicated the public `_scheduler` two lines from the
  step it frames — half a second answer, half unreachable from every asker
  upstream.  Both are refused in their retired spellings by Tier 3 negatives.
- **...and a retyped object carries the SLOT's identity, because the runtime now
  refuses one that does not** (`v0.35.187`).  A TCB, a SchedContext and a Reply
  each carry their own id in a field while the object store is keyed by `ObjId`,
  so the two can disagree; `PlatformConfig.wellFormed`'s
  `embeddedIdentitiesMatchSlots` has refused that at **boot** since PR #889
  review round 8 and **nothing refused it at the runtime**, while
  `objectOfKernelType` — the one builder the live retype installs through —
  stamped the reserved **sentinel** into all three.  Four things new code must
  respect.

  (1) **`KernelObject.embeddedIdentityMatches` is the question, with no
  wildcard**: a kernel object that starts carrying its own id must be classified
  there rather than silently answering `true`, which is the closed-inductive rule
  this file states for `ConstantInfo` applied to a kernel record.

  (2) **A refusal needs an answer, and `KernelObject.withIdentity` is it** — it
  writes the identity field and nothing else, so `withIdentity_wellFormed`,
  `_objectType` and `withIdentity_replacementFresh` carry every property the
  retype's other guards and the dispatch payoff's pack read.  A builder that
  installs a TCB, SchedContext or Reply stamps.

  (3) **Both retype wrappers read ONE named predicate**,
  `retypeReplacementAdmissible`, rather than a second `if` beside the T5-D one:
  *a named condition beside unnamed ones is a subset*, and a condition added to
  the predicate reaches both wrappers by construction.

  (4) **The boot's check and the runtime's guard are one question by theorem**
  (`embeddedIdentitiesMatchSlots_iff`), not by a shared spelling.  What the cut
  does **not** do is retire `hIdentity`, which is about the object being
  *destroyed*: that needs the store-level invariant *every stored object's
  embedded id is its key*, which the boot, the idle enqueue and now the retype
  all establish and which no transition falsifies — a preservation theorem per
  transition, registered rather than implied.
- **...and the `.replyRecv` arm declares one, by re-running its own spine** (WS-RR
  RR8.12 Cut C2, `v0.35.162`).  `schedLockSet_endpointReplyRecvOnCore` is
  `schedFootprintOfCores` of `replyRecvBodyWriteSet` — the arm's own SM8.B write
  set, which `replyRecvBody_confinedToCores` is stated at — and of
  `replyRecvHandoffReplenishCores`, the cores its **three** SchedContext hand-offs
  migrate between: the pop between the legs (`replyRecvPopDonation`, WS-RM), the
  receive leg's block-path return (`cleanupPreReceiveDonationMigrated`,
  `v0.35.161`) and the re-donation to the receiver on a dequeued `Call`
  (`replyRecvPostReceiveDonation`, WS-RR RR2.20).  **Inert** until the bracket
  cut.  Six things new code must respect.  (1) **Each hand-off is read at the
  state it runs on, through its own arm selector** — the pop's frame trigger
  `replyFrameHeadHolder?` at the reply leg's post-state
  (`replyDonationReturnReplenishCores`, the pair the `.reply` dispatch reads too
  since Cut C3a; the pop's `returned?` is that trigger's answer), the block path's
  `receivePreReturn?` at the pop's post-state (`receivePreReturnReplenishCores`),
  the re-donation's `callDonationSchedContext?` at the post-deschedule state
  (`replyRecvPostReceiveReplenishCores`, over the post-state form
  `rendezvousCallDonationReplenishCores`) — which is the discipline
  `replyRecvBodyWriteSet` established for the run segment, and the reason this arm
  could not take `.receive`'s pre-state form: the pop rewrites the receiver's
  binding between the legs, so a pre-state reading of the receive leg's donation
  guard would be a proxy for the guard the transition reads two legs later.  The
  footprint's resolution and the transition's are the same computation, so the
  asymmetry WS-HP HP10.8 registered for the reply arm's origin member has no
  instance here.  (2) **The block-path pair has one owner for both receiving
  arms**: `receivePreReturnReplenishCores` is what
  `endpointReceiveHandoffReplenishCores` reads on its block branch too, and
  `receivePreReturnReplenishCores_eq_migration` is the licence — stated once,
  consumed by both — that the pair **is** the migration's.  (3) **Every hand-off
  is covered by theorem at the cores its migration actually resolves**:
  `schedLockSet_endpointReplyRecvOnCore_covers_pop` (through
  `replyRecvPopDonation_ok_some_decompose`), `…_covers_preReturnMigration`, and
  `…_covers_postReceiveDonation` (through `applyRendezvousCallDonation_ok_migrates`).
  (4) **The empty segment is exact in both directions**: where the pop hands
  nothing back and the block path returns no loan, the footprint names no
  replenish lock (`…_no_replenishQueue_of_no_donation`) and the live transition
  writes none (`replyRecvBody_replenishQueueOnCore_of_no_donation`, composed from
  the reply leg's new frame `endpointReplyOnCore_replenishQueueOnCore`, the pop's
  `none` arm being the identity, the receive leg's `…_of_no_preReturn` frame and
  the two walks' frames).  (5) **That licence pins a divergence, deliberately.**
  On a `.replyRecv` whose pop returned nothing, a dequeued `Call` caller's context
  is **not** donated to an `.unbound` receiver — `replyRecvPostReceiveDonation`'s
  never-donated arm walks only — where this kernel's own `.receive` arm
  (`applyReceiveRendezvousHandoff`, unconditional) and seL4-MCS's `receiveIPC`
  would donate.  Reachable with one legacy `.unbound` client, measured in
  `tests/SmpIpcSuite.lean` §3.29 (b) beside the `.receive` step on the same
  state, and recorded in the register's WS-CB row as the third instance of the
  passive/legacy split; a cut that makes the arm donate widens
  `replyRecvPostReceiveReplenishCores`'s `none` arm and breaks the licence, so the
  footprint and the transition move together or not at all.  (6) **The two chain
  walks are in the run segment**: `replyRecvBodyWriteSet` re-runs the spine to the
  state each walk starts from and appends `pipChainWriteSet` there, so the walked
  members' run queues are static members, and the `pipChainStart_replyRecv*`
  obligations add the object domain's per-member TCB locks through
  `pipChainSchedFootprint` (`v0.35.162` said "declared dynamically"; corrected at
  Cut C3a).  `maxLockSetSize` is unmoved.  §3.29 drives all three shapes through the live
  operations — the steady state with a second client on a third core (three cores
  named), the legacy client (none), and a delegated invoker that blocks holding a
  loan (all four) — asserting the segment, the footprint and the post-state
  replenish queues.
- **...and the `.call` and `.reply` arms declare theirs, over write sets that now
  live in production** (WS-RR RR8.12 Cut C3a, `v0.35.163`).
  `schedLockSet_endpointCallOnCore` (`IPC/CrossCore/EndpointCallDispatch.lean` §3)
  is `schedFootprintOfCores` of `endpointCallDispatchWriteSet` — the arm's SM8.B
  write set, which `endpointCallCrossCoreDispatch_confinedToCores` is stated at —
  and of `endpointCallDispatchReplenishCores`, the donation's pair;
  `schedLockSet_endpointReplyOnCore` (`EndpointReplyDispatch.lean` §6) is the same
  over `endpointReplyDispatchWriteSet` and `endpointReplyDispatchReplenishCores`,
  the return's pair; and `schedLockSet_replyTransferOnCore` (`Fault.lean` §6) is
  the **arm's** — seL4's `doReplyTransfer` branch — over the dispatch's at the
  message each branch hands it, plus on an abandon the faulted thread's home core.
  **Inert** until the bracket cut.  Six things new code must respect.  (1) **A
  replenish segment mirrors the dispatch's own guard at the state the dispatch
  asks it**: the `.call` segment asks `callDonationSchedContext?` at the WithCaps
  post-state and reads the two homes off the pre-state, exactly as
  `applyCallDonationOnCore` is handed them, so the pair and the migration's
  endpoints are the same two expressions and no home-core frame stands between
  them; the `.reply` segment re-runs the leg and reads the return's pair at that
  leg's post-state through `replyFrameHeadHolder?`, because the recipient is
  decided there (WS-HP HP10.8's asymmetry is what a pre-state reading would
  reintroduce).  (2) **The pop's pair has ONE owner**,
  `replyDonationReturnReplenishCores` — spelled through the two named home
  resolvers the dispatch passes — and `.replyRecv`'s pop component reads it too;
  `replyRecvPopReplenishCores` is retired, since the pop's `returned?` *is* the
  trigger's answer (`replyRecvPopDonation_holder_eq_frameHead`,
  `…_ok_none_frameHead`).  (3) **The `.reply` footprint is the DISPATCH's; the
  ARM's sits over it**, and only the arm's is complete: `faultAbandonOnCore`
  deschedules the answered thread on its home core, a write the dispatch never
  performs, so `schedLockSet_replyTransferOnCore_contains_abandon_runQueue_write`
  is the member a dispatch-level footprint would have missed, and
  `…_covers_dispatch_of_no_fault` / `…_of_fault` is the relation between the two.
  (4) **Coverage is at the resolved cores, and the RR2.4 shape is covered while
  the RR2.10 shape is not**: `schedLockSet_endpointCallOnCore_covers_parametric`
  holds because every core the parametric `.call` footprint declares is written;
  the parametric `.reply` footprint declares the executing core's run queue on the
  ground that the reversion re-buckets "locally", which is false — it re-buckets
  each member on its *home* core, and nothing in the dispatch writes the
  replier's own core — so that member is an over-declaration the derived form
  drops, and what is covered is the donation-return footprint the parametric form
  declares correctly (`…_covers_donation`, `…_covers_migration`,
  `…_covers_deschedule`).  (5) **The empty segments are exact in both
  directions** (`…_no_replenishQueue_of_no_donation` / `_of_no_receiver` /
  `_of_no_head` against `endpointCallCrossCoreDispatch_replenishQueueOnCore_of_no_donation`
  / `_of_no_receiver`, `endpointReplyCrossCoreDispatch_replenishQueueOnCore_of_no_head`
  and the arm's `replyTransferOnCore_replenishQueueOnCore_of_dispatch`), over four
  new frames — the bare and WithCaps call legs', the declined donation's, and the
  walk's `propagatePipChainCrossCore_replenishQueueOnCore`, which needs **no**
  object-store hypothesis: a claim about what a transition writes should not have
  to assume the invariant it preserves.  (6) **The chain walks are in the run
  segments**, for `.call`, `.reply` and `.replyRecv` alike: each write set re-runs
  the spine to the state its walk starts from and appends `pipChainWriteSet`
  there, so the walked members' run queues are static members, bounded by the
  object count (a `SchedLockSet` carries no cardinality bound); what the
  `pipChainStart_*` obligations still add through `pipChainSchedFootprint` is the
  object domain's per-member TCB write lock, which no scheduler footprint can
  name.  `.receive` (Cut 8a-ii) is the one declared arm whose walk is not in its
  run segment.  Five write sets and one frame moved here from the staged
  `InformationFlow/NonInterferenceCrossCore.lean` (`endpointCallWriteSet`,
  `endpointCallDispatchChainWriteSet`, `endpointCallDispatchWriteSet`,
  `replyDonationDescheduleCores`, `endpointReplyDispatchWriteSet`,
  `endpointCallWithCapsOnCore_scheduler_eq`), each with a tombstone, the
  confinement theorems staying staged — the layering rule Cuts 5, 7, 8a-ii and C2
  applied.  `tests/SmpIpcSuite.lean` §3.30 drives five shapes through the live
  operations and `tests/FaultHandlingSuite.lean` §7c the abandon;
  `maxLockSetSize` is unmoved.
- **...and the three TCB-control arms declare theirs, in a module of their own,
  because their own modules cannot name a `SchedLockId`** (WS-RR RR8.12 Cut
  C3b-i, `v0.35.167`).  `schedLockSet_resumeThreadOnCore`,
  `schedLockSet_priorityControlOnCore` and
  `schedLockSet_setThreadCpuAffinityOnCore` (`SeLe4n/Kernel/SyscallSchedFootprint.lean`)
  are the live `.tcbResume`, `.tcbSetPriority` / `.tcbSetMCPriority` and
  `.tcbSetAffinity` arms' scheduler-domain footprints — **inert** until the
  bracket cut.  Six things new code must respect.  (1) **Placement is a fact
  about the import graph, not a convention this module abandons.**  `SchedLockId`
  is declared in `Scheduler/Operations/PerCoreChooseThread.lean`, which imports
  `Lifecycle/Suspend.lean` and `IPC/Operations/Endpoint.lean`; measured,
  `Lifecycle/Suspend.lean`, `SchedContext/Operations.lean`,
  `SchedContext/PriorityManagementPerCore.lean`, `Scheduler/Operations/Core.lean`
  and `Lifecycle/Operations/RetypeWrappers.lean` are all outside its reverse
  closure, so none of them can name a `SchedLockId` at all.  Moving the
  identifier down was rejected — it is declared with `RunQueueLockId`,
  `ReplenishQueueLockId` and the cross-domain order over them, which is what
  `schedFootprintOfCores` is *about*.  The rule is therefore stated once, in that
  module's header: **a resolved scheduler footprint lives beside its transition
  where that module can name a `SchedLockId`, and here where it cannot** — the
  shape the object domain reached at `Concurrency/Locks/LockSetTransitions.lean`.
  (2) **Each footprint IS `schedFootprintOfCores` of its arm's own SM8.B write
  set**, which is Cut 7's rule, and that is what forced the three write sets out
  of the staged `InformationFlow/NonInterferenceCrossCore.lean` — a production
  footprint cannot read a write set declared in a staged module.  The confinement
  theorems stay staged.  (3) **The priority pair shares one footprint**, because
  SM8.B gives the two arms one write set; `.tcbResume`'s fault retire
  (`retirePendingFaultForResume`) needs no member of its own, writing one TCB's
  `pendingFault` and no scheduler state.  (4) **The affinity arm's replenish
  segment follows the thread's BINDING**, not the arm: a migration of a thread on
  no reservation moves no entry, and over-declaring is not free — lock contention
  is an observable channel (SM8.D's CC-5), which is WS-OD OD3.5's own reason for
  narrowing a footprint.  Every empty segment is a **theorem**
  (`resumeThreadOnCoreLive_replenishQueueOnCore`,
  `setPriorityOnCore_replenishQueueOnCore`,
  `setMCPriorityOnCore_replenishQueueOnCore`,
  `setThreadCpuAffinityWithMigration_replenishQueueOnCore_of_no_context`) against
  the declaration's own half, so each narrowing is exact in both directions.
  Coverage against the *transition* is its own statement
  (`schedLockSet_setThreadCpuAffinityOnCore_covers_migration`), because the
  transition resolves its destination as `determineTargetCore stSet tid` at the
  post-affinity-write state where the footprint resolves it from the argument:
  the two are one value only through `setThreadCpuAffinity_determineTargetCore_eq`,
  and a coverage claim read off `_contains_replenishQueue_writes` alone is about
  the argument rather than about the migration.
  (5) **The parametric SM5.H.4 family is production now**, and asking for the
  coverage relation is what found it: `setThreadCpuAffinityWithMigrationLockSet`
  and `migrateRunQueueOnAffinityChangeLockSet` sat in the staged
  `Scheduler/Operations/PerCoreCbs.lean` **twenty lines below the tombstone WS-RR
  RR2.4 left when it relocated `migrateSchedContextReplenishmentLockSet` out of
  that same file for that same reason** — *a fix applied at one site and not at
  its sibling*, invisible until a production footprint had to state
  `schedLockSet_setThreadCpuAffinityOnCore_covers_parametric`.  They are beside
  that family now, in `PerCoreChooseThread.lean`, and every consumer keeps working
  with no import edit.  (6) **A write set's content needs no anchor and must not
  get one**: each footprint's `_contains_*_runQueue_write` theorem is
  `simp [<the write set>]`, so a mutation dropping a core fails to *elaborate* —
  measured, rather than asserted, at
  `schedLockSet_resumeThreadOnCore_contains_home_runQueue_write`.  *Prefer making
  the property structural over checking it at all.*  Four frames moved to
  production beside the definitions they frame in the same cut
  (`migrateRunQueueOnAffinityChange_replenishQueueOnCore` →
  `Scheduler/Operations/Core.lean`; `enqueueRunnableOnCore_replenishQueueOnCore`
  and `setThreadCpuAffinity_determineTargetCore_eq` →
  `Scheduler/Operations/Selection.lean`; the new
  `migrateRunQueueBucketOnCore_replenishQueueOnCore` →
  `SchedContext/PriorityManagement.lean`).  `tests/SmpCbsSuite.lean` §4.5 is the
  decisive witness — one state, a thread on a reservation and a thread on none,
  the same migration, opposite segments, with the **parametric** footprint
  computed beside the resolved one so the assertions are known to discriminate —
  and `tests/SuspendResumeSuite.lean` SR-035 and
  `tests/PriorityManagementSuite.lean` PM-FP-01 drive the other two arms with the
  target's home core and the executing core distinct.  `maxLockSetSize` is
  unmoved.
- **...and the three SchedContext arms declare theirs, which found a duplicate
  resolver under a docstring claiming there was none** (WS-RR RR8.12 Cut C3b-ii,
  `v0.35.168`).  `schedLockSet_schedContextConfigureOnCore`,
  `schedLockSet_schedContextBindOnCore` and
  `schedLockSet_schedContextUnbindOnCore` join the three above, in the same
  module and for the same reason — **inert** until the bracket cut.  Five things
  new code must respect.  (1) **The thread a SchedContext operation acts on has
  one resolver, `SchedContextOps.schedContextBoundThread?`**, whose own docstring
  has said since SM8.B that it is *"single-sourced here in production because two
  consumers need it and a second copy would drift"* — while the staged
  `InformationFlow/NonInterferenceCrossCore.lean` carried `schedContextSubject?`,
  clause for clause the same function, and the write set the docstring names read
  *that* one.  The copy is **deleted** and refused tree-wide; a reader asks the
  owner by its own name, never through an alias, because an alias is the second
  spelling this cut retires.  *A docstring naming a drift hazard is not a check
  that the hazard is closed.*  (2) **The configure's replenish segment keys on
  the SCHEDCONTEXT resolving, not on its being bound**: an unbound SC has no
  home, `schedContextReplenishHome` answers the boot core, and the purge still
  runs there — a stale entry left by an earlier binding is exactly what it drops,
  so a segment keyed on the binding would omit a lock the transition takes.  When
  the SC *is* bound the purge and the re-bucket land on one core
  (`schedContextConfigureReplenishCores_eq_writeSet_of_bound`), so one lock covers
  both effects.  (3) **The unbind's replenish segment is the first in this family
  that is EVERY core.**  Its sweep arm — reached when the bound TCB is already
  gone from the store — runs `purgeReplenishmentFromAllCores`, because with no
  `cpuAffinity` left to read there is no home core to name; both arms are decided
  on the pre-state, so the declaration is exact rather than a conservative union,
  and a footprint naming only the home core would be **false** there.  (4) **The
  bind declares no replenish lock**, and `schedContextBind_replenishQueueOnCore`
  is the absence; the run segment is where seL4-MCS's `SCHED_ENQUEUE` divergence
  would widen it, not this one.  (5) **Every narrowing is a theorem in both
  directions**: `schedContextConfigure_replenishQueueOnCore_ne` and
  `schedContextUnbind_replenishQueueOnCore_ne_of_tcb` say each arm writes the one
  replenish queue its own resolver names, with
  `schedContextUnbindOnCore_replenishQueueOnCore_ne_of_tcb` lifting the second
  through the wrapper's scheduling point — and the **sweep** arm needs no such
  statement and can have none, writing every core being precisely what it
  declares.  The four SM8.B write sets moved to production with tombstones, and a
  Tier 3 anchor that pinned one at its old home is repointed rather than deleted,
  the SM8.B claim it carries being unchanged.  `tests/SmpCbsSuite.lean` §4.6 is
  the witness: the sweep fixture's entries sit on two cores, the live unbind
  purges both, and the retired home-only reading — a `private def` in the suite
  and nowhere else — declares neither.  `maxLockSetSize` is unmoved.
- **...and the destroy path declares its own, over a write set that is silent
  about the thing it moves** (WS-RR RR8.12 Cut C3b-iii, `v0.35.169`).
  `schedLockSet_lifecycleRetypeOnCore` is the live `.lifecycleRetype` arm's
  scheduler-domain footprint — **inert** until the bracket cut.  Five things new
  code must respect.  (1) **SM8.B's write set is a RUN-QUEUE write set**:
  `observableSlotsConfinedToCores` covers six per-core slots and the replenish
  queue is not one of them, so `lifecycleRetypeWriteSet` says nothing about the
  two reservation steps `v0.35.164` and `v0.35.165` put on the destroy path, and
  a footprint built from it alone is **false** of the operation.  That is what
  `tests/SmpIpcSuite.lean` §3.33 measures, computing the run-only reading beside
  the live footprint on both target shapes.  (2) **The replenish segment is keyed
  on the OBJECT KIND**, with exactly two kinds naming a core because the cleanup
  has exactly two reservation steps: a `.tcb` target's is the donation arm's
  (nothing for `.unbound`, the thread's home for `.bound`, the return's two
  migration endpoints for `.donated`, the destination read at the post-return
  state), a `.schedContext` target's is the release's, and every other kind's is
  empty — with `schedLockSet_lifecycleRetypeOnCore_empty_of_other` the
  declaration's own half, so a kind that acquires a scheduling effect has to move
  a definition rather than a proof.  (3) **The release's segment is `allCores`
  where the bound TCB is gone**, for the reason `v0.35.168`'s unbind gives on the
  same shape: with no `cpuAffinity` left to read there is no home core to name.
  (4) **Both resolvers read the PRE-state, and that is a fact rather than a
  convenience**: for a SchedContext target every earlier step of the cleanup is
  the identity, and for a TCB target the donation arm *is* the first step — so
  this whole footprint is pre-state computable with no mid-state bridge, which is
  what `.replyRecv` and `.tcbSuspend` do not get.  (5) **Exactness is composed
  over all six kinds**: two step frames, two arm frames stated against their own
  resolvers, and `lifecyclePreRetypeCleanup_replenishQueueOnCore_ne` over the
  whole cleanup, every other step of it framing the scheduler outright.
  `threadOccupiedCores` and the two retype write sets moved to production with
  tombstones — their lemma family and the confinement theorems stay staged, being
  about the destroy sweep's confinement, which is that module's question — and
  `SyscallSchedFootprint.lean` imports `Lifecycle/Invariant/RetypeReservation.lean`
  for the reference sweep's frame.  `maxLockSetSize` is unmoved.  **`.tcbSuspend`
  is the one arm left**, and it is a cut of its own: its run segment re-runs a
  seven-stage pipeline and its replenish segment two migrations read at
  intermediate states.
- **...and the last arm declares one — and the two parametric footprints it
  replaces were FALSE** (WS-RR RR8.12 Cut C3b-iv, `v0.35.170`).
  `schedLockSet_suspendThreadOnCore` is the live `.tcbSuspend` arm's
  scheduler-domain footprint — **inert** until the bracket cut, and the
  sixteenth and last of the arms RR8.12's sequence enumerated (which of the
  remaining nineteen write a scheduler slot at all is
  `declaredSchedFootprintSyscall`'s question, and the next cut's).  Six things
  new code must respect.

  (1) **The finding, which is what declaring a resolved form is for.**  Since
  WS-RR RR8.11 (`v0.35.86`) the suspend's G2 teardown is
  `cancelIpcBlockingMigrated`, and since RR8.12's second cut (`v0.35.90`) the
  live pipeline runs it: it moves the reclaimed reservation's replenishments
  from the **holder's** home core to the home the context is bound to at the
  torn state, writing the replenish queue of *both*.
  `cancelIpcBlockingOnCoreSchedLockSet`'s replenish segment was `[]` and
  `suspendThreadOnCoreSchedLockSet`'s was `[home, ownerHome, outerHome]`, which
  is G3's migration read off the **victim's** binding — a different thread and a
  different state — so neither endpoint was named by either.  RR8.12's second
  cut widened the *run* segment by the holder's placed core and did not ask the
  same question of the replenish segment: *a fix applied at one site and not at
  its sibling*.  Latent rather than live (the syscall seam does not yet bracket
  the scheduler domain), so everything stated over those footprints was
  **silent** about the two queues rather than conservative — RR8.11's and
  OD3.9's own posture.  Both are fixed here, each taking a
  `reclaimReplenish : List CoreId`.

  (2) **The resolver lives beside the transition, not beside the footprints.**
  `cancelIpcBlockingReplenishCores` is in `Lifecycle/Suspend.lean` next to
  `cancelIpcBlockingMigrated`, reading the same `let`s, because both parametric
  footprints must name it and neither can see the resolved-footprint module —
  *when a question has one owner and an asker that cannot see it, the owner is
  in the wrong layer* (`v0.35.59`).  It mentions no `SchedLockId`, so nothing
  about it belonged above that layer.  A Tier 3 negative refuses it coming back
  upstream, and the positive pins its name **followed by its parameter list**,
  because `^def X` matches a suffix-renamed `X_Moved` — the presence-check one
  character down that Cut 7 recorded for theorems.

  (3) **Neither half of the replenish segment is pre-state computable**, which
  is why this arm is a cut of its own.  G2's reclaim resolver is read at the
  pre-state (it resolves the torn state itself); G3's arm resolver is read at
  the **post-revert** state, because the reclaim rebinds the victim and WS-OD
  OD5.3's second pop then migrates to the *outer caller's* home — a core the
  pre-state cannot name, the victim holding no binding there.  So the segment
  re-runs the spine, exactly as `replyRecvBodyWriteSet` does, and a Tier 3
  negative refuses a pre-state reading of G3's arm.

  (4) **The donation-arm frame has ONE owner, at an explicit purge core.**
  `donationArmAt_replenishQueueOnCore_ne` is stated over the three-way match at
  a `home` argument, because the two askers hand it different cores — the
  destroy path reads it off the state it runs on, the suspend's G3 was handed it
  from the pre-G2 state — and a frame at `determineTargetCore st tid` covers the
  first and not the second.  `cancelDonationArmOnCore_replenishQueueOnCore_ne`
  is its instance rather than a second proof.

  (5) **Exactness is over the whole arm**:
  `suspendThreadOnCore_replenishQueueOnCore_ne`, all seven stages, of which two
  move a reservation and five frame every replenish queue, with
  `cancelIpcBlockingOnCore_replenishQueueOnCore_ne` the same pair for the
  cancellation composite — a footprint owes both halves, and the fixed one had
  gained only *names what is written*.  A claim stated over
  `cancelIpcBlockingReclaimed` alone would be a claim about a prefix of the
  transition the live `.tcbSuspend` runs, and a Tier 3 relation anchor refuses
  that shape.  Coverage against the parametric form
  (`…_covers_parametric_runQueue`) is stated over the **run-queue half alone**,
  which is the honest scope: the parametric replenish segment is four free
  parameters, so a coverage claim over it would have to hypothesise that a
  caller passed what the transition writes — which is the conclusion.

  (6) **The witness computes both retired readings beside the live ones.**
  `tests/SmpCancellationSuite.lean` §3.27 drives the live reclaim and the live
  suspend on a state the kernel reaches — the reservation queued on the holder's
  home core, the victim homed elsewhere — with core 3 as the control, in neither
  footprint and written by neither transition, so the membership assertions are
  about the migration rather than about width.  `maxLockSetSize` is unmoved and
  the golden trace is byte-identical.
- **...and the sixteen declared arms have ONE resolver, whose undeclared
  direction is the load-bearing one** (WS-RR RR8.12 Cut C4, `v0.35.171`).
  `schedLockSetForSyscall` is the scheduler domain's `lockSetForSyscall`, in the
  same module as the arms it dispatches to and for the same layering reason, and
  **inert** until the bracket cut.  Four things new code must respect.

  (1) **Adding a declared arm changes `declaredSchedFootprintSyscall`**, or
  `schedLockSetForSyscall_undeclared_none` stops elaborating.  That negative is
  what the object domain's own is: a caller reading `some S` treats `S` as the
  complete set of **cores** the transition writes, so an arm that returned a
  footprint before its coverage proof existed would hand out exclusion the
  runtime never established.  The other drift direction — an arm listed as
  declared that became unconditionally `none` — is closed by the per-arm
  `_isSome_iff` family, each stating the exact operands its arm needs.

  (2) **One operand record, because they are one syscall's operands.**
  `SyscallLockOperands` carries the scheduler domain's five extra fields beside
  the object domain's, defaulted absent, because the two domains ask *different
  questions of the same arm*: an object footprint names the objects a transition
  writes, resolved from the capability it was invoked through, while a scheduler
  footprint names the cores it writes, resolved by re-running the transition's
  own control flow — which needs the transition's own arguments.  `affinity` is
  **doubly** optional and must stay so: the inner `Option` is the unpin request,
  the outer says whether the operand was supplied, and collapsing them makes an
  unsupplied operand read as an unpin.

  (3) **Two arms route to a footprint that is not the obvious one.**
  `.notificationSignal` takes the **bound** arm's, which is the one the live
  dispatch reaches; `.reply` takes the **arm's** rather than the dispatch's,
  because `v0.35.163` proved the abandon's home-core member is one the dispatch
  never writes.  Both are pinned as relations, with the wrong resolver refused.

  (4) **The ABI seam reaches it since Cut C4b** (`v0.35.172`, the bullet below).
  Cut C4 shipped the resolver with nothing calling it, because
  `abiEntryLockOperands` supplied none of the five new fields — so wiring it that
  day would have made `.call`, `.reply`, `.replyRecv` and `.tcbSetAffinity`
  answer `none`: sound, since an undeclared arm establishes no exclusion, and it
  would have silently dropped four arms out of the coverage this workstream is
  building.  The resolver's docstring said so rather than leaving a reader to
  discover it by wiring it up, and C4b closed it by extending that one builder.
- **...and the ABI seam resolves ONE decode for BOTH domains** (WS-RR RR8.12
  Cut C4b, `v0.35.172`).  `declaredSchedLockSetForAbiEntry` is
  `declaredLockSetForAbiEntry`'s twin clause for clause — `abiEntryPlan`, then
  `abiEntryLockOperands` on that plan's answer, then the domain's own resolver —
  and it is still **inert** until the bracket cut.  Five things new code must
  respect.

  (1) **One builder, not two, and that is the whole of the cut.**  The obvious
  shape is a second operand builder for the scheduler domain; it is the shape
  that lets one domain's footprint be acquired around the other domain's
  transition, because two builders may resolve a capability differently, decode
  a different argument, or read a different state.
  `declaredSchedLockSetForAbiEntry_shares_decode` states the alternative as a
  fact: both footprints are functions of the *same* `(tid, decoded, stFilled)`
  and the *same* `ops`.  A Tier 3 negative refuses the resolver re-deriving the
  gate or the capability lookup.

  (2) **What that costs is a congruence the object domain must satisfy.**  One
  record for two domains means a field added for one could move the other's
  answer, so `lockSetForSyscall_ignores_sched_operands` says it cannot — stated
  over all five fields at once, so a sixth added without extending it is a field
  nothing has checked, and measured at the seam's own operands in the witness.
  That is what makes "the object domain is byte-identical to Cut C4's" a theorem
  rather than a reading of two definitions.

  (3) **Four arms grew the operands their scheduler footprint refuses without,
  and each names what its own live dispatch arm names.**  `.call` the invoked
  capability's rights and the receiver's slot base; `.reply` the `MessageInfo`
  and register payload `decodeFaultReply` reads to tell a restart from an
  abandon; `.replyRecv` the reply *payload* — MR0 stripped, badged with the
  **reply** capability's badge rather than the endpoint receive cap's, which is
  SM6.D's own distinction and is refused in the wrong spelling by a negative;
  `.tcbSetAffinity` the destination core through both decoders, since its inner
  `Option` is the unpin request.

  (4) **Eight arms are here because the SCHEDULER domain declares for them** —
  the five TCB-directed ones, the three SchedContext ones and the retype — and
  `lockSetForSyscall` answers `none` at every one of them whatever these fields
  hold.  `.schedContextBind` names the **decoded `threadId` argument** rather
  than the capability's object, because that is the thread its own live arm
  binds, and its raw operand is validated at its own lift.

  (5) **The `.replyRecv` footprint's CSpace root is the gate's own.**  The live
  arm passes `gate.cspaceRoot`; the scheduler resolver has no gate, so it reads
  the caller's TCB at the same state.  `abiEntryGate_cspaceRoot` and
  `abiEntrySchedReceiverCspaceRoot` are what make those one lookup rather than
  two readings of one question — the shape that would let a footprint name a
  root the transition does not walk.  The witness is state-dependent by
  construction: an `.Inactive` victim declares the object-store lock alone and an
  **active** one, one field apart, additionally declares the executing core's run
  queue, which a resolver ignoring the state could not do.
- **...and the family that resolver dispatches to is derived and reconciled**
  (WS-RR RR8.12 Cut C5, `v0.35.173`).
  `SeLe4n/Testing/SchedFootprintCensus.lean` (Tier 1) is the object domain's
  `LockFootprintBoundCensus` for the scheduler domain, and it exists because Cut
  8a-ii measured the gap: **thirty-three of the family's forty-seven theorems
  had neither a consumer nor a Tier 3 anchor**, every one silently deletable,
  because their consumer is the bracket cut and the bracket cut has not landed.
  Eight hand anchors were the stopgap; a hand-written list is what a census
  retires.  It asks two questions, and reports **17 footprints, all canonical,
  15 consumed, 2 registered as superseded**.

  (1) **Every footprint is the canonical `schedFootprintOfCores` ladder, at its
  full arity** — and that is not a style rule, it is the premise every generic
  lemma is consumed under.  The scheduler domain restates none of
  `_write_only` / `_pairwise_le` / `_keys_nodup` / `_subset` / `mem_…_iff` per
  footprint, because they are stated once of `schedFootprintOfCores` and
  inherited *by being that function applied to two core lists*; a footprint
  written any other way loses all five **silently**.  `_keys_nodup` is
  `SchedLockSet.ofList?`'s own obligation, so such a footprint can make the
  constructor refuse and the arm then answers `none` — an *undeclared* arm,
  which the bracket treats as no exclusion established, so it is sound and it
  drops the arm out of the coverage this workstream is building.  `_pairwise_le`
  is the ladder's acquisition order, and there is no other proof of it.  The
  question is put to the elaborator by reducing **towards** the constant
  (`Meta.whnfUntil`), since `whnf` would run past it into the `List.cons` the
  body builds and the question would be unaskable.

  (2) **Every footprint is NAMED by `schedLockSetForSyscall`, or registered with
  a reason** — and *named*, not *reached*: a transitive closure would count a
  footprint as consumed because some reachable helper mentions it, which is the
  presence-for-relation substitution one level down and would silence the census
  exactly where it fires.  The register holds two supersessions — the **bare**
  notification signal (the live dispatch routes through the bound arm) and the
  **dispatch**-level reply footprint (the arm's sits over it, and `v0.35.163`
  proved the abandon's home-core member is one the dispatch never writes) —
  reconciled in both directions, so a stale exemption fails as loudly as an
  orphan footprint.

  (3) **Neither failing branch can fire on the live tree, so the plants are the
  measurement.**  A canonical footprint and a hand-written ladder carrying a
  member the canonical form also carries; a constant with the family's **name**
  and not its **type**, which must stay outside the derived family permanently
  rather than for the length of one mutation run; and a namer pair whose
  indirect half is what separates *named* from *reached*.  The pair alone is not
  enough — it decides `namedBy`, and a `resolverConsumed` that closed over it
  transitively would pass every plant — so the self-test carries a **wiring
  case** drawn from the live tree: a write-set helper is named by a footprint and
  by no arm, so it is reached at depth two and named at depth one by nothing.

  (4) **The shape check carries no arity test, deliberately.**  The applied term
  is the definition at its full telescope and its type is
  `List (SchedLockId × AccessMode)`, so a reduction stopping with
  `schedFootprintOfCores` as head has it fully applied by type-correctness: the
  condition could only ever be true, and *a condition no input can decide is
  indistinguishable from a wrong one*.  A Tier 3 negative refuses it coming back.
- **...and the first eight arms' footprints are proved not to be false** (WS-RR
  RR8.12 Cut C6a, `v0.35.174`).  A footprint that omits a slot the transition
  writes is **false**, and the 2PL serialisation results,
  `boundedWait_under_2pl` and the CC-5 contention bound are then *silent* about
  that slot rather than conservative —
  `UncoveredLockDomain.syscallSeamSchedulerDomain` was the register entry saying
  the scheduler domain had not met that standard at the syscall seam (retired at
  Cut C6h, `v0.35.181`, once it had).  Cut C4
  gave every declared arm a footprint and C4b wired the seam's resolver to it;
  **the coverage lands before the bracket**, which is the numbering rule's
  semantic half: a bracket acquiring a footprint nobody proved covers the writes
  hands out exclusion the runtime never established.
  `SeLe4n/Kernel/SyscallSchedContainment.lean` is staged, for the reason
  `SchedLockTimerContainment` is — every proof consumes an SM8.B confinement
  theorem, and those are staged.  Four things new code must respect.

  (1) **One bridge, and the three clauses are discharged three different ways.**
  `schedFootprintCoversWrites_of_cores` (production, beside the obligation) makes
  the **object** clause structural — `schedFootprintOfCores` always names the
  object-store table write lock, a scheduler footprint being a footprint of an
  operation that stores — and reduces the rest to two hypotheses;
  `schedFootprintCoversWrites_of_confined` (staged) supplies the **run-queue**
  clause from the arm's own `observableSlotsConfinedToCores`.  The **replenish**
  clause has no such bridge and cannot: confinement covers six per-core slots and
  the replenish queue is not one of them, which is exactly why every donating arm
  carries a frame of its own.  A new arm's coverage is one application, not a new
  argument.

  (2) **The split between this cut and the next is semantic, not convenient.**
  Where an arm's replenish segment is `[]` the clause is a **whole-state frame**
  (the transition writes no core's replenishment at all); where the segment names
  cores it is an **exactness** claim (unchanged outside exactly those).  Those are
  different propositions with different frames, so the empty-segment arms —
  `.notificationWait`, `.notificationSignal`, `.send`, `.tcbResume`,
  `.tcbSetPriority`, `.tcbSetMCPriority`, `.schedContextBind` — are here, and
  `.tcbSuspend` joins them because RR8.12's fourth cut already built its `_ne`
  frame.  The remaining eight are Cut C6b's, with the frames they need.

  (3) **Eight proved theorems cannot be wrong; they can be VACUOUS**, so the
  module carries the refutations that say the obligation is not held by every
  footprint — one per clause, and the replenish one is the sharper because it is
  the clause no confinement result can reach.  A Tier 3 negative refuses
  `schedFootprintCoversWrites_refl` anywhere in the module: discharging an arm
  with the no-op lemma is the token-preserving weakening this family admits, and
  it would turn eight measurements into eight tautologies.

  (4) **A coverage claim names the arm the live dispatch reaches.**
  `.notificationSignal`'s is stated of the **bound** arm, which is what the
  resolver names and what `API.dispatchWithCap{,Checked}` routes to; the bare
  signal's footprint is registered as superseded in `SchedFootprintCensus`, and a
  coverage theorem for it would be a claim about a transition no syscall reaches.
- **...and the first three core-naming segments are covered, with the `_ne`
  frames keyed on the FOOTPRINT rather than on a resolution** (WS-RR RR8.12 Cut
  C6b, `v0.35.175`).  `.schedContextConfigure`, `.schedContextUnbind` and
  `.tcbSetAffinity` are the first arms whose replenish segment names cores, so
  their clause is an **exactness** claim rather than a whole-state frame.  Three
  things new code must respect.

  (1) **An arm's `_ne` frame is keyed on its own replenish segment.**
  `schedFootprintCoversWrites`'s clause asks *unchanged at every core the
  footprint does not name*; a frame keyed on a resolution — "`c` is not this
  SchedContext's replenish home", "`c` is not this thread's target core" —
  answers a different question that every consumer must then case-split to reach,
  which is the duplication this family exists to avoid.  So the footprint-keyed
  form carries the plain `_ne` name and the resolution-keyed one is `_ne_of_sc` /
  `_ne_of_tcb`; a Tier 3 negative refuses the plain name re-acquiring the narrower
  hypothesis, because a family where `_ne` means two things at two arms is exactly
  what a coverage proof gets wrong without noticing.

  (2) **An unresolved segment is a refusal, not a gap.**  A
  `.schedContextConfigure` whose SchedContext does not resolve, and a
  `.schedContextUnbind` whose SchedContext has no bound thread, both make the
  *transition* fail — so the empty segment costs the claim nothing, and the proof
  says so by deriving the contradiction rather than by assuming resolution.

  (3) **`allCores` is a segment, and the clause is then vacuous — correctly.**  A
  SchedContext bound to a thread the store no longer holds has no `cpuAffinity`
  left to read, so the unbind sweeps every core's replenishment and the footprint
  declares every core's lock; there is no core outside it, which is the honest
  reading rather than a hole.
- **...and the two IPC spines get their exactness frames, with `.call` covered**
  (WS-RR RR8.12 Cut C6c, `v0.35.176`).  The IPC arms' replenish segments are
  *computed by running the transition*, so their exactness frames are the one
  place a footprint and its operation could describe different migrations.  Four
  things new code must respect.

  (1) **The segment's branch structure and the transition's are the same
  structure, by construction** (Cut C3a), so each frame is one case split that
  visits both at once rather than a second reading of the transition.  Every arm
  short of a resolving donation leaves the segment empty and the step's own frame
  applies; the resolving arm is the SM5.H migration's `_other` frame at exactly
  the pair the segment names.

  (2) **Each donation step gets its own `_ne` beside its `_of_no_donation`.**  The
  existing frames say the hand-off moves *nothing* when the resolver declines;
  the new ones say *where* it moves when it answers, which is what the replenish
  clause needs.  Both directions matter and neither implies the other.

  (3) **The `.reply` arm's frame cannot be the hypothesis-parameterised one.**
  `replyTransferOnCore_replenishQueueOnCore_of_dispatch` asks for the dispatch's
  frame at *every* message, and the segment is message-dependent — the fault
  branch composes the dispatch at `IpcMessage.empty` and the ordinary branch at
  `msg`.  So the footprint-keyed frame is stated per branch, through
  `faultReplyOnCore_replenishQueueOnCore_ne`, and `faultReplyApplyOnCore` frames
  every replenish queue on both its outcomes.

  (4) **`.call`'s coverage is stated of the UNCHECKED dispatch** — what the write
  set and the confinement result are stated at, and what the checked arm equals
  wherever its flow gate admits; a denied flow commits nothing, so the covered set
  is the same either way.  `.reply`'s coverage waits on a confinement theorem at
  `replyTransferWriteSet` that does not exist yet, which is Cut C6d's first row
  rather than an omission here.
- **...and a coverage claim names the ARM, not the dispatch beneath it** (WS-RR
  RR8.12 Cut C6d, `v0.35.177`).  `schedLockSet_replyTransferOnCore` had nothing
  behind it because the confinement surface stopped at
  `endpointReplyCrossCoreDispatch`, and the arm `API.dispatchWithCap` runs is
  `replyTransferOnCore` — seL4's `doReplyTransfer` branch — whose **post-state is
  not the dispatch's**: it adds the delivered-message staging on an unfaulted
  caller and the decoded outcome on a faulted one, the latter either installing a
  restart frame or *descheduling* the faulted thread.  A coverage claim proved at
  the dispatch is a claim about a different state, however closely the two write
  sets agree.  Three things new code must respect.

  (1) **Each member of the chain is stated at the write set its OWN definition
  derives** — `applyFaultRestart_confinedToCores` at `[]`, the abandon's at
  `[cc]`, `faultReplyApplyOnCore_confinedToCores` at `faultReplyApplyCores`,
  `faultReplyOnCore_confinedToCores` at `faultReplyWriteSet`, and the arm's at
  `replyTransferWriteSet` — so the coverage theorem is one application of
  `schedFootprintCoversWrites_of_confined` and not a second reading of the seam.
  The `regs` conjunct is what made two machine frames load-bearing and missing
  (`applyFaultRestart_machine_eq`, `faultAbandonOnCore_machine_eq`): a fault
  outcome writes the *thread's* saved context, never the executing core's bank.

  (2) **A claim about what a transition writes is read off a measurement, not off
  the shape of the definition that declares it.**  This cut's own first draft said
  the abandon "deschedules on a core the dispatch never names".  It does not:
  every arm on which the dispatch succeeds opens its write set with
  `[determineTargetCore st target]` and no step of it writes a `cpuAffinity`, so
  the appended `determineTargetCore st' faulted` is a **duplicate** — and
  `tests/FaultHandlingSuite.lean` §7c had been measuring exactly that since Cut
  C3a.  The draft was written from the definition's shape with the measurement
  sitting beside it unread.  When a cut's finding is about what a program writes,
  find the assertion the tree already makes about it *before* writing the
  sentence; where there is none, the sentence is what the cut owes.

  (3) **The declaration stays derived from the arm, and the measurement becomes an
  assertion.**  Tightening the segment to today's coincidence would make it false
  the moment either side moved, so the write set is still the arm's own; what
  changed is that the duplicate is now asserted, with the restart's *empty* append
  as its control — a write set naming every core satisfies neither.
- **...and a coverage claim's UNIT is what the footprint bounds, which may be a
  sub-composition** (WS-RR RR8.12 Cut C6f, `v0.35.179`).  `.receive` is the one
  declared arm whose chain walk sits **outside** its run segment — the walk's
  cores are state-discovered and are declared dynamically through
  `pipChainSchedFootprint` — so `schedLockSet_endpointReceiveOnCore_coversWrites`
  is stated at the leg composed with WS-OD OD3.6's donation, and a claim at the
  whole hand-off would be *false* of that footprint.  A Tier 3 negative refuses
  that spelling, because a coverage theorem naming the wrong unit reads exactly
  like one naming the right one.  Three things new code must respect.

  (1) **A footprint resolved BEFORE a transition and a resolver read AFTER it
  must be shown to name the same thing.**  The arm hands the hand-off the thread
  the *leg* reports; the segment is read off the *pre-state* send queue.
  `endpointReceiveDualWithCapsOnCore_ok_dequeued_eq_head` and its block-path
  sibling are what close that, and they did not exist: every other rendezvous
  frame did, because until a coverage proof nothing had to relate the leg's
  **output** to the resolver.  A new arm whose footprint and transition resolve at
  different states owes the same lemma.

  (2) **Look for the degenerate case before reaching for an invariant.**  The
  block path hands the hand-off the *receiver's own id*, and
  `callDonationSchedContext?_self` — a thread donates nothing to itself, because
  the resolver reads an `.unbound` binding twice — is that path's whole donation
  story.  No reasoning about the post-state `ipcState` is needed there at all.
  `queueHeadBlockedConsistent` is then taken for exactly one corner and named at
  the point of use rather than carried by the family.

  (3) **Write the helper and let the build tell you it exists.**  Two confinement
  theorems this cut needed were written, compiled, and rejected as *already
  declared* — the tree has had both since WS-OD OD3.6.  That is a cheaper search
  than grepping for a name you would have had to guess.

  One mechanical note, the same hazard as Cut C6e's at a smaller unit: an anchor
  pattern written against a witness label containing a **backtick** must count the
  characters, because `.` matches one — `the .receive. segment` misses
  ``the `.receive` segment`` by exactly one.  The sweep reported it as a failing
  command rather than as a silent pass, which is the direction that class must
  fail in.
- **...and two lock DOMAINS that write the same word are one footprint, never
  two brackets** (WS-RR RR8.12 Cut C6h, `v0.35.181`).  The syscall seam brackets
  on the scheduler domain now, which deletes
  `UncoveredLockDomain.syscallSeamSchedulerDomain` — and the design was decided
  by a measurement that **contradicted the retired constructor's own stated
  reason**.  It said the object-domain footprints hold `stateLevelLock` and
  per-object locks *"**not** the object-store table lock"*; they are the same
  lock, because `acquireLockOnObject`'s `.objStore` arm writes
  `SystemState.objStoreLock` and reads nothing else of the `LockId`.
  `schedObjStoreLockId`'s docstring had said so since SM5.A.2 and **nothing
  stated it**, which is why a claim built on the opposite could stand for
  fourteen minor versions.  Four things new code must respect.

  (1) **Nesting two brackets over one set of lock words is a ladder violation,
  not a double-acquire nuisance.**  `lockAcquireSequence` orders *one* list, so
  an inner bracket's level-0 table lock taken after an outer bracket's levels
  1..9 is a sequence the SM0.I ordering theorem says nothing about — and
  deadlock freedom in this tree rests on that ordering.  The seam therefore
  acquires one unified `SchedLockSet`, which is what `SchedLockId` was
  introduced for: *a cross-domain order exists precisely so a cross-domain
  acquisition is one ladder.*

  (2) **A canonicalisation is sound only if EVERY operation on the two keys
  agrees**, so it is pinned at all four primitives — acquire, release, withdraw
  and held.  Pinning the acquire alone would leave a release that read the
  `ObjId` free to disagree, and the two keys would then be one word for taking
  and two for giving back.

  (3) **A claim travels to a superset rather than being restated at it.**
  `schedFootprintCoversWrites_mono` is why the sixteen per-arm coverage theorems
  are not re-proved over the unified footprint: every clause of the predicate is
  of the form *"a lock the footprint does **not** name"*, so a superset only
  discharges more antecedents.  Read the direction carefully — it is about the
  *obligation*, not about footprint quality: lock contention is an observable
  channel (SM8.D's CC-5), which is why the footprints themselves stay narrowed
  per arm.

  (4) **Acquiring is not covering, and that asymmetry is what makes a bracket
  landable early.**  An arm declared in one domain and not the other acquires
  what that domain declared; the other domain's writes stay outside a footprint
  until it declares one.  An arm neither declares is the bare step, bit-identical
  to the pre-bracket seam.  That is RR7.12's posture, and it is the reason a
  bracket may precede the declarations it does not yet have while a *coverage*
  claim may not.
- **...and a claim's unit is the PROGRAM the arm runs, wrappers included** (WS-RR
  RR8.12 Cut C6g, `v0.35.180`).  The sixteenth and last declared arm, and the one
  whose transition is three wrappers deep: `.lifecycleRetype` dispatches
  `lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache` — the retype with its
  cleanup, the `.aside1` shootdown round for the destroyed and rebound ASIDs, the
  initiator's own per-core TLB drain, and the domain-wide `IC IALLUIS`.  Each of
  those two cached-structure layers writes kernel state, so a coverage claim taken
  at the retype core is a claim about a program the arm does not run, and a Tier 3
  negative refuses that spelling.  They are both scheduler-silent *by theorem*
  (`retypeInitiatorDrain_scheduler`, `Architecture.withIcacheBroadcast_frame`'s
  third conjunct), which is what lets the exactness frame descend through them by
  citation rather than by a second case analysis of the arm — the difference
  between a claim that inherits its wrappers' frames and one that re-derives them.
  Three things new code must respect.

  (1) **A segment over a destroyed object is read at the PRE-state, and that is
  not a convenience.**  The object a retype destroys is gone from the post-state,
  so a post-state reading of `lifecycleRetypeWriteSet` or
  `lifecycleRetypeReplenishCores` would name the empty set on exactly the
  transition the segments exist for.  Both take `st`, which is also what a bracket
  needs — it resolves a footprint *before* the transition runs — so this arm has
  no instance of WS-HP HP10.8's footprint/transition resolution asymmetry.

  (2) **The layering rule is a convention, not an accident, and this is its
  fourth instance in one sequence.**  `retypeInitiatorDrain_scheduler`,
  `retypeInitiatorDrain_machine` and a private `lifecycleRetypeDirect_framed` were
  declared in the **staged** `InformationFlow/NonInterferenceCrossCore.lean`, so
  the production replenish frame could not read the two frames it needs and the
  third was a private duplicate of a fact the production wrapper module can state
  outright.  They live beside the wrappers they frame now.  Cuts 5, 7, 8a-ii and
  C3a each paid the same rule; when a sequence pays it four times, a new frame
  over a production transition goes beside that transition on the day it is
  written rather than in whichever module first needed it.

  (3) **Where every mutation breaks ELABORATION, the witness is a differential
  inside the suite.**  Dropping either of this footprint's segments, or widening
  both to `allCores`, fails to elaborate — the definition's own membership
  theorems unfold it — so a coverage assertion in `tests/SmpIpcSuite.lean` cannot
  be shown decisive against the production code by mutation.  That is §3.23's
  situation for the splice's store shape, and the answer is §3.20's: §3.33 (d)
  takes the *same measurement* over `runOnlyRetypeFootprint` — the retired reading
  with no replenish segment, spelled in the suite and nowhere else — and asserts
  it **fails**.  A coverage assertion with no failing counterpart beside it is
  indistinguishable from one the fixture satisfies by accident.
- **...and a NEGATIVE anchor over prose is a prose check, which only a mutation
  tells you** (WS-RR RR8.12 Cut C6e, `v0.35.178`).  The cut retired a hand-kept
  figure — `SyscallSchedContainment.lean`'s §7 said *"Eight coverage theorems
  above"* at fourteen — and wrote a `run_negative_check` refusing its return.  It
  passed on the clean tree and **passed on the mutation that restored the
  sentence**, because the sentence lives in a `--` comment and `run_negative_check`
  reads the code view, which blanks it.  That is this file's own *gates read code,
  prose reads prose* rule at the one case it exists for — the subject genuinely
  **is** the text — and the anchor is `run_prose_negative_check` now.  What is worth
  keeping is not the instance but how it surfaced: a negative that cannot match is
  indistinguishable from a tree that is clean, so the only thing that separates them
  is breaking the relation it forbids.  Ask of every new negative whether its
  subject survives the view the helper routes through.

  Two further things that cut recorded.  **The composite's frames are keyed on the
  SUB-SEGMENT each stage appends**, not on which path the stage took: a four-stage
  arm whose frame took four path hypotheses would be a claim a bracket cannot
  discharge, since a bracket resolves the footprint before the transition runs.  And
  **a sweep's own input can be malformed, which the row accounting catches**: the
  first run reported *"accounted for 473 of 474 selected rows"* because
  `select_changed_anchors.py` writes its `# derivation:` line to stderr and the
  invocation had merged it in with `2>&1`.  The gate was right; read a shortfall as
  a question about the selection before reading it as a question about the anchors.
- **A thread's base priority has ONE home: `TCB.priority`** (`v0.35.133`).  It had
  **two** until this cut — the TCB field and, mirrored onto it by the AK2-B
  propagation convention, its reservation's `SchedContext.priority` — with
  `SystemState.threadBasePriority` choosing between them by
  `SchedContextBinding.ownScId?` and `boundThreadPriorityConsistent` keeping the
  pair in step.  The pair is what `v0.35.98` found `.tcbSetPriority` not
  maintaining: a demotion re-bucketed the thread at its new band while every
  later wake re-inserted it at the old one, permanently, because the run queue is
  keyed by `TCB.boostedPriority` (the thread's field) and the resolver read the
  reservation's.  A demotion that does not stick is a temporal-isolation break in
  exactly the mixed-criticality deployments MCS exists for, and it needed no
  authority beyond what the syscall already requires.

  **The remedy is structural rather than another writer** — for *reads*, and
  `v0.35.136` is where that qualification stops being implied and starts being
  printed.  This paragraph said "with one home the pair is unfalsifiable by
  construction, so a stale mirror is not a defect that was fixed but a state no
  writer can reach", and PR #897's review found the writer: the collapse gave the
  band one **reading** home and left it two **writing** homes, so a stale mirror
  is still reachable and `boundThreadPriorityConsistent` is still falsifiable —
  it just no longer mis-schedules anything, which is the whole of what the
  collapse bought.  See the standing constraint *a `bound*Consistent` predicate
  is a writer fact* below for the two routes and the register row.  Six things
  new code must respect.

  (1) **Every reader reads `TCB.priority`, at every binding.**  Five did the
  classification and all five are collapsed: `SystemState.threadBasePriority`,
  `resolveEffectivePrioDeadline`, `effectiveSchedParams`,
  `getCurrentPriorityChecked` and the frozen
  `FrozenSystemState.threadBasePriority`.  `threadBasePriority_eq`,
  `effectiveBucketPriority_eq` and `FrozenSystemState.threadBasePriority_eq` are
  the `rfl` statements of that, and `FrozenSystemState.threadBasePriority_eq_live`
  is the live/frozen agreement — which under two homes could only be stated per
  binding and under a consistency hypothesis, and is now the strongest form such
  an agreement can take.

  (2) **`effectiveBucketPriority` was the THIRD copy of the resolver and its body
  is gone.**  It mirrored `resolveEffectivePrioDeadline` because
  `Scheduler/Invariant.lean` sits below `Selection.lean` and could not call it —
  a second implementation held in step by a pin, which is the shape this project
  spends its length retiring and which existed only because there were two bases
  to choose between.  It is `TCB.boostedPriority` now and the pin is `rfl`.

  (3) **The run-queue invariants moved with the readers, and then COLLAPSED.**
  `effectiveParamsMatchRunQueue` and `effectiveParamsMatchRunQueueOnCore` asserted
  on their `.bound` arm that the recorded bucket equals the RESERVATION's
  `priority`.  That was over-strong the moment the base had one home — the queue
  is keyed by `TCB.boostedPriority` — and under two homes it was precisely the
  conjunct that had to hold for the `v0.35.98` defect not to strand a demoted
  thread.  With all three arms saying the same thing the binding case analysis is
  **deleted**, and auditing this cut's own diff is what showed that keeping it was
  wrong rather than merely untidy.  Its `.bound` arm ended `| _ => True`, so a
  bound thread whose reservation did not resolve was silently excused from the
  bucket claim: *a scanner's default branch is a decision* one artefact over — a
  **predicate's** default arm is one too, and that one excused a case nobody chose
  to excuse.  And under two homes this predicate and `schedulerPriorityMatch` were
  **jointly unsatisfiable** for any bound thread whose mirror had drifted, which is
  the S-H04 over-constraint `Scheduler/Operations/Core.lean`'s own header records
  — so the collapse is what makes the pair satisfiable rather than merely shorter.

  (4) **Three theorems retire into one, and the HYPOTHESES are the point.**
  `boostedPriority_eq_resolve_unbound` (AI3-A) related the selector's base
  component to `TCB.boostedPriority` at `.unbound`;
  `resolveEffectivePrioDeadline_fst_eq_boostedPriority_of_agree` (SM5.I) extended
  it to `.bound` **under the `boundThreadPriorityConsistent` agreement specialised
  to the thread**; `resolveEffectivePrioDeadline_fst_of_donated` (WS-OD) was the
  `.donated` payoff.  With one home the `.bound` arm reads the TCB field like the
  other two, so that agreement hypothesis is discharged by nothing at all — and a
  name like `_of_agree` kept past its hypothesis is not merely redundant, it
  *teaches a false dependency*: a reader would go on believing that weakening the
  bind/configure propagation costs the selector its priority ordering.  It does
  not.  The three are deleted for the one unconditional
  `resolveEffectivePrioDeadline_fst_eq_boostedPriority`, with a tombstone and
  three Tier 3 negatives.  **Deadlines have no counterpart and must not be read as
  having one**: bind copies only the priority, so a TCB-*deadline* comparison still
  diverges from the selector for exactly the bound threads CBS exists for, which is
  what the `chooseThreadEffectiveOnCore` gate says.

  (5) **`SchedContext.priority` survives as what it always was on the WRITE side**
  — the band a reservation *configures* its bound thread to, propagated into the
  TCB by `schedContextBind` and `schedContextConfigureBoundPropagate` — and no
  scheduling decision reads it.  `boundThreadPriorityConsistent` is therefore no
  longer load-bearing for any read; it is **kept, not retired**, as the only
  artefact stating that the propagation happened, which is a real property of those
  two writers and not a tautology.  A new *reader* of `SchedContext.priority` as a
  thread's band is the defect this cut closed; a new *writer* still propagates.
  **And a justification that names a constraint the cut removed invites deleting a
  live write**: `schedContextBind`'s propagation comment said the two run-queue
  invariants *jointly force* `tcb.priority = sc.priority` with no operation
  establishing it — its whole stated reason, and false the moment neither predicate
  read a reservation.  When a cut retires a constraint, sweep the comments that
  cite it as a *reason*, not only the ones that cite it as a fact.

  (6) **A witness for a collapsed mirror lives on the state the collapse makes
  UNREACHABLE.**  The soundness argument and the testability problem are the same
  sentence: on a state satisfying `boundThreadPriorityConsistent` the two readings
  agree *by construction*, so a fixture built there asserts nothing about which one
  is live and passes either way.  What discriminates is a **drifted** state — the
  shape `v0.35.98` produced — and four fixtures in this tree were already sitting
  on one, which is why all four failed when the readers collapsed.  The instinct on
  such a failure is to make the fixture consistent; that is right for a fixture
  whose subject is the *operation* and wrong for one whose subject is *which field
  the operation reads*, and doing it everywhere would have left the cut with no
  decisive witness at all.  So `AK8-E.2` and `AN10-D.6` keep their drifted states
  and flip their expectations; `PM-010b` becomes consistent because its subject is
  the cap firing, with `PM-010c` added to carry the drifted half; and the
  `v0.35.99` frozen-ceiling witness is restated over **both** branches of the cap,
  since the divergence it was written for has no state left to arise on and what
  survives is that the two surfaces fire *and decline* together.  Generalising:
  when a cut makes two readings agree everywhere, the only witness that can fail on
  a revert is one standing on the disagreement the cut abolished — keep it, name it
  as such, and say in the fixture why the state is one the kernel no longer
  reaches.

  The collapse is behaviour-preserving on every reachable state, and that is
  measured rather than argued: `schedContextConfigurePropagates` is
  `ownScId? = some scId`, which is exactly the condition the retired resolver
  classified on, so the two readings differ only where the mirror had already gone
  stale — and the golden trace is byte-identical at 239/239 with the whole library
  building.

  The **frozen** surface writes the configured band too (`v0.35.99`):

  `FrozenSystemState.threadBasePriority` is its reader and
  `frozenWriteBasePriority` the one writer both `frozenSetPriority` and
  `frozenSetMCPriority`'s ceiling call, so a new frozen priority operation reads
  and writes the pair the way the live one does rather than growing a second
  answer.

  **And a priority write moves the thread's run-queue BUCKET, on both surfaces**
  (`v0.35.101`, reported on PR #897).  `TCB.boostedPriority` is
  `priority.raisedBy pipBoost`, so a **base** write moves the run-queue key exactly
  as an inherited-**boost** write does, and every live writer of either re-buckets:
  `updatePipBoostOnCore`, `migrateRunQueueBucketOnCore` (which
  `applyPriorityChangeOnCore` composes) and `schedContextBind`'s Z5-G3 step.  On the
  frozen surface the mechanics were spelled *inline* in `frozenUpdatePipBoost`, so
  only the boost half was answered and three base writers moved nothing.  They are
  one definition now — `frozenQueuedAnywhere`, `frozenRebucketRunnable` and
  `frozenWriteTcbRebucketed` (`FrozenOps/Core.lean`, beside `frozenEnsureRunnable`)
  — and a new frozen writer of either field calls them.  Two things new code must
  respect.  (1) **The guard is per-operation and the mechanics are shared**, because
  the live writers disagree about the guard and faithfully: `updatePipBoostOnCore`
  migrates only `if oldPrio != newPrio` while the base writers migrate whenever the
  thread is queued, and the difference is observable — `RunQueue.insert` appends, so
  a remove-and-reinsert at an unchanged key moves the thread to its bucket's tail,
  and `frozenRunAgrees` compares buckets as **lists**.  (2) **The key is the live
  accessor**, read off the record being written: `frozenEnsureRunnable` and
  `frozenChooseThread` already read `TCB.boostedPriority`, so "which bucket does this
  thread belong in" has no frozen-specific answer and must not acquire one.  The
  third site was found by sweeping the *question* rather than the two the review
  named: `frozenSchedContextConfigure` propagated **neither** thread-owned parameter
  and re-bucketed nothing, so every frozen post-configure state with a bound owner
  falsified `boundThreadPriorityConsistent` **and** `boundThreadDomainConsistent`.

  What `v0.35.98` measured, on the live per-core dispatch path: a
  `seL4_TCB_SetPriority` demotion of a bound thread from 50 to 10 re-bucketed it
  at 10 and its first wake re-inserted it at **50**, the band the demotion had
  removed — permanently, since every later wake reads the same stale field.  A
  demotion that does not stick is a temporal-isolation break in the
  mixed-criticality deployments MCS exists for, and it needed no authority
  beyond what the syscall already requires.

  **And the frozen surface reads the same field because the live resolvers read
  it, which is now a theorem rather than a coincidence** (`v0.35.134`).
  `effectiveSchedParams_fst_eq_boostedPriority` states that the triple-valued
  resolver's priority component **is** `TCB.boostedPriority`, unconditionally and
  derived from the existing pair bridge; `FrozenOps.Agreement`'s
  `frozenComputeMaxWaiterPriority_eq_live_reading` carries that across to the
  frozen waiter fold, quantified over *every* live state because the reading
  turns out to read none of it.  PR #897's review reported the two as diverging,
  correctly against `v0.35.132`; `v0.35.133` closed it and swept neither the
  prose nor the missing pin, which is this file's own *sweep the forward-looking
  prose* rule unrun at the cut that made it stale.

  **Sweeping that question found `frozenResumeThread` reading the wrong priority
  in three places**, and the three are what a mirror looks like when nothing
  compares it.  It cleared `ipcState` alone where the live `restoreToReady`
  clears five fields — the fifth, `pendingReceiveReply`, keeps `replyIsStashed`
  true and so makes lifecycle cleanup of that Reply answer `revocationRequired`
  with no receive pending; it carried the pre-suspend `pipBoost` where the live
  resume re-derives it from the post-restore blocking graph; and it compared the
  two **base** priorities where the live test compares the effective ones, so the
  surfaces disagreed in both directions whenever either thread carried a boost.
  Three things new code must respect.  (1) **The field clear is
  `TCB.restoredToReady`** (`Model/Object/Types.lean`, beside `TCB.boostedPriority`
  and `TCB.blockingServer?`), because it had *no name to call* — it was spelled
  inline inside `updateTcb`'s lambda, which is why the mirror carried four fewer
  fields; both surfaces call it now, so a field added to the restore reaches both
  by construction.  (2) **A frozen scheduling decision reads
  `TCB.boostedPriority`**, never `TCB.priority`, and the live counterpart to cite
  is `resolveEffectivePrioDeadline_fst_eq_boostedPriority`.  (3) **Clearing
  `current` is the frozen spelling of the live re-enqueue-then-schedule** —
  dispatch here is `current := some tid` with the thread left in its bucket — so
  that one is *not* a divergence, which was checked rather than assumed.

  What made all three invisible is worth more than the instances: none of the
  three frozen-resume scenarios sets `scheduler.current`, so the preemption
  branch was unexecuted, and `.tcbResume` is outside `FrozenOpBranch.all`, so no
  differential reached it — while the live side has had four scenarios for the
  same two steps since R5.B and PR #811.  `frozenOpUncheckedReason` had recorded
  the gap as *"adapter owed"* the whole time.  **A stated reason bounds nothing**;
  it says who owes the work, and until it is paid a cut that touches a live
  transition with a frozen mirror sweeps the mirror by reading both bodies.

  **And the collapse had a SIXTH reader and an unswept theorem family**
  (`v0.35.134`, PR #897's review against `v0.35.133` itself).
  `threadSchedulingParams` (`Model/Object/Structures.lean`) — the Z1-N migration
  bridge, reachable from the root-imported model API — still took a `.bound` or
  `.donated` thread's band from `sc.priority`.  It is **deleted**, not
  collapsed, and on measurement: zero consumers anywhere in the tree, so
  collapsing it would have produced a fourth reading nobody asks.  New code
  reads `effectiveSchedParams`.

  The family is the same rule one file over.  `v0.35.133` deleted
  `resolveEffectivePrioDeadline`'s three arm-specific readings *because a name
  kept past its hypothesis teaches a false dependency*, and left
  `effectiveBucketPriority`'s six standing with hypotheses the same collapse had
  made dead — three binding-arm instances of the unconditional lemma, one about
  an expression shape the accessor no longer contains, and two frames demanding
  that SchedContext lookups agree of an accessor that reads no store.  All six
  are gone for the unconditional `effectiveBucketPriority_congr`, and the one
  consumer lost seventy lines of case analysis for one citation.  **When a cut
  collapses a definition, the theorems whose hypotheses that definition supplied
  are part of the collapse** — the sweep is the family, not the body.

- **A `bound*Consistent` predicate is a WRITER fact, not an invariant — and the
  domain mirror had the same hole** (`v0.35.136`, PR #897's review, reported for
  the priority half).  `returnDonatedSchedContext`'s bottom arm installs a
  `.bound` binding and writes neither the recipient's `priority` / `domain` nor
  the reservation's, so whichever home moved while the reservation was on loan
  comes back disagreeing: `boundThreadPriorityConsistent` and
  `boundThreadDomainConsistent` are both **false** on a state the kernel reaches.
  Five things new code must respect.

  (1) **Two routes, both ordinary syscalls, and the second breaks both predicates
  at once.**  `.tcbSetPriority` on the **unbound** donor writes its TCB alone —
  correctly, since it owns no reservation to mirror to — and
  `schedContextConfigure` of the **donated** reservation writes `sc.priority` and
  `sc.domain` alone, also correctly, the propagation being gated on the donee's
  `ownScId?`, which is `none` (WS-OD `v0.35.3`, and the whole point of that gate).
  Either way the pop then rebinds the origin under the disagreement.

  (2) **Neither reconciliation is available to the pop**, which is what makes this
  a fact about the *writers* rather than a defect in the pop.  `tcb.* := sc.*`
  would undo a demotion, or **migrate a thread's partition**, on an IPC reply — at
  the instance of a holder of a capability on the *reservation*, which says
  nothing about the thread, and which is the crossing WS-OD closed from the other
  side.  `sc.* := tcb.*` would silently retune what that capability's holder had
  just set, and is projection-**visible** besides, since `SchedContext.priority`
  survives `projectKernelObject`.  A cut that decides otherwise must change
  `donationReturnSchedContext_priority` / `…_domain`, which exist so that it has
  to.

  (3) **The domain now has one reading home too.**  `v0.35.133` collapsed the
  *band*'s readers and left `effectiveSchedParams`'s `.bound` arm reporting
  `sc.domain`, on the stated ground that the domain mirror had *"no writer known
  to break it"* — and this finding is that writer.  `effectiveSchedParams_domain_eq`
  is the unconditional pin that every arm reports `tcb.domain`, the sibling of
  `effectiveSchedParams_fst_eq_boostedPriority`; it was **free**, the component
  having no live consumer (every domain filter reads `tcb.domain` directly through
  `chooseBestRunnableInDomainEffective`) and the golden trace staying
  byte-identical.  *A stated reason that no writer exists is a claim about every
  writer, and it is the kind that ages.*

  (4) **So the residue is a verification gap and not a scheduling one**, and that
  distinction is measured rather than asserted: the origin resumes at its own band
  in its own partition.  `boundThreadPriorityConsistent` is consumed by nothing at
  all; `boundThreadDomainConsistent` is a conjunct of
  `schedulerInvariantBundleExtended`, whose scope is the boot and scheduler
  surface, and no IPC transition claims that bundle — so no theorem in the tree is
  false.  A proof that takes either predicate of a post-pop state is asking for a
  premise the kernel refutes.

  (5) **The refutation is executed, and it has a control.**
  `tests/PriorityManagementSuite.lean`'s `pm_od_09` drives the configure and
  the pop as **live operations** and asserts both pairs disagree; `pm_od_10` is
  the same fixture and the same pop with the reconfiguration omitted, where both
  pairs agree — which is what makes the witness a statement about the
  reconfiguration rather than about the pop, and what shows the pop is not what
  breaks the agreement but what *installs the binding under which it is asserted*.
  The closure is the model change `v0.35.133`'s register row named and deferred —
  retire `SchedContext.priority` and `SchedContext.domain` as thread-band homes,
  which is what seL4-MCS does, its `sched_context` carrying neither — and it is
  **WS-CB**'s, whose plan already reshapes this surface.

- **The scheduler liveness trace model is boot-core-pinned** (SM4.C.11's
  residual).  SM5.J lifted the per-core Liveness *predicates* at v0.31.64 —
  `eventuallyExitsOnCore`, `higherBandExhaustedOnCore`,
  `CanonicalDeploymentProgressOnCore`, `WCRTHypothesesOnCore`,
  `selectedAtOnCore` and siblings all read `currentOnCore c` / `runQueueOnCore
  c` — but `stepPrecondition`, `stepPost` and `ValidTrace`
  (`Scheduler/Liveness/TraceModel.lean`) still read `bootCoreId`, so no
  `ValidTrace` exhibits a step taken on a secondary core.  New code must not
  read an SMP liveness result off a trace: the predicates are per-core, the
  traces are not.  Owned by **WS-SL** (`docs/REGISTERED_DEBT.md`), closure
  target post-v1.0.0; the old target was a sub-task inside a plan marked
  LANDED, so no open phase owned it.
- **The WCRT liveness theorems are hypothesis-conditional**: the band-progress
  obligation `hBandProgress` consumed by `thread_eventually_scheduled_onCore` /
  `no_starvation_under_smp` is an externalized deployment hypothesis whose
  conclusion carries the substantive progress content; only its
  `eventuallyExits` sub-piece has an RPi5 discharge, and the
  FIFO/bucket-rotation composition that would construct it outright is an open
  Scheduler-subsystem follow-up (`Liveness/Yield.lean` scope — AN5-E.4
  honest-framing note, `Scheduler/Liveness/RPi5CanonicalConfig.lean`). Docs
  citing these theorems must state the hypothesis.
- **Every PE marks itself ready, on itself, before it unmasks IRQs** (WS-BP
  BP6, `v0.36.2`), through `lean_ready::become_ready_or_halt` after its per-PE
  runtime handshake; until then no core was ready anywhere and every seam
  behind the per-core `lean_ready` gate (`rust/sele4n-hal/src/lean_ready.rs`)
  degraded to its Rust-only half.  On the image the gate now passes on every
  serving PE, and the boot halts the system unless every declared PE serves
  (`smp::core_serves`).  The gate itself stays, and so does everything below:
  a new seam must still consult it, because the gate is where a PE that has
  not initialized is refused, and the not-ready arms are still what a host
  build and a refused PE take.  **The gated set is derived, not listed** (PR #887 review round
  2): `build.rs`'s `scan_lean_upcalls_readiness_gated` collects every Lean
  upcall from the Lean tree's `@[export]`s — read over a comment-free,
  string-free Lean view with attribute lists split (`lean_code_view`,
  `lean_exports_in`; PR #889 review round 2: a commented-out `@[export …]`
  had counted as live; round 9: the tree including the library root
  `SeLe4n.lean`, which compiles into the static library like any module) —
  and the HAL's `lean_`-prefixed
  externs, attributes each call to its enclosing function, and fails the
  build unless the readiness guard *dominates* it in that body
  (`readiness_guard_dominates`, PR #887 review round 3: the call sits inside
  the guard's true branch with no `||` in the condition, or after a negated
  bare guard whose block diverges — a stored `lean_ready(..)` result, a guard
  block closed above the call, or an `||` no longer satisfy it; and, since
  round 6, the guard's argument must name the **executing** PE —
  `current_core_id_from_tpidr()` inline, or an identifier a dominating
  statement binds from it or validates against it with `assert_eq!`, the
  last binding winning (`ready_argument_is_executing_core`) — so a literal,
  a parameter, a shadowed binding or a `debug_assert_eq!` reads as ungated) —
  `LEAN_READY_GATED_SEAMS`
  is the pin the derivation must reproduce.  The guard must also **resolve**
  to the gate (round 9): an unqualified `lean_ready(..)` counts only where the
  file imports `crate::lean_ready::lean_ready` and defines no `fn lean_ready`
  of its own (`bare_ready_call_resolves`, threaded through every scanner that
  asks — the condition parsers, the classifier, the SVC arm and the
  site-table's `gate_call_offset`), since a same-scope helper of that name
  satisfied every other readiness question while being a different predicate, and the **two** upcalls that run
  ungated — the Lean library initializer `initialize_seLe4n_SeLe4n`, which must
  run before any Lean definition is used, and the primary's `lean_kernel_main`
  boot install, which writes the state every gated seam reads and so precedes
  every core's readiness — are `LEAN_UPCALLS_OUTSIDE_THE_GATE`, each with its occurrence count
  and reason, reconciled in both directions
  (`reconcile_upcall_exemptions`, round 6: a second call in an exempt
  function is a count mismatch, not a free pass).  A reference to a Lean
  symbol that is not a call — an alias, a function pointer, a cast — fails
  the build outright, since no gate can be attributed to a value that
  escapes.  The classifier upcall
  (`lean_classify_synchronous_exception`) is gated too; a not-ready core
  classifies through the Rust mirror pinned to the Lean table —
  `classifier_status` (round 6) holds the hardware classifier's terminal
  `if … else …` to that shape branch by branch, the ready branch's value
  being the Lean call and the not-ready branch's only statement the mirror
  call.

  **WS-RR RR5.6–RR5.9 closed the two seams that consulted no gate**, so the
  sentence `kernel_entry.rs` had always written over its five-entry table —
  "every hardware seam above therefore also consults the per-core readiness
  gate" — is true rather than aspirational.  What a not-ready core does now
  differs by seam, because what it can safely do differs.  The three ISR seams
  degrade to their Rust-only halves.  `sele4n_suspend_thread` returns
  `KernelError::IllegalState`: a C-callable API with an error channel and no
  trapped thread waiting on it.  `dispatch_svc` **halts the core**
  (`halt_syscall_before_lean_ready`) — an `SVC` advanced the PC, so a fail-closed
  frame *would* be architecturally coherent, but the timer seam consults the same
  mask, so a thread on a not-ready core would never be preempted, charged budget
  or rescheduled again; returning an error hands it the CPU forever.  New code
  must not read the SVC seam's not-ready arm as recoverable.

  The gate precedes **every** SVC outcome (PR #889 review): `dispatch_svc`
  consults it before its id and argument-count prefilters, and the trap's SVC
  arm consults it before the full-width `x7` narrowing and the unknown-syscall
  delivery — the halt's reason is the resume (a thread on a not-ready core is
  never preempted again), which no prefilter rejection escapes.  `build.rs`'s
  `svc_arm_readiness_gate_status` pins the order structurally, because a halt
  inside an `extern "C"` handler aborts a host test rather than unwinding into
  it; the behaviour is pinned at the plain-Rust seam in the two readiness
  integration binaries, and no test in the library binary may assume core 0's
  readiness in either direction — the timer suite there marks it mid-run.

  RR5.8/RR5.9 close the compile-time half: a Lean `extern` may be **declared,
  defined or exported only under `feature = "hw_target"`**, and a host-lane
  stand-in of the same name only under its negation
  (`lean_extern_gating_status`).  Both seams used `cfg(not(test))`, so the
  default host profile compiled a call path to a bare-metal symbol nothing on
  the host provides, and `cargo test` linked one into every test binary through
  a `#[no_mangle]` stub.  The readiness gate could not close that: it decides
  whether a call *executes*, not whether it is *compiled*.  The gate's
  `hw_target` verdict is **computed, not matched**: `cfg_predicate_entailment`
  evaluates what a `cfg` predicate entails about the feature through `not` /
  `all` / `any`, under-approximating so it fails closed — a `cfg_attr` or an
  `any(…)` carrying the token satisfies nothing — and linker visibility is read
  as whole words: `extern`, `no_mangle` in both spellings, and
  `#[export_name = "…"]`, which exports a Lean name from an item of any name.
- **A hardware boot without a verified deployment labeling context fails
  closed** (WS-RR RR5.1–RR5.5).  `bootAndInitialiseFromPlatform`'s
  `LabelingContext` argument is **mandatory** — it defaulted to `none`, and on
  that path the wrapper installed the boot state and left whatever the labeling
  reference held, which was `testLabelingContext`: every entity but the reserved
  sentinel `publicLabel`, so every flow between things that can run was
  permitted and SM8/SM9's results held vacuously.  The wrapper now runs the same
  guard `syscallEntryChecked` runs **before** committing anything, so a refused
  boot leaves both references untouched, and the pre-boot labeling reference is
  `defaultLabelingContext`, which that guard rejects — no syscall can be served
  before a deployment context is installed.

  The guard itself stopped being a heuristic.  `isInsecureDefaultContext` was a
  three-sentinel *sample* (ids 0, 1, 42 across four classes) that reported
  "insecure" only when all twelve lookups came back public, which
  `testLabelingContext` evaded by labeling id `0` alone.  It is now an **exact**
  check of a **declared** witness: `LabelingContext.separatedThreads` names two
  *admissible* threads the labeling separates — neither the reserved sentinel
  nor a per-core idle thread (`separationWitnessAdmissible`), since an idle
  thread runs but never originates or receives a flow, so a labeling that
  differs only on the idle range separates nothing observable — and the kernel
  evaluates that inequality — so `isInsecureDefaultContext ctx = false` *entails*
  `LabelingContextValid.labelNonTriviality`
  (`isInsecureDefaultContext_false_implies_labelNonTriviality`), and the runtime
  guard discharges a deployment obligation instead of approximating it.  New
  contexts are built with `deploymentLabelingContext`, whose output is
  `LabelingContextValid` unconditionally (`deploymentLabelingContext_valid`),
  and whose source carries the four policy fields — `memoryOwnership`,
  `endpointPolicy`, `declassificationPolicy`, `auditMonitorClearance` — with
  their fail-closed defaults (PR #889 review round 2), so a binding configures
  them where it declares its labeling rather than every hardware boot being
  forced to the defaults;
  `confinedLabelingContext` is the production two-domain instance (the two
  *incomparable* lattice corners, so neither domain reaches the other in either
  direction — unlike `publicLabel`/`kernelTrusted`, which confine one way),
  and `harnessLabelingContext` is the fixtures'.  A constant labeling function
  is refused, so a fixture that wants one label everywhere uses
  `uniformFixtureLabelingContext`.  What the guard does **not** decide is
  whether the declared partition is the right one for the deployment's threads;
  that stays the integrator's, stated by `LabelingContextValid`'s other two
  conjuncts and discharged structurally by the constructor.  **Which labeling a
  hardware boot installs is bound, not described**: `PlatformBinding` carries
  the **`DeploymentLabeling` source** (`deploymentLabeling`), and
  `PlatformBinding.labeling` is the constructor's output on it — so admission
  (`PlatformBinding.labeling_admitted`) and the whole of `LabelingContextValid`
  (`PlatformBinding.labeling_valid`) are theorems of every binding rather than
  obligations each one carries (PR #889 review: the guard decides
  non-triviality alone, and a stored bare context it admits could still label
  a thread and its own TCB object incompatibly).  The RPi5 binding's is
  `confinedDeploymentLabeling rpi5UpperDomainBase rpi5LowerWitnessIndex …`, so
  its labeling is
  `confinedLabelingContext rpi5UpperDomainBase rpi5LowerWitnessIndex …`
  (`rpi5_deploymentLabeling`, by `rfl`; the boundary clears the boot VSpace
  root and the idle range), the simulation bindings' is
  `harnessDeploymentLabeling`, and
  `Platform.FFI.bootAndInitialisePlatform` boots under the binding's labeling —
  provably the checked idle boot on the binding's declared cores, then the
  witness check, then the two installs, with the labeling-refusal arm
  unreachable (`bootAndInitialisePlatform_eq_checked_boot`) — of the
  **bound** config (round 7): `bindPlatformConfig` puts the caller's IRQ
  table and objects under the binding's `bootVSpaceRoot` and the machine
  configuration the binding **binds for the caller's account**
  (`PlatformBinding.bindMachineConfig`, PR #892 review round 2), so a caller
  cannot omit the canonical root or describe other hardware.  The account
  selects *among* the binding's declared configurations and never becomes
  one: on the RPi5 it is the largest of the five shipped RAM variants
  (`rpi5Variants`, 1–16 GiB) the account covers, and the **smallest** when it
  covers none (`rpi5VariantFor`) — the only member that claims no RAM a
  Raspberry Pi 5 lacks, where the old unconditional 4 GiB map declared RAM
  the 1 and 2 GiB boards do not have.  The DTB bridge validates the board
  against that same function (`rpi5PlatformConfigFromDtb_ok_binds_detected_variant`),
  so the variant checked and the variant booted are one value, and every
  member declares the binding's PE count
  (`bindMachineConfig_declaredCoreCount`, consumed by
  `bootAndInitialisePlatform_checked_declaredCoreCount`).  The coverage
  predicate the two share sits upstream of the bindings in
  `Platform/Boot/MemoryCoverage.lean`.
  The hardware entry is `bootAndInitialiseRPi5`, the generic entry fixed at
  `RPi5Platform`; `lean_kernel_main` (`SeLe4n.Platform.RPi5.kernelMain`, WS-BP
  BP4.1) calls it, through `bootAndInitialiseRPi5OrHalt`, and nothing else.
  **The declared
  separation witnesses must be installed threads of the boot state** (PR #889
  review round 3): the guard decides that the labeling separates two
  admissible *ids*, and only the boot state can say whether those ids are
  threads the deployment creates, so a boot whose labeling's witnesses do not
  resolve to TCBs — the empty config's, whose only TCBs are the idle threads —
  is refused before anything is committed (`declaredWitnessesInstalled`,
  `uninstalledSeparationWitnessBootError`).  A deployment therefore installs
  the two threads its labeling names as separated, or does not boot.
  **The lower witness is the deployment's parameter, held off the boot VSpace
  root by the binding** (PR #889 review round 5): the family fixed it at
  thread `1`, which is the boot VSpace root's object id on every binding
  (`rpi5BootVSpaceRootObjId`, `simBootVSpaceRootObjId`), so a witness there
  could never be installed and every boot carrying the binding's own root was
  refused.  `indexPartitionedDeploymentLabeling` / `confinedLabelingContext`
  take `lowerWitness` with its admissibility and its position below the
  boundary as obligations; the RPi5 binding declares `rpi5LowerWitnessIndex`
  (`2`) and the harness `harnessLowerWitnessIndex` (`2`); and
  `PlatformBinding.witnessesOffBootVSpaceRoot` — neither declared witness is
  the binding's root's id — is a class obligation every binding discharges by
  evaluation, because the root is not visible where the labeling is built
  (`witnesses_ne_bootVSpaceRoot` is its Prop form).  A new binding chooses its
  witness against its own reserved ids; new code must not assume thread `1`
  is a witness.

- **The boot state enqueues each core's idle thread; it does not dispatch it**
  (WS-RR RR5.11–RR5.14).  `bootAndInitialiseFromPlatform` runs
  `bootFromPlatformCheckedWithIdleThreads`, a thin composition over
  `bootFromPlatformChecked` (same validation, same rejections, the seven results
  characterizing it unchanged) that folds a per-core idle enqueue over
  `allCores`.  **That enqueue is the kernel model's own** (`v0.35.68`):
  `Platform.Boot.enqueueIdleThread ist c` has `state := enqueueIdleThreadOnCore
  ist.state c` (`enqueueIdleThread_state`, by `rfl`), with the four
  `IntermediateState` witnesses the operation's own preservation theorems and
  every boot-level frame an instance of the kernel model's — it was a second
  body (`Builder.createObject` plus a hand-written run-queue write) held to the
  first by a docstring sentence, differing in the bookkeeping the store
  maintains and the builder skips.  The operation therefore lives in the
  production module `Scheduler/Operations/IdleEnqueue.lean`, upstream of the
  boot, and the idle TCB (`createIdleThread`, `queuedIdleThread`) in
  `Scheduler/IdleThread.lean` beside its identities; `PerCoreIdle.lean` (staged)
  keeps the per-core-invariant theorems and consumes both.  New code adding a
  boot-time write of an object the kernel model can already write runs the
  kernel model's operation on `ist.state` and carries the witnesses through its
  theorems, never a builder-side copy of its body.  So `∀ c, idleThreadEnqueuedOnCore st c` holds of the live boot
  state (`bootFromPlatformCheckedWithIdleThreads_idleThreadEnqueuedOnCore`),
  discharging the premise `chooseThreadOnCore_always_succeeds` consumes and
  `schedulerNoStall_smp`'s `hIdle` took by hypothesis — which no reachable state
  discharged before: the checked boot installed no idle threads at all, and
  `bootFromPlatformWithIdleThreads` set current slots *without* enqueuing, so
  the predicate was false on it too.  New code must respect the shape: every
  core's current slot is still `none` after boot
  (`bootFromPlatformCheckedWithIdleThreads_currentAllNone`), because a current
  slot pointing at a queued thread violates `queueCurrentConsistent` from the
  first instruction; each core's first scheduling point dispatches idle out of
  its own queue.  The enqueue stores the **queued** idle form
  (`queuedIdleThread`, `threadState := .Ready`; PR #889 review): storing the
  dispatched form `createIdleThread` (`.Running`) while queuing it made every
  successful production boot violate `threadStateConsistent` on every core,
  which the harness hid by syncing the field before checking it.  With that,
  and with `bootSafeObjectCheck` requiring every config TCB `.Inactive`, the
  production boot state is `threadStateConsistent` with no hypothesis beyond
  the boot (`bootFromPlatformCheckedWithIdleThreads_threadStateConsistent`).
  **That is a boot-state theorem, not a preserved invariant** (PR #889 review
  round 2): no scheduler dispatch writes `.Running` and no rendezvous writes a
  `.Blocked*`, so `threadStateConsistent` is false after any core's first
  dispatch, and the harness re-establishes it with `syncThreadStates` before
  it checks.  What the live decisions read is the inactive flag — `tcbSuspend`
  / `tcbResume` / the cancellation and fault suspends test the field against
  `.Inactive` only — stated as `threadInactiveFlagConsistent` and proved of the
  boot state (`…_threadInactiveFlagConsistent`).  **The per-core context switch
  preserves it** (WS-RR RR7.36,
  `switchToThreadOnCore_preserves_threadInactiveFlagConsistent`, with
  `preemptCurrentOnCore_preserves_…` for the primitive it composes), under two
  side conditions that are the two ways it genuinely breaks: a displaced thread
  stranded off every queue, and a dispatch of a thread the state classifies
  `.Inactive`.  The reusable machinery is
  `threadInactiveFlagConsistent_of_frame` / `…_of_frame_placing` over
  `threadPlacedOnSomeCore`, with `inferThreadState_eq_inactive_iff` the
  characterisation — a thread is `.Inactive` exactly when it is unplaced and
  not blocked — so a further surface is a per-transition application rather
  than a fresh argument.  The wake and idle-enqueue paths (which change the
  stored flag *and* the placement), the lifecycle pair and the IPC writers
  remain registered debt.  New code must not cite `threadStateConsistent` of a
  post-dispatch state.

  **And the classification's placement tests are the cross-core wake's
  single-placement tests** (RR7.36): `threadRunningOnSomeCore` /
  `threadQueuedOnSomeCore` are *defined as* `runningOnSomeCore` /
  `runnableOnSomeCore`, not stated to equal them.  RR5.10 wrote a second fold
  over `allCores` in a module that does not import the one where SM5.C.1 and
  SM5.D.4 had already asked the question, and this pair diverging is not
  cosmetic: the wake's guard exists to keep one TCB off two cores, so a
  disagreement would let a thread be enqueued a second time while still
  classifying as running.
  **A successful boot respects the object-capacity invariant** (PR #889
  review round 18): `wellFormed`'s fifth conjunct `objectBudgetRespected`
  requires `initialObjects.length + 1 + numCores ≤ maxObjects` — room for the
  boot VSpace root and one idle thread per *model* core, since the idle slots
  are reserved model-wide — and
  `bootFromPlatformCheckedWithIdleThreadsFor_objectIndexBounded` proves
  `objectIndexBounded` of the boot state from it.  Before, nothing bounded the
  count at all: a config filled to `maxObjects` booted, the idle fold added
  four more entries, and the state violated the invariant
  `retypeFromUntyped` enforces at every later allocation.
  The idle slots are **reserved** by `PlatformConfig.wellFormed`
  (`idleSlotsReserved`: no `initialObjects` entry and no boot VSpace root in
  `[idleThreadIdBase, idleThreadIdBase + numCores)`), so a successful checked
  boot is fresh (`bootFromPlatformChecked_ok_idleSlotsFreshAt`) and the idle
  fold provably overwrites nothing without a freshness hypothesis — before,
  an accepted config object at an idle id was silently replaced by the fold.
  The reservation also covers every object a config entry *references*
  (`bootObjectReferencesReservedIdleSlot`, total over `KernelObject` and over
  every field that can hold an object, thread or scheduling-context id — a
  notification's `boundTCB`, an untyped's `children` and `parent`, a
  TCB's own `tid` and (round 8) its `queuePPrev`, reply references and
  carried capabilities, a Reply's own id and `prev` link and a
  SchedContext's own id included, PR #889 review rounds 2, 4, 6, 7 and 8; a
  VSpace root holds none — and, since round 8, **pinned by constructor
  arity**: each kind's arm destructures its constructor
  (`tcbReferencesReservedIdleSlot` and seven siblings), so a field added to
  any kernel object fails the build until it is classified, where five
  rounds had each extended the same hand-written list), and a config that
  fails it is refused with its own diagnostic rather than as a duplicate
  id.  **A boot TCB is stored under
  its own thread id** (round 7): `PlatformConfig.wellFormed`'s fourth
  conjunct, `tcbIdentitiesMatchSlots`, requires every `.tcb` entry's
  `tid.toObjId` to be its `id` — the object store is keyed by `ObjId`, the
  TCB carries its `ThreadId`, and the lifecycle paths read the latter back
  (`cleanupTcbReferences`), so a TCB stored under a foreign id — an idle
  thread's, in the finding — would have let a retype dequeue a thread the
  config never owned.  New boot fixtures set `tid := ⟨id⟩`.  Round 8 swept
  the relation across the kinds that carry their own id: the fourth conjunct
  is `embeddedIdentitiesMatchSlots` — TCB, SchedContext (`scId`, which
  `replenishScOnCore` keys the replenishment queue by) and Reply
  (`replyId`) — with `tcbIdentitiesMatchSlots` and its two siblings as its
  parts, so a boot SchedContext or Reply is stored under its own id too; and
  `bootSafeObjectCheck` requires all three queue links of a boot TCB empty,
  `queuePPrev` included.  Beyond the config, the idle
  objects are unreachable by user authority at all: `syscallResolveCap` — the
  one resolution every invoked capability passes through — refuses a
  capability naming a reserved idle object (`capTargetsReservedIdleObject`,
  `syscallResolveCap_ok_not_reserved`), so a boot CNode or a transfer that
  carried one yields a slot that resolves like an empty one and no
  `.tcbSuspend` can remove a core's only guaranteed runnable thread.  That
  chokepoint decides on the **resolved capability's target**, so an arm whose
  operand is a raw id from a message register escapes it: until `v0.35.204`
  `.schedContextBind` resolved its capability to the SchedContext and took the
  thread from a raw `args.threadId`, which let an ordinary SchedContext
  capability bind the idle TCB and re-prioritise it (round 11, P1) — and, more
  generally, bind and re-prioritise **any** unbound same-domain thread the
  caller could name, with no TCB authority at all.  Raw operands are refused
  at their lift points — `validateThreadIdArg` and `validateObjIdArg` reject a
  reserved idle id (`validateThreadIdArg_ok_not_reserved`) — so a new arm
  taking a bare id is covered the day it is written; and the bind takes **no
  raw thread operand any more**: MR0 is a TCB capability address
  (`SchedContextBindArgs.tcbCPtr`), resolved through the caller's own CSpace
  with `.write` by `resolveSchedContextBindThread` — one resolver read by the
  live arm and by the scheduler-domain operand builder, the shape
  `.tcbBindNotification` already had — so the thread a bind names is one the
  caller holds a writable capability to
  (`resolveSchedContextBindThread_ok_authorised`) and the idle TCB is refused
  at the chokepoint (`resolveSchedContextBindThread_refuses_idle_capability`,
  `dispatchCapabilityOnly_schedContextBind_idle_capability_refused`).  `.lifecycleRetype`'s
  raw `targetObj` needs no separate guard: `lifecycleRetypeAuthority` binds it
  to the capability.  The
  one live seam that takes a **raw** id, `suspend_thread_cross_core`,
  refuses an idle id itself (round 8): its whole step is the pure
  `suspendThreadCrossCoreStep`, and `suspendThreadCrossCoreStep_idle_refused`
  proves the refusal — the sentinel's `.invalidArgument` — commits nothing,
  where before it ran `suspendThreadOnCore`, which dequeues an idle TCB like
  any other.
  The boot queue is **characterised, not bounded**: on every
  core it is exactly the empty queue with that core's idle thread enqueued
  (`bootFromPlatformCheckedWithIdleThreads_runQueueOnCore_eq`, membership
  `…_mem_runQueueOnCore_iff`), so its well-formedness and its members'
  resolution are proved of the boot state
  (`…_runQueueOnCore_wellFormed`, `…_runnable_resolve`), the staged keystone
  `bootFromPlatformCheckedWithIdleThreads_chooseThreadOnCore_succeeds` takes
  **no hypothesis beyond the boot**, and each core's first selection is pinned
  to its own idle thread (`…_chooseThreadOnCore_idle`).
  **The binding boot installs idle threads on the binding's declared cores**
  (PR #889 review round 3): `bootAndInitialisePlatform` runs
  `bootFromPlatformCheckedWithIdleThreadsFor (PlatformBinding.declaredCores platform)`,
  the first `coreCount` model cores, so a single-core binding boots one idle
  thread rather than four; the RPi5 binding declares every model core
  (`rpi5_cores_eq_allCores`), so its boot is the all-cores form by `rfl`
  (`bootAndInitialisePlatform_rpi5_all_cores`) and every all-cores boot
  theorem is a theorem of the hardware boot.  **No binding declares more cores
  than the model has** (PR #889 review round 5): `PlatformBinding.coreCountLe :
  coreCount ≤ numCores` is a class obligation, so `declaredCores` — the prefix
  `allCores.take coreCount` — has exactly `coreCount` members
  (`declaredCores_length`), membership is `c.val < coreCount`
  (`mem_declaredCores_iff`), and the boot core embeds in the model
  (`bootCoreModelId`).  **The idle-slot reservation is model-wide**: an
  undeclared core's slot is reserved and *absent* after the boot
  (`bootFromPlatformCheckedWithIdleThreadsFor_undeclared_idle_absent`), never
  free — the ids belong to the `numCores`-wide model, and the capability
  chokepoint decides on the kernel state alone, which carries no binding.
  `bootFromPlatformWithIdleThreads` remains as the SM4.G install-and-dispatch
  wrapper and is **not** the production path.

- **A boot TCB is pinned to a core the platform declares, or to none**
  (PR #889 review round 15).  `bootFromPlatformCheckedWithIdleThreadsFor`
  refuses a config whose TCB carries a `cpuAffinity` outside the core list
  it is given (`bootAffinitiesDeclared`, diagnostic
  `undeclaredAffinityBootError`), because `determineTargetCore` reads that
  field on the first resume or wake and would enqueue the thread on a PE
  the binding does not have.  The checked boot cannot decide this — it is
  binding-agnostic by design, one validation path — so the check lives
  where the core list arrives.  On `allCores` it is vacuous
  (`bootAffinitiesDeclared_allCores`), so the all-cores boot and the RPi5
  boot are unchanged; a `coreCount < numCores` binding now rejects a
  config the model would have accepted.

- **...and a running thread is too** (PR #889 review round 20).  The boot check
  above had no live counterpart: `decodeAffinity` accepts any `v < numCores`, so
  `.tcbSetAffinity` could migrate a thread onto a PE the binding does not have
  the instant after a successful boot — queued where nothing runs it, with the
  reschedule SGI sent to a core that cannot take it, and no error returned.  The
  declared count therefore travels with the machine it describes, which is the
  only thing a transition can read: `MachineConfig.declaredCoreCount` →
  `applyMachineConfig` → `MachineState.declaredCoreCount` →
  `setThreadCpuAffinityWithMigration`, which refuses an out-of-range affinity
  with `.invalidArgument` and commits nothing
  (`setThreadCpuAffinityWithMigration_rejects_undeclared_core`); unpinning names
  no core and is never caught by it
  (`setThreadCpuAffinityWithMigration_none_passes_declared_check`).  The count
  reaches the live state proved rather than by convention
  (`bootFromPlatformChecked_ok_declaredCoreCount`,
  `bootFromPlatformCheckedWithIdleThreadsFor_declaredCoreCount`), and
  `PlatformBinding.declaredCoreCountAgrees :
  machineConfig.declaredCoreCount = coreCount` holds the boot's number and the
  transition's number to one fact — `simSingleCoreMachineConfig` exists because
  the single-core binding was sharing the four-PE `simMachineConfig`, which is
  what the gap was.  The field defaults to `numCores`, so the refusal is inert
  on every existing state and fixture; a new binding that declares fewer PEs
  must give its machine config the matching count, or its instance will not
  elaborate.  New code must not read `numCores` as the set of cores a thread may
  be pinned to.  **The unpinned half closed at v0.34.79** (WS-RR RR7.30):
  `determineTargetCore_lt_declaredCoreCount` says an unpinned thread — and a
  `tid` resolving to no TCB — routes to `bootCoreId`, which is core `0` and so
  inside any declared set (`coreCountPos`), so with the two refusals above **no**
  thread of any kind is enqueued on a PE the machine does not have.  `numCores`'s
  own docstring now states this whole relation at the constant, since describing
  only the RPi5 equality there is what made a reader conclude a narrower binding
  could not shape kernel state at all.

- **Thread-state classification is per-core** (WS-RR RR5.10).
  `inferThreadState` read `currentOnCore bootCoreId` / `runQueueOnCore
  bootCoreId` only, so a thread running or queued on a secondary core
  classified `.Inactive`, `threadStateConsistent` was false of any such state,
  and `assertStateInvariantsFor` — which syncs before it checks — would rewrite
  the field rather than report the mismatch.  It now asks every core
  (`threadRunningOnSomeCore` / `threadQueuedOnSomeCore` over `allCores`), and
  the lift is conservative on every state the old definition classified
  (`inferThreadState_eq_bootCore_of_secondaries_quiescent`).  This had to land
  before the boot switch above: the boot state queues idle on all four cores.

- **A device tree is read whole, and what it withholds is not a resource**
  (PR #892 review round 5, v0.34.113).  Five facts new code must respect.  (1)
  `parseFdtNodes` refuses a structure block that does not reach a top-level
  `FDT_END` at depth zero — every partial exit is `.malformedBlob`, fuel
  exhaustion stays `.fuelExhausted` — so a *fixture* blob must carry its
  terminators or the bridge rejects it.  The header is validated first, and the two
  validators are **one question**: `FdtHeader.isValid` and
  `cmdline::validate_fdt_header` both require §5.1's layout — each block offset
  4-byte aligned (8 for the reservation block) and at or beyond the 40-byte
  header — and both require **version ≥ 17**, the version at which
  `size_dt_struct` enters the header, since both read that field
  unconditionally.  Four of those conditions were Rust-only, with Lean the
  permissive side and Lean the side `BP2.6` made the only reader of the blob's
  memory; the
  reservation-block pair and the version floor were missing from both.  A
  strings block over the header is the sharpest of them: a property's `nameoff`
  then resolves into header bytes, and every field there is the blob author's to
  choose, so `reg` or `status` can be spelled inside a `totalsize`.  The walk
  then refuses a property after a
  child (§5.4.2), a repeated property name (§2.2.4) and — since the RR7 audit
  round — **a repeated sibling node name**: §2.2.3 identifies a node by its full
  path, which is unique only if siblings differ, and every selector in the file
  reaches for a node by name and takes the **first** match.  A second
  `reserved-memory` child was therefore never read, so its carve-outs were never
  subtracted; enforcing uniqueness for properties and not for the nodes those
  properties hang on left the selectors' own premise unchecked.  (2) The machine's RAM is selected by
  `memoryNodeReg?` over that parsed tree, with the same three filters the Rust
  walk applies: the node describes memory (`device_type`), it is operational
  (`FdtNode.statusIsOperational` — `okay`/`ok` and nothing else, decided on the
  operational side because that is the side the specification's list is closed
  on), and it sits at the **top level**, so a `memory@…` under
  `/reserved-memory` is a carve-out rather than an aperture.
  `findMemoryRegPropertyChecked` is now a selector over the same tree, not a
  second token walk, and `findMemoryRegPropertyChecked_eq_memoryNodeReg?` is
  what keeps the standalone API and the boot path from disagreeing about a
  blob.  (3) **A reservation set this parser cannot read whole is a refusal**, not a
  shorter list (the RR7 audit round).  Both sources answer `Option`:
  `FdtBlob.reservations` gives `none` when the §5.3 block reaches no zero
  terminator inside its declared bound or holds an unreadable pair, and
  `fdtReservedRanges` gives `none` when a `/reserved-memory` child's `reg` is
  not a whole number of tuples at the declared cell widths — a child with **no**
  `reg` still contributes nothing, because §3.5 says that is what a dynamic
  allocation means.  `fromDtbFull` refuses on either.  The direction is the one
  `CLAUDE.md` states for scanners: this list is a set of *subtractions*, so an
  entry dropped hands back memory the firmware reserved and the map then permits
  `MachineState.addrInRange` over a firmware, DMA or crash-kernel carve-out,
  while one invented merely costs RAM.  The first cut ended the list at the
  bound, at an unreadable pair and at a fixed fuel of 64 and called that
  "fail-closed"; the fuel is now the block's own capacity, so only the
  terminator or the declared bound can end the walk.  A **fixture** blob must
  therefore carry a real reservation block: `offMemRsvmap` pointing at the
  structure block is not "no reservations", it is no room for the terminator,
  and it is refused.  (4) A peripheral's `reg` is a **child-bus** address until it is
  translated: `extractPeripherals` carries an `FdtAddressContext` and composes
  each bus's `ranges` outward, so a node under a bus with no `ranges` is not
  reported at all (Devicetree Specification v0.4 §2.3.8 — nothing maps), an
  empty `ranges` is the identity, and a node whose address falls outside every
  window is refused rather than reported raw.  The tree root is the base case:
  its children's `reg` *are* CPU physical addresses.
- **The scheduler bracket acquires in ladder order because the domain sorts**
  (PR #892 review round 5, v0.34.113).  `schedulerLockBracketDomain.sequence` is
  `SchedLockSet.lockAcquireSequence`, a `mergeSort` on the key — the same answer
  `objectLockBracketDomain` has given since SM3.B.  It was the declared list
  verbatim, which rested on every footprint being declared ascending; that holds
  for the footprints a *transition* declares and not for the one resolved from
  the state, since `pipChainVisited` follows `blockingServer` and a blocking
  chain descends in `ObjId` whenever a higher-numbered thread blocks on a
  lower-numbered one.  Two things new code must respect.  (1) A `SchedLockSet`'s
  `pairs` is **not** an acquisition order — it is whatever order the footprint
  was resolved in; the order is `lockAcquireSequence`, and
  `lockAcquireSequence_ordered` states it with no hypothesis.  (2) The change is
  transparent to every declared footprint, because an ascending list is its own
  sort (`lockAcquireSequence_eq_pairs_of_pairwise_le`), so an SM5 result stated
  over the declared list still holds — but a *new* result about what the bracket
  acquires names the sequence, not the pairs.
- **The outer-shareable TLBI wrappers cannot execute on the first hardware
  target.**  `tlbi_vmalle1os` / `vae1os` / `aside1os` / `vale1os` are
  **FEAT_TLBIOS** (ARMv8.4-A); Cortex-A76 — the core in the RPi5's BCM2712 —
  is ARMv8.2-A and does not implement them.  Each wrapper probes
  `ID_AA64ISAR0_EL1.TLB` and takes `cpu::fatal_halt()` when the feature is
  absent, deliberately **not** falling back to the inner-shareable variant,
  which would service only the inner domain while the caller asked for the
  outer one.  All platform bindings are `.inner` today, so the path is
  unreachable; a new binding that sets `sharingDomain := .outer` must be for
  a PE that implements FEAT_TLBIOS, or the kernel halts at its first TLB
  invalidation.  New code must not treat the `*OS` wrappers as
  drop-in equivalents of the `*IS` ones.  Pinned by a `build.rs` scanner and
  by `scripts/check_tlbi_broadcast_discipline.py` (Tier 0), which also
  confines the `tlbi` mnemonic to `tlb.rs` and holds every local
  (non-broadcast) call site to `scripts/tlbi_local_allowlist.txt`.
- **An `unsafe fn` body is not an unsafe context** (`v0.34.129`).  `sele4n-abi`
  and `sele4n-hal` both deny `unsafe_op_in_unsafe_fn`, so a hardware operation,
  a raw-pointer dereference or a foreign call inside one of the HAL's ten
  `unsafe fn`s must sit in its own `unsafe { … }` block with its own
  `// SAFETY:` comment — which is what makes the HAL's stated discipline
  (*every unsafe block carries a `// SAFETY:` comment*) reach the bodies where
  the hardware access actually happens.  **That discipline is enforced by
  `scripts/check_unsafe_block_justifications.py` (Tier 0) since `v0.35.9`, and
  was enforced by nothing before it**: this file and
  `docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md` row F.3 both named
  `scripts/check_arm_arm_citations.sh`, which the v0.30.11 audit planned as
  R12.C and which no commit on any branch ever contained.  A claimed gate is
  the worst kind of stale claim, because the discharge row it backs reads as
  evidence.  The live gate asks each site kind its own question — a `// SAFETY:`
  comment in the contiguous run above an `unsafe` **block**, a `# Safety` doc
  section on an `unsafe fn` **declaration**, which are Rust's two idioms and not
  interchangeable — and every site is justified (136 of 136 when the gate
  landed, 114 blocks and 22 declarations; 685 of 685 at `v0.36.2`, 484 blocks
  and 201 declarations, the kernel's Rust Lean runtime having brought most of
  them — both counts emitted by the gate rather than written down here), so its
  baseline is empty and any new unjustified site fails outright rather than
  raising a floor.  **A `macro_rules!` template declaring `unsafe … fn $name`
  is one declaration site** (the `v0.36.2` audit): the runtime's four export
  templates carry the `# Safety` section their expansions inherit, spelled
  with `///` — the gate reads a `#[doc = …]` string literal and a `concat!` of
  literals and refuses anything else, so a `stringify!($name)` title is not a
  form to teach it but a spelling to avoid.

  **The declarations became 22 at `v0.35.18`, and the ten are a domain the gate
  never examined** (PR #895 review round 5).  A foreign item carries no `unsafe`
  token of its own — the block header does, and only in edition 2024 — so every
  `extern "C" { fn … }` in this tree declared a caller-facing unsafe obligation
  that no count, no inventory and no baseline could see.  Ten are live Lean
  upcalls, and each one's precondition existed only as a `//` comment for the
  reviewer: a caller of `lean_handle_fault` had no rustdoc statement that the
  call is sound only on a ready core and only for an EL0-origin exception.  Each
  publishes a `# Safety` section now, so the empty baseline survives; a new
  foreign declaration must carry one on the day it is written.

  **The count was 125 until `v0.35.15`, and the missing site was a domain
  defect** (PR #895 review round 3).  The census globbed `*/src/**/*.rs`, which
  names the crate libraries and silently omits everything else cargo compiles —
  integration tests, `build.rs`, examples, benches.  `rust/sele4n-hal/tests/`
  carries a real `unsafe` block, so the figure described a subset of the tree
  while reading as a measurement of it, and the empty baseline would have stayed
  green over an unjustified site in any omitted file.  The set is derived now:
  every `.rs` file under the workspace that is not build output.

  **And the gate meant that sentence only from `v0.35.12`** (PR #895 review): it
  accepted a `// SAFETY:` comment on a declaration too, as a fallback, under the
  very comment saying the two are not interchangeable.  That is not leniency —
  the idioms publish to different audiences.  A `// SAFETY:` comment is inside
  the file, for the reviewer reading the next line; a `# Safety` section is
  rustdoc, for the **caller** who must discharge the obligation and never opens
  this file.  Taking the first for the second passes an `unsafe fn` that exposes
  no contract at all to the people bound by it.  All twelve declarations already
  carried a `# Safety` section, so removing the fallback failed nothing and
  refuses the next one documented the wrong way; the self-test pins the
  separation in **both** directions, each case keeping the justification and
  writing it in the other kind's idiom.  The ARM ARM citation count is reported beside it and deliberately not
  enforced: deciding which sites touch hardware needs the body, which is the
  analysis-instead-of-a-contract shape this file retires twice above.  It also makes an *absence* checkable: the host
  `raw_syscall` mock is `unsafe fn` for signature parity alone, and its body
  compiling with no block is the compiler's statement of that, where before it
  was a docstring's.  The lint was added because the claim it replaces was
  false in the direction that matters — `sele4n-abi`'s module docs said
  "exactly one `unsafe` block: the inline `svc #0` instruction in
  `trap::raw_syscall`", and under edition 2021 that block did not exist: the
  `asm!` inherited the `unsafe fn`'s implicit context and the crate's only real
  block was in `invoke_syscall`.  New Rust in either crate writes the block.
- **A fault is delivered, never returned.**  RR4 (v0.34.44) wired
  `dispatchSynchronousException`'s non-`SVC` arms and `trap.rs`'s abort arms to
  the fault delivery, which composes the live `.call` chain
  (`endpointCallCrossCoreDispatch`) with a kernel-built fault message.  Four
  facts new code must respect.  (1) The transition is **total**: no handler, an
  unresolvable one, one lacking send-**and**-grant, a flow the policy denies, or
  a Call that cannot link a reply object all converge on the fail-closed suspend
  (descheduled, `.Inactive`, keeping `TCB.pendingFault` as the diagnostic), so
  there is no error arm a caller could ignore and `eret` through — which is what
  makes `faultDeliverOnCore_not_dispatchable` (RR4.19) hold on *both*
  dispositions.  (2) The live entry calls the **flow-checked** arm
  `faultDeliverOnCoreChecked` (production, `IPC/CrossCore/Fault.lean` §5), not
  the bare transition: the live syscall seam gates every endpoint operation
  through `syscallEntryChecked`, and an ungated fault delivery would be the one
  endpoint flow in the kernel no policy can refuse — it would carry a faulting
  thread's fault address, syndrome and register window into a handler's domain
  across a boundary the deployment forbids.  A denied flow takes the same
  suspend, so the gate costs neither the progress theorem
  (`faultDeliverOnCoreChecked_not_dispatchable`) nor the bundle
  (`faultDeliverOnCoreChecked_preserves_ipcInvariantFull`).  A new fault seam
  must call the checked arm; a Tier 0/3 pair pins that relation rather than the
  name, since both names contain `faultDeliverOnCore`.  (3) The faulting
  thread's `pendingFault` is seL4's `tcbFault` and is the **only** channel from a
  delivery to the reply that answers it; a reply to a thread carrying none is
  `.illegalState`, and `applyFaultRestart` retires it, so a second reply cannot
  re-answer.  The reply that reaches it is the **ordinary** one: the live
  `.reply` dispatch arm is seL4's `doReplyTransfer`, branching on the answered
  thread's `pendingFault` (`replyTransferOnCore`, production,
  `IPC/CrossCore/Fault.lean` §4), because a fault handler holds nothing but the
  reply capability the fault Call gave it — without that branch the whole
  reply-based restart is verified and unreachable.  On an unfaulted caller the
  seam is the pre-RR4 body verbatim (`replyTransferOnCore_of_no_fault`), which
  is why every existing `.reply` theorem transfers under one pre-state
  hypothesis.  **Both branches are covered by the staged dispatch payoff since
  `v0.35.195`** (WS-RR RR8.16): RR4.14 confined it to the unfaulted one with the
  pack field `replyNoPendingFault`, because the abandon arm needs the answered
  thread to be `passiveServerIdleAllowed` at the **post**-state and threading a
  post-state hypothesis is what the RR3 de-threading gate forbids.
  `endpointReplyCrossCoreDispatch_ok_target_ready` reads that off the dispatch's
  own **outcome** — a successful reply leaves its target `.ready` — so the
  hypothesis is derived rather than carried, the confinement field is retired for
  `replyFaultStage` (the same five pre-state conditions the ordinary branch
  already carries, at `IpcMessage.empty`), and the fault reply's own bundle
  composes the **donating** form: `faultDeliverOnCore` runs the live `.call`
  chain, so a faulted thread holding a reservation lends it to its handler and
  `hNoDonationOwnedBy` was **false** in exactly the state the handler replies
  from — the premise the path it was named for refutes.
  **`.replyRecv` does not route through the seam yet**
  — `replyRecvBody` fuses a reply leg, a receive leg and a donation return, and
  a fault reply changes what the latter two are handed — so a handler must
  answer a fault with `.reply` and take its next request separately; that is
  registered debt too, and new code must not assume `.replyRecv` retires a
  fault.  (4) `IpcMessage.label` is set by kernel-originated messages only —
  a user send leaves it at `0` — because carrying a user's label would let a
  thread holding a send capability to a fault endpoint mint a message bearing a
  `seL4_Fault_tag`.  Restoring seL4's sender-side label pass-through needs its
  own authority story and is registered debt — **owner WS-CB since v0.34.68**
  (WS-RR RR7.17), with the constraint and two candidate designs stated in the
  WS-RA plan's §9 rather than inside a review narrative.  (5) The handler capability is
  gated by seL4's `sendFaultIPC` predicate — send, and grant **or**
  grant-reply (`faultHandlerCapAuthorized`) — not send-and-grant: the reply
  link is structural in this model, so the disjunct is a policy gate, and the
  idiomatic `seL4_CapRights_new(0, 1, 0, 1)` handler capability must be
  admitted; the predicate is *defined from* its clause inventory
  (`faultHandlerRequiredRights`, PR #887 review round 3), with
  `faultHandlerCapAuthorized_iff` and
  `faultHandlerCapAuthorized_depends_only_on_faultHandlerRights` holding the
  two readings together — a theorem whose conclusion is one of its own
  hypotheses, which is what pinned them before, pins nothing.  (6) The fault entry **spills the trap frame's fault window**
  (`x0`-`x7`, `SP_EL0`, `x30`) into the faulting thread's `registerContext`
  before it builds the fault context (`writeFaultRegistersToTcb`,
  `faultContextOfThread_writeFaultRegistersToTcb`): the mirror is partial and
  between syscalls holds the *last syscall's* arguments, so a context built
  from it alone would report a stale argument window and, on a payload-free
  resume, reinstall it over the thread's live registers.  `lean_handle_fault`
  therefore takes fifteen words, and new code must not build a fault context
  off the mirror without spilling first.  (7) The entry derives its cross-core
  pokes from the pre/post **diff** (`computeCrossCoreSgis`), as the syscall
  seam does, never from the single SGI the Call chain surfaces; and it runs
  the executing core's successor through `scheduleLocalSuccessor`, live since
  WS-BP BP7.6 (`v0.36.19`).  (8) **Every word of a fault message reaches the
  handler** (WS-BP BP7.8, `v0.36.21`): the words past the fourth are written into
  its IPC buffer by the delivery every wake shares, and the two fault seams drain
  the physical-write ledger that carries them, exactly as the syscall seam does.
  A handler whose buffer resolves to no writable RAM reads the four inline words
  and a length of four.  (9) **A kernel-origin exception is never
  delivered.**  `classifySynchronousException` maps the current-EL aborts
  (EC `0x25`, `0x21`) to `.kernelAbort`, `faultOfExceptionContext` yields no
  fault for it, and `faultEntryStep` / `unknownSyscallEntryStep` are inert
  unless `SPSR_EL1.M[3:2] = 0` (`ExceptionContext.takenFromEl0`); on the Rust
  side `halt_if_kernel_origin` runs before classification in
  `handle_synchronous_exception` and the `KERNEL_ABORT` arm halts on the
  syndrome alone (`build.rs` pins both as unconditional top-level statements
  of the handler, whose terminal statement is the routing match — round 6);
  the classification itself is
  Lean's only once the core is ready, and the pinned Rust mirror's before
  that.  Delivering one would hand the
  kernel's own register window to a user-level handler and let its reply
  `eret` into the kernel frame.  (10) **A handler already blocked in receive
  gets the fault message in its return frame**: `faultDeliverOnCore` stages
  it (`stageWokenDelivery`, the `.call` arm's write) — the queued-order path
  (fault first, receive later) was always right; the woken path was not.
  (11) **`.tcbResume` retires a pending fault** (`retirePendingFaultForResume`,
  run before `resumeThreadOnCoreLive`): the thread restarts at the faulting
  instruction with its trap-time window and `pendingFault = none`, so no
  later reply can decode against a stale fault; a thread carrying none is
  untouched (`retirePendingFaultForResume_of_no_fault`).  (12) **An unknown
  syscall number is a fault**, delivered through the same entry
  (`lean_handle_unknown_syscall`, `unknownSyscallEntryStep`;
  `trap.rs::deliver_unknown_syscall` on `DispatchError::InvalidSyscallId`),
  never an error frame returned to the thread — seL4's
  `handleUnknownSyscall`.  (13) **`.tcbSetFaultHandler` (id 34) is the only
  writer of `TCB.faultHandler`** (`setThreadFaultHandlerOp`, capability-only
  under the TCB write right): the CPtr is validated through the *target's*
  CSpace against `faultHandlerCapAuthorized` at set time, so "configured" and
  "usable" are the same thing; before it existed nothing outside the test
  fixtures set the field, and every live fault took the fail-closed suspend.
  (14) **The fault tags are the MCS layout**: `Timeout` is 5 and `VMFault`
  is 6 (`libsel4/arch_include/arm/sel4/arch/shared_types.bf` under
  `CONFIG_KERNEL_MCS`; the non-MCS layout's `VMFault 5` is not this ABI), and
  `faultLabel_ne_timeout` / `faultLabel_ne_debugException` pin the two
  reserved tags as never carried.  (15) **A failed capability lookup is a
  fault, on every syscall the refusal ledger does not record** (PR #887
  review round 3): `syscallDispatchFromAbi` re-runs the dispatcher's prologue
  on the refusal arm (`syscallCapFaultOf`: decode, the gate, the *resolution*
  half of the lookup, `syscallResolveCap`) and, when the resolution fails with
  the very error the dispatcher returned, delivers a `capFault` through the
  flow-checked delivery the abort entry uses (`deliverSyscallCapFault`) —
  seL4's `handleInvocation` / `handleRecv`, whose rule is the syscall's
  blocking flag, so every `seL4_Call` invocation and `seL4_Signal` fault in
  the send phase and `.receive` / `.notificationWait` / `.replyRecv` in the
  receive phase (`capFaultReceivePhase?`).  A resolved capability refused on
  rights or by its arm is still an error, a refusal raised before the lookup
  is never delivered, and the two declassifying syscalls keep returning theirs
  because SM9.B records them — the partition is pinned against
  `refusalSeamClass` (`capFaultReceivePhase?_none_iff_records`), not listed
  twice.  The context is the trap frame's window with the `SVC` as the restart
  PC (`svcFaultIP`), so a payload-free reply re-issues the syscall, and
  `ELR_EL1`, `SPSR_EL1`, `SP_EL0`, `x30` cross the ABI for it
  (`lean_syscall_dispatch_cross_core` takes fifteen words).  The outcome is
  `.faulted` — outcome tag 2, distinct from a frame (0) and a block (1), on
  which the SVC arm resumes the staged successor or, where none was staged,
  **halts** exactly as the unknown-syscall delivery does (`halt_after_delivered_syscall_fault`, PR #887 review round
  5), because a block's sentinel frame would `eret` the caller past the
  `SVC` the model has it restart at — and the caller is not dispatchable
  afterwards (`syscallDispatchFromAbi_capFault_faulted`,
  `syscallDispatchFromAbi_capFault_not_dispatchable`); every error-frame
  theorem at the seam is stated on the complementary arm (`hNoCapFault`).  A
  `.replyRecv` whose *reply* capability fails to resolve still returns the
  error (seL4-MCS's `lookupReply` faults) — registered debt.  (16) **The SVC
  arm reads the syscall number at full width**: `u32::try_from(frame.x7())`,
  with the narrowing's failure delivered as the unknown-syscall fault, so a
  wide `x7` cannot alias a valid id.
- **A core that takes an EL0 abort resumes its successor, and halts where no
  restore was staged — delivered or not.**
  The model deschedules the faulting thread, and the hardware honours that
  through the context restore (WS-BP BP7.6, `v0.36.19`): `trap.rs::deliver_fault`
  returns through `trap::take_restored` before anything else, so `trap.S`
  `eret`s into the successor rather than through the faulting thread's own
  frame, back onto the instruction that faulted.  Where no restore was staged it
  calls `cpu::fatal_halt()` after a delivered fault, and (PR #887 review round 3)
  its not-ready path calls `halt_abort_before_lean_ready` rather than
  publishing a status frame: an abort leaves `ELR_EL1` on the faulting
  instruction, so a returned frame is `eret`ed straight back into the abort.
  A fault raised at the SVC seam halts too (outcome tag 2, `.faulted`,
  `halt_after_delivered_syscall_fault`, PR #887 review round 5): the model
  restarts that caller *at* the `SVC`, and a `.blocks` sentinel would `eret`
  it past the `SVC` instead.  Round 7 located that arm and the tag-2 decode
  in the handler's and `dispatch_svc`'s own terminal matches
  (`handler_faulted_arm_halts`, `dispatch_decodes_faulted`), not at their
  first textual occurrence.
  **A fallback may publish a return frame only on a seam whose exception
  advanced the PC** — the SVC seam, where the unknown-syscall path keeps its
  not-ready frame and where the not-ready behaviour as a whole is RR5's
  decision.  The host lane keeps the abort fallback frame as the harness
  observable; `scan_trap_rs_abort_fallback_halts` pins that the write is
  host-only and the halt sits on the not-ready path.  Both halts are
  reachable since WS-BP BP6 marks each core ready, and since BP7.6 the context
  restore replaces the delivered one with the successor install wherever one was
  staged — `build.rs` requires the restored return as a top-level statement of
  each arm ahead of its halt (`is_restored_frame_return`); new code must not read
  either halt as the fault path's contract.  **And a core another core has
  vacated stages a successor** (`v0.36.40`): a remote deschedule clears a slot
  while the thread still runs there, so the fault, unknown-syscall and FP/SIMD
  entries can find no current thread; they run
  `PriorityInheritance.dispatchVacatedCore` rather than committing nothing, since
  an entry that stages no restore halts the PE — an unprivileged denial of
  service of every partition on that core.  Since `v0.36.41` every
  state-committing entry ends in `PriorityInheritance.settleResidencyOnCore`,
  which subsumes that rule and records the core's resident thread (the WS-BP
  section's `v0.36.41` paragraph); a new trap entry calls it too.  A kernel-origin exception halts the core too,
  and that one *is* the contract: `halt_if_kernel_origin` (an EL1-origin
  frame) and the `KERNEL_ABORT` arm (a current-EL abort syndrome) are
  fail-closed by design, not SM10.1 placeholders.
- **The deployed reader-writer lock is the ticket-FIFO one, and each lock has
  its own refinement bridge** (WS-RR RR6, v0.34.50).  `STATIC_RW_LOCK_POOL` is
  `[QueuedRwLock; 4]` — `build.rs` pins the element type, so a revert to the
  CAS-retry `RwLock` fails the build — and the four `rw_lock_*` helpers pass
  the executing PE's id, which the ticket protocol needs.  Four things new code
  must respect.  (1) **Cite the right relation.**  `rwLockSim`
  (`Locks/RwLockRefinement.lean`) relates the writer bit and the reader count
  and says in as many words that the abstract `waiters` field is **not**
  represented — honest for the CAS-retry lock, useless for a FIFO claim.  A
  statement about the deployed lock's admission order goes through `queuedSim`
  (`Locks/QueuedRwLockRefinement.lean`), whose ghost ledger is pinned to the
  machine words by `QueuedTicketWf` and whose capstones are
  `queuedRwLock_refines_rwLockSpec` / `queuedRwLock_admits_in_spec_order`.
  Those were proved **before** RR6.10 repointed the pool, so no released
  version carried an unrefined core lock, and the ordering is the rule for any
  future lock switch: the refinement lands first.  (2) **Cite the premise-free
  capstone.**  `rust_rwLock_refines_lean` and
  `rust_rwLock_refines_lean_via_rustImplementsRwLock` still take
  `ListBlockBisim` — which is their own conclusion, one block at a time — and
  are kept only as the general forms.  The results that assert something are
  the `_honest` ones (`rust_rwLock_refines_lean_honest`,
  `…_via_rustImplementsRwLock_honest`, `rust_rwLock_refines_lean_from_unheld`),
  derived from the trace-shape predicate `honestBlock` through
  `listHonestBlocks_listBlockBisim`.  The same shape rule applies to new
  bridges: `queuedTrace_preserves_queuedSim` and
  `ticketTrace_preserves_ticketLockSim` are both stated so they do not assume
  their own per-block conclusion, and a bridge that does is shipping the defect
  RR6 exists to remove.  (3) **`rw_lock.rs` is retained deliberately**, for
  three reasons recorded in its own module docs: it is the Tier-5 oracle's
  second implementation (the oracle drives *both* real locks and checks them
  against each other, against the ticket interval, the served ticket's
  liveness, the per-core withdrawal slots and the per-core held words, and
  against `encodeRwLock` after every operation — and it *excludes*, counted
  and under a ceiling
  rather than silently, a trace that asks a core to acquire while its own
  withdrawal is unclaimed, which parks on hardware and no single-threaded
  replay can execute), it owns the `WRITER_BIT` / `READER_MASK` layout
  `queued_rw_lock.rs` now imports rather than re-declares, and its D-4
  refinement was *completed* rather than deleted.  It is not a fallback: the
  kernel instantiates it nowhere.  (4) **The lock inventory is 30**, partitioned
  4 memory-model + 6 TicketLock + 16 RwLock + 4 refinement (25 at RR6; WS-LC
  LC1 added the withdrawal's three payoff entries and LC5 the two
  cycle-denominated bounds), and
  `LOCK_THEOREM_COUNT` in `lock_bridge.rs` must equal
  `lockPrimitives_count` (`scripts/check_lock_ffi_symmetry.sh`, Tier 0).  The
  R-10 entry names the *liveness* theorem `rwLock_writer_liveness` — admission
  under `FairTrace`, with WS-LC LC1's explicit no-withdrawal premise — and the
  single-step safety theorem it used to stand in for keeps its own entry under
  its accurate name; RR6.23's release-count bound
  (`rwLock_writer_admitted_within_release_budget`) is the "leaves the queue"
  form and is not the entry (the closure audit found both this file and the
  spec naming it as such).
  The two SM2.C **datatype** extensions RR6 did not absorb are WS-LC's (see
  below), and both are closed: **SM2.C-C** at v0.34.54 (spec, both refinements,
  the deployed lock and both consumers) and **SM2.C-T** at v0.34.55 (the timed
  execution) — see the two bullets below.
- **A queued core may withdraw its request, and a withdrawn head hands its
  turn on.**  `RwLockOp.cancel` (v0.34.51) removes `c`'s entry from `waiters`
  and — since PR #890 review round 5 — promotes the contiguous reader run at
  the head when no writer holds and the new head is a reader
  (`RwLockState.cancelPromotes`, `cancelRun`), exactly as the deployed lock's
  withdrawal of a served head passes the turn to the readers behind it; a
  writer head keeps waiting for the readers (INV-R1), and a withdrawal from
  anywhere but the head promotes nobody (`rwLock_cancel_nonhead_admits_no_one`).
  It preserves all five INV-R conjuncts (`rwLock_withdraw_preserves_wf` +
  `rwLock_promoteReaderRun_preserves_wf`), is never an effective release and
  never installs a writer (`rwLock_cancel_not_effective_release`,
  `rwLock_cancel_admits_only_the_head_reader_run`), so it costs the waiters
  behind it nothing — it can only admit them sooner.  The old `cancel` was the
  neutral `waiters.filter` (`rwLock_cancel_admits_no_one`), which contradicted
  the lock and made a served reader's holder status path-dependent; see the
  round-5 bullet below.  Four things new code must respect.
  (1) **Which liveness conclusion you may cite changed.**  A theorem concluding
  "`c` *leaves the queue*" is satisfied by a withdrawal and is unchanged
  (`rwLock_writer_admitted_within_release_budget`); a theorem concluding "`c`
  *becomes the holder*" is false of a window in which `c` withdraws, so
  `rwLock_writer_liveness`, `rwLock_queued_liveness`, `rwLock_reader_liveness`
  and every `admissionStep*_bounded` now take an explicit
  `RwLockExecution.noCancelIn c k₁ k₂` premise.  It narrows by `.mono`, and a
  concrete trace discharges it through the decidable whole-trace form
  `cancelFree`.  The premise reaches CC-5: `lockContention_delay_bounded` and
  the alphabet bound carry it, and `lockContentionRun` carries it per step, so
  an accepted run supplies it for free.  (2) **`leave_waiters_implies_holder`
  has a third disjunct**, not a narrower hypothesis — withdrawing *is* a way to
  leave the queue.  (3) **Both refinement bridges relate it.**  The CAS-retry
  one honestly performs no atomic access (`opCorresponds.cancel_no_queue`,
  `honestBlock.cancel_no_queue`) — a queueless lock has no queue for a
  withdrawal to disturb.  The ticket-FIFO one (v0.34.52) carries it properly;
  see the next bullet, and the deployed lock carries it at v0.34.53 — the one
  after that.  (4) **Both 2PL unwinds emit one** since v0.34.54 — see the
  shrinking-phase bullet below.
- **The ticket lock's ledger tombstones; the queue it represents is the
  *live* one** (WS-LC LC2, v0.34.52).  `now_serving` owes one advance per
  ticket ever issued, so a withdrawal cannot remove a ticket from the middle
  of the interval — `QueuedRwLockConcrete.cancelled` (the implementation's
  per-core slot array) marks it instead, and `liveLedger` is the ledger minus
  those.  Five things new code must respect.  (1) **`ledgerTickets` is
  unchanged**: the ticket column is still exactly `[now_serving,
  next_ticket)`, so `await_turn`'s spin bound and every other arithmetic
  consequence are untouched.  What moved is `queuedSim`'s queue conjunct,
  which now reads `liveLedger`.  (2) **`queuedSim` has a fourth conjunct**,
  `queuedHeadLive`: the served ticket is never a tombstone.  It is a
  *block-boundary* property — a `pass_turn` uncovers a head that may be
  withdrawn, and the skip loop restores it before the block ends — which is
  why it is not in `QueuedTicketWf`.  With it, "no live request" and "no
  outstanding ticket" are the same statement, so the calm-lock block shapes
  are as they were.  (3) **A turn may be passed only for a ticket nobody has
  withdrawn** (`opEnabled`), so a skip must *claim* the slot first; the claim
  is a compare-exchange and it is the arbiter between the canceller and the
  previous holder's loop.  (4) **Promotion is read off the ledger, not
  computed from the served ticket**: `promoteFrom` / `readerAdmitFrom` walk
  the live entries and retire tombstones between them, because the old
  `promoteOps` gave promoted readers *consecutive* tickets, which a mid-queue
  withdrawal falsifies.  (5) **The FIFO capstone is about position, not
  arithmetic**: `queuedRwLock_admits_in_spec_order` says the `i`-th waiter is
  the `i`-th live entry, holding some outstanding ticket — a sharper claim
  than the `now_serving + offset + i` it replaces, since that formula is
  simply false once anything has withdrawn.
- **The deployed lock's acquisition splits when it may have to be withdrawn**
  (WS-LC LC3, v0.34.53).  `QueuedRwLock::acquire_read` / `acquire_write` are
  the *fused* spellings — they take a ticket and spin to completion inside one
  call, so there is no instant at which a caller holds a ticket and could
  abandon it.  A caller that may have to unwind takes `enqueue(core, mode)`,
  spins on `is_served(ticket)`, and then calls **exactly one** of
  `complete_read`, `complete_write` or `cancel` for that ticket; a request ends
  in one of three ways — a completion followed by a release, a withdrawal that
  returns `CancelOutcome::Withdrawn`, or a withdrawal that returns `Holding`
  followed by a release (PR #890 review round 5, next bullet but two).  Five
  things new code must respect.  (1) **Exactly one terminator per ticket,
  always.**  `next_ticket` is an unconditional `fetch_add` and `now_serving`
  owes one advance per ticket ever issued, so a ticket that is neither
  completed nor withdrawn stalls the lock permanently — the failure is a hang,
  not a data race, and no assertion catches it.  (2) **The withdrawal is published before the head is checked,
  and both directions carry a `SeqCst` fence.**  `cancel` stores `ticket + 1`
  into its own slot, fences, and only then asks whether it is being served;
  `claim_withdrawal_of` fences before reading the slots.  This is the
  store-buffer (Dekker) shape — a store to one location followed by a load of
  another — and **`SeqCst` on the four accesses alone is not sufficient**: loom
  found the interleaving in which neither side retires the ticket, and the
  fences are what removed it.  Reordering the publish after the head check, or
  dropping either fence, loses the race in the direction that stalls the lock.
  (3) **The compare-exchange is the arbiter.**  Exactly one of {the
  withdrawing core, the previous holder's skip loop} succeeds in clearing a
  given slot, and that one advances `now_serving` past the ticket; the loser
  does nothing.  Deleting the arbitration and testing the slot instead admits
  two cores at once.  (4) **One outstanding ticket per core per lock, and
  `enqueue` waits for the core's last withdrawal to be retired.**  The slot
  array is indexed by core id (`MAX_WAITERS` entries, asserted in range) and
  holds one withdrawal, so a core may not take a second ticket while its
  first withdrawal is unclaimed: the second `cancel` would overwrite the
  publication and the first ticket would never be retired — `now_serving`
  stops on it and the lock stalls — on the contract-respecting sequence
  enqueue, withdraw, enqueue, withdraw (WS-LC closure audit, v0.34.56: the
  first cut shipped it, and all four LC3 loom models withdrew once per core).
  `enqueue` therefore parks until the slot is empty
  (`await_withdrawal_retired`), a wait that ends before any later ticket
  could be served and so costs nothing a fresh ticket would not, and the
  non-blocking `try_acquire_*` are refused in that state; `cancel` refuses a
  ticket `now_serving` has already passed, since a stale publication would
  park the core's next `enqueue` for good; a holder's withdrawal returns on
  the held word before it publishes (PR #890 review round 3 — the
  `debug_assert` that stood there vanishes in release builds), and a
  `debug_assert` still refuses a withdrawal naming another core's served
  write ticket.  The Lean model
  carries the rule as `QueuedTicketWf.ledgerCoresNodup` with the issue enabled
  only for a core holding no ticket, `publish_slot_empty` is the theorem that
  the unconditional store never overwrites, and the `acquire*_enqueue` blocks
  require `¬ withdrawalPending`, so the model no longer admits the trace the
  lock refuses.  A live double enqueue — two tickets, neither terminated —
  remains the caller's contract: `ledgerCoresNodup` states it and nothing at
  runtime checks it.  `pass_turn`'s skip loop is bounded by the withdrawals
  published while it runs, **not** by `MAX_WAITERS` — a core whose tombstone
  was just retired may re-enqueue at the head and withdraw again — so the
  per-core iteration cap that used to sit there fired on a correct execution
  and is gone; the invariant it checks now is `now_serving ≤ next_ticket`.
  `NO_WITHDRAWAL` is `0` and slots hold `ticket + 1`, so ticket `0` is
  withdrawable.  (5) **The split surface crosses the FFI**, because the unwind's
  caller is on the Lean side: `ffiRwLockEnqueue`, `ffiRwLockIsServed`,
  `ffiRwLockCompleteRead`, `ffiRwLockCompleteWrite`, `ffiRwLockCancel` and
  `ffiRwLockCancelCount` join the sixteen SM2.D symbols, reconciled across the
  three surfaces by `scripts/check_lock_ffi_symmetry.sh`.
- **A release by a non-holder, a re-acquisition by a holder, and a
  withdrawal by a holder are the deployed lock's no-ops — decided by its held
  word, not by the caller** (PR #890 review rounds 2 and 3).  `QueuedRwLock`
  carries one `held` word per core (`HELD_NONE` / `HELD_READ` /
  `HELD_WRITE`), set at the core's admission and cleared at its release, and
  `acquire_read` / `acquire_write` / `release_read` / `release_write` /
  `cancel` each read the caller's word before they touch anything else: a
  holder re-acquiring returns, a non-holder releasing returns, a holder
  withdrawing returns before anything is published (round 3 — a writer still
  holds its ticket, so a withdrawal that reached the publish was claimed at
  once and passed the turn under the set bit, and the release passed it
  again, past a live waiter; a `debug_assert` had stood in for the identity
  and vanishes in release builds).  The RAII guards record whether they
  acquired, so a nested same-core guard is a no-op both ways rather than a
  release of the outer scope's hold (round 3); `enqueue` by a holder is
  outside the contract and reported in debug builds.  Before the word existed `release_read` was an unconditional
  `fetch_sub` and `release_write` an unconditional clear-and-pass-turn, so a
  non-holder's release in a release build underflowed the reader count or
  handed the turn on while the real writer still held — and the
  two-phase-locking unwind (`unwindAll`, next bullet) releases **every**
  member of a footprint, holding or not, relying on exactly the identity the
  lock did not implement, while the refinement claimed it as a stutter no
  code path performed.  Four things new code must respect.  (1) **The
  relation now represents the holders**: `queuedSim`'s fifth conjunct is
  `queuedHeldSim` — a core's word reads `HELD_READ` iff the spec has it as a
  reader and `HELD_WRITE` iff the spec's writer is that core — so the
  holder no-op blocks of `queuedBlock` (`acquireRead_holder`,
  `acquireWrite_holder`, `cancel_holder`, `releaseRead_noop`,
  `releaseWrite_noop`) are the one held-word load and are
  *derived* in `queuedBlock_preserves_queuedSim`; every acquire and release
  block opens with that load (`heldLoad`), and the effective releases clear
  the word (`heldStore c none`) **before** the state word moves, and the
  withdrawal block opens with the held load before the publish
  (`cancelPublish` is enabled only for a core holding nothing) — orders
  `build.rs` pins for both releases and for `cancel`
  (`scan_queued_rw_lock_protocol_intact`, its third check).
  (2) **A queued waiter re-acquiring is decided by its request word** (the
  next bullet): at round 2 it had no block, because the implementation had
  no branch and the one-outstanding-ticket contract (`ledgerCoresNodup`) was
  what ruled the call out — `queuedBlock` said so by having no shape rather
  than a fictional stutter, and that honest gap is the one the class
  closure filled.  (3) **The CAS-retry `rw_lock.rs` has no such no-ops
  and its bridge no longer claims them**: it keeps no holder bookkeeping, so
  its four `honestBlock` `_noop` constructors and `opCorresponds.noop` —
  each a `[]` block for a call on which that code performs an atomic access
  — are gone, and its trace-level theorems cover exactly the traces that
  respect its caller contract (acquire only while uninvolved, release only
  what you hold), stated in its module docs.  **The `TicketLock` bridge
  makes the same choice** (round 4 — the sweep this fix owed its sibling):
  `ticket_lock.rs` has no per-core word, so a re-acquiring holder parks
  forever and a non-holder's release admits the next waiter under the
  holder; `ticketBlock`'s `tryAcquire_noop` / `release_noop` were the same
  fiction and are gone, `TicketLockState.callerContract` states which
  operations the bridge covers, and `ticketBlock_respects_contract` /
  `ListTicketBlocks_contractTrace` prove every shape and every admitted
  trace is inside it.  A silent no-op there would mask what the
  kernel-entry consumers halt on (`assert_not_holding_round_lock`), which
  is why the deployed `QueuedRwLock` is the only lock that implements the
  spec's no-ops as branches: the unwind relies on them there and nothing
  does here.  (4) **The gates ask the lock
  the question.**  The Tier-5 oracle issues a non-holder's release, a
  holder's re-acquisition and a holder's withdrawal (with the ticket the
  core actually held) to the real ticket lock and holds every core's word
  to the spec's holders after each op (`check_holders`); a queued
  waiter's re-acquisition is issued to the ticket lock since the class
  closure (it was issued to neither at round 2), and the CAS-retry lock
  is sent neither call.  On the host a std thread stands in for a PE and the
  per-CPU stub answers core 0 to every thread, so the bridge's cross-thread
  tests give each thread its own PE identity (`per_cpu::HostCoreIdentity`,
  test-only): several threads under one id are one PE issuing overlapping
  acquisitions, which the held word turns into no-ops and stranded counts —
  the first host lane after the word landed hung in exactly that shape.
  The loom gate gained
  `unwind_by_a_non_holder_never_touches_the_holder` and
  `every_pair_of_units_is_safe` — every unordered pair of the lock's
  single-lifecycle units, one unit per thread, unbounded (fourteen units
  since round 5, so 105 models with the diagonal); two of them are the
  unwind at a member the core holds, as a reader and as the writer (round
  3), and two the enqueue-twice-then-acquire shapes (the class closure).
  The three **chained** units (round 5: read then write, write then read,
  withdraw then read — a second acquisition beginning on the words the
  first lifecycle left) meet every unit in
  `every_chained_unit_meets_every_unit`, 48 models under a **stated
  preemption bound** (`CHAINED_PREEMPTION_BOUND = 3`), because a thread
  running two lifecycles has twice the atomic and yield points and an
  unbounded exploration of two of them did not finish in a per-PR lane; the
  bound is in the code, the script and the docs, never implied.  What that
  enumeration is **not** is the SM2.C-defer plan's "op-sequences of length
  ≤ 4" (round 5): that sentence is the single-threaded census
  `per_core_census_to_depth_four`, derived from the matrix's classification,
  and the loom claim is stated as the pairs it runs.
- **A queued core's second acquisition is the deployed lock's no-op too —
  decided by its request word — and every per-core entry point decides on
  the core's own words before it writes** (the class behind PR #890 review
  rounds 2 and 3, closed at the cause).  Rounds 2 and 3 and the closure
  audit's stall were one defect: the lock did not know the executing core's
  own situation — no held word, then one `cancel` did not read, and no
  record of a core's live request at all — so the refinement asserted no-op
  blocks of paths the code did not have and the consumers relied on caller
  contracts.  `QueuedRwLock` now carries a third word per core, `request`
  (`ticket + 1` for the core's one live request, `NO_REQUEST` for none; set
  by `take_ticket`, cleared at a reader's entry, the writer's release, a
  withdrawal's publish and a refused single attempt's pass), and every
  entry point decides the core's case — idle, queued, withdrawn, holding —
  on `held`, `request` and `cancelled` before it writes anything shared.
  Five things new code must respect.  (1) **One outstanding ticket per core
  is a fact the lock establishes, not a contract**: `enqueue` by a queued
  core returns the ticket it already holds, by a reader holder the
  `HELD_TICKET` sentinel (served at once, a no-op at every terminator), and
  the fused acquisitions and the guards return on `involved`; a `cancel` or
  `complete_*` by a core with no request is **refused** (`own_request`,
  every build), one naming a ticket other than the core's own is reported in
  debug builds and withdraws or completes the recorded one, and `complete_*`
  wait for their own turn rather than trusting the poll.  (2) **The
  per-core state matrix is the behavioural pin and `build.rs` holds it to
  the code**: `per_core_state_matrix` classifies every per-core entry point
  in every per-core state, `PER_CORE_ENTRY_POINTS` must equal the lock's
  `pub fn`s taking `core_id` (derived from the code view), and every one of
  the twelve is pinned at the level of **statements** (round 4 — order is
  not control: a harmless earlier read satisfied round 2's first-read-
  before-first-write check while the real branch was inverted or its
  `return` moved below the write): `core_entry_point_status` requires the
  controlling branch to be a top-level `if` of the entry point's own
  brace-matched body with exactly the pinned condition and a block ending
  in a diverging `return`, placed before the statement performing the
  shared write; a name the condition reads bound by the pinned load and
  not rebound in between; `own_request` called at top level; a guard's
  acquisition the only occurrence of the call, inside `if acquired`; and
  the helpers held to their exact forms (`involved` the disjunction,
  `own_request` an `assert!`).  `verify_core_entry_point_scanner` holds the
  checker itself to token-preserving mutations.  A new entry point fails
  the build until it is classified.  (3) **The Lean
  blocks are conditioned on the words, and the abstract facts are derived**:
  `queuedSim`'s sixth conjunct is `queuedRequestsSim` (a core's word
  records `t` iff `(t, c)` is a live ledger entry; the seventh,
  `queuedRequestModesSim`, pins a live request's mode word to the spec's
  queued mode — round 5, below), every per-core branch
  hypothesis of `queuedBlock` reads `c ∈ conc.heldRead` / `(c, t) ∈
  conc.requests` rather than `c ∈ abs.readers`, and
  `queuedBlock_preserves_queuedSim` derives the spec's branch from the
  relations (`queuedSim_involved_of_request`, `queuedSim_involved_of_held`,
  `queuedSim_not_involved`) — so a relation pinning a word to the wrong fact
  fails the proof, where before the step cases consumed the abstract
  hypothesis and consulted the relation nowhere.  The queued no-op blocks
  are `acquireRead_queued` / `acquireWrite_queued` (two loads); `cancel` has
  `cancel_holder`, `cancel_noRequest` and `cancel_queued`; the promotion
  carries the relation through the admitted readers' cleared requests and
  takes the live cores' distinctness (INV-R3) for it.  (4) **The gates ask
  the lock**: the Tier-5 oracle issues a queued waiter's re-acquisition and
  an uninvolved core's withdrawal to the ticket lock and holds every core's
  request word to the spec's queue and held writer (`check_requests`); the
  loom enumeration includes enqueue-twice-then-acquire in both modes, and
  its mutation inverts the `involved` load in `acquire_read`.  (5)
  **`request` lives on the second cache line by design** (128 bytes): the
  shared words fill the first, the owner-only arrays — `request` and, since
  round 5, `request_mode` — the second, and
  `shared_words_fill_the_first_line_and_requests_the_second` pins the
  layout.
- **A withdrawal of a request the spec has already admitted realises the
  admission; the deployed lock decides which on its own words, and the Tier-5
  comparison is of identities, per step** (PR #890 review round 5).  After a
  writer's `release_write` returns, the head waiter is *served* but not yet
  *completed*: the spec's release promoted it atomically, so its `cancel`
  there is the holder no-op, while the lock retired the served ticket and had
  one holder fewer than the spec.  The bridge folds every waiter's entry into
  the release block that promotes it, so that interval does not exist in the
  model, and the fold was sound only if nothing a served core can do differs
  from the entered state — which `cancel` broke.  And the spec's own `cancel`
  was the neutral filter while the lock's withdrawal of a served head passed
  the turn to the readers behind it, so whether a queued reader was a spec
  holder was **path-dependent**, and no history-free decision in the lock
  could be right.  Six things new code must respect.  (1) **The spec moved,
  not the lock's memory** (the improvement direction): `cancel` promotes the
  head reader run (the bullet above), and with that "served reader ⟹
  holder", "served writer ⟹ holder iff `state == 0`" and "queued reader ⟹
  holder iff no live write request is ahead of it" are decidable from the
  lock's words.  (2) **The mode is the lock's record.**  `enqueue(core, mode)`
  stores `request_mode` before the request word (`take_ticket`), `complete_*`
  in the other mode is refused on it in every build, and `cancel` decides on
  it: a write request enters when served with no reader (a CAS from `0` that
  cannot fail — only the served core can add a reader), a read request enters
  when `write_request_ahead` — the other cores' request and mode words, read
  in that order, over `[now_serving, ticket)` — finds no live writer, and
  waits for its turn to do so; anything else is the LC3 withdrawal verbatim.
  The verdict is stable: a writer ahead can only leave.  (3) **`cancel`
  returns `CancelOutcome`** — `Withdrawn`, nothing owed; `Holding`, the core
  holds and owes a release — and the two-phase-locking unwind needs no branch,
  since the release that follows every withdrawal releases what a `Holding`
  entered.  (4) **The Lean relation carries the mode**: `requestModes` beside
  `requests`, `requestModeStore` in `takeTicketOps` ahead of the request
  store, `queuedRequestModesSim` (a live request's recorded mode is
  `specModeOf` — the queued mode, or `write` for the held writer) as
  `queuedSim`'s seventh conjunct, carried through the promotion with INV-R3;
  the withdrawal block is `withdrawOps ++ cancelPromoteFrom`, the CAS-retry
  bridge's `cancel_promoting` carries the run as a promoting release does,
  and a `Holding` withdrawal has no block of its own — it is the deferred
  half of the entry the promoting block already folded, which is what makes
  the served interval sound to fold again.  (5) **The gates ask the lock.**
  The oracle holds each withdrawal's verdict to the spec's (`expect_outcome`:
  a queued waiter's must be `Withdrawn`, a holder's and an uninvolved core's
  the no-op), mirrors the promoting withdrawal (`promote_reader_run`), holds
  the mode words (`check_requests`), and both oracles print **one identity
  line per state** — `W=<core|->;R=<sorted reader cores>;Q=<core:r|w,...>`,
  the initial state included — read back out of the ticket lock's per-core
  words on the Rust side, where `W=<flag>;R=<count>;Q=<length>` had let a
  wrong-waiter promotion, a reordered queue or a changed mode agree on every
  count; the harness compares whole outputs and captures both exit statuses.
  The matrix has nine start states (`(CoreState, Env)` — queued and served
  in both modes, a served writer behind a reader, withdrawn, holding, idle)
  under one classification `cell`, and the census replays every sequence of
  up to four entry points from each; `build.rs` holds `run_unit` to every
  per-core entry point, which is how the two guard spellings were found to
  be in no loom unit.  `scripts/check_lock_ffi_symmetry.sh` holds every
  symbol's parameter and return types across the three surfaces, since
  `ffi_rw_lock_enqueue` gained an argument and `ffi_rw_lock_cancel` a
  result.  (6) **The unbounded loom models do not spin against each other**:
  loom's branch budget is exhausted by two threads spinning at once, so a
  model has one waiting thread and the driving thread completes served
  requests after the race; and a third acquisition in a two-thread model
  multiplies the schedules past what an unbounded run finishes, so the
  ordering in which one core withdraws twice behind two successive writers
  is pinned sequentially
  (`a_second_withdrawal_behind_a_new_writer_is_retired_by_its_release`)
  rather than modelled.
- **The two-phase-locking shrinking phase withdraws before it releases**
  (WS-LC LC4, v0.34.54).  `withLockSet`'s third phase and the revalidated
  entry's refusal path are both `unwindAll` — one definition, so the two
  cannot answer "what does a bracket do on the way out" differently.  Five
  things new code must respect.  (1) **The order is load-bearing.**  Two
  identities meet at each member: a release by a non-holder is the identity,
  and a withdrawal by a holder is the identity (INV-R4 keeps holders out of
  `waiters`) — on the deployed lock, a withdrawal by a core the spec has
  admitted *realises* the admission (`CancelOutcome::Holding`, PR #890 review
  round 5) and the release that follows releases it — so both orders are
  correct on a well-formed state and neither needs a branch.  Withdrawing first is what makes the payoff
  *unconditional* — the release arms promote **from** `waiters`, so a core
  still queued when its own release runs can be promoted into a holder slot
  the withdrawal already passed.  `rwLock_release_then_cancel_not_queued`
  records the other order so a refactor that swaps the folds has to answer
  it.  (2) **The payoff is about `waiters`, not about holding.**
  `unwindAll_leaves_no_queued_request` says the unwinding core has no queued
  request at any member, with no distinctness and no resolvability condition
  on the footprint — the withdrawal fold establishes it everywhere and no
  release arm enqueues.  It deliberately does **not** say the core is
  uninvolved: a core holding a *write* lock, unwound at a member declared
  `.read`, keeps `writerHeld`, and ruling that out needs the growing phase's
  mode agreement threaded through.  (3) **The insensitivity predicate is
  about the phase**: `UnwindInsensitive` / `UnwindInsensitiveOn` carry two
  clauses, one per operation.  A separate `CancelInsensitive` beside a
  `ReleaseInsensitive` would be one question with two answers and every
  capstone would have to remember to demand both; discharging the pair costs
  nothing, since each witness is its release half with one name changed.
  Every `withLockSet` invariant-carriage lemma likewise gained a
  withdrawal-stability hypothesis.  (4) **`releaseAll` still means release
  only** and every theorem about it is unchanged; `cancelAll` sits beside it
  and `unwindAll` is the composite.  A statement characterising what a
  *bracket* does names `unwindAll`.  (5) **The bracket stays
  projection-invisible**: the golden trace is byte-identical, and
  `unwindAll_lockWritesOnly` / `_preserves_projection` / `_confinedToCore`
  carry the information-flow results across unchanged.

  Two things were **re-homed rather than duplicated** in the same cut, each
  having lived downstream of the definition it is about: the at-any-key
  characterisation of the object-store update, and the per-primitive
  extension-invariant preservation lemmas — which existed in *three* copies
  (`LockSetHeld`, `NonInterferencePerCore`, `IPC/CrossCore/Cancellation`)
  because no two of those modules are in each other's import closure.  They
  now sit once, beside `updateObjectLockAt` in `WithLockSet`, which all three
  import.  `LockId.lookup_object_eq` — the missing third sibling of the
  lookup's kind and lock-state projections — was added, since without it a
  caller that knows what the store holds at a key could conclude nothing
  about what a lookup there returned.
- **A lock-delay bound is denominated, and by an assumption the kernel does not
  make** (WS-LC LC5, v0.34.55).  `RwLockExecution` carries `stepCost : Nat →
  Nat` — the cycles between step `k` and `k+1` — **with no default**, so all
  nine construction sites declare a cost model where a reviewer can see it.
  Five things new code must respect.  (1) **Three denominations, three
  assumptions.**  A bound in *lock operations* is unconditional given fairness
  (`rwLock_writer_admissionStep_bounded`).  A bound in *cycles* needs a
  per-critical-section ceiling (`RwLockExecution.BoundedCriticalSection`,
  supplied as a hypothesis: `rwLock_writer_admitted_within_cycle_budget`,
  `lockContention_elapsed_bounded`).  A bound in *hardware ticks* needs a
  counter frequency, which is a board fact, so it lives in a **staged** module
  (`Locks/ReleaseBudgetTiming.lean`) and not in the production lock model at
  all.  Quoting a figure as a time without naming which conversion produced it
  is quoting a number with no denominator.  (2) **`BoundedCriticalSection` is a
  Prop about the field, never a structure invariant.**  An execution whose
  critical sections are unbounded is a perfectly good execution and every step
  bound still holds of it; what fails is only the *reading* of that bound as
  wall-clock.  Do not add it to `RwLockExecution` as a field or a well-formedness
  conjunct — that would refuse executions the model should admit, and would make
  the step bounds conditional on something they do not need.  (3) **The cycle
  forms are corollaries, and each one collapses back.**
  `rwLock_writer_cycle_budget_at_unit_cost` and
  `lockContention_elapsed_at_unit_cost` instantiate the cycle bound to the step
  bound it came from, because a denomination that had quietly weakened the claim
  would look exactly like one that had not.  A new cycle-denominated result
  states its own collapse.  (4) **The generic and execution-level forms both
  stay.**  `lockContention_wallClock_bounded` takes a cost function (the general
  statement, over any cost model); `lockContention_elapsed_bounded` reads
  `e.stepCost` (the instance at this execution's own).  A caller holding an
  execution should reach for the latter and not re-supply what the execution
  already carries; the typed evidence arms consume the execution-level forms
  precisely because that pins both.  (5) **`MAX_RELEASE_DELAY` is 1024 *lock
  operations*.**  `releaseBudgetCycles` converts it under a ceiling and
  `releaseBudgetTicks` under a timer configuration; on the RPi5's 54 MHz /
  1 ms timer the same 1024 steps span from a single tick to 1024 ticks
  depending on the ceiling assumed (`releaseBudgetTicks_rpi5_range`), which is
  why the step figure alone was never a time.  **A duration converts by the
  ceiling** (PR #890 review round 4): `hardwareTimerToModelTick` floors an
  *absolute* counter value, and an interval that begins mid-tick crosses one
  boundary more than its length suggests, so `releaseBudgetTicks` uses
  `hardwareDurationToModelTicks` and `elapsed_ticks_le_releaseBudgetTicks`
  is stated from any start counter (`hardwareTimerToModelTick_sub_le_duration`
  is the relation between the two conversions).  New code converting an
  interval must not reach for the absolute conversion.

  `elapsedBetween` and its two bounds moved here from
  `InformationFlow/FineLockFlow`, where they had been introduced with a note
  that the execution datatype "has no such notion" — it has one now, so the
  vocabulary belongs beside the datatype that carries it.
- **Registered uncovered lock domains** are enumerated in Lean, not in prose:
  `UncoveredLockDomain` (`InformationFlow/FineLockFlow.lean`) names each gap and
  its owner, and its completeness theorem forces a new domain to be registered.
- **An operation's `_modifiedFields` list is a proof obligation, not a
  comment** (WS-RR RR7.19, v0.34.70; completed by the RR7 audit round,
  v0.34.109).  The six `*_modifiedFields` lists in
  `Kernel/CrossSubsystem.lean` had no consumer at all: an operation could write
  a field its own list omits and nothing would notice.  RR7.9 found one such
  omission by reading (`capabilityOp_modifiedFields`, missing the four CDT
  fields); giving the lists an obligation found a second immediately
  (`storeObject_modifiedFields`, missing `.asidTable`, which `storeObject`'s
  record update writes when the stored or displaced object is a `.vspaceRoot`);
  and writing the four theorems v0.34.70 had promised and not shipped found two
  more, plus the gap that had made one of them impossible to state.  Four
  things new code must respect.  (1) **Declaring a write-set obliges you to
  prove it**: `preservesFieldsOutside fs st st'` says every `StateField`
  outside `fs` is unchanged, quantified over the whole field type rather than
  over whatever the author enumerated, and **every one of the six lists carries
  a `_preservesFieldsOutside` theorem at its own list** — `storeObject`,
  `revokeService`, `serviceRegisterDependency`, the retype, the four capability
  operations (`cspaceMintWithCdt`, `cspaceCopy`, `cspaceMove`,
  `cspaceDeleteSlot`) and both dual-queue operations — each false at an
  under-declared list.  (2) **`StateField` is total over `SystemState`, and the
  pin is a theorem, not a count**: `SystemState.eq_of_fieldEq_all` proves that
  agreement on every constructor is state equality, through
  `SystemState.mk.injEq`, so a field added to the structure without a
  constructor fails to elaborate.  At v0.34.70 the enumeration named sixteen of
  twenty-seven fields, so a write to `scThreadIndex` — which the receive path's
  donation return performs — could not be *declared* at all, and every
  write-set claim in the tree was silent about eleven fields.  (3)
  **Over-declaring is the safe direction** (`preservesFieldsOutside_mono`); it
  costs disjointness, never soundness.  `ipcEndpointOp_modifiedFields` is
  `storeObject`'s set **plus `.scheduler` and `.scThreadIndex`** (the wake and
  the deschedule; the donation return), and `capabilityOp_modifiedFields` is
  `storeObject`'s set plus the four CDT fields.  The v0.34.70 lists were
  `storeObject`'s set alone and `[.objects, .lifecycle, …CDT]`, both *false* of
  their operations — the second under the very sentence RR7.19 had retracted
  for the first.  Tightening the index/ASID fields back out is registered debt
  (`docs/REGISTERED_DEBT.md` §C), not an assumption.  (4) **The lists are
  consumed**: `predicateFramedByDisjointWrites` turns "this read-set and that
  write-set are disjoint" into "this operation preserves that predicate", so an
  omitted field licenses a preservation conclusion the operation does not
  earn.  A list that composes another is *defined over* it
  (`lifecycleRetypeObject_modifiedFields = storeObject_modifiedFields`; the IPC
  and capability lists are `storeObject_modifiedFields ++ …`), so a correction
  cannot reach one and miss another; and each composite theorem is proved from
  one lemma per primitive the operation is built from, composed by
  `preservesFieldsOutside_trans`, never by a second reading of the operation.
- **Every declared `LockSet` footprint carries a size bound, stated at its own
  arity** (WS-RR RR7.18, v0.34.69).  `boundedWait_under_2pl`, the
  `KernelOperation` invariant and the WCRT surface all take
  `S.size ≤ maxLockSetSize` as a premise, so a footprint without one is a
  transition that reasoning is **silent** about — worse than one it bounds
  loosely.  `lockSetTransitions_within_bound` is a hand-written conjunction and
  had 31 of the tree's **47** footprints; the missing thirteen included every
  state-resolved `*OnCore` form, which is what RR7.12's bracket actually
  acquires.  New code must respect two things.  (1) **The bound is stated over
  every argument, never at a default.**  A footprint that gains a trailing
  `Option … := none` leaves its existing bound elaborating — the default fills
  the new argument in silently — so the shape the live transition declares is
  unbounded while the theorem's name still promises a bound.  That has now
  happened five times (`notificationSignal` at SM9.C.8, `endpointReceive` at
  PR #873 round 8, `endpointSend` and `endpointCall` at RR7.7, and
  `endpointReply`, found by the census: its bound was stated at five of six
  arguments while the live `.reply` dispatch resolves the sixth to `some`).
  (2) **The set is derived, not listed**:
  `SeLe4n/Testing/LockFootprintBoundCensus.lean` collects every `def` whose type
  ends in `LockSet` and named `lockSet_…`, builds the statement its bound *must*
  have from the definition's own telescope, and decides by one `isDefEq` — so a
  new footprint without a bound, or with one at the wrong arity, fails Tier 1
  the day it is written.  A legitimate exemption goes in `boundExemptions` with
  a reason; the list is empty and meant to stay so.
- **Staged modules**: 69 staged-only, listed in
  `scripts/staged_module_allowlist.txt` and gated by
  `scripts/check_production_staging_partition.sh`.  Production must not import
  staged.  (67 until `v0.35.76`, which promoted `Locks/DynamicChainExtension`
  with the RR7.40 footprint that consumes it and staged
  `Architecture/VSpaceARMv8` and `Capability/CSpaceWalkFootprint` — see the
  five-modules note below.  This sentence read **68** from that cut until
  `v0.35.191`, while the allowlist held 69: a hand-kept figure beside a
  derivation, which is what the gate's own output line reports and this prose
  should not restate.  Read the gate, not this number.)  WS-RR RR5.15 promoted five (the three state-committing kernel
  entries `SecondaryEntry` / `PerCoreTimerEntry` / `PerCoreRescheduleEntry`,
  plus the two modules their closure pulls in): an `@[export]` emits a symbol
  only when its module is in `SeLe4n.lean`'s import closure, so a linked image
  carried **one** `T lean_*` entry symbol while `kernel_entry.rs` declared five
  as hard `extern "C"`.  `scripts/check_kernel_entry_exports.py` (Tier 1) now
  verifies each symbol against the built static archive — object code, not a
  text anchor — over a requirement *derived* from **every** HAL `extern "C"`
  declaration: each must be defined by the archive, by the HAL's own assembly
  (a `.global` directive **and** a label for the same name, outside any
  preprocessor conditional, in a source on the `cc::Build` chain that
  `.compile("sele4n_hal_asm")` is called on in a function reachable from
  `main` — the cross gate's own live-chain resolution — and, when a cross
  build's assembled archive is present, also defined by that object code; a
  directive alone declares binding and defines nothing, PR #889 review
  rounds 3–4), or by a reconciled
  `EXPECTED_UNRESOLVED` entry (empty since WS-BP BP4.1 wrote
  `lean_kernel_main`, its one entry until then; an
  entry the HAL stops declaring, the archive starts defining, or — round 6 —
  the Lean tree starts exporting fails, the last because an exported symbol
  whose module sits outside the import closure is exported and undefined at
  once).  Every inventory the gate reads — the Lean exports, the HAL
  declarations, the assembly providers — is read over the shared code views
  with string contents blanked (round 6), so a quoted attribute, block or
  directive is not a symbol.  The
  first cut required the *intersection* of the Lean exports and the HAL
  declarations, which is exactly the set a rename on either side leaves — the
  unresolved spelling drops out of both and the gate passed (PR #889 review).
  **The boot entry's contract left this gate at round 17** and is decided by
  the elaborator in `SeLe4n/Testing/BootEntryContract.lean`: whichever
  declaration carries `@[export lean_kernel_main]` (found with
  `getExportNameFor?`, so any attribute list and any namespace) must call
  `Platform.FFI.bootAndInitialiseRPi5OrHalt` — the checked RPi5 boot with its
  failure handled, so a refused boot parks the PE — and no path from it may
  reach a kernel-state installer except through that call, walked over
  `Expr.getUsedConstants`.  Building the module is the check, and four
  witnesses (a compliant entry and three token-preserving deviations) keep it
  decisive whatever the entry is; since WS-BP BP4.1 wrote it the contract also
  refuses an environment with none.  What the Python gate still holds is
  the link-level half — vacuous until the entry existed, decisive since,
  so the idle-thread, labeling and reservation guarantees cannot be bypassed
  by an entry that boots through `bootFromPlatform` directly.  Executing the
  call is necessary and not sufficient (round 9): the entry must **branch** on
  the checked boot's `Except` and halt on `.error`
  (`boot_entry_handles_failure`, the round-9 scanner check, retired at round
  17 for `BootEntryContract.lean`'s `approvedBootCall`), because a failed boot installs no kernel
  state and returning to Rust would idle the image as though it had booted —
  `discard` and `let _ ←` are refused, the arms are parsed so the `.error`
  arm's own body must halt (round 10: a halt in a following `.ok` arm read as
  the error arm's), no diverging statement may precede the handling match, and
  the match must be on the binding the boot produced rather than on a
  rebinding of its name.  The inventory
  it reads includes the library root `SeLe4n.lean` (round 7), and the
  assembly providers are read off the compile's *executed* chain — top-level
  statements of its own function, at brace depth zero, at or before the
  compile — rather than by receiver spelling.  Since round 8 the receiver
  is a **binding instance**, not a name: `rust_code_view.binding_statement_before`
  resolves it to the last top-level `let [mut] <receiver>` — or, since round
  9, `<receiver> = …`, since a `mut` builder is rebound by assignment with no
  second `let` — strictly before the compile statement, `assembled_sources_in` counts `.file()` calls from
  that instance on, the cross gate's build-script check requires the
  instance and refuses a receiver the compile's function does not bind, and
  the archive parsers accept global text (`T`) only
  (`executable_definitions`), since every requirement the gate reconciles
  is an `extern "C" fn` and a data object under the old name would have
  resolved a call into data.
  Since round 12 every one of those names is **resolved** rather than
  matched: the export attribute is parsed from the list
  (`lean_code_view.attribute_arguments`, shared with `build.rs`, so
  `@[inline, export lean_kernel_main]` is the same export on both sides),
  and an `extern` declaration's requirement is its effective linker
  name, `#[link_name = "…"]` included — located on the string-free view
  and read from the aligned kept one (round 17), so an attribute quoted
  in a doc string renames nothing.  The Lean-side name resolution that
  used to sit here — the suffix rule, the binder scan, the halt
  derivation — went with the boot-entry contract to the elaborator at
  round 17.  `build.rs` refuses a `#[link_name]` alias
  outright for a Lean symbol: the readiness derivation reads the Rust
  identifier, so an aliased seam is attributed to no gate at all.
- **The WS-SM theorem total is measured, not summed — and it counts
  propositions, not registrations.**
  `SeLe4n/Kernel/Concurrency/PhaseTheoremManifest.lean` registers one entry per
  phase SM0..SM10, each naming the theorem inventories that phase owns.  Those
  inventories hold **1149 entries**, of which **927 are theorems**: the
  inventories register a phase's whole surface, so 222 entries are `def`s —
  lock-set footprints, PIP chain-start markers, per-core invariant predicates,
  WCRT cost functions — and
  every inventory's construction macro proves only that the name *resolves*,
  never that its type is a `Prop`.  **Quote 927, and quote it as theorems; 1149
  is the entry count.**  A `List.length` cannot tell the two apart, so the
  propositionality census at the end of that module resolves each identifier
  against the environment and fails elaboration on drift.  **Eight of the eleven
  phases register zero theorems**, so only SM2, SM3 and SM5 contribute: six
  (SM1, SM6..SM10) carry no inventory at all, and **SM0 and SM4 carry
  *assumption ledgers*** — `smpLatentInventory` and `smpRetiredInventory` —
  which `smpPhaseTheoremCount` correctly excludes, leaving those two phases'
  own theorems unmeasured just the same.  Building only the six missing
  inventories would therefore not close the gap; the debt is eight phases wide.
  That gap is real, and the honest zero is what makes it visible.  Adding a
  phase without an entry
  fails elaboration; adding an inventory no phase claims fails Tier 0
  (`scripts/generate_smp_theorem_manifest.py --check`).  New code must not
  reintroduce a hand-written per-phase figure.

### Closed workstreams

Every closed workstream is listed in the *Workstream registry* of
[`docs/REGISTERED_DEBT.md`](../../docs/REGISTERED_DEBT.md) with the versions it
spans; what each one changed is in [`CHANGELOG.md`](../../CHANGELOG.md) at those
versions.  **WS-RC** closed at v0.31.2 with R6–R14 absorbed into WS-SM per
SM0.Q, and **WS-AN** closed at v0.30.11.
