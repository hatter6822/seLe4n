# Audit v0.29.0 — Deferred Items (WS-V / post-1.0 scope)

**Parent audit:** [`AUDIT_v0.29.0_COMPREHENSIVE.md`](AUDIT_v0.29.0_COMPREHENSIVE.md)
**Plan:** [`AUDIT_v0.29.0_WORKSTREAM_PLAN.md`](AUDIT_v0.29.0_WORKSTREAM_PLAN.md) §17
**Workstream:** WS-AK Phase AK10 (Closure — AK10-J)
**Status:** Tracking file established under v0.30.6.

This document formalises the deferred scope from the audit's §2.5
"DEFER-to-WS-V" bucket plus two cascade items tracked for v1.1 hygiene.
Each row states (a) the underlying audit finding ID, (b) the deferral
rationale, (c) the accepting workstream, and (d) the acceptance
criteria that the future workstream must discharge.

None of the deferred items are correctness-critical at v0.30.6: the
AK1..AK9 remediation phases have either structurally closed the
primary attack surface for each finding or recorded a defensive
invariant witness that holds uniformly at the proof-obligation
boundary. The items below are post-patch hardening, hardware-binding
integration, or proof-hygiene polish.

---

## Deferred → WS-V / AG10 (Hardware Binding Integration)

These items depend on real-silicon bring-up on the Raspberry Pi 5 target
and cannot be substantively closed without either QEMU or hardware
integration. WS-V is the accepting workstream.

### DEF-A-M04 — TLB+Cache Composition Full Closure

- **Audit finding:** A-M04 (MEDIUM). D-cache→I-cache pipeline ordering
  for executable memory must be modeled end-to-end across page-table
  update, cache maintenance, and TLB invalidation.
- **AK3-G disposition:** PARTIAL+DOC. `CacheBarrierKind` inductive +
  `cacheCoherentForExecutable` predicate landed in `CacheModel.lean`;
  `pageTableUpdate_icache_coherent_under_sequence` theorem proves the
  required ordering under an externalised sequence hypothesis.
- **Deferral reason:** The full composition closure requires wiring the
  sequence through the HAL `cache` module's `clean_pagetable_range` +
  `ic_iallu` emission sites, which only meaningfully exercise on
  real ARM-v8 hardware (or a cycle-accurate model). QEMU's
  `raspi4b` and `virt` machines do not fully model I/D-cache coherence.
- **WS-V acceptance criteria:**
  - HAL cache-flush sites emit a Lean-callable ordering witness via the
    FFI layer.
  - End-to-end theorem `pageTableUpdate_icache_coherent` without an
    externalised sequence hypothesis.
  - Empirical validation on RPi5 hardware (executable page flush
    timing matches `docs/hardware_validation/`).

### DEF-A-M06 / DEF-AK3-I — `tlbBarrierComplete` Substantive Binding

- **Audit finding:** A-M06 (MEDIUM). `tlbBarrierComplete` in the
  architecture invariant is currently a stub predicate; the true
  contract (every TLB operation is sandwiched by DSB ISH + ISB) must be
  bound to the Rust HAL's emission pattern.
- **AK3-I disposition:** DEFER+DOC. TPI-DOC-AK3I annotation in
  `Architecture/Invariant.lean`.
- **Deferral reason:** The HAL's `tlb::invalidate_*` functions emit the
  correct barriers (verified by `cargo test` + cycle inspection), but a
  Lean-level proof that every invalidation call site is barrier-bracketed
  requires static analysis of the HAL's call-graph — a WS-V scope item.
- **WS-V acceptance criteria:**
  - `tlbBarrierComplete` refined to require a proof-carrying witness at
    every TLB-invalidation kernel entry point.
  - Preservation theorems updated to thread the witness.

### DEF-A-M08 / DEF-A-M09 / DEF-AK3-K — MMU/Device-Memory BarrierKind

- **Audit findings:** A-M08 + A-M09 (MEDIUM). Page-table updates must
  observe the full ARMv8 ordering (`dsb ishst`, `dc cvac + dsb ish`,
  `isb`) and Device-memory MMIO writes must observe `dsb ishst` before
  externally-observable side effects.
- **AK3-K disposition:** DEFER+DOC. Doc block at top of
  `SeLe4n/Kernel/Architecture/VSpaceARMv8.lean`.
- **Deferral reason:** Same rationale as DEF-A-M04 — needs HAL-layer
  sequencing witness for full closure.
- **WS-V acceptance criteria:**
  - `BarrierKind` composition theorem covering MMU update + MMIO side
    effects end-to-end.
  - HAL MMIO helpers emit a BarrierKind witness through the FFI.

### DEF-C-M04 — `suspendThread` Atomicity Rust-Side Proof

- **Audit finding:** C-M04 (MEDIUM). `suspendThread` transient window
  between "remove from run queue" and "clear pendingMessage" requires
  interrupts to be disabled on hardware.
- **Disposition:** DEFER+DOC (H3-ATOMICITY annotation in
  `SeLe4n/Kernel/Lifecycle/Suspend.lean`).
- **Deferral reason:** The Lean model is deterministic and sequential; a
  real hardware interrupt during the transient window is a timing issue
  only. Defense requires interrupt masking around the kernel entry
  wrapper, which is a HAL-integration concern.
- **WS-V acceptance criteria:**
  - HAL's FFI wrapper for `suspendThread` brackets the call with
    `interrupts::with_interrupts_disabled`.
  - Rust-side `#[must_use]` or clippy lint enforces bracket discipline.

### DEF-P-L9 — VSpaceRoot Boot Exclusion

- **Audit finding:** P-L9 (LOW). Boot-time `bootSafeObject` predicate
  excludes `.vspaceRoot` variant from its runtime boot-safety check;
  the rationale is that VSpaceRoot mappings are established by the
  platform-specific pre-boot stage, not by the generic `bootFromPlatform`
  harness.
- **Disposition:** DEFER+DOC (annotation in `SeLe4n/Platform/Boot.lean`
  and cross-referenced in `Platform/RPi5/Board.lean`).
- **Deferral reason:** The exclusion is correct for the AK9 checked
  boot path; closing the gap requires the platform-specific
  `RPi5/VSpaceBoot` shim (WS-V scope).
- **WS-V acceptance criteria:**
  - `RPi5/VSpaceBoot.lean` establishes the boot VSpaceRoot with full
    invariant witness.
  - `bootFromPlatformChecked` refined to include VSpaceRoot in its
    per-object `bootSafeObject` check.

### DEF-R-HAL-L14 — SVC `_syscall_id` FFI Wiring

- **Audit finding:** R-HAL-L14 (LOW). SVC handler currently returns
  `NOT_IMPLEMENTED` (17) instead of dispatching the kernel syscall
  table; the stub was placed in AI1-B.
- **Disposition:** DEFER+DOC (TODO marker at `rust/sele4n-hal/src/trap.rs`).
- **Deferral reason:** SVC dispatch requires the full FFI bridge
  (WS-V / AG10-F) that carries the typed argument decode path from
  userspace through the HAL trap frame into `syscallEntryChecked`.
- **WS-V acceptance criteria:**
  - `handle_svc(syscall_id, args)` dispatches through the Lean-provided
    syscall table via `sele4n_syscall_dispatch` FFI.
  - `cargo test --workspace` covers the SVC → dispatch path end-to-end.

---

## Deferred → Post-1.0 Proof-Hygiene Workstream (WS-AL residuals)

### DEF-F-L9 — 17-Deep Tuple Projection Refactor

- **Audit finding:** F-L9 (LOW). `allTablesInvExtK` in `SeLe4n/Model/
  State.lean` carries a 17-tuple invariant whose projection accessors
  are position-indexed; adding a new tuple entry requires updating every
  downstream caller's projection depth.
- **Disposition:** DEFER (AK7-K marker) per §14.3 of the plan.
- **Deferral reason:** Refactoring to a named structure is strictly a
  readability/maintainability win with no correctness impact. The
  WS-AF-26 design rationale stands: 17-deep tuples are tractable under
  Lean 4.28.0's elaborator, and a named-record refactor cascades
  through ~80 proof sites.
- **Post-1.0 acceptance criteria:**
  - Convert `allTablesInvExtK` to a Lean `structure` with named fields.
  - Update downstream callers to use field-access notation.
  - No behavioural change; witness-equality theorem retained.

### DEF-AK2-K.4 — `eventuallyExits` Hypothesis (by design)

- **Audit finding:** AK2-K.4. The WCRT main theorem in
  `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean` carries an externalised
  `eventuallyExits` hypothesis; the kernel cannot prove this
  unconditionally (it's a scheduler-liveness discipline imposed by
  deployment configuration).
- **Disposition:** DEFER by design (documented in
  `docs/spec/SELE4N_SPEC.md` §5.7 WCRT deployment obligations).
- **Deferral reason:** `eventuallyExits` is a deployment-layer
  obligation: the application scheduling discipline (CBS bandwidth
  admission + priority-band configuration) must admit a finite WCRT
  for every thread. The kernel's scheduler-liveness proofs bound each
  individual step; the unbounded-step case is pathological and
  indicates a mis-configured deployment.
- **Post-1.0 acceptance criteria:** none — this is a correct by-design
  externalisation. The deferred tracking is informational only so
  future readers understand why the hypothesis is still external.

### DEF-AK7-E.cascade — `ValidObjId` / `ValidThreadId` Full Rollout

- **Audit finding:** F-M03 (MEDIUM) / AK7-E. Baseline `ValidObjId` /
  `ValidThreadId` subtypes landed in v0.29.14 (WS-AL AL1b/AL8). ~240
  additional handler call sites across Lifecycle / SchedContext /
  IpcBufferValidation / Scheduler layers still take raw
  `ObjId` / `ThreadId` instead of their `Valid*` refinements.
- **Disposition:** DEFER to v1.1 (per plan §17 point 3).
- **Deferral reason:** Primary attack surfaces closed structurally via
  the AL1b / AL7 dispatch-boundary guards; the remaining migration is
  a readability pass that reduces the number of runtime `none`
  fallbacks in handler internals. Cascades through ~240 preservation
  proofs — the effort-to-risk ratio favors batching into a post-1.0
  hygiene pass.
- **Post-1.0 acceptance criteria:**
  - `scripts/ak7_cascade_baseline.sh` `SENTINEL_CHECK_DISPATCH` metric
    reaches the v1.1 target floor.
  - Handler signatures uniformly require `ValidObjId` / `ValidThreadId`
    at all public entry points.

### DEF-AK7-F.cascade — `ObjKind` Migration + Typed-Helper Adoption

- **Audit finding:** F-M04 (MEDIUM) / AK7-F. Baseline `ObjectKind` +
  `KindedObjId` parallel-structure landed in v0.29.14 (AL2); further
  hygiene items tracked as AK7-F.reader.hygiene (~304 raw `match
  st.objects[id]?` sites remaining, partially migrated to ~600 in
  WS-AM AM7) and AK7-F.writer.hygiene (~50 `storeObject` sites
  remaining candidates for `storeObjectKindChecked` wrapper adoption).
- **Disposition:** DEFER to v1.1 (per plan §17 point 2).
- **Deferral reason:** Cascade through ~354 call sites is a
  readability pass — defense-in-depth, not correctness-critical. The
  AM4 invariant-layer guarantee (`lifecycleObjectTypeLockstep` as 11th
  conjunct of `crossSubsystemInvariant`) makes the writer-side
  migration redundant at the invariant layer; the reader-side
  migration is purely cosmetic.
- **Post-1.0 acceptance criteria:**
  - `scripts/ak7_cascade_check_monotonic.sh` `RAW_MATCH_TCB` metric
    reaches the v1.1 target floor.
  - `GETTCB_ADOPTION` / `GETSCHEDCTX_ADOPTION` / `STOREOBJECTCHECKED_
    ADOPTION` metrics reach the v1.1 target ceiling.

---

## Cross-Reference Summary

| Deferred ID | Audit Finding | Severity | AK-Phase Disposition | Accepting WS |
|-------------|---------------|----------|-----------------------|--------------|
| DEF-A-M04 | A-M04 | MEDIUM | AK3-G: PARTIAL+DOC | WS-V |
| DEF-A-M06 | A-M06 | MEDIUM | AK3-I: DEFER+DOC | WS-V |
| DEF-A-M08 | A-M08 | MEDIUM | AK3-K: DEFER+DOC | WS-V |
| DEF-A-M09 | A-M09 | MEDIUM | AK3-K: DEFER+DOC | WS-V |
| DEF-C-M04 | C-M04 | MEDIUM | DEF+DOC (v0.29.11) | WS-V |
| DEF-P-L9 | P-L9 | LOW | DEF+DOC (v0.30.4) | WS-V |
| DEF-R-HAL-L14 | R-HAL-L14 | LOW | DEF+DOC (v0.29.5) | WS-V |
| DEF-F-L9 | F-L9 | LOW | DEFER | Post-1.0 WS-AL' |
| DEF-AK2-K.4 | AK2-K.4 | — | By design | — |
| DEF-AK7-E.cascade | F-M03 | MEDIUM | AL1b/AL8 baseline | v1.1 WS-AN |
| DEF-AK7-F.cascade | F-M04 | MEDIUM | AL2/AL6 baseline | v1.1 WS-AN |

Total deferred: **11 items** — 7 WS-V (hardware-binding), 4 post-1.0
proof-hygiene / by-design.

---

## Closure Criteria

This tracking file is **closed** for WS-AK: every v0.29.0 audit finding
either has a FIX landing in AK1..AK9, a DOCUMENT disposition, or an
entry in this file. The next workstream to pick up deferred items is
WS-V (hardware integration); see §17 of the parent plan for scope.
