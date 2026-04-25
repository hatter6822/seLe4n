# Audit v0.29.0 — Deferred Items (post-1.0 hardening candidates)

**Parent audit:** [`AUDIT_v0.29.0_COMPREHENSIVE.md`](AUDIT_v0.29.0_COMPREHENSIVE.md)
**Plan:** [`AUDIT_v0.29.0_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md) §17 (archived in `docs/dev_history/audits/` after WS-AK closure)
**Workstream:** WS-AK Phase AK10 (Closure — AK10-J)
**Status:** Tracking file established under v0.30.6.

This document formalises the deferred scope from the audit's §2.5
"DEFER-to-WS-V" bucket plus two cascade items tracked for post-1.0
hygiene. Each row states (a) the underlying audit finding ID, (b) the
deferral rationale, and (c) the acceptance criteria that a future
hardening workstream must discharge.

### Terminology note

An earlier revision of this file routed several items to "WS-V / AG10".
Both WS-V (pre-release audit remediation, closed at v0.21.7) and AG10
(WS-AG Phase 10, closed at v0.27.1) are **closed workstreams**; using
them as deferral buckets is misleading. Each deferred entry below is
recorded as a **post-1.0 hardening candidate; no currently-active plan
file tracks it**, matching the convention established by the AK8
second-pass audit (v0.30.3). When maintainers open a hardware-binding
or proof-hygiene workstream that takes on these items, they should
reference this file and update the row in question.

None of the deferred items are correctness-critical at v0.30.6: the
AK1..AK9 remediation phases have either structurally closed the
primary attack surface for each finding or recorded a defensive
invariant witness that holds uniformly at the proof-obligation
boundary. The items below are post-patch hardening, hardware-binding
integration, or proof-hygiene polish.

---

## Category A — Hardware-binding integration

These items depend on real-silicon bring-up on the Raspberry Pi 5 target
and cannot be substantively closed without either QEMU or hardware
integration. Recorded as **post-1.0 hardening candidates; no
currently-active plan file tracks them.**

### DEF-A-M04 — TLB+Cache Composition Full Closure **[RESOLVED AT v0.30.10]**

- **Audit finding:** A-M04 (MEDIUM). D-cache→I-cache pipeline ordering
  for executable memory must be modeled end-to-end across page-table
  update, cache maintenance, and TLB invalidation.
- **Disposition:** **RESOLVED** at v0.30.10 by WS-AN Phase AN9-A.
  Previous AK3-G disposition was PARTIAL+DOC.
- **Resolution artefacts (AN9-A):**
  - New `SeLe4n/Kernel/Architecture/TlbCacheComposition.lean` module
    proves `pageTableUpdate_full_coherency` end-to-end (TLB
    consistency + barrier discipline + I-cache coherency in one
    statement) with no externalised sequence hypothesis.
  - `CacheBarrierSequence` algebra with associativity + leaf
    coverage decision procedure.
  - `armv8DCacheToICacheSequence` canonical sequence + coverage
    theorems for `dmb_ish`, `dsb_ish`, `isb` leaves.
  - FFI witnesses `cache_clean_pagetable_range` and `cache_ic_iallu`
    in `rust/sele4n-hal/src/ffi.rs` exposed via
    `SeLe4n.Platform.FFI.ffiCacheCleanPagetableRange` and
    `ffiIcIallu`.
  - Bridge theorem `barrierKind_pt_update_aligns_with_cache_sequence`
    cross-links the AN9-C `BarrierKind` algebra with the
    cache-side `CacheBarrierSequence`.

### DEF-A-M06 / DEF-AK3-I — `tlbBarrierComplete` Substantive Binding **[RESOLVED AT v0.30.10]**

- **Audit finding:** A-M06 (MEDIUM). `tlbBarrierComplete` in the
  architecture invariant is currently a stub predicate; the true
  contract (every TLB operation is sandwiched by DSB ISH + ISB) must
  be bound to the Rust HAL's emission pattern.
- **Disposition:** **RESOLVED** at v0.30.10 by WS-AN Phase AN9-B.
  Previous AK3-I disposition was DEFER+DOC.
- **Resolution artefacts (AN9-B):**
  - `tlbBarrierComplete` predicate in `Architecture/TlbModel.lean`
    refined from `True` to require both
    (i) `MachineState.tlbBarrierEmitted = true`, and
    (ii) `lastTlbBarrierKind &&& 0x05 = 0x05` (bitmask covering
    `dsb ish | isb` leaves).
  - New machine-state fields `tlbBarrierEmitted : Bool := true` and
    `lastTlbBarrierKind : Nat := 0x05` carry the witness.
  - Substantive bridge theorems
    `tlbBarrierComplete_implies_dsbIsh_emitted` and
    `tlbBarrierComplete_implies_isb_emitted` extract individual
    barrier-leaf witnesses from the predicate.
  - Existing `adapterFlushTlb*Hw_barrier_complete` theorems updated
    to require the input state's `tlbBarrierComplete` (instead of
    proving it trivially); default-state corollaries discharge the
    common case.

### DEF-A-M08 / DEF-A-M09 / DEF-AK3-K — MMU/Device-Memory BarrierKind **[RESOLVED AT v0.30.10]**

- **Audit findings:** A-M08 + A-M09 (MEDIUM). Page-table updates must
  observe the full ARMv8 ordering (`dsb ishst`, `dc cvac + dsb ish`,
  `isb`) and Device-memory MMIO writes must observe `dsb ishst`
  before externally-observable side effects.
- **Disposition:** **RESOLVED** at v0.30.10 by WS-AN Phase AN9-C
  (Lean algebra) + AN9-H (Rust mirror).  Previous AK3-K disposition
  was DEFER+DOC.
- **Resolution artefacts (AN9-C / AN9-H):**
  - New `SeLe4n/Kernel/Architecture/BarrierComposition.lean` defines
    the `BarrierKind` inductive (`none`, `dsbIsh`, `dsbIshst`,
    `dsbOsh`, `dsbOshst`, `dcCvacDsbIsh`, `isb`, `sequenced`) with
    the `subsumes` partial order, associativity, and reflexivity
    laws.
  - Headline theorem `pageTableUpdate_observes_armv8_ordering`
    proves the canonical `armv8PageTableUpdateSequence` subsumes
    each ARM ARM D8.11–required leaf.
  - Headline theorem `mmioWrite_observes_dsbIshst_before_sideEffect`
    proves the canonical MMIO write sequence subsumes `dsbIshst`.
  - Rust mirror enum `barriers::BarrierKind` with `emit()` method
    and named composite emitters
    `emit_armv8_page_table_update`,
    `emit_tlb_invalidation_bracket`,
    `emit_mmio_cross_cluster_barrier`.
  - Test `barrier_kind_lean_parity` enforces 1:1 variant alignment
    between Lean and Rust at every commit.

### DEF-C-M04 — `suspendThread` Atomicity Rust-Side Proof **[RESOLVED AT v0.30.10]**

- **Audit finding:** C-M04 (MEDIUM). `suspendThread` transient window
  between "remove from run queue" and "clear pendingMessage"
  requires interrupts to be disabled on hardware.
- **Disposition:** **RESOLVED** at v0.30.10 by WS-AN Phase AN9-D.
  Previous disposition was DEFER+DOC (H3-ATOMICITY annotation).
- **Resolution artefacts (AN9-D):**
  - Rust FFI wrapper `sele4n_suspend_thread` in
    `rust/sele4n-hal/src/ffi.rs` brackets the inner Lean dispatch
    with `interrupts::with_interrupts_disabled`.  Direct calls to
    the inner symbol are forbidden by the docstring discipline note.
  - Lean-side `suspendThread_transientWindowInvariant` predicate
    captures the post-suspend cleanup invariant
    (`threadState = .Inactive`, `pendingMessage = none`,
    `ipcState = .ready`, `schedContextBinding = .unbound`).
  - Theorem `suspendThread_atomicity_under_ffi_bracket` is the
    formal channel that lifts the FFI bracket's promise into the
    proof layer; `suspendThread_transientWindowInvariant_default`
    proves the default-state base case.
  - Three regression tests (`sele4n_suspend_thread_*`) in
    `rust/sele4n-hal/src/ffi.rs::tests` exercise the bracket on
    host with a stub for the inner symbol.

### DEF-P-L9 — VSpaceRoot Boot Exclusion **[RESOLVED AT v0.30.8]**

- **Audit finding:** P-L9 (LOW). Boot-time `bootSafeObject` predicate
  excludes `.vspaceRoot` variant from its runtime boot-safety check;
  the rationale is that VSpaceRoot mappings are established by the
  platform-specific pre-boot stage, not by the generic
  `bootFromPlatform` harness.
- **Disposition:** **RESOLVED** at v0.30.8 by WS-AN Phase AN7-D.2
  (see `CHANGELOG.md`, `docs/WORKSTREAM_HISTORY.md` §AN7).
  Previous disposition (v0.30.4–v0.30.7): DEFER+DOC annotations in
  `SeLe4n/Platform/Boot.lean` and `Platform/RPi5/Board.lean`.
- **Resolution artefacts** (AN7-D.2 landing):
  - `SeLe4n/Platform/RPi5/VSpaceBoot.lean` establishes the canonical
    RPi5 boot VSpaceRoot (`rpi5BootVSpaceRoot`) with the full
    invariant witness: `VSpaceRootWellFormed` (ASID bounded,
    per-root W^X, non-empty mappings) + `bootSafeVSpaceRoot`.
  - Four substantively-proven theorems: `_asid`, `_wxCompliant`,
    `_wellFormed`, `_bootSafe`.
  - Three permission constants each proven `wxCompliant` by `decide`.
  - Three regression tests (`an7d2_01..03`) in
    `tests/Ak9PlatformSuite.lean`.
- **AN9-E cross-reference (v0.30.10):** the `bootSafeObject`
  predicate in `SeLe4n/Platform/Boot.lean` now carries an explicit
  pointer to AN7-D.2's substantive closure
  (`SeLe4n.Platform.RPi5.VSpaceBoot.rpi5BootVSpaceRoot_bootSafe`).
  Boot configs that include the canonical RPi5 boot VSpaceRoot
  discharge the `bootSafe` precondition via that bridge.  The
  structural `(∀ vs, obj ≠ .vspaceRoot vs)` clause in
  `bootSafeObject` is retained because boot configs are not
  required to include a VSpaceRoot — but boots that DO include
  one go through the canonical closure path.

### DEF-R-HAL-L14 — SVC `_syscall_id` FFI Wiring **[RESOLVED AT v0.30.10]**

- **Audit finding:** R-HAL-L14 (LOW). SVC handler currently returns
  `NOT_IMPLEMENTED` (17) instead of dispatching the kernel syscall
  table; the stub was placed in AI1-B.
- **Disposition:** **RESOLVED** at v0.30.10 by WS-AN Phase AN9-F.
  Previous disposition was DEFER+DOC.
- **Resolution artefacts (AN9-F):**
  - New `rust/sele4n-hal/src/svc_dispatch.rs` module owns typed
    argument marshalling (`SyscallArgs::from_trap_frame`,
    `SyscallId` 25-variant enum mirroring `sele4n-types`,
    `dispatch_svc` top-level entry).
  - `trap.rs::handle_synchronous_exception` SVC arm replaces the
    `NOT_IMPLEMENTED = 17` stub with `dispatch_svc(syscall_id,
    &args)`.  Errors decode via the canonical
    bit-63-error-flag convention into kernel-error discriminants.
  - Lean-side FFI declaration `ffiSyscallDispatchInner` in
    `SeLe4n/Platform/FFI.lean` declares the inner dispatcher.
  - 9 unit tests in `svc_dispatch::tests` cover round-trip,
    invalid-id rejection, argument-count rejection, and the
    inner-stub forwarding path.

### DEF-R-HAL-L17 — Bounded WFE Timeout Guard **[RESOLVED AT v0.30.10]**

- **Audit finding:** R-HAL-L17 (LOW, surfaced by AN1-C).  An
  unconditional `wfe()` in the idle loop hangs if no wake event
  ever arrives.
- **Disposition:** **RESOLVED** at v0.30.10 by WS-AN Phase AN9-G.
- **Resolution artefacts (AN9-G):**
  - `cpu::wfe_bounded(max_ticks: u64)` reads CNTPCT_EL0, issues
    `wfe`, and falls through after the timeout.
  - `cpu::WFE_DEFAULT_TIMEOUT_TICKS = 540_000` (10 ms at 54 MHz).
  - 3 regression tests (`wfe_bounded_no_panic_on_host`,
    `wfe_default_timeout_ticks_is_10ms_at_54mhz`, `_is_positive`)
    cover the host stub.

### DEF-R-HAL-L18 — Parameterised Barriers (`BarrierKind`) **[RESOLVED AT v0.30.10]**

- **Audit finding:** R-HAL-L18 (LOW, surfaced by AN1-C).  Generic HAL
  code cannot accept a parameterised barrier; callers must pick a
  specific `dsb_ish`/`isb` helper at the call site.
- **Disposition:** **RESOLVED** at v0.30.10 by WS-AN Phase AN9-H.
- **Resolution artefacts (AN9-H):**
  - `barriers::BarrierKind` flat enum with `None`, `DsbIsh`,
    `DsbIshst`, `DsbOsh`, `DsbOshst`, `Isb` variants.  `emit()`
    method dispatches to the appropriate instruction.
  - Composite emitters `emit_armv8_page_table_update`,
    `emit_tlb_invalidation_bracket`,
    `emit_mmio_cross_cluster_barrier`.
  - `barrier_kind_lean_parity` test enforces 1:1 alignment with
    the Lean `BarrierKind` inductive (AN9-C).

### DEF-R-HAL-L19 — OSH Widening for Multi-Core **[RESOLVED AT v0.30.10]**

- **Audit finding:** R-HAL-L19 (LOW, surfaced by AN1-C).  All
  current barriers are inner-shareable (`ish`); cross-cluster and
  device-coherent ordering require outer-shareable (`osh`) barriers.
- **Disposition:** **RESOLVED** at v0.30.10 by WS-AN Phase AN9-I.
- **Resolution artefacts (AN9-I):**
  - `barriers::dsb_osh()` and `barriers::dsb_oshst()` primitives.
  - `BarrierKind::DsbOsh` and `DsbOshst` enum variants.
  - Lean-side `BarrierKind.dsbOsh` / `dsbOshst` constructors and
    `mmioWriteCrossCluster_observes_dsbOshst` theorem.
  - `storeBarrierClosure` proves OSH+ISH composition subsumes both
    inner- and outer-shareable store ordering requirements.

### DEF-R-HAL-L20 — Secondary-Core Bring-Up (SMP) **[RESOLVED AT v0.30.10]**

- **Audit finding:** R-HAL-L20 (LOW, surfaced by AN1-C).
  Single-core boot is the only path; secondary cores are parked in
  the `boot.S` spin loop.
- **Disposition:** **RESOLVED** at v0.30.10 by WS-AN Phase AN9-J.
  v1.0.0 ships SMP code merged but **disabled by default**
  (`SMP_ENABLED = false`); the activation cost is flipping the
  runtime flag.
- **Resolution artefacts (AN9-J):**
  - New `rust/sele4n-hal/src/psci.rs` module: `cpu_on(target_mpidr,
    entry_point, context_id)` PSCI wrapper using `hvc #0`.
  - New `rust/sele4n-hal/src/smp.rs` module:
    `SMP_ENABLED: AtomicBool`, `CORE_READY: [AtomicBool; 4]`,
    `SECONDARY_MPIDR_TABLE` (3 secondaries for BCM2712),
    `bring_up_secondaries()` (primary entry),
    `rust_secondary_main()` (secondary entry).
  - 9 regression tests cover PSCI return-code roundtrip,
    secondary-MPIDR table values, default-disabled bring-up, and
    enabled-with-stub dispatch path.

---

## Category B — Post-1.0 proof-hygiene

### DEF-F-L9 — 17-Deep Tuple Projection Refactor

- **Audit finding:** F-L9 (LOW). `allTablesInvExtK` in `SeLe4n/Model/
  State.lean` carries a 17-tuple invariant whose projection
  accessors are position-indexed; adding a new tuple entry requires
  updating every downstream caller's projection depth.
- **Disposition:** DEFER (AK7-K marker) per §14.3 of the plan.
- **Deferral reason:** Refactoring to a named structure is strictly a
  readability/maintainability win with no correctness impact. The
  WS-AF-26 design rationale stands: 17-deep tuples are tractable
  under Lean 4.28.0's elaborator, and a named-record refactor
  cascades through ~80 proof sites.
- **Acceptance criteria:**
  - Convert `allTablesInvExtK` to a Lean `structure` with named
    fields.
  - Update downstream callers to use field-access notation.
  - No behavioural change; witness-equality theorem retained.

### DEF-AK2-K.4 — `eventuallyExits` Hypothesis — **RESOLVED in AN5-E (WS-AN v0.30.6)**

- **Audit finding:** AK2-K.4. The WCRT main theorem in
  `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean` carries an
  externalised `eventuallyExits` hypothesis; the kernel cannot prove
  this unconditionally (it's a scheduler-liveness discipline imposed
  by deployment configuration).
- **Disposition:** **RESOLVED** in AN5-E (v0.30.6) via the canonical
  RPi5 deployment specialisation. The general parameterised theorem is
  retained for future non-RPi5 platforms.
- **Resolution:** AN5-E added
  `SeLe4n/Kernel/Scheduler/Liveness/RPi5CanonicalConfig.lean` with:
  * `DeploymentSchedulingConfig` structure + decidable `wellFormed`
    predicate schema.
  * `rpi5CanonicalConfig` canonical RPi5 instance (54 MHz timer,
    10 000-tick CBS period, 256 priority bands, 16 domains,
    1000-tick time slice, 750 ‰ admission utilisation) +
    `rpi5CanonicalConfig_wellFormed` by `decide`.
  * `eventuallyExits_of_exit_index` bridge lemma +
    `CanonicalDeploymentProgress` deployment-obligation structure +
    `rpi5_canonicalConfig_eventuallyExits` main substantive closure
    theorem.
  * `wcrt_bound_rpi5` RPi5-specialised WCRT theorem that composes
    `bounded_scheduling_latency_exists` with the canonical-deployment
    closure.
  * `isRPi5CanonicalConfig` decidable canonical-check + soundness
    `isRPi5CanonicalConfig_iff` + runtime witness
    `rpi5CanonicalConfig_isCanonical`.
- **Acceptance criteria:** fulfilled — 13 surface anchors + 5 runtime
  witnesses in `tests/LivenessSuite.lean`; `docs/spec/SELE4N_SPEC.md`
  §8.14.1.1 documents the two-tier WCRT semantics; zero
  `sorry`/`axiom`/`native_decide` in new module.
- **Commit:** WS-AN AN5-E (branch `claude/review-scheduler-phase-2eYM8`).

### DEF-AK7-E.cascade — `ValidObjId` / `ValidThreadId` Full Rollout

- **Audit finding:** F-M03 (MEDIUM) / AK7-E. Baseline `ValidObjId` /
  `ValidThreadId` subtypes landed in v0.29.14 (WS-AL AL1b/AL8).
  ~240 additional handler call sites across Lifecycle / SchedContext
  / IpcBufferValidation / Scheduler layers still take raw `ObjId` /
  `ThreadId` instead of their `Valid*` refinements.
- **Disposition:** DEFER per plan §17 point 3.
- **Deferral reason:** Primary attack surfaces closed structurally
  via the AL1b / AL7 dispatch-boundary guards; the remaining
  migration is a readability pass that reduces the number of runtime
  `none` fallbacks in handler internals. Cascades through ~240
  preservation proofs — the effort-to-risk ratio favours batching
  into a post-1.0 hygiene pass.
- **Acceptance criteria:**
  - `scripts/ak7_cascade_baseline.sh` `SENTINEL_CHECK_DISPATCH`
    metric reaches the post-1.0 target floor.
  - Handler signatures uniformly require `ValidObjId` /
    `ValidThreadId` at all public entry points.

### DEF-AK7-F.cascade — `ObjKind` Migration + Typed-Helper Adoption

- **Audit finding:** F-M04 (MEDIUM) / AK7-F. Baseline `ObjectKind` +
  `KindedObjId` parallel-structure landed in v0.29.14 (AL2); further
  hygiene items tracked as AK7-F.reader.hygiene (~304 raw `match
  st.objects[id]?` sites remaining, partially migrated to ~600 in
  WS-AM AM7) and AK7-F.writer.hygiene (~50 `storeObject` sites
  remaining candidates for `storeObjectKindChecked` wrapper
  adoption).
- **Disposition:** DEFER per plan §17 point 2.
- **Deferral reason:** Cascade through ~354 call sites is a
  readability pass — defense-in-depth, not correctness-critical.
  The AM4 invariant-layer guarantee
  (`lifecycleObjectTypeLockstep` as 11th conjunct of
  `crossSubsystemInvariant`) makes the writer-side migration
  redundant at the invariant layer; the reader-side migration is
  purely cosmetic.
- **Acceptance criteria:**
  - `scripts/ak7_cascade_check_monotonic.sh` `RAW_MATCH_TCB` metric
    reaches the post-1.0 target floor.
  - `GETTCB_ADOPTION` / `GETSCHEDCTX_ADOPTION` / `STOREOBJECTCHECKED_
    ADOPTION` metrics reach the post-1.0 target ceiling.

---

## Cross-Reference Summary

| Deferred ID | Audit Finding | Severity | Disposition | Category |
|-------------|---------------|----------|-------------|----------|
| DEF-A-M04 | A-M04 | MEDIUM | **RESOLVED (v0.30.10 / AN9-A)** | A: hardware-binding |
| DEF-A-M06 | A-M06 | MEDIUM | **RESOLVED (v0.30.10 / AN9-B)** | A: hardware-binding |
| DEF-A-M08 | A-M08 | MEDIUM | **RESOLVED (v0.30.10 / AN9-C+H)** | A: hardware-binding |
| DEF-A-M09 | A-M09 | MEDIUM | **RESOLVED (v0.30.10 / AN9-C+H)** | A: hardware-binding |
| DEF-C-M04 | C-M04 | MEDIUM | **RESOLVED (v0.30.10 / AN9-D)** | A: hardware-binding |
| DEF-P-L9 | P-L9 | LOW | **RESOLVED (v0.30.8 / AN7-D.2; AN9-E xref)** | A: hardware-binding |
| DEF-R-HAL-L14 | R-HAL-L14 | LOW | **RESOLVED (v0.30.10 / AN9-F)** | A: hardware-binding |
| DEF-R-HAL-L17 | R-HAL-L17 | LOW | **RESOLVED (v0.30.10 / AN9-G)** | A: hardware-binding |
| DEF-R-HAL-L18 | R-HAL-L18 | LOW | **RESOLVED (v0.30.10 / AN9-H)** | A: hardware-binding |
| DEF-R-HAL-L19 | R-HAL-L19 | LOW | **RESOLVED (v0.30.10 / AN9-I)** | A: hardware-binding |
| DEF-R-HAL-L20 | R-HAL-L20 | LOW | **RESOLVED (v0.30.10 / AN9-J, off by default)** | A: hardware-binding |
| DEF-F-L9 | F-L9 | LOW | DEFER | B: proof-hygiene |
| DEF-AK2-K.4 | AK2-K.4 | — | **RESOLVED** in AN5-E (WS-AN v0.30.6) | B: proof-hygiene |
| DEF-AK7-E.cascade | F-M03 | MEDIUM | AL1b/AL8 baseline | B: proof-hygiene |
| DEF-AK7-F.cascade | F-M04 | MEDIUM | AL2/AL6 baseline | B: proof-hygiene |

Total tracked: **15 items** — **11 hardware-binding RESOLVED at AN9**
(v0.30.10), **2 proof-hygiene RESOLVED earlier**
(DEF-AK2-K.4 at AN5-E, DEF-P-L9 at AN7-D.2), **3 still tracked**
(DEF-F-L9 by-design, DEF-AK7-E.cascade and DEF-AK7-F.cascade
post-1.0 hygiene).

**WS-AN Phase AN9 hardware-binding closure: COMPLETE.**  Every
hardware-binding item from the original v0.29.0 deferred list and
every new item surfaced by AN1-C is closed at v0.30.10.  No
hardware-binding scope carries past v1.0.0.

---

## Closure Criteria

This tracking file is **closed** for WS-AK: every v0.29.0 audit
finding either has a FIX landing in AK1..AK9, a DOCUMENT disposition,
or an entry in this file. When a future workstream is opened to pick
up any of the deferred items, it should reference this file by ID,
update the corresponding row's disposition to RESOLVED, and record
the commit SHA that closes the item.
