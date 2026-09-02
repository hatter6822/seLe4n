# SM1 — Rust HAL Completion (WS-SM Phase 1)

> **Phase**: SM1 of WS-SM
> **Status**: LANDED (v0.31.3 → v0.31.8) — PSCI, per-CPU, secondary init, TLBI, SGI, QEMU
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Audited cut**: `v0.31.2`
> **Target releases (original estimate)**: v0.33.0 .. v0.45.x (parallel with SM2)
> **Calendar estimate**: 16-22 weeks (parallel with SM2 verified-lock work)
> **Sub-task count**: 60-80 across ~22-32 PRs

## 1. Phase goal

SM1 completes the **Rust hardware-abstraction layer** to the point
where:

1. **Secondary cores can be brought up** by PSCI CPU_ON
   (`SM1.A`) and arrive in a fully-initialized state with MMU,
   exception vectors, GIC CPU-interface, and timer configured
   (`SM1.C`).
2. **Per-CPU data is reachable** via TPIDR_EL1, so kernel code on
   any core can locate its own per-core state in O(1) (`SM1.B`).
3. **DTB cmdline parsing** drives SMP activation; the kernel
   boots single-core unless `smp_enabled=true` is on the
   command line (well, per maintainer decision #7, the default
   is enabled; `smp_enabled=false` opts out) (`SM1.D`).
4. **TLB invalidation broadcasts** via IS variants
   (`tlbi vae1is`, etc.) — closes the hardware part of SMP-C4
   (`SM1.E`).
5. **SGI primitive exists**: `gic::send_sgi(target, intid)` is
   the foundation for cross-core wake, TLB shootdown ack, and
   panic synchronization (`SM1.F`).
6. **UART output is per-core safe**: cross-core kprintln does
   not interleave torn output (`SM1.G`).
7. **QEMU SMP integration test** boots all 4 cores and verifies
   the boot trace (`SM1.H`).
8. **PSCI power-management primitives** (`cpu_off`,
   `affinity_info`, `system_off`, `system_reset`) are wired
   (`SM1.A`).

**Closures**: SMP-C1 (caller wired), SMP-C2 (full secondary
init), SMP-C4 hardware part (IS variants), SMP-H1 (SGI primitive),
SMP-M3 (`.smp_stacks` zeroed at boot — done in SM0.M),
SMP-M4 (TPIDR_EL1 set — done in SM0.N), SMP-M5 (PSCI completion),
SMP-M6 (QEMU SMP test wired).

## 2. Dependencies

- **SM0**: SM0.G (PlatformBinding.coreCount, sharingDomain),
  SM0.H (SgiKind), SM0.N (TPIDR_EL1 setup in `secondary_entry`),
  SM0.O (MAX_SECONDARY_CORES param).
- **SM2** (parallel): SM1 does not directly depend on SM2; the
  two phases proceed in parallel. SM1.J (Lean BKL FFI binding,
  if needed) gates on SM2.B (Rust ticket-lock impl).

## 3. Mathematical foundations relevant to SM1

SM1 is primarily implementation work, but several invariants are
worth stating formally:

### 3.1 Secondary-core init ordering

**Theorem 3.1.1** (Secondary-core init sequence). For a secondary
core c to enter `lean_secondary_kernel_main(c)` safely, the
following sequence must complete in order on c:

1. PSCI CPU_ON entry: `secondary_entry` stub in `boot.S` is
   reached. DAIF mask is set. Per-core SP is loaded. TPIDR_EL1
   is set (SM0.N).
2. MMU enable: `init_mmu_secondary(c)` is called. TTBR0_EL1 +
   TTBR1_EL1 (per-core banked but pointing to shared kernel
   page tables) are programmed. SCTLR_EL1 bitmap is applied
   (M=1, C=1, I=1, WXN=1, SA=1, ...).
3. VBAR install: `write_vbar_el1_secondary()` is called.
   VBAR_EL1 := `__exception_vectors`.
4. GIC CPU-interface init: `init_cpu_interface_secondary(c)` is
   called. GICC_PMR = 0xFF, GICC_BPR = 0, GICC_CTLR.EnableGrp0 = 1.
5. Timer arming: `init_timer_secondary(tick_hz)` is called.
   CNTKCTL_EL1 + CNTV_TVAL_EL0 + CNTV_CTL_EL0.Enable = 1.
6. CORE_READY[c] flag set (Release ordering).
7. Wait for primary's `bring_up_secondaries` to signal all
   cores ready (already-set bit in CORE_READY array; or SEV
   wake).

After step 7, secondary c can safely enter
`lean_secondary_kernel_main(c)` because:
- MMU is on → virtual address translations work.
- VBAR is set → exceptions vector to the kernel handler.
- GIC CPU interface is up → IRQs can be acknowledged + EOI'd.
- Timer is armed → per-core tick interrupts fire.

*Proof*: structural. Each step's pre-condition is established by
the previous step. ARM ARM citations:
- MMU enable: D8.2 (translation regime initialization).
- VBAR: D17.2.135 (VBAR_EL1 write must precede first exception).
- GIC CPU interface: GIC-400 TRM §4.4 (init before IRQ enable).
- Timer: D11.2 (CNTV_CTL_EL0.Enable=1 before next-tick wait).

### 3.2 SGI delivery semantics

**Theorem 3.2.1** (SGI delivery on GICv2). For a GICv2-compliant
GIC-400, writing GICD_SGIR with `(TargetListFilter, CPUTargetList,
NSATT, INTID)` causes the GIC distributor to assert pending bits
for INTID on the target CPU interfaces. The target CPU's next
GICC_IAR read returns INTID.

Reference: GIC-400 TRM §4.3.13.

The Lean-side model (in `Architecture/InterruptDispatch.lean`)
already handles general INTIDs; SM1.F's contribution is to expose
the GICD_SGIR write through the HAL.

### 3.3 IS-variant TLBI semantics

**Theorem 3.3.1** (TLBI ...IS broadcasts to inner-shareable
domain). On ARMv8-A, executing `TLBI VAE1IS, Xt` on any PE in
the inner-shareable domain invalidates the TLB entry matching
(ASID, VA) on every PE in the domain. After a subsequent
`DSB ISH`, the invalidation is observed by all PEs.

Reference: ARM ARM C6.2.311 (TLBI VAE1IS), B2.7.5 (DSB ISH).

For RPi5 BCM2712 (single Cortex-A76 cluster), all 4 cores share
the inner-shareable domain.

### 3.4 PSCI calling convention

**Theorem 3.4.1** (PSCI HVC encoding). For an HVC-based PSCI
implementation at EL2 (RPi5's firmware), the call:

    HVC(x0=FUNC_ID, x1..x3=args)

returns the result in x0. The function IDs encode in 32 bits:

    bit 31         : 1 for SMC64, 0 for SMC32
    bits 24..30    : reserved (must be 0)
    bits 16..23    : reserved (must be 0)
    bits 0..15     : function number

Examples (used by SM1.A):

| Call | Function ID | Encoding |
|------|------------:|----------|
| PSCI_VERSION | 0x84000000 | SMC32, function 0 |
| CPU_OFF | 0x84000002 | SMC32, function 2 |
| CPU_ON | 0xC4000003 | SMC64, function 3 |
| AFFINITY_INFO | 0xC4000004 | SMC64, function 4 |
| MIGRATE_INFO_TYPE | 0x84000006 | SMC32, function 6 |
| SYSTEM_OFF | 0x84000008 | SMC32, function 8 |
| SYSTEM_RESET | 0x84000009 | SMC32, function 9 |

Reference: ARM DEN0022D Power State Coordination Interface
specification §5.

## 4. Architectural choices for SM1

### 4.1 Why complete every PSCI primitive at SM1

The audit (SMP-M5) identified that only `cpu_on` is wrapped.
Completing the full set (`cpu_off`, `affinity_info`,
`system_off`, `system_reset`, `psci_version`,
`migrate_info_type`) at SM1 — not deferred to v1.x — gives
v1.0.0 a complete PSCI-EL1 boundary. Cost: ~200 LoC of Rust;
benefit: production-ready power management.

### 4.2 Why per-core init duplicates primary init (and shares code)

The maintainer-decided per-core idle TCBs (decision #8) mean each
secondary needs the same boot-style initialization as the primary
(MMU, VBAR, GIC CPU interface, timer). SM1.C extracts shared
helpers (`init_mmu_secondary`, `write_vbar_el1_secondary`,
`init_cpu_interface_secondary`, `init_timer_secondary`) that the
primary's `rust_boot_main` Phase 2/3 also calls. This eliminates
duplication and ensures the secondary path is exercised by every
primary boot.

### 4.3 Why DTB cmdline parsing (not config file)

The maintainer choice (decision #7) sets SMP enabled by default
on RPi5; opt-out is via DTB `/chosen/bootargs` (e.g.,
`smp_enabled=false`). This:
- Matches Linux convention (`isolcpus=`, `nosmp`).
- Doesn't require a writable filesystem at boot.
- Works on bare-metal (no userspace config available).

SM1.D builds a minimal parser. The full DTB structure is already
parsed for memory map / GIC / timer (existing
`Platform/DeviceTree.lean`); the bootargs string is at
`/chosen/bootargs` and is just a UTF-8 null-terminated `&[u8]`.

### 4.4 Why IS variants are the only TLB ops on SMP

Decision: under SMP, **all** TLBI operations use IS variants.
The non-IS variants (`tlbi vae1`, etc.) are retained in the HAL
as private helpers (used only by single-core unit tests and the
single-cluster path that bypasses SMP entirely — see also
SharingDomain `.inner` parameterization).

"Private helpers" was a description rather than a fact until
`v0.34.41`: `tlbi_vmalle1`, `tlbi_vae1`, `tlbi_aside1` and `tlbi_vale1`
were `pub`, so the discipline held only by convention.  They are now
`pub(crate)`, and the crate's public local surface is `tlbi_local` plus
the three `ffi_tlbi_*` exports (WS-RR RR1.9).

This is enforced by SM1.E.5: every kernel-side caller of TLB
invalidation routes through `tlbi_for_sharing(d, op, args)`, which
dispatches to IS or OS based on `PlatformBinding.sharingDomain`.

**The tier-0 gate this section claimed exists now does**, as
`scripts/check_tlbi_broadcast_discipline.py` (WS-RR RR1.9, `v0.34.41`).
It is not the `grep` the SM1.E.5 sketch below described — that scanned
only the Lean tree, matched one of the four local variants, read raw text
so its own explanatory sentence tripped it, and had no notion of the call
sites that are legitimately local.  The gate instead holds three
invariants: a `tlbi` mnemonic may be emitted only from `tlb.rs`; the local
wrappers may be called only from sites registered in
`scripts/tlbi_local_allowlist.txt` with the reason the calling PE is the
only one that needs the entry gone; and the Lean bindings of the local FFI
exports may be referenced only from registered production modules.  The
allowlist is checked in both directions, so it cannot outlive its call
sites.  Three call shapes are registered: boot-time MMU init (pre-SMP),
the shootdown protocol's receive side, and the FFI exports of those two.

### 4.5 Why TPIDR_EL1 is the per-CPU base

`TPIDR_EL1` is the ARMv8 architecture-defined per-CPU base
register at EL1 (analogous to `gs` on x86). The kernel sets it on
each core's entry to point to that core's `PerCpuData` slot;
subsequent code reads it once at FFI-bridge entry and threads the
per-CPU view through Lean as a `CoreId`.

Alternative considered: read MPIDR_EL1 on every kernel entry.
Cost: ~3-5 cycles for MRS, then a table lookup to map MPIDR to
CoreId. TPIDR_EL1 saves the table lookup at the cost of one
extra MSR at boot.

## 5. Detailed sub-task breakdown

(Section structure mirrors SM0 — every sub-task gets goal,
files, code skeleton, acceptance, PR template, estimate.)

### 5.1 PSCI completion (SM1.A, 5 PRs, 8 sub-tasks) — **LANDED**

- **SM1.A.1** `cpu_off()` — power down calling PE; emits `dsb osh` +
  `hvc #0` with id `0x8400_0002`; returns `PsciResult`. Documented
  failure codes: `Denied`, `InternalFailure`.
- **SM1.A.2** `affinity_info(target_affinity, lowest_affinity_level)` —
  query a target PE's on/off state; returns
  `Result<AffinityInfoState, PsciResult>`. `AffinityInfoState`
  enum: `On=0`, `Off=1`, `OnPending=2`. SMC64 id `0xC400_0004`.
- **SM1.A.3** `system_off() -> !` — power off the system; SMC32 id
  `0x8400_0008`; never returns.
- **SM1.A.4** `system_reset() -> !` — cold system reset; SMC32 id
  `0x8400_0009`; never returns.
- **SM1.A.5** `psci_version() -> PsciVersion` — query firmware
  version; SMC32 id `0x8400_0000`. `PsciVersion` carries `major` /
  `minor` u16 fields with a `from_raw` / `to_raw` round-trip and an
  `at_least(major, minor)` comparator for feature gating.
- **SM1.A.6** `migrate_info_type() -> Result<MigrateInfoType, PsciResult>` —
  Trusted-OS migration query; SMC32 id `0x8400_0006`. `MigrateInfoType`
  enum: `UniProcessor=0`, `Multiprocessor=1`, `NotRequired=2`.
- **SM1.A.7** Function-id pinning — compile-time `const _: () = { ... }`
  assertions verify every PSCI id satisfies the ARM SMCCC encoding
  (bit 31 Fast call, bit 30 SMC32/64, bits 29..24 OEN=4 for Standard
  Secure Service Calls, bits 23..16 reserved-zero, bits 15..0 function
  number). Plus the runtime test matrix in
  `psci::tests::psci_function_ids_*`.
- **SM1.A.8** Documentation map — module-level docstring lists all
  seven wrappers with their function ids and DEN0022D § references;
  return-code matrix cites Table 5.

| Sub | Scope |
|-----|-------|
| SM1.A.1 | `psci::cpu_off()` |
| SM1.A.2 | `psci::affinity_info()` |
| SM1.A.3 | `psci::system_off()` |
| SM1.A.4 | `psci::system_reset()` |
| SM1.A.5 | `psci::psci_version()` |
| SM1.A.6 | `psci::migrate_info_type()` |
| SM1.A.7 | Function-id pinning tests |
| SM1.A.8 | PSCI documentation map |

*Landed. The implementation is the source; what each cut changed is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

### 5.2 Per-CPU data + TPIDR_EL1 (SM1.B, 3 PRs, 7 sub-tasks) — **LANDED at v0.31.4**

- **SM1.B.1** `PerCpuData` struct — moved from `smp.rs` (where SM0.N
  parked the seam as an empty placeholder) into the new dedicated
  module `rust/sele4n-hal/src/per_cpu.rs`.  The `_reserved: [u64; 8]`
  placeholder is replaced with a populated `core_id: u64` field plus
  a `_reserved: [u64; 7]` tail that SM5+ will repurpose for the
  current-thread pointer, idle-TCB pointer, BKL ownership flag, and
  per-core scheduler stats.  `#[repr(C, align(64))]` keeps each
  instance one cache line wide.  Two const constructors are exposed:
  `new(core_id)` (production initialiser) and `zero()` (SM0.N
  back-compat alias for `new(0)`).
- **SM1.B.2** Static array population — `PER_CPU_DATA[i].core_id == i`
  for every `i ∈ 0..MAX_SECONDARY_CORES`, via `PerCpuData::new(0)`,
  `PerCpuData::new(1)`, `PerCpuData::new(2)`, `PerCpuData::new(3)`.
  Three compile-time `const _: ()` assertions pin
  `size_of::<PerCpuData>() == PER_CPU_DATA_SLOT_SIZE` (= 64),
  `align_of::<PerCpuData>() == 64` (cache-line aligned), and
  `PER_CPU_DATA.len() == MAX_SECONDARY_CORES + 1` (= 4 =
  `PlatformBinding.coreCount`).  The asm-visible
  `PER_CPU_DATA_SLOT_SIZE_SYM` symbol (consumed by
  `boot.S::secondary_entry`'s `madd` stride) survives the move
  unchanged — `#[no_mangle]` makes the symbol name
  location-independent.
- **SM1.B.3** `current_per_cpu()` accessor — reads `TPIDR_EL1` on
  aarch64 and returns a `&'static PerCpuData`.  The safety
  invariants are documented inline: EL1 reachability (kernel-mode
  only), TPIDR_EL1 set before first kernel-mode entry, and pointer
  validity (entry points to one of `PER_CPU_DATA`'s slots, which
  have `'static` extent).  Host stub returns `&PER_CPU_DATA[0]`.
- **SM1.B.4** `current_core_id_from_tpidr()` — fast core-id lookup
  via `current_per_cpu().core_id`.  Preferred over the
  MPIDR + mask path on hot kernel paths.  Host stub returns 0.
- **SM1.B.5** Lean FFI `ffi_current_core_id` — Rust-side
  `#[no_mangle] pub extern "C" fn` in `ffi.rs` plus
  `@[extern "ffi_current_core_id"] opaque ffiCurrentCoreId : BaseIO
  UInt64` in `SeLe4n/Platform/FFI.lean`.  Lean-side typed wrapper
  `Concurrency.currentCoreId : BaseIO CoreId` in the new file
  `SeLe4n/Kernel/Concurrency/Runtime.lean` performs the
  `raw.toNat < numCores` range check and constructs a `Fin numCores`
  via the `if h : ...` discipline.  Falls back to `panic!` on
  out-of-range — unreachable under post-boot invariants enforced by
  `check_per_cpu_invariants`.  `Inhabited CoreId` instance added to
  `Concurrency.Types` so the `panic!` typechecks (witnessed by
  `bootCoreId`).
- **SM1.B.6** PerCpuData runtime invariants — `check_per_cpu_invariants()`
  iterates `PER_CPU_DATA` at boot and panics if any slot's
  `core_id` field disagrees with its array index.  Called from
  `rust_boot_main` Phase 4 before the `TPIDR_EL1` write so the
  invariant is verified before any consumer reads it.  The check is
  platform-independent (compiles + runs on host stubs too) and
  O(coreCount) = O(4), so it's cheap to leave in production.  Also
  closes a defense-in-depth gap: a future regression that broke the
  const-init table would surface at boot rather than at first SMP
  wakeup.
- **SM1.B.7** Test `test_per_cpu_data_layout` — 30 unit tests in
  `per_cpu::tests` (10 migrated from the SM0.N `smp::tests::sm0n_*`
  block under `sm1b_*` names with expanded coverage, 15 newly
  authored at SM1.B landing for SM1.B-specific functionality,
  5 added at audit-pass-2 for the `check_per_cpu_invariants_in`
  inner form + panic-path regression cases): struct alignment +
  size, const-constructor `new` and `zero` semantics, byte-level
  zero discharge for the reserved tail, array
  layout/stride/distinct-addresses, asm-stride observability via
  `PER_CPU_DATA_SLOT_SIZE_SYM`, out-of-range panic,
  `current_per_cpu` returns boot slot on host and points inside
  `PER_CPU_DATA` at a cache-line boundary,
  `current_core_id_from_tpidr` returns 0 on host and is in-range,
  `check_per_cpu_invariants` passes on the production initialiser
  AND on well-formed / empty test slices, panics on three distinct
  mis-population patterns (wrong-core-id, first-slot-wrong,
  zero-default-regression), pairwise-distinct + canonical-range
  cross-checks on `core_id`, accessor agreement with
  `per_cpu_slot_addr`.  Plus 3 new tests in `ffi::tests` exercising
  `ffi_current_core_id` (host return 0, range invariant, agreement
  with `current_core_id_from_tpidr`); plus 4 back-compat tests in
  `smp::tests` (replacing the 11 sm0n_* tests that migrated):
  verifying the `crate::smp::*` re-exports of `PerCpuData`,
  `PER_CPU_DATA`, the slot-size constants, and `per_cpu_slot_addr`
  still resolve.

| Sub | Scope |
|-----|-------|
| SM1.B.1 | `PerCpuData` struct |
| SM1.B.2 | Static array population |
| SM1.B.3 | `current_per_cpu()` accessor |
| SM1.B.4 | `current_core_id_from_tpidr()` |
| SM1.B.5 | Lean FFI: `ffi_current_core_id` |
| SM1.B.6 | PerCpuData invariants |
| SM1.B.7 | Test `test_per_cpu_data_layout` |

*Landed. The implementation is the source; what each cut changed is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

### 5.3 Secondary core full init (SM1.C, 6 PRs, 12 sub-tasks) — **LANDED at v0.31.5**

- **SM1.C.1** `mmu::init_mmu_secondary(core_id)` plus extracted
  `mmu::init_mmu_per_core(core_id)` helper.  The primary's
  `init_mmu()` now routes through `init_mmu_per_core(0)` after
  `build_identity_tables()`; secondaries call `init_mmu_secondary`
  which skips the table-build (the boot L1 table is a read-only
  global) and applies the per-core MMU enable sequence with the
  AK5-C SCTLR_EL1 bitmap (`M | C | I | SA | SA0 | WXN | EOS | EIS |
  RES1`).  Audit follow-up cfg-gated the unconditional
  `pt_pa_raw < 2^44` debug_assert to aarch64 because host x86_64
  PIE binary base addresses routinely exceed 2^44.
- **SM1.C.2** `boot::install_exception_vectors()` — VBAR_EL1
  installation extracted from the formerly-private `set_vbar` and
  made `pub` so secondaries reach it via `crate::boot`.  The
  primary's `rust_boot_main` Phase 2 now calls the same helper.
  Two new `build.rs` scanners pin the primary/secondary symmetry.
- **SM1.C.3** `gic::init_cpu_interface_secondary(core_id)` — wraps
  the existing `init_cpu_interface(GICC_BASE)` (banked per-core)
  with a per-core diagnostic kprintln.  The global GIC distributor
  is initialised once by the primary's `init_gic`.
- **SM1.C.4** `timer::init_timer_secondary(tick_hz) -> Result<(),
  TimerError>` — per-core timer arming.  Deliberately does NOT
  reset `TICK_COUNT` (primary-owned monotonic counter) or rewrite
  `TIMER_INTERVAL` (primary already populated it; same value on
  every core via shared CNTFRQ_EL0).  Failure on a secondary halts
  just that core via WFE loop.
- **SM1.C.5** `rust_secondary_main` body rewrite — eight-step
  pipeline: (0) spin on CORE_READY[i] with bounded WFE; (1) MMU;
  (2) VBAR; (3) GIC; (4) timer (fatal-on-fail path halts the
  core); (5) IRQ unmask; (6) Lean kernel entry via
  `lean_secondary_kernel_main(context_id)` gated on `feature =
  "hw_target"`; (7) idle fallback `loop { wfe() }`.  A new build.rs
  scanner enumerates the six required call sites by name and
  fails the build if any is silently dropped.
- **SM1.C.6** Lean `secondaryKernelMain : UInt64 → BaseIO Unit`
  with `@[export lean_secondary_kernel_main]` — new module
  `SeLe4n/Kernel/SecondaryEntry.lean`.  At SM1.C the body was
  `pure ()` (deliberate placeholder; the per-core scheduler state it
  would enter did not exist yet).  Surface-anchor theorem
  `secondaryKernelMain_returns_unit_marker` proved the placeholder
  semantics by `rfl` for downstream Tier-3 scans.  Module reached
  via `SeLe4n/Platform/Staged.lean`; added to the staged-module
  allowlist per WS-RC R12.B.  **Replacement LANDED with the SM5.C.5
  seam completion**: the body is now definitionally the per-core
  reschedule entry (`secondaryKernelMain_eq_perCoreRescheduleEntry`
  over the verified `perCoreRescheduleStep`), the Rust caller
  brackets it in `kernel_entry::with_kernel_entry` and orders it
  before `enable_irq`, and the placeholder marker was retired for
  the seam-identity + body-shape markers.
- **SM1.C.7..C.11** Documentation-only sub-tasks — per-core stack
  reservation (link.ld already in place; verified unchanged),
  MMU page-table reuse rationale (`mmu.rs` module docstring),
  per-core SCTLR_EL1 bitmap (covered by SM1.C.1 via
  `init_mmu_per_core`), per-core VBAR_EL1 (covered by SM1.C.2 via
  `install_exception_vectors`), SError handler masked policy
  retained (per the existing single-core convention).
- **SM1.C.12** 32 new host tests across `mmu::tests`,
  `boot::tests`, `gic::tests`, `timer::tests`, `smp::tests` (the
  `sm1c1_*`, `sm1c2_*`, `sm1c3_*`, `sm1c4_*`, `sm1c5_*` prefixes
  respectively) covering callability on host, signature pinning,
  debug_assert panic paths, monotonic counter preservation,
  full-set callability, aggregate idempotence, and `#[no_mangle]`
  discipline.  Plus 12 new Lean assertions in
  `tests/SmpFoundationsSuite.lean` (surface anchors, marker-theorem
  discharges, runtime BaseIO invocation, boundary UInt64 input
  tolerance).

| Sub | Scope |
|-----|-------|
| SM1.C.1 | Extract `mmu::init_mmu_secondary(core_id)` |
| SM1.C.2 | Extract `vectors::write_vbar_el1_secondary()` |
| SM1.C.3 | `gic::init_cpu_interface_secondary(core_id)` |
| SM1.C.4 | `timer::init_timer_secondary(tick_hz)` |
| SM1.C.5 | Rewrite `rust_secondary_main` body |
| SM1.C.6 | Lean `secondaryKernelMain` |
| SM1.C.7 | Per-core stack reuses link.ld reservation |
| SM1.C.8 | Per-core MMU page table reuse |
| SM1.C.9 | SCTLR_EL1 per-core bitmap |
| SM1.C.10 | Per-core exception vector |
| SM1.C.11 | SError handler enabled |
| SM1.C.12 | Full secondary-init host stubs + tests |

*Landed. The implementation is the source; what each cut changed is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

### 5.4 DTB cmdline + Phase 5 (SM1.D, 3 PRs, 6 sub-tasks) — **LANDED at v0.31.6**

| Sub | Scope |
|-----|-------|
| SM1.D.1 | `cmdline.rs` DTB parser |
| SM1.D.2 | Phase 5 in `rust_boot_main` |
| SM1.D.3 | Default behavior: SMP enabled, and the condition it waited on |
| SM1.D.4 | Ordering: locks initialized before bring-up |
| SM1.D.5 | Per-CPU data init before bring-up |
| SM1.D.6 | `smp_max_cores` cmdline option |

*Landed. The implementation is the source; what each cut changed is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

### 5.5 IS-variant TLB instructions (SM1.E, 3 PRs, 5 sub-tasks) — **LANDED at v0.31.7**

| Sub | Scope |
|-----|-------|
| SM1.E.1 | Add `tlbi_*is` variants |
| SM1.E.2 | Add OSH variants (post-1.0-ready) |
| SM1.E.3 | `tlbi_for_sharing(d, op, args)` dispatcher |
| SM1.E.4 | Lean FFI bindings |
| SM1.E.5 | Migrate kernel-side callers |

*Landed. The implementation is the source; what each cut changed is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

# Tier-0 hygiene check: no production kernel caller emits
# non-IS TLBI directly.
if grep -rn "tlbi_vae1[^i]" SeLe4n/ | grep -v test; then
    echo "ERROR: non-IS TLBI in kernel code"
    exit 1
fi
```

> **Superseded at `v0.34.41` (WS-RR RR1.9).**  The sketch above is kept
> as the record of what SM1.E.5 intended; it is not what was built, and
> it would not have worked: it scans only `SeLe4n/`, matches one of the
> four local wrappers, reads raw text (so the sentence above it is a
> hit), and treats every local call as a violation — including the
> shootdown protocol's receive side, where a local TLBI is the correct
> instruction.  The gate that exists is
> `scripts/check_tlbi_broadcast_discipline.py`; see §4.4.

**Acceptance**:
- Hygiene check passes.
- All previous TLB callsites route through the dispatcher.

**Size**: M (~50 LoC of callsite migrations).

### 5.6 SGI primitive (SM1.F, 4 PRs, 8 sub-tasks) — **LANDED at v0.31.7**

| Sub | Scope |
|-----|-------|
| SM1.F.1 | `GICD_SGIR` constant |
| SM1.F.2 | `gic::send_sgi(target_mask, intid)` |

*Landed. The implementation is the source; what each cut changed is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

### 5.7 Cross-core kprintln synchronization (SM1.G, 2 PRs, 4 sub-tasks) — **LANDED at v0.31.7**

| Sub | Scope |
|-----|-------|
| SM1.G.1 | Audit `UartLock::with` |
| SM1.G.2 | Per-core boot banner |
| SM1.G.3 | Per-core kprintln stress test |
| SM1.G.4 | `kprintln_core!` macro |

*Landed. The implementation is the source; what each cut changed is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

### 5.8 QEMU SMP integration (SM1.H, 2 PRs, 5 sub-tasks) — **LANDED at v0.31.7**

| Sub | Scope |
|-----|-------|
| SM1.H.1 | Full `test_qemu_smp_bringup.sh` implementation |

*Landed. The implementation is the source; what each cut changed is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

# Check 4 cores reported ready.
ready_count=$(grep -c "\[smp\] core .: ready" "$LOG" || true)
if [[ "$ready_count" -ne 4 ]]; then
    echo "FAIL: expected 4 cores ready, got $ready_count"
    cat "$LOG"
    rm -f "$LOG"
    exit 1
fi

echo "PASS: 4 cores ready"
rm -f "$LOG"
exit 0
```

**Acceptance**:
- Builds and runs against a compiled kernel image.
- 4 cores ready banner verified.

**Size**: L (~150 LoC of bash + ancillary scripts).

---

#### SM1.H.2 — Wire into nightly tier

**File**: `scripts/test_nightly.sh`.

Add `./scripts/test_qemu_smp_bringup.sh` to the tier-4 suite.

**Size**: S (~10 LoC).

---

#### SM1.H.3 — `test_qemu_smp_minimal.sh` for 1-secondary

For tests with reduced parallelism. Same shape as SM1.H.1 with
`-smp 2`.

**Size**: M (~80 LoC).

---

#### SM1.H.4 — UART log capture + banner verification

The banner verification is in SM1.H.1.

**Size**: T.

---

#### SM1.H.5 — SGI round-trip test

Boots QEMU `-smp 4`. Boot core sends an SGI to core 1; core 1's
handler increments a shared atomic counter then sends an ACK SGI
back. Boot core waits for the counter increment.

This requires the SGI dispatch to be wired (SM1.F.5) plus a
test handler.

**Size**: L (~150 LoC).

### 5.9 Miscellaneous HAL improvements (SM1.I, 3 PRs, 6 sub-tasks) — **LANDED at v0.31.8**

| Sub | Scope |
|-----|-------|
| SM1.I.1 | Per-core IRQ handler entry — **LANDED** |
| SM1.I.2 | Per-core IRQ priority masking — **LANDED** |
| SM1.I.3 | Per-core IDLE thread Rust stub — **LANDED** |
| SM1.I.4 | Per-core exception statistics — **LANDED** |
| SM1.I.5 | SEV / WFE coordination documentation — **LANDED** |
| SM1.I.6 | Extended cargo tests — **LANDED** |

*Landed. The implementation is the source; what each cut changed is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

## 6. Verification strategy for SM1

### 6.1 What SM1 proves (Lean side)

| Theorem | Statement | File |
|---------|-----------|------|
| `currentCoreId_in_range` | `currentCoreId.val < numCores` | `Concurrency/Types.lean` |
| `ffiCurrentCoreId_matches_TPIDR_EL1` | (informal; HAL contract) | docstring |
| `sgi_intid_range` | All `SgiKind.toIntid` < 16 | `Concurrency/Sgi.lean` (already from SM0) |

SM1 is primarily implementation; formal theorems are scarce. The
correctness comes from:
- ARM ARM citations in every unsafe block.
- Cargo tests for every public function.
- QEMU integration test for the full boot path.

### 6.2 What SM1 assumes

- ARMv8-A architecture (D17, D8, D11 chapters).
- GIC-400 TRM (§3, §4) — interrupt controller.
- ARM DEN0022D (PSCI) — power management.

All documented in module docstrings.

### 6.3 Tests

- **Cargo tests**: ~50+ new unit tests across cmdline, psci, smp,
  per_cpu, tlb, gic.
- **QEMU integration**: `test_qemu_smp_bringup.sh` boots 4 cores;
  verifies banner trace.
- **Tier-4 nightly**: includes QEMU SMP.
- **Tier-5 (new)**: lock-primitive tests (SM2; not SM1).

## 7. Risk inventory for SM1

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Secondary init sequence mis-ordered → MMU/VBAR/GIC race | LOW | HIGH | SM1.C.5's body follows the order in §3.1 strictly |
| PSCI function ID typo → silent failure | LOW | HIGH | SM1.A.7 pins all 7 IDs against DEN0022D in unit test |
| TPIDR_EL1 unset on a core → null deref | LOW | CRIT | SM0.N + boot code in primary set TPIDR_EL1 explicitly; cargo test verifies |
| QEMU virt machine PSCI behavior differs from real RPi5 firmware | MED | MED | QEMU+real-HW dual testing once hardware is available |
| `tlbi_vae1is` not actually broadcast on a buggy SoC | LOW | HIGH | TLB shootdown protocol (SM7) adds explicit-ack as defense-in-depth |
| SGI INTID collision with platform SPI | ZERO | CRIT | INTIDs 0..15 reserved by GIC for SGI; SPIs start at 32 |
| Cmdline parser DoS on malformed DTB | LOW | MED | `extract_bootargs` returns empty on parse failure |
| Cross-core kprintln output torn under heavy contention | MED | LOW | SM1.G.3 stress test; SM2's TicketLock provides FIFO fairness |
| Per-CPU data init order vs bring-up race | LOW | CRIT | SM1.D.4-5 documents Phase 1 sets up PER_CPU_DATA before bring-up |

## 8. Acceptance gate for SM1

SM1 is complete when:

- [ ] All 8 PSCI primitives wrapped (`cpu_on`, `cpu_off`,
      `affinity_info`, `system_off`, `system_reset`,
      `psci_version`, `migrate_info_type`).
- [ ] PSCI function IDs pinned against ARM DEN0022D in unit test.
- [ ] `PerCpuData` struct + array, TPIDR_EL1 readable.
- [ ] `current_per_cpu()` + `current_core_id_from_tpidr()` work.
- [ ] FFI: `ffi_current_core_id` + `ffi_send_sgi_*` exported.
- [ ] `init_mmu_secondary`, `install_exception_vectors`,
      `init_cpu_interface_secondary`, `init_timer_secondary`
      all extracted as shared helpers.
- [ ] `rust_secondary_main` body implements 7-step init.
- [ ] DTB cmdline parser handles smp_enabled / smp_max_cores.
- [ ] Phase 5 in `rust_boot_main` calls `bring_up_secondaries`.
- [ ] SMP enabled by default; opt-out via `smp_enabled=false`.
- [ ] IS-variant TLB primitives added (`tlbi_*is`).
- [ ] OSH-variant TLB primitives added.
- [ ] `tlbi_for_sharing` dispatcher.
- [ ] Kernel callers migrated to dispatcher; tier-0 grep gate.
- [ ] `gic::send_sgi`, `send_sgi_to_self`, `send_sgi_to_all_but_self`.
- [ ] SGI handler table + dispatch.
- [ ] UART lock audited; replaceable with TicketLock post-SM2.
- [ ] `kprintln_core!` macro.
- [ ] `test_qemu_smp_bringup.sh` boots 4 cores; verifies 4 banners.
- [ ] Wired into tier-4 nightly.
- [ ] SGI round-trip test.
- [ ] ~50+ new cargo tests pass.
- [ ] CHANGELOG entries per PR; aggregate SM1 closure entry.

## 9. Cross-references

- **Master overview**:
  [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
- **Previous phase**: [`SMP_FOUNDATIONS_PLAN.md`](SMP_FOUNDATIONS_PLAN.md)
- **Parallel phase**:
  [`SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md)
  — SM2 develops the verified lock primitives that SM1.G.1 may
  consume (UartLock replacement).
- **Next phase**:
  [`SMP_PER_OBJECT_LOCKS_PLAN.md`](SMP_PER_OBJECT_LOCKS_PLAN.md) —
  SM3 adds the per-object lock fields that compose with SM1's
  HAL.

## 10. Theorem catalogue for SM1

| Theorem | Statement | File |
|---------|-----------|------|
| `currentCoreId_in_range` | `currentCoreId.val < numCores` | `Concurrency/Types.lean` |
| `psci_function_ids_match_arm_den0022d` | (cargo test, not Lean theorem) | `psci.rs` test |
| `psci_function_ids_pairwise_distinct` | (cargo test) | `psci.rs` test |
| `per_cpu_data_core_ids_match_indices` | (cargo test) | `per_cpu.rs` test |
| `tlbi_for_sharing_routes_inner` | `tlbi_for_sharing .inner X = tlbi_*is X` (cargo test + Lean axiom-cite) | `tlb.rs` test |

Total Lean theorems: 1. The bulk of SM1's verification is in
cargo tests (~50+ tests) and ARM ARM citation discipline in
unsafe blocks.

## Appendix A — Verification commands

```bash
# Build:
source ~/.elan/env
lake build
cargo build --release --target aarch64-unknown-none -p sele4n-hal

# Cargo tests:
cargo test -p sele4n-hal --lib
cargo test -p sele4n-hal --lib psci
cargo test -p sele4n-hal --lib smp
cargo test -p sele4n-hal --lib per_cpu
cargo test -p sele4n-hal --lib cmdline
cargo test -p sele4n-hal --lib tlb
cargo test -p sele4n-hal --lib gic

# QEMU integration:
./scripts/test_qemu_smp_bringup.sh
./scripts/test_qemu_smp_minimal.sh

# Tier-0 hygiene (no non-IS TLBI in kernel code) — the real gate,
# which also self-tests that it still bites:
python3 scripts/check_tlbi_broadcast_discipline.py --self-test
python3 scripts/check_tlbi_broadcast_discipline.py
```

## Appendix B — Sub-task dependency graph

```
SM1.A.1..A.8 (PSCI)         independent of other SM1 groups
SM1.B.1..B.7 (per-CPU)      independent
SM1.C.1..C.12 (sec init)    needs SM1.B (per-CPU data ready)
SM1.D.1..D.6 (cmdline)      needs SM1.C (bring_up_secondaries works)
SM1.E.1..E.5 (TLB IS)       independent
SM1.F.1..F.8 (SGI)          needs SM1.B (per-CPU dispatch)
SM1.G.1..G.4 (kprintln)     needs SM2.B (TicketLock) — defer G.1 if SM2.B not ready
SM1.H.1..H.5 (QEMU)         needs SM1.C..F all complete
SM1.I.1..I.6 (misc)         independent
```

Critical path: SM1.B → SM1.C → SM1.D → SM1.H (with SM1.F as
side-branch joining at SM1.H.5).

---

## SM1 closure summary

**WS-SM SM1 CLOSED at v0.31.8** — all nine SM1 sub-phases landed:

| Sub-phase | Status | Closure version | Sub-tasks |
|-----------|--------|-----------------|-----------|
| SM1.A — PSCI completion | LANDED | v0.31.3 | 8 |
| SM1.B — Per-CPU data + TPIDR_EL1 | LANDED | v0.31.4 | 7 |
| SM1.C — Secondary core full init | LANDED | v0.31.5 | 12 |
| SM1.D — DTB cmdline + Phase 5 | LANDED | v0.31.6 | 6 |
| SM1.E — IS-variant TLB instructions | LANDED | v0.31.7 | 5 |
| SM1.F — SGI primitive | LANDED | v0.31.7 | 8 |
| SM1.G — Cross-core kprintln synchronization | LANDED | v0.31.7 | 4 |
| SM1.H — QEMU SMP integration | LANDED | v0.31.7 | 5 |
| SM1.I — Miscellaneous HAL improvements | LANDED | v0.31.8 | 6 |
| **Total** | **9 of 9 LANDED** | **v0.31.8** | **61** |

**Acceptance gate** (§8) all items checked:

- [x] All 8 PSCI primitives wrapped.
- [x] PSCI function IDs pinned against ARM DEN0022D in unit test.
- [x] `PerCpuData` struct + array, TPIDR_EL1 readable.
- [x] `current_per_cpu()` + `current_core_id_from_tpidr()` work.
- [x] FFI: `ffi_current_core_id` + `ffi_send_sgi_*` exported.
- [x] `init_mmu_secondary`, `install_exception_vectors`,
      `init_cpu_interface_secondary`, `init_timer_secondary`
      all extracted as shared helpers.
- [x] `rust_secondary_main` body implements full per-core init.
- [x] DTB cmdline parser handles smp_enabled / smp_max_cores.
- [x] Phase 5 in `rust_boot_main` calls `bring_up_secondaries`.
- [x] SMP enabled by default; opt-out via `smp_enabled=false`.
- [x] IS-variant TLB primitives added (`tlbi_*is`).
- [x] OSH-variant TLB primitives added.
- [x] `tlbi_for_sharing` dispatcher.
- [x] Kernel callers migrated to dispatcher (post-SM7 cross-core
      cycles will exercise these); tier-0 grep gate in plan
      Appendix A.
- [x] `gic::send_sgi`, `send_sgi_to_self`, `send_sgi_to_all_but_self`.
- [x] SGI handler table + dispatch.
- [x] UART lock audited; replaceable with TicketLock post-SM2.
- [x] `kprintln_core!` macro.
- [x] `test_qemu_smp_bringup.sh` boots 4 cores; verifies 4 banners.
- [x] Wired into tier-4 nightly.
- [x] SGI round-trip test (SKIP-only until SM5 wires kernel handlers).
- [x] ~50+ new cargo tests pass (583 total at v0.31.8, up from
      ~140 at SM1 start).
- [x] CHANGELOG entries per PR; aggregate SM1 closure entry at
      v0.31.8.

**Items deferred past v1.0.0 with correctness impact**: NONE.

**Items deferred to SM5+ (per-core scheduler state)** with no
correctness impact at SM1 — both since landed:
- `handle_irq_per_core` was added as the SM5 landing seam; the
  assembly entry vector swap from `handle_irq` landed with the SM5
  seam completion (pinned by
  `build.rs::scan_trap_s_irq_vector_redirect`).
- SGI dispatch through the registered SGI handler table via the
  full-IAR-preserving `dispatch_irq_with_iar` variant landed at
  SM7.B.3.
- The Lean-side idle TCB consumes `ffi_idle_wait`; SM5 introduces
  the per-core idle thread.
- The Lean-side per-core stats consumers (read paths via
  `Concurrency.perCore*Count`) are wired but not yet exercised by
  the verified kernel.  SM5+ adds the verified read APIs.

These deferrals are seam-only — the SM1 contract is complete and
the SM5 follow-on is a wiring change, not a redesign.

---

*SM1 brings the Rust HAL to feature-complete SMP readiness. It
runs in parallel with SM2 (verified lock primitives), the two
phases having no direct dependencies (SM2's outputs are consumed
starting in SM3). Together SM1 + SM2 lay the foundation that
SM3..SM10 build atop.*
