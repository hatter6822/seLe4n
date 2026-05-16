# SM1 — Rust HAL Completion (WS-SM Phase 1)

> **Phase**: SM1 of WS-SM
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Audited cut**: `v0.31.2`
> **Target releases**: v0.33.0 .. v0.45.x (parallel with SM2)
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

This is enforced by SM1.E.5: every kernel-side caller of TLB
invalidation routes through `tlbi_for_sharing(d, op, args)`, which
dispatches to IS or OS based on `PlatformBinding.sharingDomain`.
A `grep` test in tier-0 ensures no production caller emits
`tlbi vae1` (non-IS).

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

**Status**: COMPLETE on branch `claude/implement-psci-completion-TUW1u`.
All eight sub-tasks landed in one cut. The PSCI surface now wraps every
ARM DEN0022D §5 call the kernel needs:

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

**Test coverage**: 45 unit tests (43 active + 2 `#[ignore]`'d for
`system_off` / `system_reset` since they return `!` and would hang the
test runner). Two audit passes added: 8 decoder-failure-path tests
(`decode_affinity_info_result_*` and `decode_migrate_info_type_result_*`)
covering the i32 → Result failure branches without an HVC trap, plus 5
edge-case / const-context tests covering boundary inputs
(`from_raw(0)`, `from_raw(u32::MAX)`, round-trip at u16::MAX) and
forcing every `const fn` decoder into a compile-time `const` binding.
All function ids pinned in three layers: compile-time `const _: ()`
assertions, runtime `psci_function_ids_match_arm_den0022d`, runtime
pairwise-distinctness. The `affinity_info` and `migrate_info_type`
decoders refuse vendor-undocumented values by returning `None`
(mapped by the caller to `PsciResult::Unknown`).

**Audit-pass-1 refinements** applied post-initial-landing:

- **HIGH-severity soundness fix**: `system_off` / `system_reset` no
  longer use `options(..., noreturn)` on their HVC asm blocks (which
  would be UB if firmware returns `NOT_SUPPORTED`).  Replaced with
  `clobber_abi("C")` + an explicit `loop { spin_loop() }` post-asm
  so `-> !` is honoured on every path.
- **Documentation accuracy**: DEN0022D sub-section citations
  realigned to revision D numbering throughout the module
  (CPU_OFF §5.1.3, CPU_ON §5.1.4, AFFINITY_INFO §5.1.5,
  MIGRATE_INFO_TYPE §5.1.7, SYSTEM_OFF §5.1.9, SYSTEM_RESET §5.1.10).
- **Testability**: extracted pure decoders `decode_affinity_info_result`
  and `decode_migrate_info_type_result` so the failure paths
  (`ret < 0` and `ret > 2`) are unit-testable without an HVC trap.
- **API**: `#[must_use]` added to `cpu_on`, `cpu_off`,
  `psci_version` (Result-returning functions inherit `#[must_use]`
  from `Result`).
- **Test coverage**: `psci_result_is_success_only_for_zero` now
  covers all 10 variants (was 4).
- **Documentation honesty**: removed a false claim that wrappers
  route through `PlatformBinding.psciConduit = HVC` (no such field
  exists at v1.0.0).

**Audit-pass-2 refinements** applied in a second deep audit:

- **Labeling correctness**: `cpu_on` is the pre-existing AN9-J.1
  (DEF-R-HAL-L20) wrapper, not SM1.A.1.  SM1.A.1 in this plan is
  `cpu_off`.  Section header and docstring relabeled accordingly.
- **Documentation accuracy — barrier rationale**: The module
  docstring's cross-cluster-ordering section was rewritten to
  honestly distinguish PE-affecting calls (`cpu_on`, `cpu_off`,
  `system_off`, `system_reset` — barrier required so the
  target/other cores see caller state) from pure queries
  (`psci_version`, `migrate_info_type`, `affinity_info` — no
  state transfer, barrier defensive but not required).
- **Broken rustdoc link**: A link to
  `docs/planning/SMP_RUST_HAL_PLAN.md` in the module docstring used
  a relative path (`../../../`) that resolved to a non-existent
  target in rustdoc's HTML output.  Replaced with plain-text
  reference.
- **SAFETY-comment clarity**: `cpu_on`'s "disable preserved-flags"
  wording reworked — the asm doesn't disable anything; it simply
  omits `preserves_flags` (default off).
- **Test MPIDR realism**: `cpu_on_host_stub_returns_success` now
  uses `0x0000_0001` (Aff0=1, matching
  `smp::SECONDARY_MPIDR_TABLE[0]`) instead of `0x0001_0000`
  (Aff2=1, no real BCM2712 core matches).
- **Missing edge-case tests added**: `PsciVersion::from_raw(0)`,
  `from_raw(u32::MAX)`, `to_raw` inverse directions; round-trip
  extended to cover `(0, 0)`, `(u16::MAX, u16::MAX)`, and
  asymmetric mid-range bit-pattern combinations.  `at_least`
  edge cases (`(0, 0)` queries, smallest/largest representable,
  major-only-dominates).
- **Const-context evaluation test**: a new
  `const_context_decoders_evaluate` test forces every `const fn`
  decoder into a compile-time `const` binding.  A future PR that
  loses const-ness would fail to compile — the binding itself is
  the proof.
- **Stale `lib.rs` annotation**: the `pub mod psci` line in
  `lib.rs` cited only AN9-J.1 (DEF-R-HAL-L20).  Extended to
  mention WS-SM SM1.A and the DEN0022D §5 surface it adds.

#### SM1.A.1 — `psci::cpu_off()`

**Goal**: Issue PSCI CPU_OFF HVC. Allows powering down secondary
cores at shutdown. Per ARM DEN0022D §5.1.5.

**File**: `rust/sele4n-hal/src/psci.rs`.

**Code skeleton**:

```rust
/// AN9-J.1 (SM1.A.1): PSCI CPU_OFF — power down the calling PE.
///
/// ARM DEN0022D §5.1.5: function id 0x84000002 (SMC32).
/// Caller must not return: on success the PE is powered down
/// and this function does not return. On failure (DENIED,
/// INTERNAL_FAILURE, ON_PENDING) the function returns and the
/// caller continues executing.
///
/// Returns: `PsciResult`. Note `Success` is encoded as 0, but
/// successful invocations DO NOT return (the PE is off); this
/// function returns only on failure.
#[inline]
pub fn cpu_off() -> PsciResult {
    // AN9-I: ensure cross-cluster ordering before HVC.
    crate::barriers::dsb_osh();

    #[cfg(target_arch = "aarch64")]
    {
        let mut ret: i32;
        // SAFETY: HVC #0 with PSCI calling convention. Caller
        // guarantees PE has nothing to lose by powering down
        // (caller has hand-off state to another core).
        unsafe {
            core::arch::asm!(
                "hvc #0",
                in("x0") PSCI_FN_CPU_OFF as u64,
                lateout("x0") ret,
                clobber_abi("C"),
                options(nostack)
            );
        }
        PsciResult::from_raw(ret)
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        PsciResult::Success
    }
}
```

**Acceptance**:
- Compiles on aarch64 target.
- Host stub returns `Success`.
- Unit test: `psci_cpu_off_returns_psci_result_type` (host stub).

**Size**: S (~60 LoC).

---

#### SM1.A.2 — `psci::affinity_info()`

**Goal**: Query whether a specific PE is on, off, or pending.
Per ARM DEN0022D §5.1.8.

**File**: `psci.rs`.

**Code skeleton**:

```rust
/// PSCI AFFINITY_INFO result.
///
/// ARM DEN0022D §5.1.8 returns:
/// - 0 = ON  (the target PE is on)
/// - 1 = OFF (the target PE is off)
/// - 2 = ON_PENDING (transitioning on)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(i32)]
pub enum AffinityInfoState {
    On = 0,
    Off = 1,
    OnPending = 2,
}

impl AffinityInfoState {
    pub const fn from_raw(raw: i32) -> Option<Self> {
        match raw {
            0 => Some(Self::On),
            1 => Some(Self::Off),
            2 => Some(Self::OnPending),
            _ => None,
        }
    }
}

/// PSCI AFFINITY_INFO: query the on/off state of a target PE.
///
/// `target_affinity` — MPIDR_EL1 of the target PE.
/// `lowest_affinity_level` — 0 to query exact PE (typical for
///   per-CPU queries; non-zero queries cluster-level).
///
/// ARM DEN0022D §5.1.8: function id 0xC4000004 (SMC64).
/// Returns `Ok(state)` on success, `Err(PsciResult)` on failure
/// (typically INVALID_PARAMETERS for unknown MPIDR).
pub fn affinity_info(
    target_affinity: u64,
    lowest_affinity_level: u32,
) -> Result<AffinityInfoState, PsciResult> {
    crate::barriers::dsb_osh();

    #[cfg(target_arch = "aarch64")]
    {
        let mut ret: i32;
        // SAFETY: HVC #0 with PSCI calling convention.
        unsafe {
            core::arch::asm!(
                "hvc #0",
                in("x0") PSCI_FN_AFFINITY_INFO as u64,
                in("x1") target_affinity,
                in("x2") lowest_affinity_level as u64,
                lateout("x0") ret,
                clobber_abi("C"),
                options(nostack)
            );
        }
        if ret < 0 {
            return Err(PsciResult::from_raw(ret));
        }
        AffinityInfoState::from_raw(ret).ok_or(PsciResult::Unknown)
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        let _ = (target_affinity, lowest_affinity_level);
        Ok(AffinityInfoState::On)  // host stub
    }
}

pub const PSCI_FN_AFFINITY_INFO: u32 = 0xC400_0004;
```

**Acceptance**:
- Compiles.
- Host stub returns `Ok(On)`.
- Unit tests cover all 3 raw values + an Unknown.

**Size**: M (~120 LoC including enum + 3 tests).

---

#### SM1.A.3 — `psci::system_off()`

**Goal**: PSCI SYSTEM_OFF. Per ARM DEN0022D §5.1.13.

**Code skeleton**:

```rust
pub const PSCI_FN_SYSTEM_OFF: u32 = 0x8400_0008;

/// PSCI SYSTEM_OFF: power off the entire system.
///
/// ARM DEN0022D §5.1.13. Does not return on success.
/// Caller should follow with a busy loop in case the firmware
/// fails to power off.
pub fn system_off() -> ! {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: HVC #0; system is being powered down.
        unsafe {
            core::arch::asm!(
                "hvc #0",
                in("x0") PSCI_FN_SYSTEM_OFF as u64,
                options(nostack, noreturn)
            );
        }
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        // Host stub: infinite loop.
        loop {
            core::hint::spin_loop();
        }
    }
}
```

**Acceptance**:
- Compiles (signature is `-> !`).
- Host stub spin-loops (test runner times out on first call
  — verified by `#[ignore]` annotation).

**Size**: T (~40 LoC).

---

#### SM1.A.4 — `psci::system_reset()`

**Goal**: PSCI SYSTEM_RESET. Per ARM DEN0022D §5.1.14.

Same shape as SM1.A.3 with function ID `0x8400_0009`.

**Size**: T (~40 LoC).

---

#### SM1.A.5 — `psci::psci_version()`

**Goal**: PSCI VERSION query. Returns version number.
Per ARM DEN0022D §5.1.1.

**Code skeleton**:

```rust
pub const PSCI_FN_PSCI_VERSION: u32 = 0x8400_0000;

/// PSCI version, encoded as (major << 16) | minor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PsciVersion {
    pub major: u16,
    pub minor: u16,
}

impl PsciVersion {
    pub const fn from_raw(raw: u32) -> Self {
        Self {
            major: ((raw >> 16) & 0xFFFF) as u16,
            minor: (raw & 0xFFFF) as u16,
        }
    }
}

pub fn psci_version() -> PsciVersion {
    #[cfg(target_arch = "aarch64")]
    {
        let raw: u32;
        unsafe {
            core::arch::asm!(
                "hvc #0",
                in("x0") PSCI_FN_PSCI_VERSION as u64,
                lateout("x0") raw,
                clobber_abi("C"),
                options(nostack)
            );
        }
        PsciVersion::from_raw(raw)
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        PsciVersion { major: 1, minor: 1 }  // pretend PSCI 1.1
    }
}
```

**Acceptance**:
- Compiles.
- Host stub returns 1.1.
- Encoding/decoding round-trip test.

**Size**: T (~50 LoC).

---

#### SM1.A.6 — `psci::migrate_info_type()`

**Goal**: Trusted-OS migration query. Per ARM DEN0022D §5.1.7.

Same shape as SM1.A.2 (returns enum). For seLe4n's usage,
typically returns `MIGRATE_NOT_REQUIRED` (no Trusted OS).

**Size**: T (~50 LoC).

---

#### SM1.A.7 — Function-id pinning tests

**Goal**: Every new PSCI function id is pinned against ARM
DEN0022D values by a compile-time const assert + a unit test.

**Code skeleton** (extension of existing test module in psci.rs):

```rust
#[test]
fn psci_function_ids_match_arm_den0022d() {
    // ARM DEN0022D §5.1 function-id matrix:
    assert_eq!(PSCI_FN_PSCI_VERSION,    0x8400_0000);
    assert_eq!(PSCI_FN_CPU_OFF,         0x8400_0002);
    assert_eq!(PSCI_FN_CPU_ON,          0xC400_0003);  // SMC64
    assert_eq!(PSCI_FN_AFFINITY_INFO,   0xC400_0004);  // SMC64
    assert_eq!(PSCI_FN_MIGRATE_INFO_TYPE, 0x8400_0006);
    assert_eq!(PSCI_FN_SYSTEM_OFF,      0x8400_0008);
    assert_eq!(PSCI_FN_SYSTEM_RESET,    0x8400_0009);
}

#[test]
fn psci_function_ids_pairwise_distinct() {
    let ids = [
        PSCI_FN_PSCI_VERSION,
        PSCI_FN_CPU_OFF,
        PSCI_FN_CPU_ON,
        PSCI_FN_AFFINITY_INFO,
        PSCI_FN_MIGRATE_INFO_TYPE,
        PSCI_FN_SYSTEM_OFF,
        PSCI_FN_SYSTEM_RESET,
    ];
    for (i, a) in ids.iter().enumerate() {
        for b in &ids[i + 1..] {
            assert_ne!(a, b, "duplicate PSCI function id");
        }
    }
}
```

**Size**: S (~80 LoC of tests).

---

#### SM1.A.8 — PSCI documentation map

**Goal**: Module-level docstring on `psci.rs` mapping each ARM
DEN0022D function to its wrapper, with the return-code matrix.

**File**: `psci.rs` header.

**Acceptance**:
- Docstring lists all 7 wrapped functions.
- Each entry cites DEN0022D §5.1.x.
- Return-code matrix cites Table 5 (PSCI return codes).

**Size**: T (~50 LoC of documentation).

### 5.2 Per-CPU data + TPIDR_EL1 (SM1.B, 3 PRs, 7 sub-tasks) — **LANDED at v0.31.4**

**Status**: COMPLETE on branch `claude/per-cpu-tpidr-el1-1OBHA`,
landed in patch release **v0.31.4**.  All seven sub-tasks landed in
one coherent cut, closing SMP-M4 (TPIDR_EL1 per-CPU base) at the
Lean ↔ Rust seam:

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

**Test coverage**: 281 HAL tests, zero `#[ignore]`'d (up from 253 at
SM1.A close, with 2 ignored tests converted to compile-time
signature checks at v0.31.4 audit-pass-3), zero
clippy warnings workspace-wide, zero new fmt diffs in modified files.
4 new Lean surface-anchor `#check`s in `tests/SmpFoundationsSuite.lean`
(`Platform.FFI.ffiCurrentCoreId`, `Concurrency.currentCoreId`,
`Concurrency.currentCoreId_in_range_marker`,
`Concurrency.instInhabitedCoreId`), 4 new decidable examples
discharging the `Inhabited CoreId` default + marker theorem, plus a
new §2.16 runtime-assertion section in `runCurrentCoreIdChecks` that
exercises the structural properties under the executable test
harness.  Items deferred past v1.0.0 with correctness impact: NONE.

**Module reachability**: `Concurrency.Runtime` is in the production
import closure via `SeLe4n/Platform/Staged.lean` (added to the
staged-module allowlist per the WS-RC R12.B partition gate); SM5
will move it from staged → production-reached when per-core
scheduler state lands.

**Build-system note**: The Lean test executables (run via `lake exe
<suite>`) do NOT link against `libsele4n_hal.a` — this is the
project's fail-closed FFI convention (`Platform/FFI.lean` header
docstring): any path that invokes an `@[extern] opaque` symbol from
host code surfaces as a link error rather than a silent stub call.
The SmpFoundationsSuite test therefore exercises only the structural
properties of `currentCoreId` (typed signature, marker theorem,
`Inhabited` default).  The runtime behaviour of the host stub is
covered exhaustively by the Rust `per_cpu::tests` and `ffi::tests`
modules; the hardware behaviour (the actual `mrs tpidr_el1` read)
will be covered by SM1.H's QEMU `-smp 4` boot-trace test.

#### SM1.B.1 — `PerCpuData` struct

**Goal**: Define the per-CPU data block. At SM1 the struct is
mostly empty; later phases populate it (SM5 adds current-thread
pointer, idle-TCB pointer, scheduler stats).

**File**: New `rust/sele4n-hal/src/per_cpu.rs`.

**Code skeleton**:

```rust
// SPDX-License-Identifier: GPL-3.0-or-later
//! Per-CPU data block.
//!
//! Each core has its own `PerCpuData` slot in a global array;
//! TPIDR_EL1 points to the slot.

/// Per-CPU data block. Cache-line aligned to avoid false
/// sharing between cores.
#[repr(C, align(64))]
pub struct PerCpuData {
    /// Core ID (0..coreCount-1). Redundant with TPIDR_EL1 array
    /// index but useful for sanity checks.
    pub core_id: u64,

    // SM5 additions (populated later):
    // pub current_thread_ptr: AtomicU64,
    // pub idle_thread_ptr: u64,
    // pub local_irq_count: AtomicU64,
    // ...
}

impl PerCpuData {
    /// Const constructor for static initialization.
    pub const fn new(core_id: u64) -> Self {
        Self { core_id }
    }
}

/// Global per-CPU data array. One slot per core; index 0 is
/// the boot core.
#[no_mangle]
#[used]
pub static PER_CPU_DATA: [PerCpuData; 4] = [
    PerCpuData::new(0),
    PerCpuData::new(1),
    PerCpuData::new(2),
    PerCpuData::new(3),
];
```

**Acceptance**:
- Compiles.
- `PER_CPU_DATA` symbol exported (verified by linker).
- Cargo test: `per_cpu_data_layout_is_64_byte_aligned`.

**Size**: M (~120 LoC + tests).

---

#### SM1.B.2 — Static array population

**Goal**: Each PerCpuData slot has its index pre-populated as
`core_id`. The array is in BSS (already zeroed at boot via
SM0.M; the `core_id` is set by `const fn new`).

This is part of SM1.B.1; no separate sub-task needed unless we
want to verify the static layout.

**Actual goal**: compile-time assert that PER_CPU_DATA's size and
alignment match expectations:

```rust
const _: () = assert!(
    core::mem::size_of::<[PerCpuData; 4]>() % 64 == 0,
    "PER_CPU_DATA must be 64-byte aligned per cache line"
);

const _: () = assert!(
    PER_CPU_DATA.len() == 4,
    "PER_CPU_DATA size must match PlatformBinding.coreCount"
);
```

**Size**: T (~20 LoC).

---

#### SM1.B.3 — `current_per_cpu()` accessor

**Goal**: Read TPIDR_EL1 and return a `&'static PerCpuData`.

**File**: `per_cpu.rs`.

**Code skeleton**:

```rust
/// Reads TPIDR_EL1 and returns a reference to this core's
/// PerCpuData.
///
/// # Safety
///
/// Must be called at EL1 (TPIDR_EL1 is only accessible at EL1+).
/// Must be called after the corresponding `secondary_entry` or
/// `rust_boot_main` has set TPIDR_EL1 to a valid PER_CPU_DATA
/// element address.
///
/// On host (non-aarch64), returns `&PER_CPU_DATA[0]`.
#[inline(always)]
pub fn current_per_cpu() -> &'static PerCpuData {
    #[cfg(target_arch = "aarch64")]
    {
        let tpidr: u64;
        // SAFETY: MRS TPIDR_EL1 is safe at EL1; ARM ARM D17.2.135
        unsafe {
            core::arch::asm!(
                "mrs {}, tpidr_el1",
                out(reg) tpidr,
                options(nomem, nostack, preserves_flags)
            );
        }
        // SAFETY: TPIDR_EL1 was set by boot code to a valid
        // PER_CPU_DATA element address.
        unsafe { &*(tpidr as *const PerCpuData) }
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        &PER_CPU_DATA[0]
    }
}
```

**Acceptance**:
- Compiles.
- On aarch64: TPIDR_EL1 read works (validated by `current_core_id_from_tpidr`).
- On host: returns first element.

**Size**: S (~50 LoC).

---

#### SM1.B.4 — `current_core_id_from_tpidr()`

**Goal**: Preferred over `mrs mpidr_el1; mask` for hot paths.
TPIDR_EL1 holds a pointer; `(tpidr - &PER_CPU_DATA[0]) / sizeof(PerCpuData)`
yields the core_id.

**Code skeleton**:

```rust
/// Returns the current core's CoreId from TPIDR_EL1.
///
/// Faster than `current_core_id()` (MPIDR read + mask) by ~3
/// cycles since TPIDR_EL1 is also a per-CPU register but doesn't
/// require masking.
///
/// On host (non-aarch64), returns 0.
#[inline(always)]
pub fn current_core_id_from_tpidr() -> u64 {
    current_per_cpu().core_id
}
```

**Acceptance**:
- Returns the right ID on each core (verified by QEMU `-smp 4`
  boot trace).
- Tests via `PER_CPU_DATA[i].core_id == i`.

**Size**: T (~20 LoC).

---

#### SM1.B.5 — Lean FFI: `ffi_current_core_id`

**Goal**: Expose `current_core_id_from_tpidr` to Lean.

**Files**:
- `rust/sele4n-hal/src/ffi.rs`: new `#[no_mangle] pub extern "C"
  fn ffi_current_core_id() -> u64`.
- `SeLe4n/Platform/FFI.lean`: matching `@[extern "ffi_current_core_id"]
  opaque ffiCurrentCoreId : BaseIO UInt64`.

**Code skeleton (Rust)**:

```rust
/// Lean FFI: returns the current core's ID (0..coreCount-1).
///
/// Reads TPIDR_EL1 on aarch64 to avoid the MPIDR+mask cost on
/// hot paths.
#[no_mangle]
pub extern "C" fn ffi_current_core_id() -> u64 {
    crate::per_cpu::current_core_id_from_tpidr()
}
```

**Code skeleton (Lean)**:

```lean
@[extern "ffi_current_core_id"]
opaque ffiCurrentCoreId : BaseIO UInt64

namespace SeLe4n.Kernel.Concurrency
  /-- Read the current core's CoreId from TPIDR_EL1 via FFI. -/
  def currentCoreId : BaseIO CoreId := do
    let raw ← ffiCurrentCoreId
    -- Range check: raw < numCores. Under correct setup, this
    -- always succeeds; failure is a hardware fault.
    if h : raw.toNat < PlatformBinding.coreCount then
      return ⟨raw.toNat, h⟩
    else
      panic! s!"ffi_current_core_id returned {raw} ≥ {PlatformBinding.coreCount}"
end SeLe4n.Kernel.Concurrency
```

**Acceptance**:
- FFI symbol exported, Lean side compiles.
- Range check via `if h : raw.toNat < ...`.
- QEMU `-smp 4` boot prints distinct core_ids from each core.

**Size**: S (~60 LoC across Rust + Lean).

---

#### SM1.B.6 — PerCpuData invariants

**Goal**: Compile-time + runtime invariants on `PerCpuData`
layout and content.

**Code skeleton**:

```rust
/// Compile-time: PerCpuData is 64-byte aligned.
const _: () = assert!(
    core::mem::align_of::<PerCpuData>() == 64,
    "PerCpuData must be cache-line aligned"
);

/// Runtime check (called once at boot): every slot's core_id
/// matches its array index.
pub fn check_per_cpu_invariants() {
    for (i, slot) in PER_CPU_DATA.iter().enumerate() {
        assert_eq!(slot.core_id, i as u64,
            "PER_CPU_DATA[{}].core_id = {} ≠ {}", i, slot.core_id, i);
    }
}
```

**Acceptance**:
- Compile-time assert holds.
- `check_per_cpu_invariants()` is called from `rust_boot_main`
  Phase 1.

**Size**: S (~40 LoC).

---

#### SM1.B.7 — Test `test_per_cpu_data_layout`

**Goal**: Cargo unit test verifying PER_CPU_DATA layout and
content.

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn per_cpu_data_size_is_multiple_of_cache_line() {
        assert_eq!(core::mem::size_of::<PerCpuData>() % 64, 0);
    }

    #[test]
    fn per_cpu_data_array_has_4_slots() {
        assert_eq!(PER_CPU_DATA.len(), 4);
    }

    #[test]
    fn per_cpu_data_core_ids_match_indices() {
        for (i, slot) in PER_CPU_DATA.iter().enumerate() {
            assert_eq!(slot.core_id, i as u64);
        }
    }
}
```

**Acceptance**:
- All 3 tests pass on host.

**Size**: S (~40 LoC).

### 5.3 Secondary core full init (SM1.C, 6 PRs, 12 sub-tasks) — **LANDED at v0.31.5**

**Status**: COMPLETE on branch `claude/review-codebase-secondary-core-PgqGR`,
landed in patch release **v0.31.5**.  All twelve sub-tasks landed in
one coherent cut, closing SMP-C2 (secondary cores arrive at the
Lean kernel with the same hardware posture as the primary):

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
  `SeLe4n/Kernel/SecondaryEntry.lean`.  At SM1.C the body is
  `pure ()` (deliberate placeholder; SM5 replaces with the
  per-core scheduler entry).  Surface-anchor theorem
  `secondaryKernelMain_returns_unit_marker` proves the placeholder
  semantics by `rfl` for downstream Tier-3 scans.  Module reached
  via `SeLe4n/Platform/Staged.lean`; added to the staged-module
  allowlist per WS-RC R12.B.
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

**Test coverage**: 313 HAL tests (was 281 at SM1.B close), zero
`#[ignore]`'d, zero clippy warnings workspace-wide.  Tier 0+1+2+3
all green.  Items deferred past v1.0.0 with correctness impact:
NONE.

**Audit-pass refinements** (post-initial-landing):
- HIGH-portability fix: `enable_mmu`'s `pt_pa_raw < 2^44`
  debug_assert was unconditional and false-faulted on host
  x86_64 PIE binaries (whose base addresses routinely exceed
  2^44).  Cfg-gated on `cfg!(target_arch = "aarch64")`.
- Build-script regression scanners: three new scanners in
  `rust/sele4n-hal/build.rs` (`scan_boot_rs_uses_install_exception_vectors`,
  `scan_smp_rs_uses_install_exception_vectors`,
  `scan_smp_rs_invokes_secondary_init_helpers`) pin the SM1.C.2
  primary/secondary symmetry and the SM1.C.5 init-helper call
  chain at build time.

#### SM1.C original detailed sub-task breakdown (preserved for reference)

This section closed SMP-C2. Each sub-task extracts a helper from the
primary boot path and applies it to secondaries.

#### SM1.C.1 — Extract `mmu::init_mmu_secondary(core_id)`

**Goal**: Refactor existing `mmu::init_mmu` into shared core
(callable from primary boot Phase 2) and a per-secondary
variant.

**File**: `rust/sele4n-hal/src/mmu.rs`.

**Mathematical specification**:

The MMU initialization sequence on ARMv8-A (per ARM ARM D8.2):
1. Set MAIR_EL1 (memory attributes).
2. Set TCR_EL1 (translation control).
3. Set TTBR0_EL1 + TTBR1_EL1.
4. Issue `dsb sy ; isb`.
5. Set SCTLR_EL1 to enable MMU (M=1, C=1, I=1).

On secondaries: TTBR0/1 and MAIR/TCR are per-core banked but
should point to the same physical-table state the primary set up.
SCTLR_EL1 is set per-core to the same bitmap.

**Code skeleton**:

```rust
/// Initialize the MMU on this core. Shared between primary
/// (Phase 2 of `rust_boot_main`) and secondaries
/// (`rust_secondary_main`).
pub fn init_mmu_per_core(core_id: u64) {
    set_mair_el1();
    set_tcr_el1();
    set_ttbrs();  // TTBR0 + TTBR1 to the shared kernel tables

    // SAFETY: DSB SY + ISB required between TTBR program and
    // SCTLR enable. (ARM ARM D8.2)
    crate::barriers::dsb_sy();
    crate::barriers::isb();

    apply_sctlr_el1_bitmap();

    // After SCTLR.M=1, MMU is on. Subsequent accesses use virtual
    // addresses; the boot identity-map allows continuity.

    crate::barriers::isb();
}

/// Primary boot's MMU init. Identical to per-core but with
/// extra setup of the boot page tables (called once at boot
/// before any secondary is brought up).
pub fn init_mmu() {
    setup_boot_page_tables();
    init_mmu_per_core(0);
}

/// Secondary core's MMU init. Reuses the boot page tables
/// (already set up by primary).
pub fn init_mmu_secondary(core_id: u64) {
    debug_assert!(core_id > 0, "init_mmu_secondary called with core 0");
    init_mmu_per_core(core_id);
}
```

**Acceptance**:
- Refactor preserves primary-boot behavior (regression test on
  primary).
- Secondary path: QEMU smoke test shows MMU enabled on all 4 cores.
- Cargo test: `init_mmu_secondary_compiles_with_core_id`.

**Size**: L (~200 LoC of refactor + 4-6 tests).

---

#### SM1.C.2 — Extract `vectors::write_vbar_el1_secondary()`

**Goal**: Refactor primary's `set_vbar` into a shared helper.

**File**: `rust/sele4n-hal/src/boot.rs` (existing `set_vbar`) +
new `vectors.rs` helper or inline.

**Code skeleton**:

```rust
/// Install the exception vector table at VBAR_EL1.
///
/// Shared between primary and secondary boot.
pub fn install_exception_vectors() {
    #[cfg(target_arch = "aarch64")]
    {
        extern "C" {
            static __exception_vectors: u8;
        }
        let vbar = unsafe { &raw const __exception_vectors as u64 };
        debug_assert_eq!(vbar % 2048, 0,
            "VBAR must be 2048-byte aligned (ARM ARM D17.2.135)");
        crate::registers::write_vbar_el1(vbar);
    }
    crate::barriers::dsb_sy();
    crate::barriers::isb();
}
```

The primary's `set_vbar` becomes a thin wrapper or is replaced
entirely by `install_exception_vectors`.

**Acceptance**:
- Primary boot uses the new helper.
- Secondary boot uses the same helper.
- Compile-time alignment check.

**Size**: S (~60 LoC).

---

#### SM1.C.3 — `gic::init_cpu_interface_secondary(core_id)`

**Goal**: GIC-400's CPU interface is banked per-core but at the
same MMIO address (`GICC_BASE`). The init sequence is identical
to the primary's, just on a different core's banked view.

**File**: `rust/sele4n-hal/src/gic.rs`.

**Code skeleton**:

```rust
/// Initialize this core's GIC-400 CPU interface.
///
/// Per GIC-400 TRM §4.4. GICC registers (PMR, BPR, CTLR) are
/// banked per-core, so each core writes them independently.
///
/// `core_id` is informational (used in kprintln); the actual
/// MMIO target is GICC_BASE for all cores.
pub fn init_cpu_interface_secondary(core_id: u64) {
    // Step 1: priority mask = 0xFF (accept all priorities).
    mmio_write32(GICC_BASE + gicc::PMR, 0xFF);

    // Step 2: binary point = 0 (no grouping).
    mmio_write32(GICC_BASE + gicc::BPR, 0);

    // Step 3: enable.
    mmio_write32(GICC_BASE + gicc::CTLR, 1);

    crate::kprintln!("[smp] core {}: GIC CPU interface initialized", core_id);
}
```

**Acceptance**:
- Secondary's GICC_CTLR shows enabled post-init (verified via
  MMIO read).
- Per-core boot banner emitted.

**Size**: S (~50 LoC).

---

#### SM1.C.4 — `timer::init_timer_secondary(tick_hz)`

**Goal**: Per-core timer. CNTKCTL_EL1 and CNTV_TVAL_EL0 are
per-core banked.

**File**: `rust/sele4n-hal/src/timer.rs`.

**Code skeleton**:

```rust
/// Initialize this core's ARM Generic Timer.
///
/// Per ARM ARM D11.2. CNTV (virtual counter) is per-core. Tick
/// frequency is set globally by firmware (CNTFRQ_EL0 read-only).
pub fn init_timer_secondary(tick_hz: u32) -> Result<(), TimerError> {
    // Read firmware-programmed CNTFRQ_EL0.
    let cntfrq = read_cntfrq_el0();
    if cntfrq == 0 {
        return Err(TimerError::CntfrqNotProgrammed);
    }

    // Compute ticks per tick_hz period.
    let counts_per_tick = (cntfrq / tick_hz) as u64;

    // CNTKCTL_EL1.EL0VCTEN = 1 (allow EL0 read of CNTVCT).
    set_cntkctl_el1(1 << 1);

    // Arm the timer.
    write_cntv_tval_el0(counts_per_tick);
    write_cntv_ctl_el0(1);  // Enable=1, IMask=0

    Ok(())
}
```

**Acceptance**:
- Per-core CNTV_CTL_EL0.Enable = 1 post-init.
- Timer interrupt fires on each core within the expected window.

**Size**: M (~100 LoC).

---

#### SM1.C.5 — Rewrite `rust_secondary_main` body

**Goal**: The main contribution. Replace the current
`wfe_bounded` loop with a full per-core init sequence followed
by entry into the Lean kernel.

**File**: `rust/sele4n-hal/src/smp.rs`.

**Code skeleton**:

```rust
/// Secondary-core entry point. Called from `boot.S::secondary_entry`
/// (via PSCI CPU_ON) on each secondary core.
///
/// Performs the full per-core init sequence (SM1.C):
/// 1. MMU enable (TTBR + SCTLR).
/// 2. VBAR install.
/// 3. GIC CPU interface init.
/// 4. Timer arm.
/// 5. CORE_READY[core_idx] := true.
/// 6. Wait for primary's bring-up to complete (SEV ack).
/// 7. Enter Lean kernel (`lean_secondary_kernel_main(core_id)`).
///
/// Never returns.
#[no_mangle]
pub extern "C" fn rust_secondary_main(context_id: u64) -> ! {
    let core_id = context_id;

    // Boot banner.
    crate::kprintln!("[smp] core {}: entering secondary init", core_id);

    // Step 1: MMU.
    crate::mmu::init_mmu_secondary(core_id);
    crate::kprintln!("[smp] core {}: MMU enabled", core_id);

    // Step 2: VBAR.
    crate::boot::install_exception_vectors();
    crate::kprintln!("[smp] core {}: VBAR installed", core_id);

    // Step 3: GIC CPU interface.
    crate::gic::init_cpu_interface_secondary(core_id);

    // Step 4: Timer.
    if let Err(e) = crate::timer::init_timer_secondary(crate::timer::DEFAULT_TICK_HZ) {
        crate::kprintln!("[smp] core {}: FATAL: timer init failed: {}",
            core_id, e);
        // Cannot recover; halt this core.
        loop { crate::cpu::wfe(); }
    }
    crate::kprintln!("[smp] core {}: timer armed at {} Hz",
        core_id, crate::timer::DEFAULT_TICK_HZ);

    // Step 5: Signal ready.
    let core_idx = core_id as usize;
    if core_idx < CORE_READY.len() {
        CORE_READY[core_idx].store(true, Ordering::Release);
    }

    crate::kprintln!("[smp] core {}: ready, entering kernel", core_id);

    // Step 6: enable IRQ delivery.
    crate::interrupts::enable_irq();

    // Step 7: enter Lean kernel.
    #[cfg(feature = "hw_target")]
    {
        extern "C" {
            fn lean_secondary_kernel_main(core_id: u64);
        }
        // SAFETY: lean_secondary_kernel_main is Lean-compiled entry.
        unsafe { lean_secondary_kernel_main(core_id) };
    }

    // Idle fallback if kernel entry returns.
    loop {
        crate::cpu::wfe();
    }
}
```

**Acceptance**:
- Body matches the docstring claim from `smp.rs:202-211`.
- QEMU `-smp 4` boot trace shows 4 ready banners.
- All 4 cores reach `lean_secondary_kernel_main`.

**Size**: M (~150 LoC).

---

#### SM1.C.6 — Lean `secondaryKernelMain`

**Goal**: Lean-side `@[export]` entry for secondaries.

**File**: New `SeLe4n/Kernel/SecondaryEntry.lean`.

**Code skeleton**:

```lean
import SeLe4n.Platform.FFI
import SeLe4n.Kernel.Concurrency.Types

namespace SeLe4n.Kernel

/-- Secondary-core kernel entry. Called from Rust
    `rust_secondary_main` once per secondary core after
    per-core init completes.

    SM1: this is a placeholder that enters a per-core idle loop.
    SM5 adds the per-core scheduler entry that drives this core's
    runnable threads. -/
@[export lean_secondary_kernel_main]
def secondaryKernelMain (coreId : UInt64) : BaseIO Unit := do
  -- Future: SM5 replaces this with the per-core scheduler loop.
  -- At SM1, just park in idle.
  let _ ← ffiKprintln s!"[lean] secondary core {coreId} entering idle"
  -- Park forever.
  while true do
    let _ ← ffiWfe  -- HAL wfe_bounded

end SeLe4n.Kernel
```

**Acceptance**:
- Lean module compiles.
- `@[export]` symbol resolves at link time.
- QEMU boot shows the Lean-side kprintln from each core.

**Size**: S (~50 LoC).

---

#### SM1.C.7 — Per-core stack reuses link.ld reservation

The `link.ld` already has `.smp_stacks` reserving 3 × 64 KiB.
`secondary_entry` (boot.S) computes the per-core stack offset.
SM1.C.7 is documentation-only at this phase — verifying the
existing infrastructure works with SM1.C.5's expanded entry path.

**Size**: T.

---

#### SM1.C.8 — Per-core MMU page table reuse

**Goal**: Secondaries reuse the kernel page tables (TTBR1)
already set up by the primary. TTBR0 starts as the boot
process's address space; future per-process scheduling on
secondaries will rebind TTBR0 as threads switch.

**Documentation**: in `mmu.rs` module docstring.

**Size**: T.

---

#### SM1.C.9 — SCTLR_EL1 per-core bitmap

The `apply_sctlr_el1_bitmap` helper from SM1.C.1 is called on
each core. Verified by post-init MRS test.

**Size**: T.

---

#### SM1.C.10 — Per-core exception vector

VBAR_EL1 is banked per-core; SM1.C.2's `install_exception_vectors`
runs on each core. All cores point to the same `__exception_vectors`
table (the table itself is shared; PSTATE per-core handles
the context).

**Size**: T (documentation).

---

#### SM1.C.11 — SError handler enabled

SError (asynchronous abort) is masked by DAIF.A. On each
core's post-init, DAIF.A should be cleared if we want to handle
SErrors. For v1.0.0 we leave SError masked (matches existing
single-core policy).

**Size**: T (documentation).

---

#### SM1.C.12 — Full secondary-init host stubs + tests

**File**: cargo test in `smp.rs::tests`.

**Code skeleton**:

```rust
#[test]
fn rust_secondary_main_compiles() {
    // Host stub: secondary_main loops; we can't actually call it.
    // The compile-time test verifies the function exists and has
    // the right signature.
    let _: extern "C" fn(u64) -> ! = rust_secondary_main;
}

#[test]
fn init_mmu_secondary_callable_with_core_id() {
    crate::mmu::init_mmu_secondary(1);  // host stub: no-op
}

#[test]
fn init_cpu_interface_secondary_callable() {
    crate::gic::init_cpu_interface_secondary(1);  // host stub
}

#[test]
fn init_timer_secondary_returns_ok_on_host() {
    let r = crate::timer::init_timer_secondary(1000);
    assert!(r.is_ok());
}
```

**Acceptance**: 4+ tests pass on host.

**Size**: S (~60 LoC).

### 5.4 DTB cmdline + Phase 5 (SM1.D, 3 PRs, 6 sub-tasks)

#### SM1.D.1 — `cmdline.rs` DTB parser

**Goal**: Minimal DTB `/chosen/bootargs` parser. Supports
key=value, flag-only, quoted strings.

**File**: New `rust/sele4n-hal/src/cmdline.rs`.

**Code skeleton**:

```rust
// SPDX-License-Identifier: GPL-3.0-or-later
//! DTB /chosen/bootargs command-line parser.

#[derive(Debug, Clone, Copy)]
pub struct CmdlineConfig {
    pub smp_enabled: bool,
    pub smp_max_cores: usize,
}

impl Default for CmdlineConfig {
    fn default() -> Self {
        Self {
            smp_enabled: true,    // SM1.D.3: default = enabled
            smp_max_cores: 4,
        }
    }
}

/// Parse the kernel command-line string into a CmdlineConfig.
///
/// Format: space-separated tokens. Each token is either:
/// - `flag` (boolean true)
/// - `key=value` (typed: bool / usize)
/// - `key="value with spaces"` (quoted)
///
/// Unknown tokens are silently ignored (forward-compat).
pub fn parse_cmdline(s: &str) -> CmdlineConfig {
    let mut cfg = CmdlineConfig::default();
    for token in s.split_ascii_whitespace() {
        if let Some(eq) = token.find('=') {
            let (key, value) = token.split_at(eq);
            let value = &value[1..];  // skip '='
            match key {
                "smp_enabled" => {
                    cfg.smp_enabled = parse_bool(value).unwrap_or(cfg.smp_enabled);
                }
                "smp_max_cores" => {
                    if let Ok(n) = value.parse::<usize>() {
                        cfg.smp_max_cores = n.min(4);
                    }
                }
                _ => {}  // unknown key
            }
        } else {
            // Flag-only token (none currently used).
        }
    }
    cfg
}

fn parse_bool(s: &str) -> Option<bool> {
    match s {
        "true" | "1" | "yes" | "on" => Some(true),
        "false" | "0" | "no" | "off" => Some(false),
        _ => None,
    }
}

/// Extract the bootargs string from the DTB.
///
/// Looks for /chosen/bootargs in the device tree blob. Returns
/// empty if absent.
pub fn extract_bootargs(dtb_ptr: u64) -> &'static str {
    // SM1: use existing DeviceTree parser (Platform/DeviceTree.lean
    // is Lean-side; the Rust HAL needs a thin local parser).
    // For simplicity, the bootargs is delegated to Lean via FFI;
    // here we provide a stub that returns "".
    let _ = dtb_ptr;
    ""  // TODO: real DTB parser (separate work item, perhaps
        // SM1.D.1.a) — Lean does the real parse and pokes
        // the cmdline_config via a FFI export.
}
```

**Acceptance**:
- Parses `smp_enabled=false` → `cfg.smp_enabled = false`.
- Parses `smp_enabled=true` → `cfg.smp_enabled = true`.
- Parses empty string → defaults (smp_enabled=true).
- Robust to malformed: `smp_enabled=foo` → keeps default.
- 10+ unit tests cover all branches.

**Size**: L (~250 LoC including tests).

---

#### SM1.D.2 — Phase 5 in `rust_boot_main`

**Goal**: Wire the bring-up call after Phase 4 completes.

**File**: `rust/sele4n-hal/src/boot.rs`.

**Code skeleton** (insert before the `lean_kernel_main` call):

```rust
// -----------------------------------------------------------------
// Phase 5: Parse cmdline; bring up secondaries if enabled.
// -----------------------------------------------------------------
let bootargs = crate::cmdline::extract_bootargs(_dtb_ptr);
let cmdline_cfg = crate::cmdline::parse_cmdline(bootargs);

crate::kprintln!("[boot] cmdline: smp_enabled={}, smp_max_cores={}",
    cmdline_cfg.smp_enabled, cmdline_cfg.smp_max_cores);

if cmdline_cfg.smp_enabled {
    crate::kprintln!("[boot] Phase 5: bringing up secondary cores...");
    crate::smp::SMP_ENABLED.store(true, core::sync::atomic::Ordering::Release);
    let online = crate::smp::bring_up_secondaries();
    crate::kprintln!("[boot] {} secondary cores brought up", online);
} else {
    crate::kprintln!("[boot] Phase 5: SMP disabled (single-core boot)");
}
```

**Acceptance**:
- Phase 5 banner in boot trace.
- QEMU `-smp 4` with default cmdline brings up 4 cores.
- QEMU `-smp 4 -append "smp_enabled=false"` boots single-core.

**Size**: S (~50 LoC).

---

#### SM1.D.3 — Default behavior: SMP enabled

Per maintainer decision #7, default is enabled. This is encoded
in `CmdlineConfig::default()::smp_enabled = true`. Tests verify
the default.

**Size**: T (in SM1.D.1's default impl).

---

#### SM1.D.4 — Ordering: locks initialized before bring-up

**Goal**: Per-object locks live in objects (Default-initialized
to `.unheld`). The `BKL` static (if any) — none under per-object
fine locks — is irrelevant. The per-CPU data array's
`PER_CPU_DATA` is BSS-initialized (SM0.M zeroed it). All good.

**Acceptance**:
- No initialization-order hazards.

**Size**: T (documentation only).

---

#### SM1.D.5 — Per-CPU data init before bring-up

`init_per_cpu_data()` (which is mostly a no-op at SM1 since
PerCpuData is small) runs in Phase 1 of `rust_boot_main`.
Document this ordering in Phase 1.

**Code skeleton**:

```rust
// Phase 1 addition:
crate::per_cpu::check_per_cpu_invariants();
crate::kprintln!("[boot] per-cpu data verified ({} cores)",
    crate::per_cpu::PER_CPU_DATA.len());
```

**Acceptance**:
- Phase 1 prints per-CPU data verification.

**Size**: T.

---

#### SM1.D.6 — `smp_max_cores` cmdline option

**Goal**: Allow testing with fewer cores than the platform
supports. Useful for QEMU tests with `-smp 2`.

**File**: `cmdline.rs` (parser) + `smp.rs` (loop bound).

**Code skeleton** (smp.rs change):

```rust
pub fn bring_up_secondaries_with_limit(max_cores: usize) -> u32 {
    let limit = max_cores.min(MAX_SECONDARY_CORES + 1);
    let table = &SECONDARY_MPIDR_TABLE[..limit.saturating_sub(1)];
    bring_up_secondaries_inner(
        &SMP_ENABLED, &CORE_READY, &SECONDARY_CORES_ONLINE, table)
}
```

**Acceptance**:
- `smp_max_cores=2` brings up only 1 secondary.
- `smp_max_cores=4` brings up all 3 secondaries.

**Size**: S (~30 LoC).

### 5.5 IS-variant TLB instructions (SM1.E, 3 PRs, 5 sub-tasks)

#### SM1.E.1 — Add `tlbi_*is` variants

**File**: `rust/sele4n-hal/src/tlb.rs`.

**Code skeleton**:

```rust
/// TLBI VMALLE1IS: flush all TLB entries, inner-shareable broadcast.
#[inline(always)]
pub fn tlbi_vmalle1is() {
    #[cfg(target_arch = "aarch64")]
    {
        unsafe {
            core::arch::asm!("tlbi vmalle1is",
                options(nostack, preserves_flags));
        }
    }
    crate::barriers::dsb_ish();
    crate::barriers::isb();
}

/// TLBI VAE1IS: flush by VA + ASID, inner-shareable broadcast.
#[inline(always)]
pub fn tlbi_vae1is(asid: u16, vaddr: u64) {
    let _operand = ((asid as u64) << 48) | ((vaddr >> 12) & 0xFFFF_FFFF_FFFF);
    #[cfg(target_arch = "aarch64")]
    {
        unsafe {
            core::arch::asm!("tlbi vae1is, {0}",
                in(reg) _operand,
                options(nostack, preserves_flags));
        }
    }
    crate::barriers::dsb_ish();
    crate::barriers::isb();
}

/// TLBI ASIDE1IS: flush by ASID, inner-shareable broadcast.
#[inline(always)]
pub fn tlbi_aside1is(asid: u16) {
    let _operand = (asid as u64) << 48;
    #[cfg(target_arch = "aarch64")]
    {
        unsafe {
            core::arch::asm!("tlbi aside1is, {0}",
                in(reg) _operand,
                options(nostack, preserves_flags));
        }
    }
    crate::barriers::dsb_ish();
    crate::barriers::isb();
}

/// TLBI VALE1IS: flush last-level by VA, inner-shareable.
#[inline(always)]
pub fn tlbi_vale1is(asid: u16, vaddr: u64) {
    let _operand = ((asid as u64) << 48) | ((vaddr >> 12) & 0xFFFF_FFFF_FFFF);
    #[cfg(target_arch = "aarch64")]
    {
        unsafe {
            core::arch::asm!("tlbi vale1is, {0}",
                in(reg) _operand,
                options(nostack, preserves_flags));
        }
    }
    crate::barriers::dsb_ish();
    crate::barriers::isb();
}
```

**Acceptance**:
- 4 new functions compile.
- Per-function host stub returns (no-op on non-aarch64).
- ARM ARM C6.2.311-316 cited in docstrings.

**Size**: M (~150 LoC).

---

#### SM1.E.2 — Add OSH variants (post-1.0-ready)

Same pattern with `tlbi vae1os`, `tlbi aside1os`, etc. RPi5 uses
the IS variants; OSH variants are pre-positioned for multi-cluster
ports.

**Size**: M (~150 LoC).

---

#### SM1.E.3 — `tlbi_for_sharing(d, op, args)` dispatcher

**Goal**: Single entry point that routes to IS or OS variant
based on `SharingDomain`.

**Code skeleton**:

```rust
pub enum TlbInvalidation {
    Vmalle1,
    Vae1 { asid: u16, vaddr: u64 },
    Aside1 { asid: u16 },
    Vale1 { asid: u16, vaddr: u64 },
}

pub fn tlbi_for_sharing(
    domain: SharingDomain,
    op: TlbInvalidation,
) {
    match (domain, op) {
        (SharingDomain::Inner, TlbInvalidation::Vmalle1) => tlbi_vmalle1is(),
        (SharingDomain::Outer, TlbInvalidation::Vmalle1) => tlbi_vmalle1os(),
        (SharingDomain::Inner, TlbInvalidation::Vae1 { asid, vaddr }) =>
            tlbi_vae1is(asid, vaddr),
        // ... 6 more cases
    }
}
```

**Acceptance**:
- Dispatcher compiles.
- Per-case routing test verifies the right instruction is
  emitted (via mock).

**Size**: M (~80 LoC + 8 tests).

---

#### SM1.E.4 — Lean FFI bindings

Lean side: `@[extern "ffi_tlbi_is"] opaque tlbiIs : TlbOp → BaseIO Unit`.

**File**: `SeLe4n/Platform/FFI.lean`.

**Size**: S (~40 LoC).

---

#### SM1.E.5 — Migrate kernel-side callers

**Goal**: Every kernel-side TLB invalidation routes through the
sharing-domain-routed variant. Grep test in tier-0:

```bash
# Tier-0 hygiene check: no production kernel caller emits
# non-IS TLBI directly.
if grep -rn "tlbi_vae1[^i]" SeLe4n/ | grep -v test; then
    echo "ERROR: non-IS TLBI in kernel code"
    exit 1
fi
```

**Acceptance**:
- Hygiene check passes.
- All previous TLB callsites route through the dispatcher.

**Size**: M (~50 LoC of callsite migrations).

### 5.6 SGI primitive (SM1.F, 4 PRs, 8 sub-tasks)

#### SM1.F.1 — `GICD_SGIR` constant

**File**: `gic.rs`.

**Code skeleton**:

```rust
/// GICD_SGIR offset from GICD base. Per GIC-400 TRM §4.3.13.
pub const GICD_SGIR: usize = 0xF00;
```

**Size**: T.

---

#### SM1.F.2 — `gic::send_sgi(target_mask, intid)`

**Code skeleton**:

```rust
/// Send an SGI to one or more target CPUs.
///
/// `target_mask` — bitmask of target CPU interfaces (bit i = CPU i).
/// `intid` — SGI INTID (0..15).
///
/// GIC-400 TRM §4.3.13: write to GICD_SGIR with:
///   bits [25:24] = 0b00 (use CPUTargetList)
///   bits [23:16] = CPUTargetList
///   bit 15       = 0 (non-secure)
///   bits [3:0]   = SGIINTID
///
/// # Panics
///
/// Panics if `intid >= 16` (only SGIs 0..15 are valid).
pub fn send_sgi(target_mask: u8, intid: u8) {
    assert!(intid < 16, "SGI INTID must be 0..15, got {}", intid);
    let encoding: u32 = (0b00 << 24)
        | ((target_mask as u32) << 16)
        | (intid as u32);
    // DSB ISH before SGI write to ensure prior writes visible
    // to target cores before the SGI fires.
    crate::barriers::dsb_ish();
    mmio_write32(GICD_BASE + GICD_SGIR, encoding);
}
```

**Acceptance**:
- `send_sgi(0b1110, 1)` writes `0x000E_0001` to GICD_SGIR (mock test).
- Panic on invalid INTID.
- DSB ISH issued before write.

**Size**: S (~50 LoC).

---

#### SM1.F.3 — `gic::send_sgi_to_self(intid)`

```rust
/// Send an SGI to the calling CPU only.
///
/// Equivalent to `send_sgi` with TargetListFilter=10 (to-self).
pub fn send_sgi_to_self(intid: u8) {
    assert!(intid < 16, "SGI INTID must be 0..15");
    let encoding: u32 = (0b10 << 24) | (intid as u32);
    crate::barriers::dsb_ish();
    mmio_write32(GICD_BASE + GICD_SGIR, encoding);
}
```

**Size**: T.

---

#### SM1.F.4 — `gic::send_sgi_to_all_but_self(intid)`

```rust
/// Send an SGI to all CPUs except the caller.
///
/// TargetListFilter=01 (all but requester).
pub fn send_sgi_to_all_but_self(intid: u8) {
    assert!(intid < 16, "SGI INTID must be 0..15");
    let encoding: u32 = (0b01 << 24) | (intid as u32);
    crate::barriers::dsb_ish();
    mmio_write32(GICD_BASE + GICD_SGIR, encoding);
}
```

**Size**: T.

---

#### SM1.F.5 — SGI handler dispatch

**Goal**: Wire SGI INTIDs 0..15 into a per-SGI handler table.

**Code skeleton**:

```rust
/// SGI handler table. One entry per SGI INTID (0..15).
type SgiHandler = fn(intid: u8, source_cpu: u8);

static mut SGI_HANDLERS: [Option<SgiHandler>; 16] = [None; 16];

/// Register a handler for a specific SGI INTID.
///
/// # Safety
///
/// Must be called from boot before any SGI can fire on this core.
pub unsafe fn register_sgi_handler(intid: u8, handler: SgiHandler) {
    assert!(intid < 16);
    SGI_HANDLERS[intid as usize] = Some(handler);
}

/// Dispatch an SGI. Called from the IRQ handler when an SGI is
/// pending.
pub fn dispatch_sgi(intid: u8, source_cpu: u8) {
    if intid < 16 {
        let handler = unsafe { SGI_HANDLERS[intid as usize] };
        if let Some(h) = handler {
            h(intid, source_cpu);
        } else {
            crate::kprintln!("[gic] no handler for SGI {}", intid);
        }
    }
}
```

**Acceptance**:
- Handlers registered for each SgiKind (reschedule, tlbShootdownReq,
  tlbShootdownAck, cacheBroadcast, haltAll) — actual handler
  bodies in SM5/SM7.
- Unit tests verify dispatch routing.

**Size**: M (~100 LoC).

---

#### SM1.F.6 — Lean FFI for SGI send

**File**: `SeLe4n/Platform/FFI.lean`.

```lean
@[extern "ffi_send_sgi_to_core"]
opaque ffiSendSgiToCore (coreId : UInt64) (intid : UInt8) : BaseIO Unit

@[extern "ffi_send_sgi_to_self"]
opaque ffiSendSgiToSelf (intid : UInt8) : BaseIO Unit

@[extern "ffi_send_sgi_to_all_but_self"]
opaque ffiSendSgiToAllButSelf (intid : UInt8) : BaseIO Unit
```

**Size**: T.

---

#### SM1.F.7 — Tests

```rust
#[test]
fn send_sgi_encoding_to_cpu_2() {
    // Mock MMIO write captures the value.
    let capture = capture_sgi_write(|| {
        send_sgi(0b0100, 1);
    });
    assert_eq!(capture, 0x0004_0001);  // TargetListFilter=00, CPUTargetList=0b0100, INTID=1
}

#[test]
fn send_sgi_to_self_encoding() {
    let capture = capture_sgi_write(|| {
        send_sgi_to_self(3);
    });
    assert_eq!(capture, 0x0200_0003);  // TargetListFilter=10, INTID=3
}

#[test]
fn send_sgi_to_all_but_self_encoding() {
    let capture = capture_sgi_write(|| {
        send_sgi_to_all_but_self(0);
    });
    assert_eq!(capture, 0x0100_0000);  // TargetListFilter=01, INTID=0
}

#[test]
#[should_panic]
fn send_sgi_with_intid_16_panics() {
    send_sgi(0b1, 16);
}
```

**Size**: S (~80 LoC).

---

#### SM1.F.8 — GICD_SGIR ordering documentation

`send_sgi` already issues `dsb ish` before the write. Document
why: ARM ARM B2.7.5 says writes prior to a DSB are observed
by all PEs in the IS domain before subsequent operations; the
SGI write itself triggers the SGI delivery, so prior kernel-state
writes must be visible.

**Size**: T.

### 5.7 Cross-core kprintln synchronization (SM1.G, 2 PRs, 4 sub-tasks)

#### SM1.G.1 — Audit `UartLock::with`

The existing `UartLock::with` in `uart.rs` uses a CAS loop. SM1.G.1
audits it for SMP correctness:

- The lock is a single AtomicBool with CAS acquire / store release.
- Under 4-core contention: cores race; one acquires, others spin
  on the CAS.
- Correctness: relies on acquire/release semantics of the AtomicBool.

**Decision**: SM2's TicketLock primitive (also under construction)
provides FIFO fairness. Once SM2.B lands, SM1.G.1 replaces
`UartLock` with a `TicketLock` for fairness.

**Acceptance**:
- Audit document in `uart.rs` header.
- Replacement deferred to post-SM2.B.

**Size**: M (~80 LoC of audit + refactor).

---

#### SM1.G.2 — Per-core boot banner

Already done in SM1.C.5 (banner per core). SM1.G.2 just verifies
the trace.

**Size**: T.

---

#### SM1.G.3 — Per-core kprintln stress test

```rust
#[test]
#[ignore]  // Hardware-only test
fn cross_core_kprintln_stress() {
    // Run on QEMU -smp 4. Each core emits 1M kprintln
    // calls. Verify no torn output via parser.
    unimplemented!("populated by QEMU test infrastructure")
}
```

Actual test: `scripts/test_qemu_smp_kprintln_stress.sh`.

**Size**: M.

---

#### SM1.G.4 — `kprintln_core!` macro

```rust
macro_rules! kprintln_core {
    ($($arg:tt)*) => {{
        let core_id = $crate::per_cpu::current_core_id_from_tpidr();
        $crate::kprintln!("[core {}] {}", core_id,
            format_args!($($arg)*));
    }};
}
```

**Size**: S.

### 5.8 QEMU SMP integration (SM1.H, 2 PRs, 5 sub-tasks)

#### SM1.H.1 — Full `test_qemu_smp_bringup.sh` implementation

Replaces the SKIP stub. Boots QEMU `-smp 4 -machine virt,secure=on`;
captures UART; greps for 4 core-ready banners.

**File**: `scripts/test_qemu_smp_bringup.sh`.

**Code skeleton**:

```bash
#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

if ! command -v qemu-system-aarch64 &>/dev/null; then
    echo "[SKIP] qemu-system-aarch64 not found"
    exit 0
fi

KERNEL="${REPO_ROOT}/target/aarch64-unknown-none/release/sele4n-kernel"
if [[ ! -f "$KERNEL" ]]; then
    echo "[SKIP] kernel image not built (run 'cargo build --release')"
    exit 0
fi

LOG=$(mktemp)
timeout 30s qemu-system-aarch64 \
    -M virt,secure=on \
    -cpu cortex-a76 \
    -smp 4 \
    -m 1G \
    -kernel "$KERNEL" \
    -nographic \
    -serial mon:stdio \
    -d guest_errors \
    < /dev/null \
    > "$LOG" 2>&1 \
    || true

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

### 5.9 Miscellaneous HAL improvements (SM1.I, 3 PRs, 6 sub-tasks)

#### SM1.I.1 — Per-core IRQ handler entry

`trap.rs::handle_irq_perCore`: reads current core's ID, dispatches
per-core handler. Details in SM5.

**Size**: M.

#### SM1.I.2 — Per-core IRQ priority masking

GICC_PMR is per-CPU-interface, so already per-core. SM1.I.2
documents this.

**Size**: T.

#### SM1.I.3 — Per-core IDLE thread Rust stub

A small extern "C" function the Lean side can call to invoke
WFE on this core. SM5 uses it.

**Size**: T.

#### SM1.I.4 — Per-core exception statistics

Optional informational counters per core. Useful for benchmarking;
not required for correctness.

**Size**: M.

#### SM1.I.5 — SEV / WFE coordination documentation

Module-level docstring explaining how SEV broadcasts wakeup to
WFE-parked cores.

**Size**: T.

#### SM1.I.6 — Extended cargo tests

`cargo test -p sele4n-hal --lib smp` extends with cross-core
scenarios where host stubs permit.

**Size**: M.

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

# Tier-0 hygiene (no non-IS TLBI in kernel code):
grep -rn "tlbi_vae1[^i]" SeLe4n/ | grep -v test && \
  echo "FAIL: non-IS TLBI in kernel" || echo "OK"
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

*SM1 brings the Rust HAL to feature-complete SMP readiness. It
runs in parallel with SM2 (verified lock primitives), the two
phases having no direct dependencies (SM2's outputs are consumed
starting in SM3). Together SM1 + SM2 lay the foundation that
SM3..SM9 build atop.*
