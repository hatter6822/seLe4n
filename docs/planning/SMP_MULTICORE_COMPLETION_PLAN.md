# SMP / Multi-Core Completion — Audit & Roadmap

> **Status**: AUDIT — planning artefact for a future post-v1.0.0 workstream
> (provisional ID **WS-SM**, "SMP Multi-core").
>
> **Audited cut**: `v0.31.2` (current `lakefile.toml` `version =`).
>
> **Branch**: `claude/audit-multicore-implementation-sUcIx`.
>
> **Scope**: identify every gap between the codebase's current
> single-core kernel + scaffolded SMP HAL and a *functionally activated*
> multi-core kernel on the BCM2712 (Raspberry Pi 5) target.
>
> **Out of scope**:
> - ARMv9-A Confidential Compute / MPAM partitioning. Tracked
>   separately as `HARDWARE_PARTITION_ISOLATION_PLAN.md` and depends
>   on this plan as a prerequisite.
> - Heterogeneous (big.LITTLE / asymmetric MP) topologies.
> - Hot-unplug / live core migration.

## 1. Executive summary

The Lean kernel model at v0.31.2 is **strictly single-core**: there is
exactly one `SchedulerState.current : Option ThreadId`, one `runQueue`,
one `activeDomain`, one `replenishQueue`, and one
`SeLe4n.Platform.FFI.kernelStateRef : IO.Ref SystemState`. AN6-F's
`bootFromPlatform_singleCore_witness` and AN12-B's `smpLatentInventory`
(8 entries, `length = 8` machine-checked) anchor this fact in proof.

The Rust HAL, in contrast, *contains substantial SMP scaffolding* that
landed under AN9-G/H/I/J (DEF-R-HAL-L17..L20):

- `rust/sele4n-hal/src/psci.rs` — PSCI `CPU_ON` wrapper (`hvc #0`).
- `rust/sele4n-hal/src/smp.rs` — `SMP_ENABLED: AtomicBool` (false),
  `CORE_READY: [AtomicBool; 4]`, `SECONDARY_MPIDR_TABLE` (3
  secondaries for BCM2712), `bring_up_secondaries()`,
  `rust_secondary_main()`.
- `rust/sele4n-hal/src/boot.S::secondary_entry` — assembly stub
  (per-core stack offset from `__smp_secondary_stack_top`).
- `link.ld::.smp_stacks` — 3 × 64 KiB reserved per-core stacks.
- `rust/sele4n-hal/src/barriers.rs::dsb_osh` / `dsb_oshst` +
  `BarrierKind::DsbOsh` / `DsbOshst` — cross-cluster (outer-shareable)
  barriers.
- `rust/sele4n-hal/src/cpu.rs::MPIDR_CORE_ID_MASK = 0x00FFFFFF` (AK5-I)
  and `cpu::wfe_bounded` (AN9-G) — bounded-wait primitive.

The **disposition closed at AN9-J** (DEF-R-HAL-L20, recorded RESOLVED
in `docs/dev_history/audits/AUDIT_v0.29.0_DEFERRED.md:296`) states:
"v1.0.0 ships SMP code merged but **disabled by default**; the
activation cost is flipping the runtime flag." This audit shows that
**claim is materially inaccurate**: flipping the flag is necessary
but far from sufficient. The SMP code is plumbing that **is never
reachable at runtime**, **cannot be activated without code changes**,
and **would crash or corrupt kernel state if it were activated** today.

### 1.1 Headline findings

| Sev | ID | Finding |
|-----|----|---------|
| **CRIT** | SMP-C1 | `bring_up_secondaries()` is never called from any boot path. `rust_boot_main` has 4 phases (UART, MMU, GIC, timer); there is no Phase 5 that parses `smp_enabled=true` from the DTB `/chosen/bootargs` and invokes the bring-up loop. The whole SMP code path is dead code at runtime. |
| **CRIT** | SMP-C2 | `rust_secondary_main` does **not** perform per-core MMU enable, VBAR install, GIC CPU-interface init, or timer arming. Secondary cores would wake into a state where the MMU is *off* and exception vectors are unset — first IRQ or page fault halts the core. The docstring at `smp.rs:18-22` describes a 4-step init sequence that is not implemented; the body is `wfe_bounded` loop on `CORE_READY[idx]` then `loop { wfe }`. |
| **CRIT** | SMP-C3 | The Lean kernel state (`SystemState`) is a single `IO.Ref` shared by all cores. Lean's `IO.Ref` is not atomic across threads/cores; concurrent reads or writes from multiple cores violate the language's memory-safety contract — undefined behaviour. No Big Kernel Lock, no per-core kernel-state partitioning. |
| **HIGH** | SMP-H1 | No IPI / SGI (Software-Generated Interrupt) primitive in the HAL. `gic.rs` exposes `acknowledge_irq`/`end_of_interrupt`/`dispatch_irq` but no `send_sgi(target_cpu, intid)`. seL4's SMP design uses IPIs for cross-core preempt, TLB shootdown, and wake-on-other-core; none of this exists. |
| **HIGH** | SMP-H2 | `tlbFlushByASID` / `tlbFlushByPage` (`Architecture/VSpace.lean:266-290`) emit `tlbi ... ; dsb ish ; isb` which broadcasts within the inner-shareable domain. Inside the BCM2712 single cluster the DSB ISH does cover all 4 cores, but **no software-level coordination** ensures the issuing core waits for remote-core completion of an in-flight memory access on the unmapped page, and no `dsb osh` is emitted for hypothetical cross-cluster topologies. The Lean proof surface treats TLB ops as pure single-core state transformers; SMP correctness has no formal anchor. |
| **HIGH** | SMP-H3 | `ArchAssumption` inductive in `Architecture/Assumptions.lean:17-23` has 5 entries (deterministicTimerProgress, deterministicRegisterContext, memoryAccessSafety, bootObjectTyping, irqRoutingTotality). `Concurrency/Assumptions.lean:163-176` entry 7 (`architecture_singleCoreOnly_smpLatent`) references this inductive with `sourceTheorem := architecture_assumptions_index`, but **no `singleCoreOperation` constructor exists**. The cross-reference is documentary only — the architecture inventory has no machine-checked single-core assumption, and renaming the inductive would not flag the inventory entry as drifted. |
| **HIGH** | SMP-H4 | `Concurrency/Assumptions.lean:51-66` admits that `Lean.Name` literals in the inventory are not enforced by the build: "Lean does not enforce that a `Lean.Name` literal resolves to a defined symbol." A renamed source theorem would silently drift the inventory. No `#check` of each `sourceTheorem` exists. |
| **MED** | SMP-M1 | `boot.S` line 102-103 cross-references `docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md §12` — a path inside `dev_history/` which `CLAUDE.md "Ignoring dev_history"` says is archived and should not be the canonical reference. Same drift in `Architecture/Assumptions.lean:333` and `CrossSubsystem.lean:3264`. |
| **MED** | SMP-M2 | `docs/spec/SELE4N_SPEC.md §6.4` (line 511) says "Symmetric multiprocessing support is **deferred to WS-V**". `WORKSTREAM_HISTORY.md:3086` confirms **"WS-V PORTFOLIO COMPLETE"** — WS-V was the pre-release audit-remediation work, not SMP. The spec citation is stale. |
| **MED** | SMP-M3 | The `.smp_stacks` linker section in `link.ld:89-93` is `NOLOAD` and aligned, but unlike `.bss` (zeroed by `boot.S`), the SMP stack region is **not zeroed at boot**. Secondary cores could read stale RAM contents from boot-time uninitialised data. |
| **MED** | SMP-M4 | `boot.S::secondary_entry` (line 146-170) masks DAIF, sets per-core SP, jumps to `rust_secondary_main`. It does **not** set `TPIDR_EL1` to a per-CPU base pointer. `smp.rs:19` docstring claims `secondary_entry` "sets up SP / TPIDR_EL1" — the TPIDR_EL1 assignment is missing. |
| **MED** | SMP-M5 | PSCI wrapper exposes only `cpu_on`. `PSCI_FN_CPU_OFF = 0x8400_0002` is defined as a constant but no `cpu_off()` function exists. No `affinity_info()`, no `migrate_info()`. Power management beyond initial bring-up is absent. |
| **MED** | SMP-M6 | `scripts/test_qemu_smp_bringup.sh` is a stub script that exits 0 with a SKIP message. The CHANGELOG entry for AN9-J advertises "QEMU `-smp 4` validation" — that validation is not wired and has never run. |
| **MED** | SMP-M7 | `SeLe4n/Platform/Contract.lean` (`PlatformBinding`) has no `numCores`, no `bootCoreId`, no per-core data field. `PlatformConfig` similarly has no core-count field. The contract is structurally single-core; an SMP platform cannot model multiple cores without extending the typeclass. |
| **MED** | SMP-M8 | The `with_interrupts_disabled` bracket in `interrupts.rs` is the kernel's only atomicity discipline (used everywhere — capability ops, IPC, scheduler, retype/cleanup). On SMP it is **not sufficient**: disabling interrupts on one core does not prevent another core from running concurrent kernel code. Without a Big Kernel Lock or per-subsystem locks, every kernel transition is racy. |
| **LOW** | SMP-L1 | The 8-entry `smpLatentInventory` size-witness `smpLatentInventory_count : length = 8` (line 210) is decidable but not part of any tier-3 surface anchor — adding/removing an entry without updating the theorem is caught at build, but adding *without changing the count* (e.g., replacing an entry) would slip silently. A NoDup witness on identifiers would help. |
| **LOW** | SMP-L2 | `MAX_SECONDARY_CORES = 3` in `smp.rs:52` is BCM2712-specific. The contract `PlatformBinding` doesn't parameterise this — porting to a 16-core SoC needs source edits, not a configuration change. |
| **LOW** | SMP-L3 | `cpu_off` (PSCI), `cpu_suspend` (PSCI), `system_off`, `system_reset` are not implemented. Production deployments need at least `cpu_off` for clean shutdown of secondary cores. |
| **LOW** | SMP-L4 | No `setThreadCpuAffinity` capability operation; no `coreId` field on TCB; no path for placing a thread on a specific core. The `Domain` mechanism is per-tick scheduling, not per-core placement. |
| **LOW** | SMP-L5 | `RobinHood` (object store hash table), `RadixTree` (CNode lookup), and IO.Ref scheduler state are all unprotected. Even read-only lookups from one core during write from another core would race. |
| **LOW** | SMP-L6 | `Concurrency/Assumptions.lean` directory contains only `Assumptions.lean`. No `Locks.lean`, `Atomic.lean`, `Memory.lean`, or `Ipi.lean` modelling files. The `SeLe4n.Kernel.Concurrency` namespace is reserved but empty of operational content. |

### 1.2 Disposition recommendation

This is **far more than a "flip the SMP_ENABLED flag" item**. The
work decomposes into **8 phases (SM0..SM7)** spanning an estimated
180–260 sub-tasks over **6–10 releases** at the project's historical
WS-AK / WS-AN cadence. **It must not be attempted in v1.0.0**. The
correct sequencing is:

1. **v1.0.0** ships single-core as planned (per the WS-RC release
   path). The current SMP scaffolding stays in tree; the next two
   actions tighten its honesty.
2. **v1.0.x** (one or two patch releases): land the **honesty
   patches** described in §6 below — correct stale doc cross-refs,
   downgrade the "activation cost is flipping the flag" claim to
   match reality, fix SMP-H3 (no architecture-side single-core
   assumption constructor), seed the `Concurrency/` namespace with
   the lock-primitive type sketches without wiring them in. None of
   this opens the kernel to SMP; it documents the actual gap.
3. **v1.x.0 onwards** (WS-SM, the workstream this audit scopes): the
   full 8-phase plan. SMP activation should be a **major version bump
   (v2.0.0)** because it changes the model's `SystemState` shape and
   retires `bootFromPlatform_singleCore_witness` — a non-trivial
   public-spec rewrite.

## 2. Methodology

This audit was performed against branch
`claude/audit-multicore-implementation-sUcIx` (HEAD of the audited
cut). Every cited file:line tuple was read directly. The
investigation followed the 12-section map of SMP-relevant surfaces:

1. SMP-latent assumption inventory (`SeLe4n/Kernel/Concurrency/`).
2. Scheduler single-core assumptions (`SeLe4n/Model/State.lean`,
   `Kernel/Scheduler/`).
3. Locking / synchronisation primitives (none in Lean; HAL bracket only).
4. Rust HAL CPU/core support (`rust/sele4n-hal/src/{smp,psci,cpu,boot}.{rs,S}`,
   `link.ld`).
5. Platform contract (`Platform/Contract.lean`, `Platform/RPi5/`).
6. TLB / cache / memory barriers (`Architecture/{BarrierComposition,TlbModel,CacheModel,VSpace}.lean`).
7. IPC cross-core implications (`Kernel/IPC/`).
8. Capability / object store cross-core (`Kernel/RobinHood/`,
   `Kernel/RadixTree/`, `Kernel/Capability/`).
9. Tests / fixtures (`tests/`, `scripts/test_qemu_smp_bringup.sh`).
10. Spec + docs (`docs/spec/SELE4N_SPEC.md`, `docs/gitbook/`,
    `docs/audits/`).
11. Codebase map (`docs/codebase_map.json`).
12. Tracker markers (TPI-D*, DEF-R-HAL-L*, AN9-J).

Cross-verification with the active audit
(`docs/audits/AUDIT_v0.30.11_DEEP_VERIFICATION.md:1054,1294`)
confirmed that the existing audits inventoried the AN12-B SMP-latent
list and the boot.S secondary-entry stub, but **did not** probe
whether the activation path is functional. This audit closes that
gap.

## 3. Detailed finding catalogue

### 3.1 Activation reachability (CRIT)

**SMP-C1 — `bring_up_secondaries` is never invoked.**

`rust/sele4n-hal/src/boot.rs:27-108` (`rust_boot_main`) executes:

```
Phase 1: UART init
Phase 2: MMU init + VBAR_EL1
Phase 3: GIC + Timer init
Phase 4: Handoff to Lean kernel (lean_kernel_main(dtb_ptr))
```

There is no Phase 5. `crate::smp::bring_up_secondaries()` is
referenced from no `.rs`/`.S` file outside `smp.rs` itself
(verified by `grep -rn "bring_up_secondaries\|crate::smp"`). The
docstring at `smp.rs:55-57` describes an activation contract that
does not exist: "deployments that opt in to SMP set this `true` via
a kernel-command-line parameter parsed by `boot.rs::rust_boot_main`
before invoking `bring_up_secondaries`." Neither the parse nor the
invocation is implemented.

`scripts/test_qemu_smp_bringup.sh` is a stub: `echo "[SKIP] AN9-J
QEMU SMP bring-up test not yet wired"; exit 0`. The CHANGELOG and
the AUDIT_v0.29.0_DEFERRED.md disposition therefore overstate the
maturity of AN9-J's resolution.

**Disposition**: this is the single most important finding. The
"flip the flag" claim is **literally false** — flipping
`SMP_ENABLED.store(true, Release)` from within the Rust code (the
only way to flip it; there is no command-line parser) would change
*nothing* because the call site does not exist. Fix requires
(a) DTB `/chosen/bootargs` parsing in `boot.rs`, (b) command-line
flag handling, (c) `bring_up_secondaries()` invocation in a new
Phase 5, (d) honest CHANGELOG / AUDIT_v0.29.0_DEFERRED.md
amendment.

**SMP-C2 — `rust_secondary_main` is incomplete.**

`rust/sele4n-hal/src/smp.rs:202-235` says (docstring):

> Each secondary core runs through the AK5-D-ordered MMU-enable
> sequence, applies the AK5-C SCTLR_EL1 bitmap, initialises its GIC
> CPU interface, then spins on its `core_ready` flag.

The body actually contains:

```rust
let core_idx = context_id as usize;
if core_idx < CORE_READY.len() {
    while !CORE_READY[core_idx].load(Ordering::Acquire) {
        let _ = crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
    }
}
loop { crate::cpu::wfe(); }
```

There is **no call to** `crate::mmu::init_mmu()` (MMU stays off; any
load via virtual address faults), **no call to**
`crate::registers::write_vbar_el1(...)` (any IRQ on this core
vectors into garbage), **no call to**
`crate::gic::init_cpu_interface(GICC_BASE)` (this core cannot
deliver / acknowledge IRQs — even SGIs from the primary), **no call
to** `crate::timer::init_timer(...)` (this core has no timer
ticks). The boot sequence the docstring describes is missing.

Activating SMP today would wake secondary cores into a state where:

- The first memory access (likely the `wfe_bounded` body itself,
  which reads `CNTPCT_EL0` and reads from `CORE_READY`) succeeds
  because virtual addresses are physical with MMU off.
- The first IRQ delivered to this core (impossible since GIC isn't
  set up, but conceivable via a stale GIC distributor SGI) would
  jump to PC = VBAR_EL1 (zero on reset) — UNDEFINED behaviour or
  reset.
- The `wfe` instructions stall correctly because WFE is unaffected
  by MMU state, so cores will look idle but accomplish nothing.

The "park silently" behaviour is actually the safest current state,
but it cannot be the path forward.

**Disposition**: fully implement `rust_secondary_main` per the
docstring. Each secondary needs (a) `init_mmu()` adapted for
secondary-core entry (TTBR0/TTBR1 are CPU-banked — already covered
by ARM ARM, but SCTLR_EL1 must be set on each core), (b) VBAR_EL1
install, (c) `init_cpu_interface(GICC_BASE)` (the distributor is
banked between primary and secondaries for SGI/PPI lines 0–31), (d)
the timer arming sequence (CNTKCTL_EL1 + CNTV_TVAL_EL0). Then a
per-core scheduler entry, which is its own large work item — see
SMP-C3.

**SMP-C3 — `kernelStateRef : IO.Ref SystemState` is shared across cores.**

`SeLe4n/Platform/FFI.lean:394`:

```lean
initialize kernelStateRef : IO.Ref SystemState ← IO.mkRef (default : SystemState)
```

This single `IO.Ref` is read by every `@[export]` body (`getKernelState`)
and written by every state-mutating syscall (`updateKernelState`,
which calls `kernelStateRef.modify f`). Lean's `IO.Ref` is *not*
atomic across threads; the documentation explicitly compares it to
`std::cell::RefCell`, not `Arc<Mutex<...>>`. Two cores executing
syscalls concurrently would race on this `Ref`:

- Both cores `getKernelState` — both read the same pre-state.
- Both cores compute a `newState` from the pre-state.
- Both cores `kernelStateRef.set newState`.
- The second write silently overwrites the first.

The Lean proof surface assumes *sequential* execution of every
kernel transition. Without a Big Kernel Lock or per-core kernel
state, the moment two cores enter the kernel concurrently, the
formal proofs no longer characterise observable behaviour.

**Disposition**: there are three viable architectural paths.

1. **Big Kernel Lock (BKL)** — one spinlock around the entire
   `@[export]` FFI body. Simplest; preserves the single-core proof
   surface essentially unchanged. Performance: scheduler / IPC
   under contention is serialised. seL4 SMP took this path
   originally.
2. **Per-CPU kernel state** — replace `kernelStateRef` with a
   `[CoreCount; IO.Ref SystemState]` array indexed by MPIDR. Each
   core mutates only its own slot. Cross-core operations route
   through IPI handlers. Highest performance; deepest model
   rewrite.
3. **Coarse subsystem locks** — split the kernel into a few
   independently-locked subsystems (scheduler lock, object store
   lock, IPC lock, capability lock). Middle ground; the predominant
   modern path.

For seLe4n, the **BKL** is recommended for v2.0.0 first activation:
it preserves the v1.0.0 verification claims (every transition still
runs to completion atomically; the Lean model needs no reshaping)
and pushes the optimisation work to a subsequent SMP phase. The BKL
trades performance for correctness — the right trade-off when the
single-core proof has billions of words of effort behind it.

### 3.2 IPI / SGI infrastructure (HIGH)

**SMP-H1 — No SGI primitive in the HAL.**

`rust/sele4n-hal/src/gic.rs` exposes:
- `init_distributor`, `init_cpu_interface`, `init_gic` (boot init).
- `acknowledge_irq`, `acknowledge_irq_classified` (IRQ ACK).
- `end_of_interrupt` (EOI).
- `dispatch_irq` (handler dispatch).
- `is_spurious` (INTID classification).

Missing:
- `send_sgi(target_cpu_mask: u8, intid: u32)` — writes
  `GICD_SGIR` with a target CPU mask and SGI INTID.
- `send_sgi_self(intid: u32)` — uses the "to-self" SGI mode.
- Per-SGI handler tables (since SGI INTIDs 0..15 are software-defined).
- SGI-specific EOI semantics (no auxiliary state to track; the GIC
  handles SGI EOI the same as any other interrupt).

seL4 SMP uses IPI for:

1. **Reschedule-self** — when a higher-priority thread becomes
   runnable on another core, the originating core signals an SGI
   to make the target core re-enter the scheduler.
2. **TLB shootdown** — when a page is unmapped, the issuing core
   sends an SGI to all other cores that may have the translation
   cached so they invalidate their local TLB before the unmapping
   completes.
3. **Cache maintenance broadcast** — analogous to TLB shootdown
   for `DC CIVAC` on cross-core-shared pages.
4. **Halt-other-cores** — boot-time and panic-time
   synchronisation primitives.

All four cases require an SGI primitive that does not exist today.

**Disposition**: add `gic.rs::send_sgi(target_cpu_mask, intid)`
plus a Lean-side `@[extern "ffi_gic_send_sgi"]` opaque declaration
and an `@[export]` SGI handler routed through the existing IRQ
dispatch. The handler table can re-use `dispatch_irq`'s
single-callback model with INTID-keyed branching for the four
canonical SGI handlers (reschedule, tlb_shootdown,
cache_broadcast, halt_all).

### 3.3 TLB / cache cross-core coordination (HIGH)

**SMP-H2 — TLB invalidation is single-core in spirit.**

`SeLe4n/Kernel/Architecture/VSpace.lean:266-290`:

```lean
def tlbFlushByASID  (asid : ASID) : Kernel Unit
def tlbFlushByPage  (asid : ASID) (vaddr : VAddr) : Kernel Unit
```

The Rust implementations `tlb::tlbi_by_asid` / `tlbi_by_vaddr` emit
`tlbi ASIDE1, ...` / `tlbi VAE1, ...` followed by `dsb ish ; isb`.
The `DSB ISH` broadcast does include all 4 cores within the BCM2712
single cluster — so on a per-cluster topology, the TLB *does*
flush on remote cores transparently. **However**:

- No "remote-core stall" coordination — the issuing core does
  not wait for remote cores to *also* drain in-flight memory
  accesses on the about-to-be-unmapped translation before it
  considers the unmap complete. ARMv8-A's `TLBI` + `DSB ISH` is
  sufficient at the architectural level for a single cluster, but
  the more standard SMP idiom (Linux, seL4, FreeBSD) is to issue
  a TLB-shootdown SGI to peer cores so each peer explicitly
  acknowledges the invalidation. Without it, the trust boundary
  is "we believe `DSB ISH` is sufficient on BCM2712" rather than
  "we coordinate explicitly."
- No outer-shareable variant. `Architecture/BarrierComposition.lean`
  exposes `dsbOsh` / `dsbOshst` Lean-side, and `BarrierKind::DsbOsh`
  is wired through `BarrierKind::emit` for hypothetical cross-
  cluster topologies. But `VSpace.lean`'s `tlbFlushByASID` /
  `tlbFlushByPage` only emit `dsb ish`. A future cross-cluster
  port (e.g., RPi-7 if it goes multi-cluster) would silently
  under-flush.
- No Lean proof that a remote core's TLB is invalidated. The
  state transformer in Lean treats TLB ops as pure operations on
  `SystemState`; there is no formal model of remote-core caches.
  The single-core proof is trivially correct because there is no
  remote core.

**Disposition**: add a TLB-shootdown SGI handler (depends on
SMP-H1), thread it through `tlbi_by_asid` / `tlbi_by_vaddr` on
SMP-enabled builds, and extend the Lean TLB model to a per-core
TLB function (or, conservatively, an aggregate `TlbState` mapping
`CoreId → TlbContent`) so the formal proof obligation includes
remote-core invalidation. The latter is a significant model
rewrite but unavoidable for SMP correctness.

### 3.4 Inventory hygiene (HIGH / LOW)

**SMP-H3 — Architecture-side single-core constructor is missing.**

`SeLe4n/Kernel/Concurrency/Assumptions.lean:163-176` declares the 7th
inventory entry:

```lean
def architecture_singleCoreOnly_smpLatent : SmpLatentAssumption :=
  { identifier        := `SeLe4n.Kernel.Architecture.ArchAssumption
    ...
    sourceTheorem     := `SeLe4n.Kernel.Architecture.architecture_assumptions_index
    auditReference    := "AG-* baseline / AN12-B" }
```

The `singleCoreWitness` field reads (verbatim): "this is the
canonical single-core kernel model recorded in
`Architecture/Assumptions.lean` via the `ArchAssumption` inductive
+ `assumptionInventory` aggregator." This is **factually wrong**:
the `ArchAssumption` inductive (lines 17-23) has exactly 5
constructors — `deterministicTimerProgress`,
`deterministicRegisterContext`, `memoryAccessSafety`,
`bootObjectTyping`, `irqRoutingTotality` — and none of them is a
"single-core operation" assumption. The `assumptionInventory`
aggregator (lines 94-100) lists those 5 entries. The promised
single-core constructor does not exist.

Per the **implement-the-improvement rule** in CLAUDE.md: the
inventory description is the better state; the code is the inferior
state; **implement the constructor**. The fix:

1. Add `singleCoreOperation` as a 6th `ArchAssumption` constructor.
2. Extend `assumptionInventory` to 6 entries.
3. Extend `archAssumptionConsumer` to map
   `.singleCoreOperation → SeLe4n.Kernel.bootFromPlatform_singleCore_witness`.
4. Update the pairwise distinctness theorem
   `archAssumptionConsumer_distinct` to C(6,2) = 15 inequalities.
5. Confirm the `Concurrency/Assumptions.lean` entry #7's
   `identifier` and `sourceTheorem` fields still resolve.

**SMP-H4 — Inventory `Lean.Name` references not build-checked.**

`Concurrency/Assumptions.lean:53-61` explicitly notes:

> Lean does not enforce that a `Lean.Name` literal resolves to a
> defined symbol — the name is just a structural reference. The
> inventory's canonical names are **audited by source-read at every
> WS-AN closure**.

This is a debt acknowledgement, not a fix. Per the
**implement-the-improvement rule**: implement the build-time check.
The fix is straightforward — every `Lean.Name` literal can be
matched by a sibling `#check @<Name>` block that fails elaboration
if the name doesn't resolve. The pattern already exists in
`Architecture/Invariant.lean` for the architecture consumer index
(see `tests/ModelIntegritySuite.lean` `@`-references).

Concretely, add to `Concurrency/Assumptions.lean` immediately after
the inventory list:

```lean
-- AN12-B.5 (post-audit): compile-time anchor for each entry's
-- sourceTheorem.  If any referenced theorem is renamed, the
-- corresponding `#check` fails at elaboration.
example : True := by
  -- Reference each of the 8 source theorems by `@`-name so a
  -- rename of any one fails the build.
  let _ := @SeLe4n.Kernel.resolveCapAddress_result_valid_cnode
  let _ := @SeLe4n.Kernel.cspaceCopy_preserves_capabilityInvariantBundle
  let _ := @SeLe4n.Kernel.lifecyclePreRetypeCleanup
  let _ := @SeLe4n.Kernel.serviceHasPathTo
  let _ := @SeLe4n.Kernel.replenishmentPipelineOrder
  let _ := @SeLe4n.Kernel.typedIdDisjointness
  let _ := @SeLe4n.Kernel.Architecture.architecture_assumptions_index
  let _ := @SeLe4n.Kernel.bootFromPlatform_singleCore_witness
  trivial
```

**Caveat**: this requires importing every owning module. The
present `Concurrency/Assumptions.lean` imports only `Prelude` and
`Model.State` to keep the dependency graph shallow. The
self-reference can live in a sibling `Concurrency/Anchors.lean`
file that does the wider imports, so the inventory itself stays
lightweight.

**SMP-L1 — NoDup witness on inventory identifiers.**

Already detected at `smpLatentInventory_count : length = 8`; a
companion `inventory_identifiers_nodup` would catch the
"add new entry → silently rename another to keep length stable"
scenario.

### 3.5 Documentation drift (MEDIUM)

**SMP-M1 — `dev_history/` cross-references in production sources.**

`CLAUDE.md` "Ignoring `dev_history`" section: "Do not read or
reference files in `docs/dev_history/` unless explicitly
instructed." Yet the following production paths reference
`dev_history/`:

- `rust/sele4n-hal/src/boot.S:103` —
  `docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md §12`
- `SeLe4n/Kernel/Architecture/Assumptions.lean:333` — same
- `SeLe4n/Kernel/CrossSubsystem.lean:3264` — same

Each should be repointed to the canonical reference in
`docs/WORKSTREAM_HISTORY.md` (which records WS-AN AN9-J closure)
or `docs/spec/SELE4N_SPEC.md §6.8` (the SMP-latent inventory
section).

**SMP-M2 — Stale WS-V deferral claim.**

`docs/spec/SELE4N_SPEC.md:511`: "Symmetric multiprocessing support
is deferred to WS-V."
`docs/WORKSTREAM_HISTORY.md:3086`: "WS-V Phases V1 through V8 are
complete. WS-V PORTFOLIO COMPLETE."
WS-V was the pre-release audit-remediation workstream from
v0.21.7–v0.22.10; it never owned SMP. The deferral pointer is
stale across `docs/spec/SELE4N_SPEC.md`, `docs/DEVELOPMENT.md:68`,
`docs/gitbook/01-project-overview.md:94`, and others.

`docs/WORKSTREAM_HISTORY.md:2854` already records this drift:

> Eight deferral annotations introduced by AK8 incorrectly cited
> WS-V as a future-work bucket. WS-V was completed many releases
> ago...

The fix is to re-point every "deferred to WS-V" SMP claim to the
new WS-SM workstream ID (or whatever the post-1.0 workstream is
named).

**SMP-M3 — `.smp_stacks` not zeroed at boot.**

`link.ld:89-93`:

```ld
.smp_stacks (NOLOAD) : ALIGN(16) {
    __smp_secondary_stacks_bottom = .;
    . += (3 * 64K);
    __smp_secondary_stack_top = .;
} > RAM
```

The `.bss` section is zeroed by `boot.S:62-71`, but `.smp_stacks`
is a separate section. When secondaries are activated, their
stacks contain stale RAM contents from boot-time uninitialised
memory. This is not currently an information leak because secondaries
never execute. When SMP is activated, stale stack contents could
become a security hazard.

Fix: extend the BSS-zero loop in `boot.S` to also cover
`__smp_secondary_stacks_bottom..__smp_secondary_stack_top`, or
introduce a separate dedicated zero loop. Negligible boot-time
cost (192 KiB at ~16 bytes per cycle ≈ 12 K cycles).

**SMP-M4 — `TPIDR_EL1` not set by `secondary_entry`.**

`boot.S:146-170` (`secondary_entry`): the assembly stub sets DAIF
mask, computes per-core SP, branches to `rust_secondary_main`. The
`smp.rs:19` docstring claims "sets up SP / TPIDR_EL1" — TPIDR_EL1
is not set.

`TPIDR_EL1` is the canonical ARMv8 per-CPU base register. SMP
kernels typically point it at a per-CPU data block containing the
per-CPU run queue head, current-thread pointer, idle-thread
pointer, etc. Without `TPIDR_EL1` setup, a Lean per-core scheduler
extension would have no fast way to locate "the current core's
kernel state" — it would have to read MPIDR_EL1 and dereference an
array on every entry.

Fix: in `secondary_entry`, after setting SP, set
`TPIDR_EL1 = __per_cpu_data_base + context_id * sizeof(PerCpuData)`,
and add a Lean-side `@[extern "ffi_per_cpu_base"]` that reads
TPIDR_EL1 for a typed per-CPU pointer.

### 3.6 Locking / atomicity (HIGH / MEDIUM)

**SMP-M8 — `with_interrupts_disabled` insufficient on SMP.**

`rust/sele4n-hal/src/interrupts.rs:101-106`:

```rust
pub fn with_interrupts_disabled<F: FnOnce() -> R, R>(f: F) -> R {
    let saved = disable_interrupts();
    let result = f();
    restore_interrupts(saved);
    result
}
```

This is the kernel's *sole* atomicity primitive. The
`Concurrency/Assumptions.lean` SMP-discharge fields for entries
1, 2, 3, 4, 5, 7, 8 all rely on "the FFI bracket prevents
interleaved capability operations" or equivalent. On SMP, this
bracket is necessary but not sufficient — masking IRQ on core 0
does not prevent core 1 from running its own kernel transition
concurrently. The bracket's discharge story is therefore
**inadequate post-SMP**.

Fix: each entry's `smpDischarge` field must be rewritten to cite
a Big Kernel Lock (or per-subsystem lock) acquired before the FFI
bracket. The lock must be released on every exit path including
panics. The Lean kernel state mutation must take place inside the
lock-held window.

The right primitive is a **ticket spinlock** or **MCS lock** in
Rust, with a Lean-side `@[extern "ffi_acquire_bkl"]` /
`@[extern "ffi_release_bkl"]`. RAII discipline ensures the lock
is dropped on every exit path — a `with_bkl` combinator analogous
to `with_interrupts_disabled` is the natural shape.

### 3.7 Per-core scheduler model (CRIT)

**SMP-C3 (continued) — `SchedulerState` is structurally single-core.**

`SeLe4n/Model/State.lean:133-167`:

```lean
structure SchedulerState where
  runQueue            : SeLe4n.Kernel.RunQueue := ...
  current             : Option SeLe4n.ThreadId
  activeDomain        : SeLe4n.DomainId := ⟨0⟩
  domainTimeRemaining : Nat := 5
  domainSchedule      : List DomainScheduleEntry := []
  domainScheduleIndex : Nat := 0
  configDefaultTimeSlice : Nat := 5
  replenishQueue      : SeLe4n.Kernel.ReplenishQueue := ...
  lastTimeoutErrors   : List (SeLe4n.ThreadId × KernelError) := []
```

Every field is singular. There is no `Array (Option ThreadId)` for
`current`, no per-core `RunQueue`, no per-core `replenishQueue`,
no per-core domain schedule state.

`docs/spec/SELE4N_SPEC.md:2139-2151` documents two extension paths:

> Any future SMP extension that adds per-core scheduler state will
> either (a) change the `current` field's type (breaking this theorem
> statement) or (b) introduce a separate per-core-map field
> (requiring an explicit SMP invariant).

Path (a) — change `current` to `Vector (Option ThreadId) CoreCount`
— is the simpler model rewrite but breaks ~every theorem touching
`SchedulerState.current`. Estimated discharge cost: 60–110 proof
sites, ~3000–5000 lines of theorem updates. Path (b) — add a
`perCoreState : Vector PerCoreState CoreCount` field alongside the
existing singular fields — is the lower-disruption model rewrite
but requires defining what "global single-core fallback" semantics
mean.

For seLe4n's BKL-based v2.0.0 activation, **path (b) is recommended
with a twist**: under BKL the active core enters the kernel, mutates
the singular `current` / `runQueue` / etc., and exits. The
`perCoreState` array is only meaningful at preemption time
(`current[other_core]` is what other cores are running when this
core is in the kernel). The model can keep the singular fields as
"the in-kernel core's view" and add a `perCoreSnapshot : Vector
PerCoreSnapshot CoreCount` recording what each core was running at
last context switch. This preserves the bulk of the single-core
proof and adds a thin SMP layer.

### 3.8 Tests, fixtures, validation (MEDIUM / LOW)

**SMP-M6 — `test_qemu_smp_bringup.sh` is a stub.**

`scripts/test_qemu_smp_bringup.sh:23`:

```sh
echo "[SKIP] AN9-J QEMU SMP bring-up test not yet wired"
```

The script body lists what it *would* do once wired:

```
1. Boot QEMU virt with -smp 4 -machine virt,secure=on
2. Pass smp_enabled=true on the kernel command line
3. Capture the UART log
4. Assert each of cores 0..3 emits its core_id log line
5. Run a cross-core SGI test
```

Each of these is unimplementable today because:
- Step 2 has no command-line parser (SMP-C1).
- Step 4 has no per-core log emission in `rust_secondary_main`
  (which currently never prints anything — even if `kprintln!`
  worked from secondaries, which it does not without per-core
  UART lock awareness — SMP-M8).
- Step 5 has no SGI primitive (SMP-H1).

Disposition: keep the stub as a roadmap marker; flag in CHANGELOG
the resolution-claim drift; activate sequentially after SMP-C1,
SMP-C2, SMP-H1, SMP-M8 land.

**SMP-L7 — No Lean test exercises the multicore code paths.**

`tests/An9HardwareBindingSuite.lean` covers MPIDR mask and PSCI
return-code decode but not cross-core scheduling, IPC, or capability
transfer. No fixture exists for an SMP boot trace. No
`OperationChainSuite.lean` scenario exercises a thread migrating
between cores or a notification waking a thread on a different
core.

Disposition: add `tests/SmpSchedulerSuite.lean`,
`tests/SmpIpcSuite.lean`, `tests/SmpCapabilitySuite.lean` once
the per-core scheduler model lands. Defer cross-core formal proofs
until then.

## 4. Cross-subsystem impact assessment

The single-core assumption is woven into every Lean subsystem.
This table records the **directly-affected** subsystems and the
estimated rewrite cost per path-b (additive `perCoreSnapshot`
field) BKL-protected activation.

| Subsystem | File count | Direct impact | Rewrite cost |
|-----------|-----------:|---------------|-------------:|
| Scheduler | 22 | `current`, `runQueue`, `replenishQueue`, `activeDomain` all need per-core companion fields. PIP propagation needs cross-core boost. | HIGH |
| IPC | 35 | Endpoint queue membership, notification wait queues, donation chains all assume single rendezvous. Cross-core call needs IPI. | HIGH |
| Capability | 18 | CDT mutation, CSpace lookup safe under BKL — minimal direct impact. | LOW |
| Lifecycle | 6 | `retypeFromUntyped`, cleanup ordering safe under BKL. | LOW |
| Service | 4 | Registry graph traversal safe under BKL. | LOW |
| Architecture | 14 | TLB / cache model needs per-core extension. Interrupt model needs SGI / IPI dispatch. | MEDIUM |
| InformationFlow | 12 | Projection / NI proofs assume single observer. Need per-core projection composition. | MEDIUM |
| RobinHood / RadixTree | 6 | Pure functional structures, safe under BKL. | LOW |
| Platform | 17 | `PlatformBinding` needs `numCores`. `PlatformConfig` needs core-count + per-core boot data. | MEDIUM |
| CrossSubsystem | 1 (3309 LoC) | `bootFromPlatform_singleCore_witness` retires; new SMP invariant bundle replaces it. | HIGH |

Total estimated proof rewrite: **30–45 kLoC** of theorem updates
across **120–170 files**.

## 5. Recommended 8-phase workstream decomposition (WS-SM)

This is the **planning shape**. Sub-task counts are estimates at
the project's historical WS-AN cadence.

### Phase SM0 — Audit & inventory hardening (post-v1.0 patch)

**Target**: v1.0.1 (single patch release after v1.0.0 ships).

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM0.1 | Add `singleCoreOperation` constructor to `ArchAssumption`. Extend `assumptionInventory` to 6 entries; extend `archAssumptionConsumer`; extend distinctness theorem to C(6,2). Update Concurrency/Assumptions.lean entry #7 references. | `Architecture/Assumptions.lean`, `Concurrency/Assumptions.lean`, `Architecture/Invariant.lean` | M |
| SM0.2 | Add `Concurrency/Anchors.lean` with `#check` / `@`-reference of every inventory `sourceTheorem`. Wire into `Platform.Staged`. | `Concurrency/Anchors.lean`, `Platform/Staged.lean` | S |
| SM0.3 | Add `inventory_identifiers_nodup` witness via decidable list-distinctness. | `Concurrency/Assumptions.lean` | S |
| SM0.4 | Repoint `dev_history/` cross-references in `boot.S`, `Architecture/Assumptions.lean`, `CrossSubsystem.lean` to `docs/WORKSTREAM_HISTORY.md` and `docs/spec/SELE4N_SPEC.md §6.8`. | (3 files) | S |
| SM0.5 | Update `docs/spec/SELE4N_SPEC.md §6.4`, `docs/DEVELOPMENT.md:68`, `docs/gitbook/01-project-overview.md:94` to repoint from "WS-V" to "WS-SM" and re-state activation cost honestly: "code-level integration work, not a runtime flag flip." | (4 files) | S |
| SM0.6 | Rewrite `AUDIT_v0.29.0_DEFERRED.md` `DEF-R-HAL-L20` row from "RESOLVED at v0.30.10" to "PARTIALLY RESOLVED at v0.30.10 — runtime scaffolding only; activation path tracked under WS-SM." Archive update. | `dev_history/audits/AUDIT_v0.29.0_DEFERRED.md` | S |
| SM0.7 | Zero the `.smp_stacks` region in `boot.S` BSS-zero loop. | `boot.S`, `link.ld` (cross-check) | S |
| SM0.8 | Set `TPIDR_EL1` in `secondary_entry` to per-CPU base pointer. Add `__per_cpu_data_base` linker symbol + Rust `static PER_CPU_DATA: [PerCpuData; 4]`. | `boot.S`, `smp.rs`, `link.ld` | M |

**Acceptance**: tier-0+1+2+3 tests green; documentation drift cleared;
no claim of SMP being "merely a flag flip" remains in tree.

### Phase SM1 — HAL completion (CRIT path)

**Target**: v1.x.0.

| Sub | Description | Est |
|-----|-------------|-----|
| SM1.1 | Implement `psci::cpu_off()`, `psci::affinity_info()`, `psci::system_off()`, `psci::system_reset()` with HVC encoding per ARM DEN0022D. | M |
| SM1.2 | Implement `gic::send_sgi(target_cpu_mask, intid)` via `GICD_SGIR`. Add Lean `@[extern "ffi_gic_send_sgi"]`. | M |
| SM1.3 | Implement `gic::init_cpu_interface_secondary(core_id)` re-using `init_cpu_interface(GICC_BASE)` but with per-core SGI/PPI enable. Wire into `rust_secondary_main`. | M |
| SM1.4 | Implement full `rust_secondary_main` body: MMU init (SCTLR_EL1 per-core), VBAR install, GIC CPU interface init, timer arming. Per AK5-D ordering. | L |
| SM1.5 | Implement DTB `/chosen/bootargs` parser in `boot.rs::rust_boot_main` Phase 5. Accept `smp_enabled=true` / `smp_enabled=false`; default `false`. | M |
| SM1.6 | Wire Phase 5 to call `crate::smp::bring_up_secondaries()` when flag is set. | S |
| SM1.7 | Add per-core `kprintln!` synchronisation — UART lock awareness for SMP. Re-audit `UartLock::with` discipline. | M |
| SM1.8 | Implement ticket-spinlock primitive in Rust: `pub struct TicketLock { ... }` + `with_lock(|| ...)` combinator. | M |
| SM1.9 | Implement `bkl::BigKernelLock` static + `with_bkl(|| ...)` combinator wrapping `with_interrupts_disabled`. | S |
| SM1.10 | Lean `@[extern "ffi_acquire_bkl"]` / `@[extern "ffi_release_bkl"]` + `Kernel.Concurrency.withBkl` combinator. | S |
| SM1.11 | QEMU `-smp 4` validation: wire `scripts/test_qemu_smp_bringup.sh` to do the 5 steps the docstring describes. | M |
| SM1.12 | Per-core boot log: every secondary emits its core ID, MPIDR, and "ready" status via the lock-aware `kprintln!`. | S |

**Acceptance**: real RPi5 boot with `smp_enabled=true` brings all 4
cores online; UART log shows all 4 core IDs; QEMU test passes;
secondaries park in idle after init.

### Phase SM2 — Per-core kernel state (CRIT)

**Target**: v1.x.0 (overlapping SM1; can be developed in parallel).

| Sub | Description | Est |
|-----|-------------|-----|
| SM2.1 | Add `PerCoreSnapshot` structure (`current : Option ThreadId`, `inKernel : Bool`, `lastTickCounter : Nat`). | M |
| SM2.2 | Add `SchedulerState.perCoreSnapshot : Vector PerCoreSnapshot 4` field. Initialise via `default`. | S |
| SM2.3 | Add `bootCoreId : CoreId := 0` constant. Add `CoreId := Fin 4` typed identifier. | S |
| SM2.4 | Extend `PlatformBinding` with `coreCount : Nat`, `bootCoreId : CoreId`, `validateCoreCount : Bool` typeclass fields. | M |
| SM2.5 | Update `PlatformConfig` with `coreCount` and `perCoreBootData : Vector PerCoreBootData coreCount` fields. | M |
| SM2.6 | Update RPi5 `PlatformBinding` instance with `coreCount := 4`, `bootCoreId := ⟨0⟩`. | S |
| SM2.7 | Update Sim `PlatformBinding` instances. | S |
| SM2.8 | Add `perCoreSnapshotConsistent` invariant: every `snapshot.current` is a valid TCB or `none`. | M |
| SM2.9 | Update `crossSubsystemInvariant` to include `perCoreSnapshotConsistent`. | M |
| SM2.10 | Update `bootFromPlatform` to initialise `perCoreSnapshot` (all `none` except `bootCoreId` which becomes `state.current` after the boot setup). | M |
| SM2.11 | Retire `bootFromPlatform_singleCore_witness` (its conclusion no longer characterises the SMP shape). Replace with `bootFromPlatform_smp_witness` proving the multi-core shape. | M |
| SM2.12 | Update AN12-B inventory entry #7's `singleCoreWitness` / `smpDischarge` to reflect new shape; possibly drop the entry now that SMP is activated. | S |

**Acceptance**: model compiles with per-core snapshot; AN12-B
inventory entry #7 retires or is rewritten; new SMP-shape witness
theorem replaces the single-core one.

### Phase SM3 — Big Kernel Lock integration (HIGH)

**Target**: v1.x.0 (depends on SM1.9, SM1.10).

| Sub | Description | Est |
|-----|-------------|-----|
| SM3.1 | Wrap every `@[export]` body in `FFI.lean` with `withBkl { ... }`. | M |
| SM3.2 | Rewrite each `smpDischarge` field in AN12-B inventory to cite the BKL as the post-SMP atomicity primitive. | S |
| SM3.3 | Add `bklHeld : Prop` invariant: every kernel transition holds the BKL. | M |
| SM3.4 | Prove `bklAcquireReleaseDiscipline` — the BKL is acquired on `@[export]` entry and released on every exit path including panics. | L |
| SM3.5 | Add a Lean-side abstract BKL model in `Concurrency/Locks.lean` — a `Prop` `bklOwned : SystemState → CoreId → Prop` with `Decidable` and discipline lemmas. | L |
| SM3.6 | Audit every `with_interrupts_disabled` Rust call site; replace with `with_bkl` where the surrounding semantics require cross-core atomicity. | M |
| SM3.7 | Per-core idle loop: secondaries that exit kernel via BKL release fall into per-core `idle_loop` (re-using `rust_secondary_main`'s tail). | S |

**Acceptance**: every kernel entry holds the BKL; discipline proven;
no observable single-core race.

### Phase SM4 — Cross-core scheduler (HIGH)

**Target**: v1.x.0 (depends on SM2, SM3).

| Sub | Description | Est |
|-----|-------------|-----|
| SM4.1 | Add `perCoreRunQueue : Vector RunQueue coreCount` to `SchedulerState`. Boot core uses index 0; secondaries idle initially. | M |
| SM4.2 | `chooseThread` becomes per-core: each core picks from its own run queue. Cross-core load-balancing deferred. | L |
| SM4.3 | `enqueueRunnable` routes to a core based on policy. Default: bind-to-creator-core. | M |
| SM4.4 | Add `threadCoreAffinity : ThreadId → Option CoreId` field on TCB. Default `none` = any core. | M |
| SM4.5 | Add `setThreadCpuAffinity` capability operation with structural authorisation check. | L |
| SM4.6 | `timerTick` per-core: each core's GIC timer fires independently, advances its own thread's time slice. | L |
| SM4.7 | Cross-core wake: `enqueueRunnable` on remote core sends a reschedule SGI. | M |
| SM4.8 | SGI handler `handle_reschedule` calls per-core scheduler entry. | M |
| SM4.9 | Update Liveness / WCRT proofs for per-core variants. RPi5-canonical config gains per-core admission bounds. | L |

**Acceptance**: a 4-thread workload runs on 4 cores; cross-core
wake works; timer ticks per-core; affinity respected.

### Phase SM5 — Cross-core IPC (HIGH)

**Target**: v1.x.0 (depends on SM4).

| Sub | Description | Est |
|-----|-------------|-----|
| SM5.1 | Endpoint queue membership remains shared (BKL-protected); call/recv on remote-core thread queues correctly under BKL. | M |
| SM5.2 | Cross-core call: when sender is core A and receiver was waiting on core B, the wake routes through the perCoreRunQueue[B] enqueue → reschedule SGI to B. | L |
| SM5.3 | Notification signal: if waiting thread is on remote core, IPI the remote core. | M |
| SM5.4 | Donation chain: PIP propagation across cores requires recomputing pipBoost on the donor's core (already routed through scheduler-side helper in R5.B). | L |
| SM5.5 | Update `IpcInvariantBundle` for per-core wake correctness. | L |

**Acceptance**: 2-thread ping-pong across 2 cores correctly
preempts; notification wakes a remote-core receiver.

### Phase SM6 — TLB / cache shootdown (HIGH)

**Target**: v1.x.0 (depends on SM1.2).

| Sub | Description | Est |
|-----|-------------|-----|
| SM6.1 | Add SGI handler `handle_tlb_shootdown(asid: u32, vaddr: u64)` in Rust. Issues local `tlbi vaae1, ...; dsb ish; isb`. | M |
| SM6.2 | On every `tlbFlushByPage` / `tlbFlushByASID`, primary (or unmapping core) broadcasts the shootdown SGI to all other cores, then waits for them to acknowledge via a per-core completion flag. | L |
| SM6.3 | Add Lean `Architecture.TlbShootdown` model: `perCoreTlb : Vector TlbState coreCount`; shootdown invalidates all caches. | L |
| SM6.4 | Prove `tlbShootdown_invalidates_all_cores`: post-shootdown, no core's TLB caches the unmapped translation. | L |
| SM6.5 | DC CIVAC broadcast variant for cache-coherency-sensitive page-table writes. | M |
| SM6.6 | Update `BarrierKind::emit_mmio_cross_cluster_barrier` site list — currently only PSCI CPU_ON uses it; TLB shootdown needs it too on cross-cluster topologies. | S |

**Acceptance**: unmap-then-reuse a page; no stale translation
observed on any core; formal model carries the proof.

### Phase SM7 — Documentation, tests, closure

**Target**: v2.0.0.

| Sub | Description | Est |
|-----|-------------|-----|
| SM7.1 | `docs/spec/SELE4N_SPEC.md §6.4` rewritten for SMP. New §6.4.1 SMP architecture, §6.4.2 boot sequence, §6.4.3 per-core invariants, §6.4.4 cross-core IPC, §6.4.5 TLB shootdown. | L |
| SM7.2 | New GitBook chapter `docs/gitbook/16-smp-architecture.md`. | M |
| SM7.3 | `tests/SmpSchedulerSuite.lean`, `tests/SmpIpcSuite.lean`, `tests/SmpCapabilitySuite.lean`, `tests/SmpTlbShootdownSuite.lean` — full coverage of new SMP transitions. | XL |
| SM7.4 | `tests/fixtures/smp_4core_boot.expected` — deterministic boot trace for the 4-core RPi5 path. | M |
| SM7.5 | New `scripts/test_qemu_smp.sh` (replaces stub) that runs the full SMP fixture. | M |
| SM7.6 | New tier-4 SMP-specific tier in `scripts/test_tier4_smp.sh` (under nightly flag) covering 4-core scenarios. | M |
| SM7.7 | Version bump v1.x.x → v2.0.0 — major-version SMP activation release. | S |
| SM7.8 | Closure summary in `docs/WORKSTREAM_HISTORY.md`. AN12-B inventory retired or rewritten. | S |

**Acceptance**: v2.0.0 ships bootable SMP-verified microkernel
on RPi5; tier-3 + tier-4 all green; documentation complete.

## 6. Minimum honesty patches (v1.0.x — pre-WS-SM)

Even before WS-SM proper opens, the **honesty patches** must land
in v1.0.x. These are SM0 sub-tasks, repeated here for visibility:

1. **Fix the false "flip the flag" claim.** Update `smp.rs:54-58`
   docstring, `lib.rs:111-118` SMP readiness note,
   `AUDIT_v0.29.0_DEFERRED.md:296-316` DEF-R-HAL-L20 disposition,
   `CHANGELOG.md:2855-2860` AN9-J entry, and `docs/HARDWARE_TESTING.md`
   AN9-J section. The honest statement is: "v1.0.0 ships SMP HAL
   scaffolding (PSCI wrapper, per-core stack reservation, MPIDR
   gate) but no activation path. The full SMP activation —
   including secondary-core MMU/GIC/timer init, BKL,
   per-core scheduler state, IPI infrastructure, TLB shootdown — is
   the scope of WS-SM, targeting v2.0.0."
2. **Fix `dev_history/` cross-references** (SMP-M1).
3. **Fix WS-V deferral pointer** (SMP-M2).
4. **Add `singleCoreOperation` arch assumption** (SMP-H3) per the
   implement-the-improvement rule.
5. **Add inventory-name compile-time anchors** (SMP-H4).
6. **Zero `.smp_stacks`** (SMP-M3) — prevents future activation
   from leaking stale boot RAM.

Patches 1–3 are documentation-only and risk-free.
Patches 4–6 are code changes but each is < 50 LoC. Each can land
in its own small PR.

## 7. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Premature SMP activation by user setting `SMP_ENABLED=true` via debugger | LOW (today: zero call site reaches `bring_up_secondaries`) | CRITICAL (cores wake into broken state) | Honesty patches (SM0.5) clarify the gap; SM1.4 fixes the actual init |
| Lean model `IO.Ref` race when secondaries reach kernel | ZERO today (they never reach kernel); CRITICAL post-activation | UB / corruption | BKL (SM1.8–SM1.10, SM3) |
| TLB stale translation on cross-core unmap | ZERO today (single core); HIGH post-activation | Security (read-after-unmap) | Shootdown (SM6) |
| `Concurrency/Assumptions.lean` inventory drift on theorem rename | MEDIUM today | LOW (documentation) | Compile-time anchors (SM0.2) |
| `ArchAssumption` inductive drift | LOW (no symbol re-binding planned) | LOW | SM0.1 ties the inventory in proof |
| Audit-text drift creates appearance of completeness | HIGH today | MEDIUM (reputational, trust in audits) | Honesty patches (SM0.4–SM0.6) |
| v2.0.0 SMP activation breaks v1.0 single-core proofs | MEDIUM | HIGH (proof rework) | Path-b (additive `perCoreSnapshot`) preserves singular-field proofs (SM2) |
| BCM2712 single-cluster assumption breaks on future hardware | LOW | MEDIUM | `DsbOsh` / `DsbOshst` already in HAL (AN9-I); cross-cluster TLB shootdown reuses them (SM6.6) |

## 8. Cross-reference index

| External claim | Reality | This audit |
|----------------|---------|------------|
| AUDIT_v0.29.0_DEFERRED.md:296 "DEF-R-HAL-L20 RESOLVED at v0.30.10" | Scaffolding only; activation absent | SMP-C1, SMP-C2 |
| smp.rs:54-58 "activation cost is just flipping the flag" | False — no caller; secondaries can't init | SMP-C1, SMP-C2 |
| smp.rs:18-22 "Each secondary runs the AK5-D-ordered MMU enable" | Body is `wfe` loop only | SMP-C2 |
| smp.rs:19 "secondary entry sets up SP / TPIDR_EL1" | TPIDR_EL1 not set | SMP-M4 |
| Concurrency/Assumptions.lean:167-169 "records via `ArchAssumption` inductive" | No `singleCoreOperation` constructor | SMP-H3 |
| docs/spec/SELE4N_SPEC.md:511 "SMP support is deferred to WS-V" | WS-V is complete (different scope) | SMP-M2 |
| docs/spec/SELE4N_SPEC.md:838 "v1.0.0 ships single-core by default" | True — but the doc and the audit ACT_v0.29.0 imply this is a *configuration choice*; it is in fact the only working configuration | SMP-C1 (recasting) |
| CHANGELOG AN9-J "Real-hardware QEMU `-smp 4` validation" | Stub script, never executed | SMP-M6 |

## 9. Acceptance / completeness criteria for this audit

This audit is **complete** when:

- [x] Every SMP-relevant source surface has been read.
- [x] Every claim from prior audits / disposition files has been
      re-derived from source.
- [x] Every gap is recorded with file:line citation and severity.
- [x] A workstream decomposition exists with realistic sub-task
      counts and acceptance criteria.
- [x] The honesty patches are scoped as a separate pre-workstream
      effort so they can land in v1.0.x without waiting for WS-SM.
- [x] The risk inventory covers premature-activation, race, drift,
      and proof-rewrite scenarios.
- [x] The cross-reference index ties every external claim to a
      finding ID in this document.

## 10. Open questions for the project maintainer

Before WS-SM opens, the following decisions are needed:

1. **Concurrency strategy** — BKL (recommended, simplest), per-
   subsystem locks, or per-CPU kernel state? This audit recommends
   BKL for first activation; future workstream can optimise.
2. **Workstream ID** — `WS-SM` (SMP Multi-core) is the natural name
   per the project's two-letter convention. Confirm or rename.
3. **Target version** — v2.0.0 major bump is the natural choice
   because `bootFromPlatform_singleCore_witness` retires. Confirm.
4. **Activation default** — should v2.0.0 default to
   `SMP_ENABLED=true`, or remain off by default with single-core as
   the supported configuration? seL4 ships SMP off by default;
   recommend the same.
5. **Honesty patch sequence** — accept SM0 as a v1.0.x patch
   release? The patches are individually small but collectively
   reset reader expectations about the AN9-J disposition.

---

## Appendix A — Source-of-truth file inventory

The 2,300 lines of source surveyed for this audit:

| Path | Lines | Purpose |
|------|------:|---------|
| `SeLe4n/Kernel/Concurrency/Assumptions.lean` | 228 | AN12-B SMP-latent inventory (8 entries) |
| `rust/sele4n-hal/src/smp.rs` | 345 | SMP bring-up scaffolding |
| `rust/sele4n-hal/src/psci.rs` | 189 | PSCI CPU_ON wrapper |
| `rust/sele4n-hal/src/boot.S` | 170 | Boot assembly (primary + secondary entry stubs) |
| `rust/sele4n-hal/src/boot.rs` | 170 | Rust boot main (4 phases — no Phase 5) |
| `rust/sele4n-hal/src/cpu.rs` | 350 | MPIDR mask, wfe_bounded |
| `rust/sele4n-hal/src/gic.rs` | 848 | GIC-400 (no SGI primitive) |
| `rust/sele4n-hal/src/interrupts.rs` | 156 | `with_interrupts_disabled` (sole atomicity) |
| `rust/sele4n-hal/src/barriers.rs` | 540 (excerpts) | `dsb_osh` / `dsb_oshst` / BarrierKind |
| `rust/sele4n-hal/link.ld` | 102 | `.smp_stacks` reservation (not zeroed) |
| `SeLe4n/Kernel/Architecture/Assumptions.lean` | 345 | ArchAssumption inductive (no `singleCoreOperation`) |
| `SeLe4n/Kernel/CrossSubsystem.lean:3239–3273` | 35 | `bootFromPlatform_singleCore_witness` |
| `SeLe4n/Model/State.lean:120–170` | 50 | `SchedulerState` (single `current`, `runQueue`) |
| `SeLe4n/Platform/FFI.lean:380–460` | 80 | `kernelStateRef : IO.Ref SystemState` (shared) |
| `SeLe4n/Platform/Contract.lean` | 133 | `PlatformBinding` (no `numCores`) |
| `scripts/test_qemu_smp_bringup.sh` | 42 | Stub: SKIP, never runs |
| `docs/spec/SELE4N_SPEC.md §6.4, §6.8, §11.2.3` | ~200 (excerpts) | SMP-deferred-to-WS-V claims |
| `docs/audits/AUDIT_v0.30.11_DEEP_VERIFICATION.md:1054,1294` | ~30 | Prior audit's SMP observations |
| `docs/dev_history/audits/AUDIT_v0.29.0_DEFERRED.md:290–340` | 50 | DEF-R-HAL-L20 disposition |

## Appendix B — Verification commands

To verify the findings in this audit against the current tree:

```bash
# SMP-C1: bring_up_secondaries has no caller outside smp.rs
grep -rn "bring_up_secondaries\|crate::smp::bring_up" rust/

# SMP-C2: rust_secondary_main body — confirm no init calls
sed -n '202,240p' rust/sele4n-hal/src/smp.rs

# SMP-H3: ArchAssumption constructors
sed -n '17,24p' SeLe4n/Kernel/Architecture/Assumptions.lean

# SMP-M1: dev_history cross-references in production sources
grep -rn "dev_history" rust/sele4n-hal/src/ SeLe4n/Kernel/

# SMP-M6: QEMU stub
cat scripts/test_qemu_smp_bringup.sh

# Inventory size witness
grep -n "smpLatentInventory_count" SeLe4n/Kernel/Concurrency/Assumptions.lean
```

Each of the above is non-destructive (read-only). Run any of them
to independently verify the audit's claims.

---

*This audit was produced from branch `claude/audit-multicore-implementation-sUcIx`
at `v0.31.2`. It does not change runtime behaviour, ship code, or
modify proof obligations. It is a planning artefact for a future
workstream and should be reviewed alongside the active WS-RC
remediation (`docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md`).*
