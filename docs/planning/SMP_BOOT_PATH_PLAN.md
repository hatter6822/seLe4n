# WS-BP — The bare-metal boot path

> **Status**: **PLANNED — BLOCKED on WS-RR.**  Registered at `v0.34.59`
> by WS-RR RR7.5 + RR7.15 (register §6 findings 19, 40–44).  No sub-task
> has started.
>
> **Workstream**: WS-BP
> **Produces**: the content of **SM10.1**
> ([`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md) §3), whose
> `SM10.1.1` row — the `kernel8.img` packaging — is this workstream's BP5.3
> deliverable seen from the release cut's side
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Blocked on**: **WS-RR** ([`SMP_RELEASE_READINESS_PLAN.md`](SMP_RELEASE_READINESS_PLAN.md)) —
> WS-BP must not open until RR8 closes
> **Consumed by**: SM10.2 (documentation), SM10.3 (the test suites that boot
> the kernel), SM10.5 (release validation) — every one of them takes an image
> **Audited cut**: `v0.34.3`
> ([`UNFINISHED_SMP_WORK.md`](UNFINISHED_SMP_WORK.md) §2.2)
> **Calendar estimate**: **9–20 weeks**, the figure
> [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md) §1.1 derives
> from a sized breakdown; this plan sequences that breakdown without
> re-pricing it
> **Sub-task count**: 38 across 8 phases (BP1..BP8), each phase numbered in
> execution order

## 1. Why this plan exists

Register finding 42: *"SM10's stated scope contradicts the obligations SM10.1
has accumulated"*.  SM10 is a release cut — documentation, test suites, a
version bump — and SM10.1 is a **bare-metal Lean runtime port**.  Those are
different kinds of work, priced differently, sequenced differently, and
reviewed differently, and holding them in one phase produced a plan whose
§1 goal sentence ("all substantive SMP work is complete") was false of its
own first phase.

The remedy the register names is to split SM10.1 out with a proper PR
sequence.  [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md)
§1.1 sized the port at RR1.11 and deliberately did **not** number it, for a
reason worth restating because it shapes this document:

> Numbering rows 2–13 as sub-tasks of SM10.1 would move the image build off
> `SM10.1.1`, and `SM10.1.1` is bound to "the image build" by three
> `CHANGELOG.md` entries […] The two rules collide: *numbering is execution
> order* wants the port first, *IDs in CHANGELOG entries are frozen* wants
> `SM10.1.1` unchanged.

**This plan resolves the collision by taking its own prefix**, which is the
resolution that note itself names ("a restructuring of SM10, with its own
prefix and no repurposed ID").  `SM10.1.1` keeps its meaning — the image
packaging, the deliverable the release cut consumes — and every citation of
it stays true.  WS-BP numbers the work that produces that image, in
execution order, under `BP1..BP8`.  Nothing is renumbered; something is
numbered that never was.

## 2. What does not exist at HEAD

Measured, not assumed — the register's §2.2 table, re-verified at `v0.34.59`:

| Required | State |
|----------|-------|
| A bootable binary target | `rust/` has **no `[[bin]]`** except `src/bin/rw_lock_oracle.rs`, a host test oracle |
| Lean → aarch64 object code | `lakefile.toml` declares one **host** `[[lean_lib]]` and 70 **host** `[[lean_exe]]`s; no `precompileModules`, no cross rule |
| `libsele4n.a` for aarch64 | Nothing produces it, though `rust/sele4n-hal/src/boot.rs` asserts it is linked |
| Bare-metal Lean runtime hosting | Zero occurrences of `lean_initialize_runtime_module` / `lean_io_mark_end_initialization` anywhere in the tree |
| `@[export] lean_kernel_main` | **Absent**; `check_kernel_entry_exports.py` carries it as the one reconciled `EXPECTED_UNRESOLVED` entry |
| An RPi5 `PlatformConfig` | **Absent**: no `rpi5PlatformConfig`, no root task, no initial objects |
| A real context switch | `ffi_switch_to_thread` stores a `u64` into an atomic; TTBR0 is never rebound |
| A core marked ready | **None**: every seam behind `lean_ready` degrades to its Rust-only half |

What *does* exist, and is the reason this is a port rather than a project:
the HAL compiles and lints for `aarch64-unknown-none` in both profiles, all
three `.S` sources assemble, and `_start`, `secondary_entry` and
`__exception_vectors` are present in the assembled archive (WS-RR RR1,
`v0.34.41`).  The verified kernel above it is complete for SMP through SM9.

## 3. Dependencies

- **WS-RR** must close first.  WS-BP consumes RR7.14's cancellation/timeout
  error-frame **staging** at BP7.5, and the whole of RR7's fine-lock work is
  a prerequisite for the WCRT claims BP8 validates.
- **SM2 / SM5.I** supply the kernel-entry lock BP4.2's install ordering must
  respect.
- **WS-RA** supplies the staged return frame BP7 delivers; its two named
  obligations are BP7.5 and BP7.6 (register finding 32).
- Nothing in WS-BP may be started before its own lower-numbered phase, and
  no phase may overlap another: each one leaves the image in a state the
  next one boots.

## 4. Phase map

Phase number is execution order.  Every phase consumes only lower-numbered
phases, and the ordering is load-bearing rather than conventional: the link
in BP5 cannot resolve until BP4 defines the boot seam, the boot seam cannot
be written until BP3 supplies the configuration it boots, and BP3's
configuration cannot be elaborated into an image until BP1 emits Lean object
code for the target.

| Phase | Scope | Sub | Est |
|-------|-------|-----|-----|
| BP1 | aarch64 Lean object code — the cross-compile lane and `libsele4n.a` | 4 | L |
| BP2 | Bare-metal Lean runtime hosting — heap, shims, initialization, and the boot map the arena lives in | 6 | XL |
| BP3 | The RPi5 deployment — `PlatformConfig`, root task, labeling | 4 | L |
| BP4 | The boot seam — `lean_kernel_main` and its install ordering | 5 | L |
| BP5 | The bootable image — `[[bin]]`, the link, `kernel8.img` | 4 | M |
| BP6 | Per-core readiness — the five dormant seams go live | 3 | M |
| BP7 | The context restore — TTBR0, the full frame, delivery | 7 | XL |
| BP8 | First boot and bring-up — QEMU, then the board | 5 | XL |

## 5. Phases

### BP1 — aarch64 Lean object code (4 sub-tasks)

The kernel's proofs are Lean; the target has no libc and no host toolchain.
Everything downstream needs Lean object code for `aarch64-unknown-none`, so
this is first.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| BP1.1 | A Lake target emitting the production closure's Lean C output — the C for `SeLe4n.lean`'s import closure and nothing else, so a staged or test module cannot reach the image | `lakefile.toml` | M |
| BP1.2 | Cross-compile that C to `aarch64-unknown-none` with `leanc`/`clang`, `-ffreestanding`, no libc | `lakefile.toml`, `scripts/` | L |
| BP1.3 | Archive the objects as `libsele4n.a`, the name `rust/sele4n-hal/src/boot.rs` already asserts is linked, and add the CI lane that builds it | `lakefile.toml`, `.github/workflows/` | M |
| BP1.4 | Point `scripts/check_kernel_entry_exports.py` at the **cross** archive as well as the host one, so its `EXPECTED_UNRESOLVED` reconciliation decides the symbol set the image actually links.  Consumes BP1.3 | `scripts/check_kernel_entry_exports.py` | S |

**Acceptance**: `libsele4n.a` exists for `aarch64-unknown-none`, CI builds it
on every push, and the export gate reads it.

### BP2 — Bare-metal Lean runtime hosting (6 sub-tasks)

The largest single unknown in the workstream, and the one with no precedent
in this tree to calibrate against.  The Lean runtime expects a heap, a small
set of libc entry points, and an initialization handshake; the target
supplies none of them.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| BP2.1 | A kernel heap arena in the image's own memory, and the allocator behind `lean_alloc_small` / `lean_alloc_object` / the free paths.  Its extent is a boot-time constant the linker script places, not a runtime negotiation | `rust/sele4n-hal/src/`, `rust/sele4n-hal/link.ld` | L |
| BP2.2 | The libc surface the runtime calls — `memcpy`, `memset`, `memcmp`, `strlen` and whatever the measured link demands — as `no_std` definitions, derived from the *unresolved symbols of the BP1.3 archive* rather than from a guessed list | `rust/sele4n-hal/src/` | L |
| BP2.3 | `lean_initialize_runtime_module` and `lean_io_mark_end_initialization` called once, on the primary, before any Lean code runs.  Consumes BP2.1 and BP2.2 | `rust/sele4n-hal/src/boot.rs` | M |
| BP2.4 | Fail closed when initialization cannot complete: the primary parks with `cpu::fatal_halt()` rather than entering a kernel whose runtime is half-built.  Never a silent continue | `rust/sele4n-hal/src/boot.rs` | S |
| BP2.5 | A host witness suite for the shims and the allocator — the arena's bounds, exhaustion, alignment — since the first place they run for real is a board with no debugger attached | `rust/sele4n-hal/src/` | M |
| BP2.6 | **The boot map is built from constants, and the blob is parsed with translation on.**  `init_mmu` reads the firmware's device tree *before* the MMU is enabled — an attacker-influenced parser running in the window with no memory protection and no recovery but a halt — and it does so to obtain a RAM *size* the boot map does not need.  Build the map from what the boot actually stands on: the image `[_start, __bss_end)`, the primary and secondary stacks, BP2.1's arena, a bounded window at the firmware's DTB pointer, and the board's device window — every one a linker symbol or a board constant, and every one already enumerated by `boot_critical_ranges_mapped`, which is the map rather than a check on one.  Retires `ram_top_from_dtb`, `find_ram_top_in_dtb`, `clamp_ram_top`, `dtb_dereferenced_range` and `boot_ranges_mapped_under`, deleting the Rust FDT walker from the boot path: the boot seam's Lean parse becomes the blob's **only** parse, so the device-tree half of the WS-XV pair stops existing rather than being gated (`docs/REGISTERED_DEBT.md` table C, whose remedy for that pair is this row).  Consumes BP2.1 — the arena is a window the map must cover | `rust/sele4n-hal/src/mmu.rs`, `rust/sele4n-hal/src/cmdline.rs`, `rust/sele4n-hal/link.ld` | L |

**Acceptance**: a Lean `IO` action that allocates runs to completion on
`aarch64-unknown-none` under QEMU, the arena's exhaustion path halts, and
`init_mmu` names no device-tree entry point — the boot map is built from
linker symbols and board constants alone.

### BP3 — The RPi5 deployment (4 sub-tasks)

Register finding 44: there is no `rpi5PlatformConfig`, no root task, and no
initial objects.  The boot seam in BP4 boots *a configuration*; this phase
is that configuration, and it is placed before the seam because a seam with
nothing to boot cannot be reviewed.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| BP3.1 | `rpi5PlatformConfig`: the IRQ table from `rpi5InterruptContract`, `bootVSpaceRoot = rpi5BootVSpaceRootEntry`, and `machineConfig` from the binding — the last two supplied by `bindPlatformConfig`, so this row states the *caller's* half | `SeLe4n/Platform/RPi5/` | M |
| BP3.2 | The initial objects: a root-task TCB, its CSpace and its VSpace, each `.Inactive`, stored under its own id, with all three queue links empty — the shape `bootSafeObjectCheck` requires | `SeLe4n/Platform/RPi5/` | L |
| BP3.3 | Discharge `PlatformConfig.wellFormed`'s six conjuncts by evaluation, including `idleSlotsReserved`, `embeddedIdentitiesMatchSlots` and `declaredCoreCountInRange`.  Consumes BP3.1 and BP3.2 | `SeLe4n/Platform/RPi5/` | M |
| BP3.4 | Install the two threads `confinedDeploymentLabeling` declares as separated, so `declaredWitnessesInstalled` holds of the boot state and the deployment boots at all.  Consumes BP3.2 | `SeLe4n/Platform/RPi5/` | M |

**Acceptance**: `bootAndInitialiseRPi5OrHalt rpi5PlatformConfig` evaluates to
`.ok` in Lean, with every refusal arm shown unreachable for this
configuration.

### BP4 — The boot seam and its install ordering (5 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| BP4.1 | `@[export lean_kernel_main]` calling `Platform.FFI.bootAndInitialiseRPi5OrHalt` applied to BP3's configuration — the exact program `SeLe4n/Testing/BootEntryContract.lean` requires, decided by a head-directed reduction (`Meta.whnfUntil`) and one reducible `Meta.isDefEq`.  Consumes BP3.3 | `SeLe4n/Platform/FFI.lean` (or a new entry module in the production closure) | M |
| BP4.2 | The install ordering: perform the kernel-state install **before** `apply_cmdline_and_start_smp` releases any secondary, so no bracketed committer exists during the unbracketed install (option 1 of the two `SMP_RELEASE_CLOSURE_PLAN.md` §3 records).  The lost-commit shape `kernel_entry.rs` documents is closed by construction rather than by a lock | `rust/sele4n-hal/src/boot.rs`, `rust/sele4n-hal/src/smp.rs` | M |
| BP4.3 | Turn `rust_boot_main`'s `dtb_ptr` into the `ByteArray` `bootAndInitialiseRPi5FromDtbOrHalt` takes — a Lean-runtime allocation, hence the dependency on BP2.  This is what gives WS-RR RR7.27's board-versus-binding check a hardware caller | `rust/sele4n-hal/src/boot.rs`, `SeLe4n/Platform/FFI.lean` | M |
| BP4.4 | Move the boot entry to the DTB wrapper and `BootEntryContract.lean`'s `approvedBootCall` with it — the one-line change that file anticipates by name.  Consumes BP4.3 | `SeLe4n/Testing/BootEntryContract.lean` | S |
| BP4.5 | **The boot image's clean-to-PoU** (WS-RR RR7.20, SM7.D deferred item 4).  `kernelCodeWriteEmitted .bootImageLoad = false` records that the one remaining kernel-code-write site emits no `DC CVAU` → `DSB ISH` → `IC IALLUIS` sequence, and `kernelCodeWriteSites_emission_pending` pins that it is the only one.  The initial task's code is in the image before the first instruction fetch, so the clean must run in the boot seam before any user code can be fetched — the site could not name its extent while there was no image and no physical backing, which is why SM7.D deferred it here rather than closing it.  Flipping the `kernelCodeWriteEmitted` arm breaks a `decide`, so the closure cannot land silently.  Consumes BP4.2 (the install ordering).  The emission needs no image — it is a boot-seam instruction sequence — so this row does not wait on one; observing it on hardware is BP8's | `SeLe4n/Kernel/Architecture/`, `rust/sele4n-hal/src/boot.rs` | M |

**Acceptance**: `check_kernel_entry_exports.py` reports `lean_kernel_main`
defined by the archive rather than reconciled as expected-unresolved, and
`BootEntryContract.lean` elaborates against the DTB wrapper.

### BP5 — The bootable image (4 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| BP5.1 | A `[[bin]]` `no_std` / `no_main` target whose entry is `_start` from `boot.S` under `link.ld` | `rust/Cargo.toml`, `rust/sele4n-hal/` | M |
| BP5.2 | Link `libsele4n.a` and the HAL together into that binary; the first link is where BP2.2's shim list stops being a guess.  Consumes BP1.3, BP2.2, BP4.1 | `rust/`, `link.ld` | M |
| BP5.3 | `scripts/build_rpi5_image.sh` — `kernel8.img` plus `config.txt`.  **This is the deliverable `SM10.1.1` names**; the release cut consumes it from here | `scripts/build_rpi5_image.sh` | M |
| BP5.4 | Build the image in CI, and publish its size and section map so a regression in either is visible in the run rather than on the board | `.github/workflows/` | S |

**Acceptance**: `kernel8.img` is produced by CI on every push, and its
`.text` contains `_start`, `__exception_vectors` and `lean_kernel_main`.

### BP6 — Per-core readiness (3 sub-tasks)

Every seam behind the per-core `lean_ready` gate is wired end to end and
dormant: the IRQ vector redirect, the `.reschedule` SGI receiver, the
secondary bring-up entry, the SVC dispatch and the classifier.  A core that
is not ready halts on a syscall rather than serving it, because the timer
seam consults the same mask and a thread on a not-ready core would never be
preempted again.  Flipping the mask is what makes the kernel run.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| BP6.1 | Per-core Lean runtime initialization on a secondary — whatever of BP2's handshake is per-PE rather than per-image, established before the core takes its first interrupt.  Consumes BP2.3 | `rust/sele4n-hal/src/smp.rs` | M |
| BP6.2 | Mark the core ready, on the core itself, after its own initialization and before `enable_irq`.  Consumes BP6.1 | `rust/sele4n-hal/src/lean_ready.rs`, `rust/sele4n-hal/src/smp.rs` | S |
| BP6.3 | A gate that no seam is left dormant: `LEAN_READY_GATED_SEAMS` is already derived, so this row adds the *runtime* half — a boot-time assertion that every declared PE published readiness within the bounded window, failing the boot rather than running a kernel one core cannot serve.  Consumes BP6.2 | `rust/sele4n-hal/src/boot.rs`, `rust/sele4n-hal/build.rs` | M |

**Acceptance**: all four PEs publish readiness under QEMU, and a PE that
does not makes the boot fail rather than hang.

### BP7 — The context restore (7 sub-tasks)

`contextRestoreSeamLive` is `false`, and the three prerequisites its
docstring names (register finding 19) are here, in the order they must
land.  Until it flips, a blocked caller's frame is poisoned with the
fail-closed `blocked_resume_sentinel_regs()` and a delivered fault halts the
core; both are interim artefacts this phase removes.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| BP7.1 | Extend the model's `VSpaceRoot` with a translation-table **physical base**.  The model carries an ASID and an abstract `VAddr → PAddr` table, which is not something a PE can be told to use | `SeLe4n/Kernel/Architecture/VSpace.lean`, `SeLe4n/Model/` | L |
| BP7.2 | The FFI that installs it: a `TTBR0_EL1` write with the ASID, and the TLB discipline around a root change.  Consumes BP7.1 | `SeLe4n/Platform/FFI.lean`, `rust/sele4n-hal/src/mmu.rs` | L |
| BP7.3 | The full outgoing-frame save: `writeFfiRegistersToTcb` spills `x0`–`x5` and `x7`, so `regsOnCore` is stale for `x6`, `x8`–`x30`, `SP` and `PC`.  Widen the trap frame and the spill together, since a restore of a half-saved context is worse than no restore | `SeLe4n/Platform/FFI.lean`, `rust/sele4n-hal/src/trap.S`, `rust/sele4n-hal/src/trap.rs` | L |
| BP7.4 | Per-core return-frame staging: the kernel-entry lock closes in `dispatch_svc` before the trap handler would install the frame, so the staged frame has nowhere to live.  Give the frame a per-core mailbox the handler reads after the lock releases.  Consumes BP7.3 | `rust/sele4n-hal/src/kernel_entry.rs`, `rust/sele4n-hal/src/svc_dispatch.rs` | M |
| BP7.5 | Deliver the cancellation/timeout error frames WS-RR RR7.14 stages, so a cancelled waiter resumes reading an error rather than its own stale arguments.  Consumes RR7.14 and BP7.4 | `rust/sele4n-hal/src/svc_dispatch.rs`, `SeLe4n/Kernel/IPC/Operations/Timeout.lean` | M |
| BP7.6 | Flip `contextRestoreSeamLive` to `true` — one constant, three guards — and retire the sentinel poison and the two SM10.1 halts with it.  Consumes BP7.2, BP7.4, BP7.5 | `SeLe4n/Kernel/Concurrency/ContextRestoreSeam.lean`, `rust/sele4n-hal/src/svc_dispatch.rs`, `rust/sele4n-hal/src/trap.rs` | M |
| BP7.7 | **The declassified badge, delivered** (WS-RR RR7.23, register finding 6).  SM9.C's data-carrying declassification is the one flow the kernel *deliberately* makes visible, and in the **wait-before-signal** ordering its badge reaches the waiter only through the return frame: the waiter blocked first, so there is no in-line result to read, and until the restore is live its frame is poisoned with `blocked_resume_sentinel_regs()`.  The transition and its audit record are proved; what is unproven is that the badge arrives.  Exercise it end to end on the live restore — a thread waits on a notification, a cleared sender declassifies a signal to it, and the waiter resumes reading *that badge* in `x0` with the trail carrying the matching record.  A sentinel value in `x0` is a failure of this row, not of SM9.  Consumes BP7.6 | `rust/sele4n-hal/src/svc_dispatch.rs`, `scripts/`, `docs/planning/SMP_DECLASSIFICATION_COMPLETION_PLAN.md` | M |

**Acceptance**: a thread blocked in `seL4_Recv` is resumed by its partner
with the frame the kernel staged, on hardware, no path in the image still
installs a sentinel, and a wait-before-signal declassified badge reaches the
waiter's `x0` with its audit record.

### BP8 — First boot and bring-up (5 sub-tasks)

Sixteen QEMU scripts exist in `scripts/` and every one of them has always
reported SKIP for want of an image.  This phase is the first time any of
them executes a line of kernel code.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| BP8.1 | Single-core boot under QEMU to the first idle dispatch — the first execution of `BP4.5`'s boot clean-to-PoU, whose emission is a boot-seam instruction sequence and whose *observation* is here | `scripts/` | L |
| BP8.2 | Four-core bring-up under QEMU — `scripts/test_qemu_smp_bringup.sh` runs for the first time, and the two SM1.H acceptance boxes WS-RR RR7.16 unchecked are decided by it rather than asserted.  Consumes BP8.1 | `scripts/test_qemu_smp_bringup.sh`, `docs/planning/SMP_RUST_HAL_PLAN.md` | L |
| BP8.3 | Boot on the board.  QEMU's `virt` machine is not a BCM2712: the PSCI implementation, the memory map and the GIC differ, and BP3's device-tree check is what refuses the wrong one | `docs/HARDWARE_TESTING.md` | XL |
| BP8.5 | Read the per-core counters on the booted machine and check the containment `Concurrency.perCoreStatsPlausible` states — WS-RR RR7.33's registered half of register finding 98.  `Concurrency.perCoreStats` reads all four accessors and the predicate is proved and runtime-checked, but its *invocation* needs a machine: on hardware every core that has serviced a tick must report `0 < irqs`, and the timer-PPI and SGI counts must fit inside the IRQ total on every core.  A core reporting ticks it never took, or an accessor resolving to the wrong slot, fails here — which is what the counters were declared for and what nothing has ever executed.  Consumes BP8.2 | `SeLe4n/Kernel/Concurrency/Runtime.lean`, `rust/sele4n-hal/src/per_cpu_stats.rs` | S |
| BP8.4 | Run the Tier-4 acceptance gates, which have never executed, and record what they actually report — **including the two QEMU shootdown exercisers** (`test_qemu_smp_shootdown.sh`, `test_qemu_smp_shootdown_stress.sh`), which SKIP for want of an image and hold [`SMP_TLB_SHOOTDOWN_PLAN.md`](SMP_TLB_SHOOTDOWN_PLAN.md) §8's one unchecked acceptance box open (WS-RR RR7.20).  Check that box in the same cut as the run; a shootdown-round-serialisation break or a missing acknowledgment is a failure of SM7, not of the harness.  Consumes BP8.2 | `scripts/test_tier4_smp_bootcheck.sh`, `scripts/test_qemu_smp_shootdown.sh`, `docs/planning/SMP_TLB_SHOOTDOWN_PLAN.md` | M |

**Acceptance**: four banners under QEMU, four banners on the board, and a
Tier-4 run whose output is a result rather than a SKIP.

## 6. Acceptance gate

WS-BP closes when every box is ticked **by an executed run**, not by an
artefact existing.  The distinction is the one WS-RR RR7.16 had to enforce
against this plan's predecessor, where two boxes claimed a four-core boot
that no script had ever performed.

- [ ] `libsele4n.a` is produced for `aarch64-unknown-none` by CI (BP1.3).
- [ ] `check_kernel_entry_exports.py` reads the cross archive (BP1.4).
- [ ] A Lean `IO` action that allocates completes on the target (BP2.5).
- [ ] The Lean runtime's failure path halts rather than continues (BP2.4).
- [ ] `bootAndInitialiseRPi5OrHalt rpi5PlatformConfig` evaluates to `.ok`
      with every refusal arm shown unreachable (BP3.3, BP3.4).
- [ ] `lean_kernel_main` is defined by the archive; the `EXPECTED_UNRESOLVED`
      entry is removed rather than retained (BP4.1).
- [ ] The kernel-state install precedes the release of any secondary (BP4.2).
- [ ] The device tree reaches Lean, and a foreign board is refused (BP4.3).
- [ ] `kernel8.img` is built by CI and contains `_start`,
      `__exception_vectors` and `lean_kernel_main` (BP5.3, BP5.4).
- [ ] Every declared PE publishes readiness within the bounded window, and a
      PE that does not fails the boot (BP6.3).
- [ ] `contextRestoreSeamLive` is `true`, and no path installs a sentinel
      frame or halts pending SM10.1 (BP7.6).
- [ ] A blocked caller is resumed with the frame the kernel staged, on
      hardware (BP7.6).
- [ ] A wait-before-signal declassified badge reaches the waiter's `x0`
      through the live restore, with the matching audit record (BP7.7).
- [ ] `scripts/test_qemu_smp_bringup.sh` boots four cores and verifies four
      banners — **executed**, and the two SM1.H boxes re-ticked on its
      evidence (BP8.2).
- [ ] The board boots and reaches the first idle dispatch (BP8.3).
- [ ] Tier-4 reports a result rather than a SKIP (BP8.4).
- [ ] Every booted core's counter snapshot satisfies `perCoreStatsPlausible`, and every
      core that serviced a tick reports a nonzero IRQ total (BP8.5).

## 7. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Bare-metal Lean runtime hosting is larger than 2–4 weeks | MED | HIGH | BP2.2 derives the shim list from the *measured* unresolved symbols of BP1.3's archive rather than from a guess, so the size is known before the work is done rather than after |
| The Lean heap's footprint does not fit the kernel's memory budget | MED | HIGH | BP2.1 places the arena from the linker script, so the constraint is a link-time failure rather than a boot-time surprise |
| QEMU `virt` diverges from BCM2712 enough that BP8.2 green means nothing for BP8.3 | HIGH | MED | Known and accepted: BP8.2 validates the *kernel*, BP8.3 validates the *port*.  BP3's device-tree check is what refuses a board the image was not built for |
| A partial context restore is worse than none | LOW | CRIT | BP7.3 widens the trap frame and the spill in one sub-task, and BP7.6 gates the flip on BP7.2, BP7.4 and BP7.5 together |
| `SM10.1.1`'s meaning drifts as this plan lands | LOW | MED | It cannot: WS-BP takes its own prefix and BP5.3 *names* `SM10.1.1` as the row it satisfies.  §8 states the invariant |

## 8. What this plan does not renumber

`SM10.1.1` is the release cut's row for the image packaging, cited by three
`CHANGELOG.md` entries, by
[`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md),
[`SMP_RUST_HAL_PLAN.md`](SMP_RUST_HAL_PLAN.md),
[`UNFINISHED_SMP_WORK.md`](UNFINISHED_SMP_WORK.md),
[`../REGISTERED_DEBT.md`](../REGISTERED_DEBT.md) and
[`../HARDWARE_TESTING.md`](../HARDWARE_TESTING.md).  **It keeps that
meaning.**  WS-BP produces what `SM10.1.1` packages; BP5.3 is the sub-task
that does it, and the two ids name the same deliverable from the two plans
that care about it.

The rule this preserves is CLAUDE.md's: sub-task ids are frozen once they
appear in commit messages and CHANGELOG entries.  The rule it satisfies is
the other one: phase and sub-task numbers are execution order.  A plan
cannot obey both while renumbering, which is why this one does not.

## 9. Cross-references

- [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md) §1.1 — the
  sizing this plan sequences; §3 SM10.1 — the row this plan fills.
- [`SMP_RELEASE_READINESS_PLAN.md`](SMP_RELEASE_READINESS_PLAN.md) §RR7 —
  RR7.5 and RR7.15, the rows that registered this plan; RR7.14, whose
  staging BP7.5 delivers.
- [`UNFINISHED_SMP_WORK.md`](UNFINISHED_SMP_WORK.md) §2.2 and §6 findings
  19, 32, 40–44 — the register entries this plan closes as *scheduled*.
- [`../REGISTERED_DEBT.md`](../REGISTERED_DEBT.md) — the SM10.1 debt rows,
  each now naming a BP sub-task.
- `SeLe4n/Kernel/Concurrency/ContextRestoreSeam.lean` — the flag BP7.6
  flips and the docstring that names BP7.1, BP7.3 and BP7.4.
- `SeLe4n/Testing/BootEntryContract.lean` — the contract BP4.1 satisfies
  and BP4.4 re-points.

## Appendix A — Verification commands

```bash
source ~/.elan/env
lake build SeLe4n:static
./scripts/check_kernel_entry_exports.py
./scripts/test_aarch64_cross_build.sh
./scripts/build_rpi5_image.sh          # BP5.3 onward
./scripts/test_qemu_smp_bringup.sh     # BP8.2 onward
./scripts/test_full.sh
```
