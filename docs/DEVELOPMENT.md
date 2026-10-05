# seLe4n Development Guide

The operating manual for working on seLe4n. Everything here is a rule you will
be held to by a gate, a command you will actually run, or a fact about the tree
you need before you write code.

**What this file is not.** It is not a status report. What is in flight is in
[`REGISTERED_DEBT.md`](REGISTERED_DEBT.md); what changed in a given
version is in [`CHANGELOG.md`](../CHANGELOG.md); what new code must assume
about the kernel today is in `docs/agent_guide/WORKSTREAM_CONTEXT.md`'s *Standing constraints and registered
debt*.

---

## 1. The project in one page

seLe4n is a microkernel written in **Lean 4**, improving on the seL4
architecture, with machine-checked proofs and **zero `sorry` and zero `axiom`**
in the production proof surface. Every kernel transition is an executable pure
function. The first hardware target is the **Raspberry Pi 5** (BCM2712,
Cortex-A76, ARMv8.2-A, 4 cores).

The tree has two halves that must both build:

| Half | Language | Where | Builds with |
|------|----------|-------|-------------|
| The kernel model, its transitions and all proofs | Lean 4.28.0 | `SeLe4n/`, `Main.lean`, `tests/` | Lake |
| The hardware abstraction layer, boot assembly, trap seam | Rust + aarch64 asm | `rust/` | Cargo |

They meet at `SeLe4n/Platform/FFI.lean` (`@[extern]` / `@[export]`) and at
`rust/sele4n-hal/src/`. A change on one side of that seam almost always needs a
change on the other.

**The kernel does not boot yet.** SM10.1 owns the bootable image; until it
lands, every runtime seam behind the per-core readiness gate
(`rust/sele4n-hal/src/lean_ready.rs`) is wired and dormant. Do not assume a
Lean seam executes on hardware merely because it is wired.

---

## 2. Set up

```bash
# Toolchain, elan, Lean 4.28.0, and the git hooks. Runs automatically as a
# SessionStart hook; run it by hand on a fresh clone.
./scripts/setup_lean_env.sh                  # includes shellcheck + ripgrep
./scripts/setup_lean_env.sh --skip-test-deps # toolchain only, no test deps
./scripts/setup_lean_env.sh --build          # also run a full build

# Every shell that runs lake needs this first:
source ~/.elan/env
```

### The pre-commit hook is not optional

```bash
./scripts/install_git_hooks.sh          # install (idempotent)
./scripts/install_git_hooks.sh --check  # verify (non-zero if absent)
./scripts/install_git_hooks.sh --force  # overwrite, backing up a diverging hook
```

The hook builds every staged `.lean` module, rejects `sorry` in staged content,
runs the identifier-naming gate against the **git index**, and verifies version
sync when a version-bearing file is staged. **Do not bypass it with
`--no-verify.**

Because the naming gate reads the index rather than the working tree, a Tier 0
run over unstaged edits checks the *previous* content: **stage first, then run
the gate.** The hook is the backstop, not the first line.

### Rust

```bash
rustup target add aarch64-unknown-none-softfloat   # listed in rust-toolchain.toml, with llvm-tools
```

`rust/rust-toolchain.toml` pins the toolchain, and rustup's directory override
only applies **inside `rust/`**. Run cargo from there, never with
`--manifest-path` from the repo root — that silently selects the default
toolchain, which does not have the cross target.

---

## 3. Build

```bash
source ~/.elan/env
lake build                    # the default target
lake exe sele4n               # the executable trace harness
lake build <Module.Path>      # ONE module — see the rule below
```

### Module build verification is mandatory

**Before committing any `.lean` file, build that module by name:**

```bash
lake build SeLe4n.Kernel.RobinHood.Bridge     # after editing Bridge.lean
```

`lake build` on the default target is **not sufficient**. It builds only what
is reachable from `Main.lean` and the test executables, so a module not yet
imported by the kernel passes the default target with broken proofs. The
pre-commit hook enforces this; the rule is here because you should not need the
hook to tell you.

`SeLe4n/Platform/Staged.lean` is the build anchor that pulls staged modules
into CI, so a staged module still compiles on every PR even though no linked
image carries it.

---

## 4. Test

Tiers are cumulative. Run the smallest one that covers what you changed, and at
minimum `test_smoke.sh` before any PR.

| Command | Tiers | Covers | Run it when |
|---------|-------|--------|-------------|
| `./scripts/test_fast.sh` | 0–1 | hygiene gates + full build | iterating locally |
| `./scripts/test_smoke.sh` | 0–2 | + trace, determinism, negative state, Rust | **minimum before any PR** |
| `./scripts/test_full.sh` | 0–3 | + invariant surface anchors | changing theorems, invariants or Tier 3 anchors |
| `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh` | 0–4 | + nightly candidates, Tier-5 cross-language | before a release cut |

What each tier is for:

| Tier | Script | Question it answers |
|------|--------|---------------------|
| 0 | `test_tier0_hygiene.sh` | Is the tree well-formed? (code gates: naming, versions, website links, staging partition, axioms, TLBI discipline, cross-target config, de-threading) |
| 1 | `test_tier1_build.sh` | Does everything compile, including staged modules? |
| 2 | `test_tier2_trace.sh`, `_determinism.sh`, `_negative.sh` | Does the kernel produce the fixture trace, deterministically, and reject bad states? |
| 3 | `test_tier3_invariant_surface.sh` | Do the named theorems, invariants and code shapes still exist? |
| 4 | `test_tier4_smp_bootcheck.sh`, `_nightly_candidates.sh` | SMP acceptance on the QEMU `virt` image — the bring-up, the PE-withheld boot and the in-image exercisers execute on both images (WS-BP BP8.4), the per-core counter check on the Lean-linked one alone (BP8.5); the eight gates that need a user program report NOT RUN until SM10's root task |
| 5 | `test_tier5_cross_language.sh` | Do the Rust lock primitives agree with their Lean specs? |

The Tier-5 oracle **drives** both real reader-writer locks — a
`rw_lock::RwLock` and the deployed `queued_rw_lock::QueuedRwLock` — through
every generated operation and checks three relations after each one: that the
two implementations agree, that the queued lock's `[now_serving, next_ticket)`
interval matches the abstract waiter queue, and that the state word is
`encodeRwLock` of the abstract state.  It does not model them; the state it
renders is read back from the lock's own words.  Since v0.34.53 the driver
holds a **real ticket** for every queued waiter and the alphabet carries a
fifth letter, the withdrawal — so the interval check is derived from the
tombstoned invariant (outstanding tickets are the live waiters *plus* the
not-yet-passed tombstones) rather than from the writer bit alone.  Since PR
#890 review round 5 both oracles print one **identity** line per state — the
initial state, then one after each op — `W=<core|->;R=<sorted reader
cores>;Q=<core:r|w,...>`, read back out of the ticket lock's per-core held,
request and mode words on the Rust side; the flag, count and length they used
to print let a wrong-waiter promotion, a reordered queue or a changed mode
agree on every number.  The harness compares the whole of both outputs and
captures both exit statuses, so a divergence in the middle of a trace is a
mismatch too.

### Rust, and the cross target

```bash
./scripts/test_rust.sh                 # host: build, tests, fmt, clippy
./scripts/test_aarch64_cross_build.sh  # the kernel's real target
./scripts/test_lean_aarch64_archive.sh # the kernel's Lean for that target
```

**Run the cross build after any change under `rust/`.** The tier scripts and
`test_rust.sh` compile the *host* target, where every
`#[cfg(target_arch = "aarch64")]` block is removed before rustc or clippy sees
it — so the hardware half of the HAL, which is most of it, is invisible to
them. The cross gate builds `sele4n-hal` for `aarch64-unknown-none-softfloat`
in both profiles, verifies `boot.S` / `vectors.S` / `trap.S` actually
assembled, lints the cross target with `-D warnings`, disassembles the
release objects with `scripts/check_fp_simd_free_objects.py`, and (WS-BP BP2.1)
links a probe under `link.ld` with `scripts/check_link_script.py` — nothing else
links the script before the image exists, so its Lean heap arena, the section
boundaries the boot map reads (`__text_end`, `__rodata_start`, `__rodata_end`)
and every `ASSERT` are checked on an ELF and each assertion is proved live by
mutation.

**The boot map is built from constants** (WS-BP BP2.6): `mmu::init_mmu` reads
no device tree.  It maps the kernel's reserved extent (`KERNEL_RESERVED_END`;
the first gigabyte until WS-BP BP7.10, whose top the firmware withholds) and the
device window, with the image's text read-only and executable at EL1,
its read-only data read-only and never executable, and everything else
writable and never executable.  `boot_mapping_for` is the one answer to what an
address is mapped as, and `boot_map_tests` walks every table against it and
against `tests/fixtures/boot_map.expected`.  A section added to `link.ld`
between `.text` and `.rodata` fails `__rodata_start == __text_end`; section
boundary symbols are assigned *inside* their sections, since lld attaches a
location-counter change between sections to the following one.
**The kernel's reserved extent** (WS-BP BP3.2) is one number in three places —
`link.ld`'s `KERNEL_RESERVED_END`, `mmu::KERNEL_RESERVED_END` and the Lean
`rpi5KernelReservedEnd` — held together through the fixture's `kernelReserved`
line; the image must end inside it (an `ASSERT`) and so must the device-tree
window, and the boot refuses an untyped over it.  Moving it is a three-file
change that the HAL test and `check_link_script.py` refuse to see half done.
It runs in CI as the
`aarch64 Cross Build` job.

**The Lean half has its own lane** (WS-BP BP1): `test_lean_aarch64_archive.sh`
builds `libsele4n.a` — the elaborator's closure of `SeLe4n`, compiled
freestanding and soft-float by the Lean toolchain's clang — and decides the
kernel-entry reconciliation on it as well as on the host archive.  The first run
on a new toolchain regenerates the stdlib C (several minutes, cached under
`.lake/build/aarch64-unknown-none-softfloat/`).  It fails when a production
module imports `Lean.*` or a staged module, when a generated file carries a
warning outside the generator's two known shapes, or when the archive references
a symbol no provider accounts for, or when the HAL's object code for the target
does not define a symbol the archive attributes to it; `libsele4n.unresolved`
lists what the archive needs, by provider.

**The Lean heap** (WS-BP BP2.1) is `rust/sele4n-hal/src/lean_heap.rs` over
`link.ld`'s `.lean_heap` section: one arena, sized by `LEAN_HEAP_SIZE`, serving
`lean.h`'s small-allocator API and a general `malloc`-shaped interface.  Its state
lives in the arena's metadata pages and never inside an object, so keep it there;
`Heap::check_invariants` states the invariants and the host witness suite
(`cargo test -p sele4n-hal lean_heap`) runs it after every mutation.

**The Lean runtime** (WS-BP BP2.2) is `rust/sele4n-hal/src/lean_runtime/`: the
kernel's own, in Rust, providing every symbol the archive's reachable link needs
(the lane's step [7/8] links it and names any gap).  A symbol added to it is
faithful to upstream, environmental or fail-closed, and says which in its
docstring.  A primitive that computes gets lines in
`tests/LeanRuntimeConformanceSuite.lean`, whose fixture upstream's runtime
produces (`lake exe lean_runtime_conformance_suite --emit >
tests/fixtures/lean_runtime_conformance.expected` regenerates it; then refresh
the `.sha256`) and `cargo test -p sele4n-hal lean_runtime`
recomputes.  An environmental or fail-closed one joins
`io::UNPROVIDED_SEMANTICS` and `RuntimeEnvironmentCensus`'s list together; a Rust
test holds them equal.  A helper that dereferences an object pointer it was
handed is an `unsafe fn` with a `# Safety` section, private ones included.

**Entering the Lean kernel** (WS-BP BP2.3/BP2.4) is
`rust/sele4n-hal/src/lean_entry.rs`: the library initializer runs once, its
`IO` result is checked, and a refusal halts the system.  `lean_kernel_main` is
reachable only through `enter_lean_kernel`, which consumes the
`LeanLibraryInitialised` token a successful initialization returns; a new Lean
entry on the primary takes that token too, rather than declaring its own
`extern`.  A HAL-declared `initialize_…` symbol is Lean code to `build.rs`'s
readiness scan, so a call to one must be registered in
`LEAN_UPCALLS_OUTSIDE_THE_GATE` or sit behind the gate.

**The boot entry and its ordering** (WS-BP BP4.1/BP4.2).  `lean_kernel_main` is
`SeLe4n.Platform.RPi5.kernelMain`, exactly the halting device-tree boot of the
deployment on the `ByteArray` the HAL copies from the firmware's blob (BP4.3/BP4.4);
`SeLe4n/Testing/BootEntryContract.lean` refuses any other shape — a fixed or
edited blob included — and refuses its absence.  The deployment is
`rpi5PlatformConfigFor board`, proved to boot on every RAM variant, so a change
to it that breaks any variant fails to elaborate.  Releasing a secondary consumes a
`lean_entry::SecondaryReleasePermit`: with `hw_target` the only one is what
`enter_lean_kernel` returns after the install, and `no_lean_kernel()` is for
images and tests that link no kernel.  A new bring-up path takes the permit too
— it is how the install is kept ahead of every secondary without a lock.
**The boot map grows once, before the seal** (BP4.6): the accepting arm maps the
verified configuration's RAM outside the kernel's extent (BP7.10: the first
gigabyte's part as far as the firmware reports it, then everything above) through
`ffiExtendBootRamMap` before the install, and `enter_lean_kernel` seals the map
(`mmu::seal_boot_map`) before it mints the permit.  Extend the boot tables only
through `mmu::extend_boot_ram_map` — it writes invalid entries only, decides every
refusal first, and widens `is_boot_cacheable_range` by the same record — and never
after the seal.
**The deployment's objects are a function of the variant** (BP4.7):
`rpi5PlatformConfigFromDtb` applies `initialObjectsFor` to the variant its parse
selected, and the RPi5 deployment's root-task untypeds over RAM above the
gigabyte are derived from `rpi5BootRamExtensions v` — add RAM by changing the
variant's memory map, never by listing untypeds per board.
**The kernel image is one bare-metal binary** (BP5.1): `sele4n-kernel`
(`rust/sele4n-hal/src/bin/sele4n_kernel.rs`) is built with
`cargo build --release --target aarch64-unknown-none-softfloat -p sele4n-hal
--features kernel_image --bin sele4n-kernel` from `rust/`, laid out by
`link.ld` (the build script passes `-T` to that binary alone), and checked by
`scripts/check_kernel_image.py` in the cross lane's step [7/7].  Its panic
handler is `gic::halt_all`.  That lane builds it without `hw_target`, so it is
the HAL half alone.
**With `hw_target` the image carries the Lean kernel** (BP5.2): the build script
links `.lake/build/aarch64-unknown-none-softfloat/libsele4n.a` and the
`libsele4n.roots.ld` the archive builder writes beside it, with
`--gc-sections`, so build the archive first (`scripts/test_lean_aarch64_archive.sh`
does both, then runs `check_kernel_image.py --lean-kernel` and the FP/SIMD gate
over the linked image).  A missing archive fails the link naming the path.
**The firmware's boot files** (BP5.3): `./scripts/build_rpi5_image.sh [ELF
[OUT]]` writes `kernel8.img` and `config.txt` to `.lake/build/rpi5-image/`
from that image (the archive lane's step [5/6] does this).  Copy both to the
SD card's boot partition.  `config.txt` is generated — its `kernel_address` is
the image's entry and its `device_tree_address` / `device_tree_end` are
`link.ld`'s `.dtb_window` — and `rpi5_boot_files.py check` refuses a key it
does not set, so add a firmware option there, not by hand.  The script ends by
printing the image's size and section map (`kernel_image_report.py`, BP5.4),
which CI appends to the job summary and uploads with the boot files.
**Both boot entries reach EL1 through `boot.S`'s `.L_enter_el1`** (BP5.5):
the RPi5 firmware enters at EL2 and QEMU's `virt` at EL1.  The routine is pinned
item for item by `build.rs`'s `EL1_ENTRY_ROUTINE`, so change the two together,
and no other code may name an EL2 register.  PSCI calls go through
`psci::psci_call`, whose conduit `rust_boot_main` selects from the entry level;
never write an `hvc` or `smc` of your own.
**A core is marked Lean-ready only by `lean_ready::become_ready_or_halt`**
(BP6), which runs the per-PE handshake and hands its token to the safe
`mark_lean_ready`; each PE calls it on itself before its one `enable_irq`, and
`build.rs` (`readiness_publication_status`) refuses any other caller or order.
A host test that needs a ready core uses the `unsafe`
`LeanRuntimeReadyOnCore::assume_initialised`.
Lean 4.28 returns an `IO`/`BaseIO` function's value directly (no world, no
result wrapper): declare a `BaseIO Unit` export `-> lean_runtime::LeanBaseIoUnit`
and hand the value to `lean_runtime::discharge_base_io`; only a module
initializer returns an `IO` result (`lean_runtime::LeanIoResult`).  A HAL
definition of a `BaseIO Unit` `@[extern]` returns `lean_runtime::base_io_unit()`.
`check_kernel_entry_exports.py` checks both directions against the C prototypes
the Lean compiler generated.

**`cargo check` is not a substitute.** It stops before code generation, so it
never hands an `asm!` template to an assembler. The first real cross build
found six defects and three lints; four of the defects were `check`-clean.

**The kernel is FP-free, and the target is what makes it so.** `boot.S` traps
FP/SIMD at EL0 and EL1 from each entry's first instruction and the trap frame
saves general-purpose registers only, so kernel code must never touch a vector
register. The hard-float `aarch64-unknown-none` target lets the compiler use
them for zeroing, copies and spills — it put 129 such instructions in the HAL —
so the HAL builds for `aarch64-unknown-none-softfloat`, and the cross gate's
step [5/7] checks the generated code rather than trusting the flag. Do not
write `neon`/`fp-armv8` target features, FP inline assembly or a second
`CPACR_EL1` write: `build.rs` and the disassembly gate refuse all three, save
for `fp_context.S`'s four pinned routines. A user FP/SIMD instruction traps and
is the lazy switch: the thread's own context is loaded and the trap lifted for
it (WS-BP BP7.9, `v0.36.22`).

### Concurrency model checking and miri

The deployed reader-writer lock is exercised by two tools the host test lane
cannot substitute for:

```bash
./scripts/test_loom_queued_rw_lock.sh   # exhaustive-interleaving model checking (about seven minutes)
./scripts/test_miri_queued_rw_lock.sh   # UB / strict-provenance checking
```

`loom` explores the lock's interleavings exhaustively — every schedule of each
two-thread model, with no preemption bound (the first cut capped it at three
preemptions and still called the run exhaustive; PR #890 review) — which is what
catches an ordering bug a stress test only makes *unlikely*.  Setting
`LOOM_MAX_PREEMPTIONS=n` bounds the run for a quick local pass, and that pass is
not the gate.  It
needs the lock compiled against its own instrumented atomics, so
`queued_rw_lock.rs` aliases `core::sync::atomic` under `cfg(loom)` and its
models live in a `#[cfg(loom)] mod loom_model`; a `loom` entry in the manifest
alone explores nothing.  The gate runs in CI as the
`test-loom-concurrency-model` job.

`miri` runs the lock's own suite under `-Zmiri-strict-provenance` and is wired
into `test_nightly.sh` behind `NIGHTLY_ENABLE_EXPERIMENTAL=1`.  The stress and
FIFO iteration counts scale down under `cfg(miri)` (`STRESS_ITER`,
`FIFO_ACQUISITIONS`) so the interpreter finishes, without weakening the
native-speed thresholds.

Both gates were verified decisive by a **relation-breaking** mutation rather
than by deleting a token: removing `await_turn` from `acquire_read` — which
leaves every symbol the gate might grep for in place — fails two of the five
loom models.  The two models PR #890 review round 2 added — a non-holder's
unwind against a holder, and `every_pair_of_units_is_safe`, every unordered
pair of the lock's single-lifecycle units on two threads (fourteen since
review round 5, 105 models with the diagonal; `build.rs` holds the unit list
to the lock's entry points), with the three chained units — read then write,
write then read, withdraw then read, so a second acquisition starts on the
per-core words the first left — meeting every unit in
`every_chained_unit_meets_every_unit` under a stated preemption bound of 3
(48 models; two lifecycles per thread double the atomic and yield points, and
an unbounded exploration of two such threads did not finish in a per-PR
lane) — are pinned the same way: keeping a release's held-word load and comparison and dropping only
its early return fails both, and keeping the `involved` load in `acquire_read`
and inverting its comparison fails the enqueue-twice-then-acquire units the
class closure behind rounds 2 and 3 added.  What the loom gate does **not**
enumerate is arbitrary sequences of entry points: that is the single-threaded
census `per_core_census_to_depth_four`, which replays every sequence of up to
four entry points from each of the lock's nine start states and holds every
step to the matrix's classification (`cell`) — 158,015 sequences in under a
second, in the ordinary host lane.  Round 5's five withdrawal models race a
served or promoted request's withdrawal against the release that admitted it
and tally that both verdicts occur; their mutations — the read arm withdrawing
regardless of its scan, the served writer's state test inverted, the scan's
mode read dropped — each fail the named model.

### Running one suite

There are 71 `lean_exe` targets. Run one directly:

```bash
lake exe negative_state_suite
lake exe information_flow_suite
lake exe fault_handling_suite
```

Or interpret it without building an executable — useful when a suite hits the
clang bracket-depth limit described in `CLAUDE.md`:

```bash
lake env lean --run tests/NegativeStateSuite.lean
```

### QEMU and hardware

`scripts/test_qemu*.sh` cover SMP bring-up, IPC, scheduler, timer, SGI
round-trip, TLB shootdown, deadlock and kprintln stress.
`scripts/test_hw_full.sh` and `docs/HARDWARE_TESTING.md` cover the RPi5 path.
`scripts/test_qemu.sh` is live: with no argument it boots the HAL-only image on
QEMU's `virt` at EL1 and at EL2, and with `--lean-kernel` (which needs the
archive `scripts/test_lean_aarch64_archive.sh` builds, and which that lane runs
as its step [6/6]) it boots the Lean-linked image on four PEs to every core's
first idle dispatch, under `-icount shift=0,sleep=off` — without it, one
emulated Lean tick outlasts the 1 ms tick period on multi-threaded TCG and four
PEs' ticks saturate the kernel-entry lock.  `scripts/test_qemu_smp_bringup.sh`
(WS-BP BP8.2) is live too: it boots the HAL-only image, and with `--lean-kernel`
the Lean-linked one, on four PEs at EL1 and EL2, and requires every secondary's
per-core init in order and every banner as a whole line; the same lane runs both
modes.  The image build, the raw cut and the run are `scripts/qemu_boot_lib.sh`'s,
shared by the two scripts, and the `virt` images build under `rust/target/qemu-virt*`
so the Raspberry Pi 5 image in `rust/target/<target>/release` is never
overwritten.  A console line is one lock acquisition, and a PE prints nothing
before its own MMU is on.  The other QEMU scripts and the board need artefacts
BP8.3–BP8.5 produce.

---

## 5. Repository layout

```
SeLe4n/PackedString.lean         Packed strings: one Nat per inventory string, kernel-cheap distinctness
SeLe4n/Prelude.lean              Typed identifiers, monad foundations
SeLe4n/Machine.lean              Machine state primitives
SeLe4n/Model/                    Object types, kernel/system state, builder, freeze
SeLe4n/Kernel/Scheduler/         Scheduler transitions, run queues, EDF, PIP, liveness
SeLe4n/Kernel/Capability/        CSpace/capability ops + invariants
SeLe4n/Kernel/IPC/               Endpoint/notification IPC, dual-queue, capability transfer
SeLe4n/Kernel/Lifecycle/         Thread suspend/resume, retype, cleanup
SeLe4n/Kernel/Service/           Service orchestration + policy
SeLe4n/Kernel/Architecture/      ARM64 page tables, exceptions, interrupts, TLB/cache,
                                 register/syscall decode, IPC buffer validation, faults
SeLe4n/Kernel/InformationFlow/   Security labels, projection, non-interference
SeLe4n/Kernel/RobinHood/         Verified Robin Hood hash table
SeLe4n/Kernel/RadixTree/         Verified flat-array CNode radix tree
SeLe4n/Kernel/SchedContext/      CBS budgets, replenishment queue, MCP authority
SeLe4n/Kernel/FrozenOps/         Frozen-state kernel operations, refined against the live API
SeLe4n/Kernel/Concurrency/       Locks, memory model, SMP assumption inventory
SeLe4n/Kernel/CrossSubsystem.lean  Cross-subsystem invariants, discharge index marker
SeLe4n/Kernel/API.lean           Public kernel interface + syscall wrappers
SeLe4n/Platform/Contract.lean    PlatformBinding typeclass
SeLe4n/Platform/DeviceTree.lean  FDT parsing
SeLe4n/Platform/FFI.lean         Lean <-> Rust HAL bridge (@[extern] / @[export])
SeLe4n/Platform/Boot.lean        Boot sequence (PlatformConfig -> IntermediateState)
SeLe4n/Platform/Sim/             Simulation platform contracts
SeLe4n/Platform/RPi5/            Raspberry Pi 5 (BCM2712) bindings, boot VSpace
SeLe4n/Platform/Staged.lean      Build anchor pulling staged modules into CI
SeLe4n/Testing/                  Test harness, state builder, fixtures
Main.lean                        Executable entry point
tests/                           Executable test suites + fixtures
rust/                            ARM64 boot assembly + HAL crates
scripts/                         Every gate, tier script and generator
docs/                            Canonical documentation (see §10)
```

The filesystem is the authoritative file list; this map changes more slowly
than the tree does.

### Two structural rules

**Operations / Invariant split.** Each kernel subsystem has `Operations.lean`
(transitions) and `Invariant.lean` (proofs). Keep them apart. Both may be
re-export hubs over per-concern submodules in a sibling directory of the same
name — import-only files that keep existing `import` statements working.

**Staged vs production.** 67 modules are staged-only, listed in
`scripts/staged_module_allowlist.txt` and gated by
`check_production_staging_partition.sh`. **Production must not import staged.**
CI builds staged modules on every PR through `Platform/Staged.lean`; a linked
kernel image does not carry them.

---

## 6. Rules you will be held to

The project rules are stated once, canonically, in [`CLAUDE.md`](../CLAUDE.md)
— the rules file for every contributor, human or agent (it is named for the
tool that auto-loads it; `AGENTS.md` is a pointer file to it). Read it before your
first PR. The rules about code are enforced by gates, so violating one fails the
build rather than a review; documentation is not gated and is held by review:

| Rule (in `CLAUDE.md`) | Enforced by |
|---|---|
| No `sorry` / `axiom` in the production proof surface (`TPI-D*` exceptions only) | Tier 0, `check_module_axioms.py` |
| Deterministic semantics; typed identifiers | Tier 2, review |
| Internal-first naming — no workstream codes in identifiers or paths | `check_identifier_naming.py` (Tier 0, reads the git index) |
| Fixture-backed evidence — `Main.lean` output matches its golden fixture line for line | `test_tier2_trace.sh` |
| Gates and tests check code, not documentation or comment prose; gates read code, prose reads prose; a presence check is not a relation check; test a gate by breaking the relation | the code-view overlay, the self-test harnesses, review |
| Implement the improvement — never weaken documentation to match inferior code | review |
| Deferrals are registered, never silent | review |
| Code never points into `docs/dev_history/`; comments cite an archived plan by workstream ID, never by path | Tier 0 negative check over the code view of `SeLe4n/`, `Main.lean`, `tests/`, `rust/` (code); review (comments) |
| Report a possible vulnerability the moment you find it | — |

The long-form rationale behind each rule, with the history that earned it, is
in [`agent_guide/CONVENTIONS_DETAIL.md`](agent_guide/CONVENTIONS_DETAIL.md) and
[`agent_guide/RULES_DETAIL.md`](agent_guide/RULES_DETAIL.md).

---

## 7. Working in Lean here

The working rules — read and edit large files in chunks, avoid the deep
`do`-chain build trap, keep search and command output bounded — are in
[`CLAUDE.md`](../CLAUDE.md). The curated large-file list and its tooling:

```bash
./scripts/find_large_lean_files.sh                  # list files over threshold
./scripts/find_large_lean_files.sh --format bullets # regenerate docs/agent_guide/LARGE_FILES.md's list
```

### Proof hygiene

```bash
python3 scripts/check_proof_depth.py    # flags single-tactic bodies with no structure
python3 scripts/check_module_axioms.py  # axiom sweep, map-driven
```

---

## 8. Versioning: every PR bumps the patch version

The policy — canonical source, the version sites, what is not a version site —
is in [`CLAUDE.md`](../CLAUDE.md) *Versioning policy*; the authoritative site
list is `scripts/version_locations.sh`.

```bash
./scripts/bump_version.sh 0.34.46     # rewrites every site, then self-verifies
./scripts/check_version_sync.sh       # verify only (Tier 0 + pre-commit)
```

Then add `## v<new-version> — <summary>` at the top of
[`CHANGELOG.md`](../CHANGELOG.md); the bumper reminds you but does not write it.

---

## 9. Documentation rules

What to update when you change behaviour, theorems or workstream status, and
who owns which topic, are rules in [`CLAUDE.md`](../CLAUDE.md) *Documentation
rules*; the full ownership map is
[`DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`](DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md).
This section holds the procedures.

### Sync commands

```bash
./scripts/sync_documentation_metrics.sh          # the whole chain, in order
python3 scripts/generate_codebase_map.py --pretty # regenerate the map
python3 scripts/generate_codebase_map.py --pretty --check  # is it current?
./scripts/sync_readme_from_codebase_map.sh       # README + spec metrics
python3 scripts/generate_doc_navigation.py       # GitBook README + SUMMARY
python3 scripts/report_current_state.py          # current metrics, one per line
```

`AGENTS.md` is a short static pointer to `CLAUDE.md` that copies none of its
text; edit `CLAUDE.md` only.

### Fixture updates

A fixture change is a claim that the kernel's observable behaviour changed on
purpose.

```bash
lake exe sele4n > tests/fixtures/main_trace_smoke.expected   # only with a reason
./scripts/test_smoke.sh                                       # then prove it holds
```

State the rationale in the PR body and in the CHANGELOG entry: what transition
changed, why the new trace is correct, and what would have been wrong about
keeping the old one. A fixture updated to make a test pass is a defect.

**Two-sided fixtures** (WS-BP BP0, `v0.36.2`) are read by a Lean suite *and* a
Rust suite, so a change to one is a claim about both implementations:

```bash
./scripts/generate_dtb_corpus.py            # tests/fixtures/dtb/: edit a CASE, never a .dtb.hex
lake exe syscall_return_abi_suite           # prints the live abi_layout.expected on mismatch
lake exe ak9_platform_suite                 # prints the live boot_map.expected on mismatch
(cd rust && cargo test --all --features std,host_tools)   # the Rust side of all three
```

Expectations for the device-tree corpus are written by hand in the generator's
case table — per blob, whether its structure is readable and which memory
regions it declares (or that the region read refuses it); the two tables are emitted by Lean and must then be matched by the
Rust side, never edited to match it.  A divergence one of them exposes is fixed
on the side that is wrong.  `boot_map.expected` also carries the RPi5's MMIO windows
(`mmio uart|gicd|gicc`, from `mmioRegions`), which the HAL's UART and GIC tests
read, so a driver base that drifts from `Board.lean` fails there — the
literal-beside-a-comment tests they replaced agreed with `Board.lean` while
both carried the BCM2711's addresses (spec §6.2.14).

### Generated artefacts

```bash
python3 scripts/generate_smp_theorem_manifest.py           # regenerate
python3 scripts/generate_smp_theorem_manifest.py --check   # Tier 0 check
```

The SMP theorem total is **measured, not summed**: the manifest registers one
entry per phase and the propositionality census resolves each identifier
against the environment. Never reintroduce a hand-written per-phase figure.

### Website links, session URLs, `docs/dev_history/`

Protected website paths (`scripts/website_link_manifest.txt`, checked by
`scripts/check_website_links.sh`), the ban on `claude.ai/code/session_*` URLs
in anything that ships, and the rule not to read or reference
`docs/dev_history/` are stated in [`CLAUDE.md`](../CLAUDE.md).

---

## 10. Where the documentation is

| Read this | For |
|-----------|-----|
| [`../README.md`](../README.md) | the project at a glance, current metrics |
| [`spec/SELE4N_SPEC.md`](spec/SELE4N_SPEC.md) | the kernel specification |
| [`spec/SEL4_SPEC.md`](spec/SEL4_SPEC.md) | what seL4 does, for comparison |
| [`CLAIM_EVIDENCE_INDEX.md`](CLAIM_EVIDENCE_INDEX.md) | every public claim and the theorem or test backing it |
| [`THREAT_MODEL.md`](THREAT_MODEL.md) | the security model and its boundaries |
| [`HARDWARE_TESTING.md`](HARDWARE_TESTING.md) | the RPi5 bring-up path |
| [`DEPLOYMENT_GUIDE.md`](DEPLOYMENT_GUIDE.md) | building and deploying an image |
| [`CI_POLICY.md`](CI_POLICY.md) | what CI runs and why it is pinned |
| [`INFORMATION_FLOW_ROADMAP.md`](INFORMATION_FLOW_ROADMAP.md) | the non-interference surface |
| `*_ADR.md` | architecture decisions and their alternatives |
| [`planning/`](planning/) | per-phase schedules |
| [`gitbook/`](gitbook/) | the handbook: a reading path that links to the above |

---

## 11. The contribution loop

1. **Find the workstream.** Check
   [`REGISTERED_DEBT.md`](REGISTERED_DEBT.md) for what is in flight and
   the phase plan for the sub-task you are taking. Sub-task numbers are
   execution order: a plan that says `RR5.10` before `RR5.11` means exactly
   that, and a sub-task may only consume a lower-numbered one.
2. **Read the standing constraints.** `docs/agent_guide/WORKSTREAM_CONTEXT.md`'s *Standing constraints and
   registered debt* is current facts about the tree — what a live seam does,
   what is dormant, what new code must not assume. It changes what you may
   write.
3. **Scope one coherent slice.** One PR is one sub-task or less.
4. **Write transitions and their proofs together.** A live kernel transition
   must not land ahead of its own invariant surface. If the two cannot be
   split — the theorems unfold the function the switch replaces — they are one
   PR, not two.
5. **Build the module by name** (§3) and run the right tier (§4).
6. **Bump the version and write the CHANGELOG entry** (§8).
7. **Sync the documentation** (§9).
8. **Stage, then run Tier 0** — the naming and plan gates read the index.
9. **Commit.** The hook runs; do not bypass it.

### PR checklist

Copy the checklist in [`CLAUDE.md`](../CLAUDE.md) *PR checklist* into the PR body.

### Definition of done for a milestone-moving change

- The theorem or transition exists, is named for what it does, and is reachable
  from production (or explicitly staged, with the allowlist entry to prove it).
- Tier 0–3 green; Tier 4 honest about what it could not run.
- Every claim the change makes is cited in `CLAIM_EVIDENCE_INDEX.md`.
- Every deferral it creates is a row in the debt register with an owner.
- The CHANGELOG entry says what changed, what it found, and how it was
  verified.

---

## 12. When something fails

| Symptom | Cause | Fix |
|---------|-------|-----|
| `lake: command not found` | elan not on PATH | `source ~/.elan/env` |
| Module passes `lake build` but CI fails | default target does not reach it | `lake build <Module.Path>` by name |
| `bracket nesting level exceeded maximum of 256` | deep `do`-chain in a suite | split into per-area helpers (`CLAUDE.md`) |
| Tier 0 naming gate passes locally, fails in CI | gate reads the git index | `git add` first, then re-run |
| `check_version_sync.sh` fails | a version site missed | `./scripts/bump_version.sh <version>` |
| `docs/codebase_map.json is stale` | Lean sources changed after the last sync | `python3 scripts/generate_codebase_map.py --pretty` |
| `LARGE_FILES.md 'Known large files' differs` | a file crossed the 10% tolerance | `./scripts/find_large_lean_files.sh --format bullets`, replace the block in `docs/agent_guide/LARGE_FILES.md` |
| Cross build fails but `cargo check` was clean | `check` never reaches codegen | that is the point — fix the `asm!` or the encoding |
| A `TLBI *OS` wrapper halts the core | FEAT_TLBIOS is ARMv8.4-A; Cortex-A76 is ARMv8.2-A | use the `*IS` variant; the `*OS` path is fail-closed by design |
| Production module cannot import what it needs | it is on the staged allowlist | promote it deliberately, or restructure — production must not import staged |
| A push to `main` is rejected | branch protection | branch first; never push to the default branch |

Proxy or TLS failures on outbound HTTPS: see `/root/.ccr/README.md` and
`curl -sS "$HTTPS_PROXY/__agentproxy/status"`. Never disable TLS verification
and never unset `HTTPS_PROXY`.

---

## 13. Command reference

```bash
# --- setup -------------------------------------------------------------
./scripts/setup_lean_env.sh [--skip-test-deps] [--build] [--quiet]
./scripts/install_git_hooks.sh [--check|--force]
source ~/.elan/env

# --- build -------------------------------------------------------------
lake build                                   # default target
lake build <Module.Path>                     # one module (required before commit)
lake exe sele4n                              # trace harness
lake env lean --run tests/<Suite>.lean       # interpret a suite

# --- test --------------------------------------------------------------
./scripts/test_fast.sh                       # tiers 0-1
./scripts/test_smoke.sh                      # tiers 0-2   (PR minimum)
./scripts/test_full.sh                       # tiers 0-3
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh   # tiers 0-4
./scripts/test_rust.sh                       # host Rust
./scripts/test_aarch64_cross_build.sh        # cross target (after any rust/ change)
./scripts/test_lean_aarch64_archive.sh       # the kernel's Lean for the cross target
./scripts/test_tier5_cross_language.sh       # Lean <-> Rust lock oracle
SELE4N_REQUIRE_GATES=1 ./scripts/test_tier4_smp_bootcheck.sh   # gate honesty

# --- gates you can run alone -------------------------------------------
./scripts/test_tier0_hygiene.sh
./scripts/check_version_sync.sh
./scripts/check_website_links.sh
python3 scripts/check_identifier_naming.py
python3 scripts/check_module_axioms.py
python3 scripts/check_proof_depth.py
python3 scripts/check_ipc_invariant_dethreading.py
python3 scripts/check_aarch64_cross_target.py
python3 scripts/check_tlbi_broadcast_discipline.py
./scripts/check_production_staging_partition.sh

# --- version and docs --------------------------------------------------
./scripts/bump_version.sh <x.y.z>
./scripts/sync_documentation_metrics.sh
python3 scripts/generate_codebase_map.py --pretty [--check]
python3 scripts/generate_doc_navigation.py
python3 scripts/generate_smp_theorem_manifest.py [--check]
python3 scripts/report_current_state.py
./scripts/find_large_lean_files.sh [--format bullets]
```

---

## 14. Third-party code

seLe4n is GPLv3+ (see [`../LICENSE`](../LICENSE)). The Rust workspace pulls a
small set of **build-time only** crates (`cc`, `find-msvc-tools`, `shlex`) to
assemble ARM64 boot assembly; **no third-party code is linked into the runtime
kernel binary.** Their upstream MIT notices are reproduced verbatim in
[`../THIRD_PARTY_LICENSES.md`](../THIRD_PARTY_LICENSES.md).

1. Adding a **runtime** dependency (`[dependencies]` of any crate under
   `rust/`) means updating `THIRD_PARTY_LICENSES.md` in the same PR with the
   verbatim upstream copyright lines, and adding the path to
   `scripts/website_link_manifest.txt`.
2. Bumping an external crate means re-checking its `LICENSE-MIT` and
   `Cargo.toml` for authorship changes, and re-checking for a new upstream
   `NOTICE` (Apache-2.0 § 4(d)).
3. Prefer `core::*` and hand-written minimal code over a crate. **A
   microkernel's trusted computing base must stay small.**
