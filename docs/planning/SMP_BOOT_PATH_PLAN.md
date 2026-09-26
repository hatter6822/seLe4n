# WS-BP — The bare-metal boot path, and the cross-implementation
# agreement it ends

> **Status**: **IN FLIGHT — BP0, BP1, BP2, BP3, BP4, BP5 and BP6 LANDED at `v0.36.2`; BP7.10 LANDED at `v0.36.3`**; the rest of BP7, and BP8, not started.
> Unblocked at `v0.35.203`, WS-RR RR8 having closed.  Registered at `v0.34.59`
> by WS-RR RR7.5 + RR7.15 (register §6 findings 19, 40–44).  BP7.8 was added at `v0.35.203` by WS-RR
> RR8.16's hand-off check, which re-homed the registered `MR4`-onward
> IPC-buffer write here rather than leave it owned by a finished phase.
> BP3.5 was added at `v0.36.2` by BP3's own cut, which found the production
> boot state's proof-layer bundle stated nowhere (see the row).
> BP4.7 was added at `v0.36.2` by BP4.6's cut: mapping the RAM above the
> guaranteed gigabyte does not hand it to anyone, and the deployment's
> untypeds are variant-independent (see the row).
>
> **Workstream**: WS-BP.  **Absorbs WS-XV** (cross-implementation
> behavioural agreement), which was register-only and is now this plan's
> BP0 — see §4.1 for why the two belong in one document
> **Produces**: the content of **SM10.1**
> ([`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md) §3), whose
> `SM10.1.1` row — the `kernel8.img` packaging — is this workstream's BP5.3
> deliverable seen from the release cut's side
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Was blocked on**: **WS-RR** ([`SMP_RELEASE_READINESS_PLAN.md`](SMP_RELEASE_READINESS_PLAN.md)) —
> RR8 closed at `v0.35.203`, so this workstream may open
> **Consumed by**: SM10.2 (documentation), SM10.3 (the test suites that boot
> the kernel), SM10.5 (release validation) — every one of them takes an image
> **Audited cut**: `v0.34.3`
> ([`UNFINISHED_SMP_WORK.md`](UNFINISHED_SMP_WORK.md) §2.2)
> **Calendar estimate**: **9–20 weeks**, the figure
> [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md) §1.1 derives
> from a sized breakdown; this plan sequences that breakdown without
> re-pricing it
> **Sub-task count**: 50 across 9 phases (BP0..BP8), each phase numbered in
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
execution order, under `BP1..BP8`, with `BP0` added at `v0.34.124` for the
cross-implementation work WS-XV had registered and never scheduled.  Nothing
is renumbered — `BP0` sits *before* `BP1` precisely so that `BP2.6` and every
other cited ID keeps its meaning; something is numbered that never was.

## 2. What did not exist at `v0.34.59`

Measured, not assumed — the register's §2.2 table, re-verified at `v0.34.59`.
Every row below has since landed (BP0–BP6, `v0.36.2`) except the context
switch, which is BP7's; the table is kept as the baseline the plan was priced
against:

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

**BP0 is first because its value decays as the rest lands**, and it is the
one phase that may run **in parallel** with any other: it touches test
harnesses and generated tables, not the boot path itself.  Nothing in BP1..BP8
consumes it, and it consumes nothing — the only coupling is the other way
round, where BP2.6 changes what BP0.4 compares and must keep it passing.
Every other phase pair here is strictly sequential.

| Phase | Scope | Sub | Est |
|-------|-------|-----|-----|
| BP0 | Cross-implementation agreement — the pairs held while this path removes one of them | 4 | M |
| BP1 | aarch64 Lean object code — the cross-compile lane and `libsele4n.a` | 4 | L |
| BP2 | Bare-metal Lean runtime hosting — heap, shims, initialization, and the boot map the arena lives in | 6 | XL |
| BP3 | The RPi5 deployment — `PlatformConfig`, root task, labeling, the boot state's proof-layer bundle | 5 | L |
| BP4 | The boot seam — `lean_kernel_main`, its install ordering, and the board's RAM | 7 | L |
| BP5 | The bootable image — `[[bin]]`, the link, `kernel8.img`, the firmware's entry state | 5 | M |
| BP6 | Per-core readiness — the five dormant seams go live | 3 | M |
| BP7 | The context restore — TTBR0, the full frame, delivery, per-thread FP/SIMD state, the firmware's memory account, the initial threads' start | 11 | XL |
| BP8 | First boot and bring-up — QEMU, then the board | 5 | XL |

### 4.1 Why WS-XV is BP0 rather than a workstream of its own

WS-XV was registered at `v0.34.114` after the review rounds on PR #892 showed
that **twenty of thirty-six findings across nine rounds** were two
implementations of one question that had drifted.  It was never given a plan
file, and reading its five rows back shows why it should not have one: they
are not a workstream, they are this workstream's first phase and one of its
later rows.

- **XV1** — the device-tree pair's *removal* — was always a WS-BP obligation,
  and `v0.34.120` made it **BP2.6**.  It is not restated below.
- **XV2 and XV3** — a shared device-tree fixture corpus and a check that both
  suites consume all of it — are **interim by their own text**: *"only if XV1
  is far off"*.  BP2.6 was far off, so they were indicated.  BP2.6 then
  retired the `/memory` half of the pair they tie and kept the structural half,
  so they were retargeted onto that half rather than deleted (see the phase's
  preamble below).  A workstream whose work exists only until another workstream
  reaches a particular row is a phase of that workstream.
- **XV4 and XV5** — the ABI layout table and the boot-map pair — are the two
  genuinely two-sided pairs, permanent, and both sit on surfaces this plan
  changes: the ABI is what BP7's context restore delivers, and the boot map is
  what BP2.6 rebuilds.

So the merge is not tidying.  Half of WS-XV is deleted by this plan's own
work, and the other half is a harness over surfaces this plan modifies.  Held
apart, the two documents would each have had to describe the other's schedule
to be readable.

**What the merge does not claim.**  BP0 does not make the pairs behaviourally
equivalent; it makes a divergence *fail a gate* rather than wait for a
reviewer.  The three device-tree divergences fixed at `v0.34.121`–`v0.34.123`
were each found by a person reading two files side by side, which is the
method BP0 exists to replace and the evidence that the method does not scale.

## 5. Phases

### BP0 — Cross-implementation agreement (4 sub-tasks)

The tree maintains a verified Lean model beside an executable Rust HAL, and in
several places the same question is answered on both sides.  Every mechanical
gate that reconciles them today is **nominal** — `check_lock_ffi_symmetry.sh`
reconciles symbols and their types, `check_kernel_entry_exports.py` an
`extern` set against object code, `build.rs` the readiness seams against the
Lean `@[export]` inventory.  **None is behavioural**: nothing drives one input
through both implementations of a question and requires the same answer.  The
surface actually named "conformance" (`rust/sele4n-abi/tests/conformance.rs`,
114 tests) did it with hand-transcribed literals until BP0.3, so a Lean-side
layout change left every one of them green; since BP0.3 it reads
`tests/fixtures/abi_layout.expected`.

This phase is independent of BP1..BP8 and may run beside any of them.  Two of
its four rows (BP0.1, BP0.2) were written as **interim**, to be retired by
BP2.6 with the device-tree pair they tied.  **BP2.6 retired half of that pair**
— the Rust `/memory` walk the boot map was sized from — and kept the other half:
the bootargs reader still walks the structure block in Rust, after translation
is on, and "is this structure block readable at all" is still answered on both
sides.  So the corpus and its consumer check were **retargeted** rather than
retired: the manifest carries a hand-written `structure` verdict both suites
drive, and its `regions` column is the Lean parser's alone.  They stay for as
long as the Rust structure walk does.  The other two rows are permanent.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| BP0.1 | **LANDED `v0.36.2`.**  **The shared device-tree fixture corpus** (was XV2).  Blobs checked in as reviewable hex with a generator, and a manifest stating the regions each declares and the RAM top they imply, read by **both** the Rust walker's suite and the Lean parser's.  A filter added to one side alone then fails that side's assertion instead of passing silently.  **Retargeted** when the boot map stopped reading the device tree: the Rust `/memory` walk is retired, so the manifest's Rust-read column is a hand-written `structure` verdict (`readable` / `refused`) both suites drive against `fdt_structure_check` and `parseFdtNodes` + `fdtRoot?`, and its `regions` column is the Lean parser's alone — the phase preamble says why it stays | `tests/fixtures/dtb/`, `rust/sele4n-hal/src/cmdline.rs`, `tests/Ak9PlatformSuite.lean` | M |
| BP0.2 | **LANDED `v0.36.2`** (`scripts/check_dtb_corpus_consumers.py`).  A Tier 0 check that **both** sides consume **every** fixture of the corpus, so adding a case to one suite alone is a failure rather than a silent gap.  Consumes BP0.1.  **Retargeted** with it: the Rust body it requires drives `fdt_layout` and `fdt_structure_check`, the Lean runner `corpusStructureReadable` beside `corpusDeclaredRegions` | `scripts/`, `tests/fixtures/dtb/` | S |
| BP0.3 | **LANDED `v0.36.2`** (`tests/fixtures/abi_layout.expected`, which also carries the register assignment from `arm64DefaultLayout`).  **The ABI layout, stated once** (was XV4).  Emit the `MessageInfo` field layout and its bounds from Lean — the field shifts, `maxLabel`, `maxMessageRegisters`, `maxExtraCaps`, `errorLabelBase`, `SYSCALL_ABI_VERSION` — into a checked-in table, and have the Rust conformance suite assert its own constants against it, with a Tier 0 freshness gate on the pattern `generate_smp_theorem_manifest.py --check` already sets.  Today both sides spell `(length) \| (extraCaps <<< 7) \| (label <<< 9)` by hand.  **Permanent**: this pair is genuinely two-sided, the Rust encoder being the userspace ABI and the Lean decoder the kernel's | `SeLe4n/Model/Object/Types.lean`, `rust/sele4n-abi/`, `scripts/` | M |
| BP0.4 | **LANDED `v0.36.2`** (`tests/fixtures/boot_map.expected`; `DEVICE_WINDOW_TOP` made exact, the straddling block described by an L3 table — deleted later in `v0.36.2` by the BCM2712 address-map correction, which put the window on the SoC bus at `0x10_7C00_0000`, block aligned at both ends, and added the fixture's `mmio` lines the HAL's UART and GIC tests read).  **The boot-map pair, driven rather than mirrored** (was XV5).  One address set through `mmu::boot_mapping_for` and `rpi5MemoryMapForConfig`, replacing the single `the_boot_map_boundaries_mirror_the_lean_memory_map` test and the comment that says the boundaries "mirror" the Lean map.  Reuses BP0.3's emitter, so it is materially cheaper second.  **Permanent**, and the one row a later phase must keep passing: the boot map's extent changes source, not the requirement that the two sides agree on it | `rust/sele4n-hal/src/mmu.rs`, `SeLe4n/Platform/RPi5/Board.lean` | S |

**Acceptance**: a divergence introduced on either side of any of the three
pairs fails a gate rather than a review; and `check_lock_ffi_symmetry.sh`'s
docstring no longer overstates what a nominal reconciliation proves.

**Met at `v0.36.2`**, each clause by a mutation rather than by an artefact
existing: the corpus fails on the pre-fix Lean parser (8 fixtures) and the
pre-fix Rust walker (13); the ABI table fails on a moved label shift and on two
swapped register slots; the boot-map table fails on the old 2 MiB round-up.
Where the two sides disagreed, the side that was wrong was fixed rather than the
divergence recorded — see `CHANGELOG.md` `v0.36.2` for the twenty-two fixes (twenty-one in the device-tree pair, one in the boot map).  One
decision the rows did not anticipate: BP0.3's freshness is decided where Lean
can be asked (the suite that emits the table, Tier 2, and the Rust suite that
reads it) rather than by a Tier 0 script, because deriving the table before a
build would mean reading Lean source with a scanner, which this project retires;
Tier 0 holds the *wiring* (both consumers named and reading the file) through
the fixture index's `Used by` reconciliation.

### BP1 — aarch64 Lean object code (4 sub-tasks)

The kernel's proofs are Lean; the target has no libc and no host toolchain.
Everything downstream needs Lean object code for `aarch64-unknown-none`, so
this is first.

**The kernel is FP-free, and that is a property of its object code**
(`v0.36.2`).  `boot.S` traps every FP/SIMD access at EL0 and EL1 from each
entry's first instruction at EL1 (`msr cpacr_el1, xzr`, written once
`.L_enter_el1` has returned — at EL2 with `HCR_EL2.E2H` set, which is UNKNOWN
at reset, that encoding names `CPTR_EL2`; the `v0.36.2` audit reordered the
two), and the trap frame saves
general-purpose registers only, so no kernel object may carry an FP/SIMD
register operand: at EL1 it would halt the core, and with the trap lifted it
would silently overwrite the interrupted thread's `q0`–`q31`.  The HAL is
built for `aarch64-unknown-none-softfloat` for that reason — the hard-float
target put 129 vector instructions in it — and
`scripts/check_fp_simd_free_objects.py` verifies the release objects in the
cross gate.  The Lean C this phase emits is held to the same rule, which is
why BP1.2 compiles it with `-mgeneral-regs-only` and runs that gate over it.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| BP1.1 | **LANDED `v0.36.2`** (`scripts/build_lean_aarch64_archive.py`).  The production closure's Lean C output — the C for `SeLe4n.lean`'s import closure and nothing else, so a staged or test module cannot reach the image.  The closure is the **elaborator's** (`Environment.header.moduleNames` of `SeLe4n`: 258 package + 609 stdlib modules), refused unless its package half equals Lake's `SeLe4n:modules`, it holds nothing outside `SeLe4n`/`Init`/`Std` and it is disjoint from the staged allowlist and `SeLe4n.Testing`.  Package C is Lake's module `c` facet for exactly those modules; stdlib C is regenerated by the toolchain's own `lean -c` (the toolchain ships `libInit.a`/`libStd.a` and no C), cached per toolchain hash.  **Files corrected**: `lakefile.toml` cannot declare a custom target, so the target is the script driving Lake's facet rather than a Lake declaration | `scripts/` | M |
| BP1.2 | **LANDED `v0.36.2`**.  Cross-compile that C to `aarch64-unknown-none` with the toolchain's own clang (the compiler `leanc` uses), `-ffreestanding -nostdlibinc`, `-mgeneral-regs-only -mabi=aapcs-soft -mstrict-align` (Rust's `aarch64-unknown-none-softfloat`: `+v8a,+strict-align,-neon`, static relocation), no libc, and run `scripts/check_fp_simd_free_objects.py` over the objects.  `-mgeneral-regs-only` turns `double` arithmetic into soft-float library calls with a general-register ABI (measured: a multiply becomes a call, a negation an `eor`), which is what lets the runtime's `Float` coexist with the EL1 FP trap; `-mabi=aapcs-soft` is what makes a `double` **parameter** legal there at all (clang 19 refuses one without it) and passes it as a soft-float Rust caller does.  `lean.h`'s allocator is selected by a kernel `lean/config.h` (`rust/sele4n-hal/lean_include/`): the toolchain's with `LEAN_MIMALLOC` replaced by `LEAN_SMALL_ALLOCATOR`, held to that relation on every build and confirmed on the objects (they call `lean_alloc_small`, no `mi_*`).  `-Wall -Wextra -Werror`, with the generator's two by-construction shapes demoted to warnings and **classified per instance** (87 discarded-`BaseIO Unit` temporaries, 1 import-less initializer's `res`).  Measured: 3,670,048 instructions, no FP/SIMD register operand | `scripts/`, `rust/sele4n-hal/lean_include/` | L |
| BP1.3 | **LANDED `v0.36.2`** (`scripts/test_lean_aarch64_archive.sh`, CI job `Lean aarch64 Archive`).  Archive the objects as `libsele4n.a` (deterministic, members sorted), the name `rust/sele4n-hal/src/boot.rs` already asserts is linked, and add the CI lane that builds it.  The archive is checked, not trusted: one module initializer per object and per closure module, every initializer referenced defined, no symbol defined twice, and **every regenerated stdlib module defines exactly the global symbols the toolchain's own object for it defines** (609 of 609).  Its unresolved set is written **attributed by provider**, each class derived from the provider's own object code or declarations, and an unattributed symbol stops the build.  Since the kernel's own runtime landed (BP2) the classes are 1 allocator (`lean_alloc_small`, which the mimalloc host runtime lacks), 73 HAL (the kernel's `@[extern]`s; 74 since the boot map's extension binding `ffi_extend_boot_ram_map` landed later in `v0.36.2`, which takes the total to 382), 118 runtime (the kernel's own), 78 compiler builtins (Rust's `compiler_builtins` for the target) and 111 *unreachable* (upstream runtime functions and stdlib `@[extern]`s — `acosh`/`asinh`/`atanh` among them — that the lane's reachable link proves no initializer or kernel entry names); at BP1 the runtime class was upstream's `libleanrt.a`, which the kernel no longer links | `scripts/`, `.github/workflows/` | M |
| BP1.4 | **LANDED `v0.36.2`**.  Point `scripts/check_kernel_entry_exports.py` at the **cross** archive as well as the host one, so its `EXPECTED_UNRESOLVED` reconciliation decides the symbol set the image actually links: a requirement is met only where **both** archives define it, an exemption is stale where **either** does, and `--require-cross` (which the lane passes) makes an absent cross archive a failure rather than a narrower check.  Reading the pair that way is fail-closed for a stale cross archive.  Consumes BP1.3 | `scripts/check_kernel_entry_exports.py` | S |

**Acceptance**: `libsele4n.a` exists for `aarch64-unknown-none`, CI builds it
on every push, and the export gate reads it.  **Met at `v0.36.2`.**

### BP2 — Bare-metal Lean runtime hosting (6 sub-tasks)

The largest single unknown in the workstream, and the one with no precedent
in this tree to calibrate against.  The Lean runtime expects a heap, a small
set of libc entry points, and an initialization handshake; the target
supplies none of them.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| BP2.1 | **LANDED `v0.36.2`** (`rust/sele4n-hal/src/lean_heap.rs`, `link.ld`).  A kernel heap arena in the image's own memory, and the allocator behind `lean_alloc_small` / `lean_alloc_object` / the free paths.  Its extent is a boot-time constant the linker script places, not a runtime negotiation: `link.ld`'s `NOLOAD` `.lean_heap` section of `LEAN_HEAP_SIZE` (64 MiB), bounded by `__lean_heap_start` / `__lean_heap_end`, above the image and both stack regions, with three `ASSERT`s — whole pages, page-aligned, and ending inside the smallest board's `[0, 1 GiB)` — each proved live by `scripts/check_link_script.py` (cross lane step 6), which links a probe under the script and mutates it until every assertion fires.  The HAL exports `lean.h`'s three small-allocator functions under `hw_target` (512 classes, indexed as `lean_get_slot_idx` indexes them) and a general `malloc`-shaped interface over the same arena, so `lean_alloc_object`'s big path is served by the one heap the next row's libc surface calls.  **All allocator state is out of band** — a page map, a free-page bitmap and per-page occupancy bitmaps in the arena's leading pages — so the allocator never touches the memory it serves, every free is validated (a double free is refused, not absorbed), each operation is bounded (eight words per small allocation; a bitmap scan from the first free word per page run), an emptied small page returns to the pool, and the C entry points halt on a refusal and on exhaustion.  The arena lies inside the guaranteed gigabyte the boot map covers, and `mmu::kernel_extent` keeps the device-tree window off it (the boot map built from constants, later in this phase, retired `mmu::image_ranges`), and the Lean lane now verifies that the HAL's object code defines every symbol the archive attributes to it (the allocator and the 73 production `@[extern]`s — 74 since `ffi_extend_boot_ram_map`).  **What the runtime inherits**: upstream's `alloc.cpp` defines the same three functions under `LEAN_SMALL_ALLOCATOR`, over per-thread heaps built on `new` and `std::vector`; the kernel's runtime (the next row) links none of it — its big-object path and scratch buffers call `Heap::alloc` / `Heap::free` on this arena, so one allocator serves the inline paths and the runtime | `rust/sele4n-hal/src/`, `rust/sele4n-hal/link.ld` | L |
| BP2.2 | **LANDED `v0.36.2`** (`rust/sele4n-hal/src/lean_runtime/`).  **The kernel's own Lean runtime, in Rust** (maintainer's decision at this row: no C++ in the image).  Upstream's runtime is `libleanrt` — C++ over the C++ standard library, threads and an operating system — and the toolchain ships it only for the host; the kernel instead provides the part its Lean objects reach.  **That part is derived, not chosen**: the builder's step [7/8] links `libsele4n.a` with `--gc-sections` rooted at the library initializer and every production `@[export]`, and requires every symbol that link leaves undefined to be a global function of the HAL's rlib for the target, or `compiler_builtins`'.  **Measured at `v0.36.2`**: the archive references 381 symbols it does not define (382 since `ffi_extend_boot_ram_map`); the reachable link needs **144** (8 kernel exports + the initializer; 145 since `ffi_extend_boot_ram_map`, a HAL symbol), of which the runtime provides **118**; the other **111** upstream runtime functions and stdlib `@[extern]`s are classified *unreachable* and provably dropped — which makes the image link's `--gc-sections` over those roots an obligation of BP5's image link, not a choice.  (An earlier measurement of 62 rooted the link at `initialize_SeLe4n`; the initializer carries the package prefix, `initialize_seLe4n_SeLe4n`, and the root was silently absent — the lane now takes the root from the archive's own initializer.)  **Three kinds of symbol, each recorded where it is defined**: *faithful* — objects and the iterative last-reference release (the to-do list threaded through freed headers, as upstream does, so a million-cell list frees without recursion), persistence, closures at every arity (one algorithm, `lean_apply_1`..`16`, `_n`, `_m`), arbitrary-precision `Nat`/`Int` (sign and magnitude over 64-bit limbs; Knuth division with Theorem B's two-correction bound asserted), strings and UTF-8 navigation, arrays, `ST.Ref`, `Name.beq`, `ShareCommon`, the two Murmur hashes — each ported from `lean4` at the toolchain's commit; *environmental* — platform queries, `Lean.githash` (pinned to `lean --githash` by the lane), zero-byte entropy, temporary files failing with `unsupportedOperation`; *fail-closed* — `Float` formatting, `scaleB` and `pow`/`powf` halt (the last override `compiler_builtins`' weak libm port by the linker's own rule, which the lane checks is weak).  **Upstream is the oracle**: `tests/LeanRuntimeConformanceSuite.lean` runs on upstream's runtime and holds `tests/fixtures/lean_runtime_conformance.expected` (9 215 results over a boundary corpus: the `2^63` and `±2^31` representation edges, limb edges, signs, zero divisors, every UTF-8 width, positions inside a character and past the end) to what upstream computes; `lean_runtime::conformance` recomputes every line with the kernel's runtime, on both the exclusive and shared paths of each mutating string operation, checks every result canonical, and ends with the heap holding exactly what it held.  **What the environmental answers rest on is proved, not assumed**: `SeLe4n/Testing/RuntimeEnvironmentCensus.lean` (Tier 1) walks everything every production `@[export]` reaches — bodies and `implemented_by` — and fails if it meets `IO.stdGenRef` or a constant implemented by one of the nine unprovided symbols, so the zero seed is dead and a kernel use of randomness, a file or a float's text fails the build.  The runtime never calls back into the program it serves (`build.rs`'s readiness scanner refused the first draft's call to an `@[export]`ed `IO.Error` builder).  Not a libc surface: the kernel's Lean objects call no libc symbol, and the runtime is Rust | `rust/sele4n-hal/src/`, `tests/`, `SeLe4n/Testing/`, `scripts/` | L |
| BP2.3 | **LANDED `v0.36.2`** (`rust/sele4n-hal/src/lean_entry.rs`).  The library initializer (`initialize_seLe4n_SeLe4n`, `builtin = 1`) called once, on the primary, before any Lean code runs, its `IO` result checked.  Upstream's `lean_initialize_runtime_module` and `lean_io_mark_end_initialization` set up thread-local heaps, the task manager and an "initialization finished" flag the kernel's runtime does not have (its heap is taken into service on first use, it has no thread state, and no production path reads the flag), so this row calls neither unless the reachable link starts to name them.  The call the entry makes is measured on the host first: `SeLe4n`'s initializer, run under upstream's runtime, calls 39 runtime functions — every one a faithful or environmental symbol of BP2.2.  **The order is a type, not a convention**: `lean_kernel_main` is reachable only through `enter_lean_kernel`, which consumes a `LeanLibraryInitialised` token that only a successful `initialise_with` constructs (private field, neither `Clone` nor `Copy`), so entering the kernel uninitialised or twice from one initialization does not compile; a second initialization is refused at runtime by a guard set *before* the initializer runs, since Lean's generated initializer marks itself done before it calls anything and would answer `ok` to a retry.  An `IO` result is success exactly when it is a heap constructor of tag 0; a scalar or any other tag is refused as malformed, never read as success, and the result's reference is released either way.  `build.rs`'s readiness derivation now recognises a HAL-declared `initialize_…` symbol as Lean code (`is_hal_declared_lean_symbol`, shared with the `link_name` alias scan), so the initializer call is an ungated upcall registered in `LEAN_UPCALLS_OUTSIDE_THE_GATE` with its reason — dropping the prefix from the predicate fails the build through that entry — and `check_kernel_entry_exports.py` now requires both archives to define the initializer.  Consumes BP2.1 and BP2.2 | `rust/sele4n-hal/src/lean_entry.rs`, `rust/sele4n-hal/src/boot.rs` | M |
| BP2.4 | **LANDED `v0.36.2`** (`rust/sele4n-hal/src/lean_entry.rs`).  Fail closed when initialization cannot complete — an `IO` error, a malformed result, or a second run — rather than entering a kernel whose runtime is half-built.  Never a silent continue.  **The halt is `gic::halt_all()`, not the per-PE `cpu::fatal_halt()` this row first named**: by the time the primary initializes the library the secondaries have entered `rust_secondary_main`, unmasked IRQs and are servicing interrupts, so parking the boot PE alone would leave them running for a kernel that was never entered — the reason `boot.rs`'s IRQ-readiness topology refusal uses the same barrier (PR #889 review round 22).  The refusal is reported on the boot UART by kind; the `IO.Error` itself is released unread, because reading it means calling back into Lean and the runtime never does | `rust/sele4n-hal/src/lean_entry.rs` | S |
| BP2.5 | A host witness suite for the shims and the allocator — the arena's bounds, exhaustion, alignment — since the first place they run for real is a board with no debugger attached.  **Both halves have landed**: the runtime's with BP2.2 (`lean_runtime::tests`: a 200 000-cell list released without recursion, persistence over a shared graph, external finalizers, closures exact, under- and over-applied at arities 1–20 on exclusive and shared closures, arrays and byte-array slicing against upstream's clamping, the lossy UTF-8 decoder, reference cells, `Name` equality, `ShareCommon`'s hash consistency, the environmental answers, Knuth division against bit-by-bit long division over structured divisors, and every fail-closed path; fourteen token-preserving mutations of the runtime are each caught, and the one equivalent mutant found — a length argument the next statement overwrites — is dropped rather than counted); **the allocator's half landed with BP2.1** (`lean_heap::tests`: the layout's maximality and disjointness, every size class, every alignment to a page, capacity and page recycling, every refused free including a double free, run coalescing, exhaustion and recovery on a private heap and on the kernel heap, and a 30 000-step random trace against a model of the live set, the invariant checked after every mutation; ten token-preserving mutations of the allocator are each caught) | `rust/sele4n-hal/src/` | M |
| BP2.6 | **LANDED `v0.36.2`** (`rust/sele4n-hal/src/mmu.rs`, `link.ld`).  **The boot map is built from constants, and nothing is parsed before translation is enabled.**  `init_mmu` used to walk the firmware's device tree for a RAM size *before* the MMU was on — an attacker-influenced parser with no memory protection and no recovery but a halt — to size a map that needs no size.  **The map**: `[0, GUARANTEED_RAM_TOP)` Normal — the 1 GiB every Raspberry Pi 5 has, which the driven BP0.4 comparison requires to be RAM in every variant and all of the smallest one's — with the image's text read-only and executable, its read-only data read-only and never executable, and everything else (data, `.bss`, both stacks, the Lean heap, the rest of the gigabyte) writable and never executable; the device window Device; everything else unmapped.  `boot_mapping_for(addr, layout)` is a function of the address and the image's layout (`ImageLayout`, `link.ld`'s `_start` / `__text_end` / `__rodata_end`, page aligned and adjacent by `ASSERT`) and nothing else, and `is_boot_cacheable_range` was a pure constant question until the RAM above the gigabyte was mapped (`extend_boot_ram_map`), which made it the union over the runtime extension record.  **This deviates from the row's first wording on purpose**: mapping only the image, stacks, arena and a DTB window would have left every cache-maintenance operand outside the image — page tables, retyped frames — failing closed with nothing scheduled to map them; the guaranteed gigabyte is a board constant, and RAM above it is mapped by the boot seam's last row, after the verified parse.  **The device tree** is not read here at all: `init_mmu` only checks that the window a reader may dereference (`dtb_window`, `MAX_DTB_SIZE` from the pointer — the bound every reader enforces before forming a slice) lies in guaranteed RAM and outside `[_start, __lean_heap_end)` (`dtb_window_admissible`), and refuses otherwise.  **Retired**: `ram_top_from_dtb`, `find_ram_top_in_dtb`, the `/memory` fold and contiguity machinery, `clamp_ram_top`, `boot_ram_top`, `dtb_dereferenced_range`, `boot_ranges_mapped_under`, `boot_critical_ranges_mapped`, `UNDESCRIBED_RAM_TOP` and the RAM-top constants — Tier 3 negatives refuse each.  **The bootargs reader stays** (a Rust-only question with no Lean counterpart, which QEMU lanes use), now reading with translation on inside the checked window; so the structure-readability pair stays two-sided and **BP0.1/BP0.2 are retargeted rather than retired** (see BP0's preamble).  **Found while building it**: every Normal page was mapped writable and PXN-clear while `SCTLR_EL1.WXN` is set, which makes a writable page execute-never — the first fetch after `enable_mmu` would have faulted, invisible only because no image has run.  The text now has its own read-only descriptor and data states PXN; `no_page_is_writable_and_executable_and_the_text_executes` checks every mapped page.  **And the firmware's DTB window must lie in the guaranteed gigabyte and outside the image**: the firmware places the blob by the image *file*'s size, and everything past it is `NOLOAD` (BP2.1's finding); the image build's `config.txt` pins `device_tree_address` so the placement is a stated contract.  Consumes BP2.1 | `rust/sele4n-hal/src/mmu.rs`, `rust/sele4n-hal/src/cmdline.rs`, `rust/sele4n-hal/link.ld` | L |

**Acceptance**: a Lean `IO` action that allocates runs to completion on
`aarch64-unknown-none` under QEMU, the arena's exhaustion path halts, and
`init_mmu` names no device-tree entry point — the boot map is built from
linker symbols and board constants alone.

### BP3 — The RPi5 deployment (5 sub-tasks)

Register finding 44: there is no `rpi5PlatformConfig`, no root task, and no
initial objects.  The boot seam in BP4 boots *a configuration*; this phase
is that configuration, and it is placed before the seam because a seam with
nothing to boot cannot be reviewed.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| BP3.1 | **LANDED `v0.36.2`** (`SeLe4n/Platform/RPi5/Deployment.lean`).  `rpi5PlatformConfig`, the caller's half: the IRQ table routes every SPI the interrupt contract supports (INTIDs 32–223) to the root task's notification, badged by INTID — SGIs are the kernel's inter-processor channel and PPIs are per-core, so neither is delegated — and the machine configuration is the board account (the smallest board's), which `bindPlatformConfig` binds to a variant alongside the binding's boot root | `SeLe4n/Platform/RPi5/` | M |
| BP3.2 | **LANDED `v0.36.2`**.  The initial objects, in two domains as `confinedDeploymentLabeling` declares them: the root task (TCB `2`, CNode `3`, VSpace `4` on ASID 1, notification `5`, untypeds `6`/`7` over `[256 MiB, 1 GiB)`) and the untrusted initial thread (TCB `0x10_0000`, its CNode and VSpace on ASID 2), each `.Inactive`, stored under its own id, with all three queue links empty, and no capability crossing the boundary.  **"Its VSpace" needed the boot to admit one**: the checked boot refused every configured VSpace root (`noVSpaceRootsInInitialObjects`) because the builder registered no ASID, so the only VSpace it could install was the kernel's EL1-only map; the write is made (`createBootObject`, `bootEntryAsidTable`), a collision is refused (`bootVSpaceAsidsDistinct`), and a configured root is checked as a thread's — a user ASID and no mappings (`bootSafeUserVSpaceRootCheck`).  **And the untypeds, with the boot refusing one over memory it may not describe** (closes `docs/REGISTERED_DEBT.md` table B's row): `PlatformConfig.wellFormed`'s seventh conjunct `untypedPlacementRespected` — inside one declared region of its own kind, clear of `MachineConfig.kernelReserved`, and pairwise disjoint (the runtime check of the proof bridge's `untypedRegionsDisjoint`).  The RPi5 reserved extent is `[0, 0x1000_0000)`, one number in three places — `rpi5KernelReservedEnd`, `link.ld`'s `KERNEL_RESERVED_END` (whose `ASSERT` refuses an image that outgrows it) and `mmu::KERNEL_RESERVED_END` — held together through `tests/fixtures/boot_map.expected` by the HAL's test and `scripts/check_link_script.py`; the device-tree window must lie in it (`dtb_window_admissible`), so no untyped can describe the blob | `SeLe4n/Platform/RPi5/`, `SeLe4n/Platform/Boot.lean`, `rust/sele4n-hal/` | L |
| BP3.3 | **LANDED `v0.36.2`**.  Every gate of the checked boot discharged **by evaluation**, with no `native_decide`: the boot's hash-set duplicate checks are proved equal to their transparent forms (`irqsUnique_eq_transparent`, `objectIdsUnique_eq_transparent`), after which `rpi5BoundPlatformConfig_wellFormed` (all seven conjuncts) and the nine other gates are `decide`; `rpi5BoundPlatformConfig_checked` and `rpi5BoundPlatformConfig_boot` pin the success arms — generalised per variant once the device tree selected the board, so the live statements are `rpi5BoundPlatformConfigAt_wellFormed`, `rpi5BoundPlatformConfigAt_checked` and `rpi5BoundPlatformConfigAt_boot` (`v : BCM2712Config`).  Consumes BP3.1 and BP3.2 | `SeLe4n/Platform/RPi5/` | M |
| BP3.4 | **LANDED `v0.36.2`**.  Both separated threads are TCBs of the boot state (`rpi5DeploymentBootState_witnessesInstalled` (now `rpi5DeploymentBootStateAt_witnessesInstalled`, per variant since the device tree selects the board)), read off the configuration through the new general `bootFromPlatformChecked_ok_objects_of_mem` — every configured object is in a successful boot's state at its own id — rather than evaluated out of the boot.  The acceptance: `bootAndInitialiseRPi5_rpi5PlatformConfig` (now `bootAndInitialiseRPi5_rpi5PlatformConfigFor`) (the hardware entry commits the state and labeling and returns `.ok`) and `bootAndInitialiseRPi5OrHalt_rpi5PlatformConfig` (now `bootAndInitialiseRPi5OrHalt_rpi5PlatformConfigFor`) (the halting entry is exactly the two installs).  Consumes BP3.2 | `SeLe4n/Platform/RPi5/` | M |
| BP3.5 | **LANDED `v0.36.2`**.  `bootFromPlatformCheckedWithIdleThreadsFor_proofLayerInvariantBundle` proves the bundle of the checked, idle-enqueued boot of any configuration the checked boot accepts over any duplicate-free core list, `bootToRuntime_invariantBridge_checked` adds its freeze, and `rpi5DeploymentBootState_invariantBridge` is the deployment's instance.  Both boots are instances of one argument, `proofLayerInvariantBundle_of_bootShape`, over a boot-shaped state (`bootObjectShape`, `bootQuiescentFields`, ASID-table consistency, the scheduler's run-queue facts); the unchecked theorem is now its first instance rather than a second copy.  Proving it found the checked boot's CNode check blind to slot contents — a reply capability or an out-of-range badge passed and the installed state violated the capability bundle — so `bootSafeCapCheck` refuses both and `bootSafeObjectCheck_sound` (was `…_sound_structural`, partial) is whole.  *As registered:* **The production boot state's proof-layer bundle.**  `bootFromPlatform_proofLayerInvariantBundle_general` and `bootToRuntime_invariantBridge_general` are stated over the *unchecked* `bootFromPlatform` of a config carrying no VSpace root, and the state the hardware boot installs is neither: it carries the binding's root (since WS-RC R3) and the threads' roots (since BP3.2), and the checked boot enqueues idle threads on top.  So no theorem states `proofLayerInvariantBundle` — or its freeze — of `rpi5DeploymentBootState`, and the bridge's docstring called that "a post-R3 hardening item" registered nowhere.  State and prove it for the checked, idle-enqueued boot of any well-formed config (the RPi5 deployment an instance), which needs the VSpace bundle over installed roots: the ASIDs `bootVSpaceAsidsDistinct` keeps apart are what `vspaceAsidRootsUnique` and `asidTableConsistent` read, and a thread's root maps nothing.  **Before the boot seam**: the next phase's first row makes this boot live, and a transition goes live only after the proofs that cover it.  Registered in `docs/REGISTERED_DEBT.md` table C.  Consumes BP3.4 | `SeLe4n/Platform/Boot.lean`, `SeLe4n/Platform/RPi5/` | L |

**Acceptance**: `bootAndInitialiseRPi5OrHalt rpi5PlatformConfig` evaluates to
`.ok` in Lean, with every refusal arm shown unreachable for this
configuration (met at `v0.36.2`: `bootAndInitialiseRPi5OrHalt_rpi5PlatformConfig`),
and the state it installs satisfies the proof-layer invariant bundle (met at
`v0.36.2`: `rpi5DeploymentBootState_invariantBridge`, BP3.5).  BP4.4 generalised
both over every board account the device tree can supply and retired the
single-board names: `bootAndInitialiseRPi5OrHalt_rpi5PlatformConfigFor` and
`rpi5DeploymentBootStateAt_invariantBridge` are the live statements.

### BP4 — The boot seam, its install ordering and the board's RAM (7 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| BP4.1 | **LANDED `v0.36.2`** (`SeLe4n/Platform/RPi5/KernelMain.lean`, in the library root).  `SeLe4n.Platform.RPi5.kernelMain`, `@[export lean_kernel_main]`, is `Platform.FFI.bootAndInitialiseRPi5OrHalt rpi5PlatformConfig` and nothing else; `BootEntryContract.lean` accepts it by its head-directed reduction and, since the entry exists, **refuses an environment with none** rather than logging the contract vacuous.  `kernelMain_installs` states the program it is: the deployment's boot state and the binding's labeling installed, the halt arm never taken.  `check_kernel_entry_exports.py`'s `EXPECTED_UNRESOLVED` is **empty** and both archives define the symbol (10 HAL declarations); the export-commit census records the eighth committing seam as unbracketed with the ordering as its reason, and nineteen boot-path transformers left the reachability census's pin because a committing export now reaches them.  The reachable link rooted at the initializer and the nine kernel exports still needs **144** symbols (145 since `ffi_extend_boot_ram_map`, a HAL binding) — the boot path adds no runtime symbol.  The device-tree pointer was not yet read; a later row of this phase moved the entry onto the device-tree wrapper, so the body quoted here is the landing's, not HEAD's | `SeLe4n/Platform/RPi5/KernelMain.lean` | M |
| BP4.2 | **LANDED `v0.36.2`**, as a type.  `rust_boot_main` runs the library initializer and the install in Phase 5, on the boot core alone, and releases the secondaries in Phase 6; the PE-topology refusal moves after the release, to Phase 7, which cost nothing until BP6 made every PE Lean-ready in the same version.  The order is not a comment: `smp::bring_up_secondaries_inner`, which every bring-up path reaches, consumes a `lean_entry::SecondaryReleasePermit`, and on an image that links the kernel (`hw_target`) the only one is what `enter_lean_kernel` returns after `lean_kernel_main`; an image without the kernel gets `SecondaryReleasePermit::no_lean_kernel`, which does not exist under `hw_target`.  The permit is neither `Clone` nor `Copy`, so one install licenses one release.  The lost-commit shape `kernel_entry.rs` documented is closed by construction rather than by a lock (option 1 of `SMP_RELEASE_CLOSURE_PLAN.md` §3) | `rust/sele4n-hal/src/boot.rs`, `rust/sele4n-hal/src/lean_entry.rs`, `rust/sele4n-hal/src/smp.rs`, `rust/sele4n-hal/src/cmdline.rs` | M |
| BP4.3 | **LANDED `v0.36.2`**.  `lean_entry::enter_lean_kernel` reads the firmware's blob through `cmdline::dtb_blob_from_ptr` — header first, `totalsize` bounded by `MAX_DTB_SIZE`, inside the window `init_mmu` admitted — and copies it onto the kernel's Lean heap (`lean_runtime::array::byte_array_of`), handing the `ByteArray`'s one reference to `lean_kernel_main`.  A pointer that yields no blob is handed over as the **empty** array rather than refused in Rust, so the verified parser is the one owner of the refusal.  The Rust declaration is `fn lean_kernel_main(dtb: Obj) -> LeanIoResult`, held by `check_kernel_entry_exports.py` to the C the Lean compiler generated.  *As registered:* turn `rust_boot_main`'s `dtb_ptr` into the `ByteArray` `bootAndInitialiseRPi5FromDtbOrHalt` takes — a Lean-runtime allocation, hence the dependency on BP2.  This is what gives WS-RR RR7.27's board-versus-binding check a hardware caller | `rust/sele4n-hal/src/boot.rs`, `SeLe4n/Platform/FFI.lean` | M |
| BP4.4 | **LANDED `v0.36.2`**.  `kernelMain (dtb : ByteArray)` is `bootAndInitialiseRPi5FromDtbOrHalt dtb rpi5IrqTable rpi5InitialObjects none` (the object list is now `rpi5InitialObjectsFor`, a function of the variant); `approvedBootCall` is that wrapper, the entry's type `ByteArray → BaseIO Unit`, and the blob must be the entry's **own parameter** — a fixed blob, an edited copy and the retired `bootAndInitialiseRPi5OrHalt` call are refused witnesses.  It was not one line: the device tree now selects the RAM variant, so BP3's single-board proofs were generalised — every gate decided on each of the five variants (`rpi5BoundPlatformConfigAt_*`), the boot proved for every board account (`bootAndInitialiseRPi5_rpi5PlatformConfigFor`), the smallest-board `rpi5PlatformConfig` retired — and `rpi5PlatformConfigFromDtb_ok_eq_fromDeviceTree` lets `kernelMain_refuses` / `kernelMain_installs` name the halt and the installed state.  `tests/Ak9PlatformSuite.lean` runs the decision on 1, 2, 3, 4 and 8 GiB device trees.  *As registered:* move the boot entry to the DTB wrapper and `BootEntryContract.lean`'s `approvedBootCall` with it — the one-line change that file anticipates by name.  Consumes BP4.3 | `SeLe4n/Testing/BootEntryContract.lean` | S |
| BP4.5 | **LANDED `v0.36.2`**.  `lean_entry::enter_lean_kernel` runs `cache::clean_boot_image_to_pou` after the install and immediately before it mints the `SecondaryReleasePermit`: `CleanRangeIallu` (op tag 3, the model's `bootImageIcacheOp`) over the image's loaded bytes, `link.ld`'s `[_start, __image_load_end)`, which a live-by-mutation `ASSERT` holds between `__rodata_end` and `__bss_start`.  `kernelCodeWriteEmitted .bootImageLoad` is `true`, `bootImageIcacheOp_discharges_obligation` proves the operand discharges the obligation, and `kernelCodeWriteSites_all_emitted` replaces the partition marker.  The row as registered: **The boot image's clean-to-PoU** (WS-RR RR7.20, SM7.D deferred item 4).  `kernelCodeWriteEmitted .bootImageLoad = false` records that the one remaining kernel-code-write site emits no `DC CVAU` → `DSB ISH` → `IC IALLUIS` sequence, and `kernelCodeWriteSites_emission_pending` pins that it is the only one.  The initial task's code is in the image before the first instruction fetch, so the clean must run in the boot seam before any user code can be fetched — the site could not name its extent while there was no image and no physical backing, which is why SM7.D deferred it here rather than closing it.  Flipping the `kernelCodeWriteEmitted` arm breaks a `decide`, so the closure cannot land silently.  Consumes BP4.2 (the install ordering).  The emission needs no image — it is a boot-seam instruction sequence — so this row does not wait on one; observing it on hardware is BP8's | `SeLe4n/Kernel/Architecture/`, `rust/sele4n-hal/src/boot.rs` | M |
| BP4.6 | **LANDED `v0.36.2`**.  The device-tree wrapper's accepting arm runs `extendBootRamMap (rpi5BootRamExtensionsFor config.machineConfig)` before the install: `bootRamExtensionsOf` derives, from the memory map of the variant the binding installs, every RAM region above `rpi5GuaranteedRamTop` clipped to it, and `mem_bootRamExtensionsOf` / `bootRamExtensionsOf_covers` prove it is exactly that map's RAM above the gigabyte in both directions; `rpi5BootRamExtensions_values` evaluates the five variants (nothing on 1 GiB, one region on every larger board — the BCM2712's DRAM is contiguous from 0) and `rpi5BootRamExtensions_admissible` that each is 2 MiB aligned and inside the tables' 512 GiB reach.  Each region crosses to `ffi_extend_boot_ram_map` → `mmu::extend_boot_ram_map`, which decides every refusal before it writes (`RamExtensionRefusal`: empty, overflow, unaligned, below the gigabyte, beyond reach, a partial gigabyte with no level-2 table, an already-valid entry, a full record, a sealed map), writes 1 GiB level-1 blocks and — in the device window's gigabyte — 2 MiB blocks into entries the tables leave invalid, Normal, writable and never executable, cleans the table extent to the PoC (a secondary enables translation with its cache off), then one `DSB ISH` + `ISB`, and records the region so `is_boot_cacheable_range` (now the union `ram_range_covered`) widens with the tables.  A refusal halts the system.  The boot seam seals the map (`mmu::seal_boot_map`) before it mints the `SecondaryReleasePermit`, so the tables have one writer.  `tests/fixtures/boot_map.expected` carries each variant's `extend` lines and the HAL test applies them and requires the extended Normal window to be **exactly** that variant's RAM, on every variant.  *As registered:* **Map the verified board's RAM above the guaranteed gigabyte.**  BP2.6's boot map covers `[0, GUARANTEED_RAM_TOP)` on every board, so on a 2–16 GiB board the RAM above it is unmapped: a lost resource, never a false claim, and cache maintenance on a frame there fails closed (`is_boot_cacheable_range`).  Once BP4.3 has handed the blob to the verified Lean parser and `rpi5VariantFor` has chosen the board, the kernel extends the identity map to that variant's RAM — Normal, writable, never executable — through a HAL call that adds descriptors to entries the boot tables leave invalid (no break-before-make, one `DSB ISH` + `ISB`), and widens the cacheable window to the same extent.  Until this row lands, BP3.2's untypeds are confined to the guaranteed gigabyte.  Consumes BP4.3 | `rust/sele4n-hal/src/mmu.rs`, `SeLe4n/Platform/RPi5/`, `SeLe4n/Platform/FFI.lean` | M |
| BP4.7 | **LANDED `v0.36.2`**.  `rpi5PlatformConfigFromDtb` and the wrapper take `initialObjectsFor : BCM2712Config → List ObjectEntry` and apply it to `rpi5VariantFor dt.machineConfig` — the variant the check just read — and the deployment's is `rpi5InitialObjectsFor v`: the nine objects every board has, then `rpi5RootTaskRamUntypeds v`, one normal-memory untyped per `rpi5BootRamExtensions v` entry at ids `8 + i` and root-CNode slots `7 + i`.  `rpi5RootTaskRamUntypeds_regions` states the untypeds' regions **are** the extensions BP4.6 maps; every gate is re-decided on the five variants, with `rpi5RootTaskCNodeFor_slotsAddressable` added (the boot bounds a CNode's slot count, not its indices); `rpi5InitialObjectsFor_covers_ram` is the payoff — every RAM address outside the kernel's reserved extent lies in some root-task untyped, on every board — and `rpi5DeploymentBootStateAt_ramUntypedInstalled` that the boot installs each.  `approvedBootCall` is unchanged; the contract's witnesses take the wrapper's new argument, which is data like the rest.  `tests/Ak9PlatformSuite.lean` checks the installed untypeds and their root-CNode capabilities on 1, 2, 3, 4 and 8 GiB device trees.  The variant-independent `rpi5InitialObjects` and `rpi5RootTaskCNode` are retired.  *As registered:* **Hand the RAM above the guaranteed gigabyte to the root task as untypeds.**  BP4.6 maps it; nothing yet describes it as an object anyone can retype, so on a 2–16 GiB board it is mapped and idle.  The deployment's initial objects are variant-independent (`rpi5InitialObjects`) and `kernelMain` passes them to the device-tree wrapper before the parse has chosen a variant, so the untypeds over `rpi5BootRamExtensions` must become a function of that variant: the wrapper builds the deployment's objects from the variant it selects, every gate is re-decided per variant (`untypedPlacementRespected`, `objectBudgetRespected`, the root CNode's slots), and `BootEntryContract.lean`'s `approvedBootCall` moves with the wrapper's signature.  Consumes BP4.6 | `SeLe4n/Platform/RPi5/Deployment.lean`, `SeLe4n/Platform/FFI.lean`, `SeLe4n/Testing/BootEntryContract.lean` | M |

**Acceptance**: `check_kernel_entry_exports.py` reports `lean_kernel_main`
defined by the archive rather than reconciled as expected-unresolved, and
`BootEntryContract.lean` elaborates against the DTB wrapper.

### BP5 — The bootable image (5 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| BP5.1 | **LANDED `v0.36.2`**.  `sele4n-kernel` (`rust/sele4n-hal/src/bin/sele4n_kernel.rs`) is the tree's one final bare-metal binary.  It is `no_std` / `no_main` and requires the `kernel_image` feature, so no ordinary build links it; on a hosted target it is a program that refuses to run.  The HAL's build script passes `-T link.ld` to that binary's link alone, on a bare-metal target only.  Its `#[panic_handler]` is `gic::halt_all`, the system-wide barrier every boot-fatal refusal uses.  The cross lane's step [7/7] builds it in both profiles, and `scripts/check_kernel_image.py` checks the release image.  It is an AArch64 executable entered at `_start`, at `link.ld`'s `ORIGIN` and `.text.boot`'s first byte.  Nothing is undefined, weak symbols included.  Every allocated section is one `link.ld` names, in its order and of its kind, with the loaded ones inside `[_start, __image_load_end)`.  The vector table is `.text.vectors`' 2 KiB-aligned first byte.  `check_link_script`'s layout relations hold of the image's own symbols.  The FP/SIMD gate then disassembles it.  The image is built **without** `hw_target` and so boots the Rust half only (`SecondaryReleasePermit::no_lean_kernel`); the next row links the Lean kernel.  *As registered:* a `[[bin]]` `no_std` / `no_main` target whose entry is `_start` from `boot.S` under `link.ld` | `rust/Cargo.toml`, `rust/sele4n-hal/` | M |
| BP5.2 | **LANDED `v0.36.2`**.  With `hw_target`, on a bare-metal target, `build.rs` links `libsele4n.a` and `libsele4n.roots.ld` into `sele4n-kernel`, with `--gc-sections`.  The roots script is written by `scripts/build_lean_aarch64_archive.py` beside the archive and read by its own reachable link, so the image and the runtime-surface proof take one root set: the library initializer, then every production `@[export]`.  A missing input stops the link naming the file, and the builder's self-test holds the three paths `build.rs` names to its own output.  The Lean archive lane's step [4/5] builds the release image after the archive.  `scripts/check_kernel_image.py --lean-kernel` then requires every root to be the image's text, the initializer first, and `lean_kernel_main` among them.  The FP/SIMD gate then disassembles the image, and none of `compiler_builtins`' FP-using members is in it.  `check_aarch64_cross_target.py` holds the lane to those relations.  *As registered:* link `libsele4n.a` and the HAL together into that binary, **with `--gc-sections` rooted at the same symbols the archive lane's reachable link uses** (the library initializer and every production `@[export]`): the archive references 111 upstream runtime functions the kernel's runtime does not define, and the lane's proof that none is reachable is a proof about that link.  **Run `scripts/check_fp_simd_free_objects.py` over the linked image**, which is where it becomes conclusive: the target's `compiler_builtins` is **not** FP-free even for `aarch64-unknown-none-softfloat` (measured at `v0.36.2`: `__mulsc3`, `__muldc3`, `__multc3`, `__divsc3`, `__divdc3`, `__negsf2` and `__negdf2` use `d`/`v` registers, and `__negdf2` takes its argument in `d0`, a hard-float ABI a soft-float caller cannot satisfy), so what the gate decides on the objects BP1.2 and the cross gate check is necessary and not sufficient — only the image shows which members the link pulled in.  Consumes BP1.3, BP2.2, BP4.1 | `rust/`, `link.ld`, `scripts/` | M |
| BP5.3 | **LANDED `v0.36.2`**.  `scripts/build_rpi5_image.sh [ELF [OUT]]` runs `check_kernel_image.py --lean-kernel` over the image and then `scripts/rpi5_boot_files.py package`, which writes `kernel8.img` (`llvm-objcopy -O binary`) and `config.txt` and then checks both against the image; the archive lane runs it as step [5/5].  **The device tree's window is the linker's, not a computed address**: `link.ld` places a `NOLOAD` `.dtb_window` of `DTB_WINDOW_SIZE` (2 MiB, held equal to `cmdline::MAX_DTB_SIZE` by the HAL's test) after the Lean heap, and three `ASSERT`s — each proved live by `check_link_script.py` — require that size on a page, after `__lean_heap_end`, and ending inside `KERNEL_RESERVED_END`.  **The check**: `kernel8.img` is byte-identical to `[_start, __image_load_end)` rebuilt from the section headers; `config.txt` sets exactly `arm_64bit=1`, `kernel=kernel8.img`, `kernel_address` (= entry = `_start` = `ORIGIN`) and `device_tree_address` / `device_tree_end` (= the linker's window, 8-byte aligned, inside the Lean-stated reserved extent, outside `[_start, __lean_heap_end)`), and refuses an unknown key, a repeated or missing one, and a conditional section.  Measured on the real image: 0x4b5030 bytes entered at 0x80000, the device tree pinned to `[0x45b5000, 0x47b5000)`.  *Scoped as*: `scripts/build_rpi5_image.sh` — `kernel8.img` plus `config.txt`.  **This is the deliverable `SM10.1.1` names**; the release cut consumes it from here.  `config.txt` pins `kernel_address` to `link.ld`'s load address (its `MEMORY` `ORIGIN`, which `scripts/check_kernel_image.py` holds equal to the image's entry) rather than relying on the firmware's default, and sets `device_tree_address` inside the kernel's reserved extent (below `KERNEL_RESERVED_END`, 256 MiB) and above the image's `__lean_heap_end`, because `init_mmu` refuses a device tree anywhere else — the extent is where no boot untyped may reach (BP3.2) | `scripts/build_rpi5_image.sh`, `scripts/rpi5_boot_files.py`, `rust/sele4n-hal/link.ld` | M |
| BP5.4 | **LANDED `v0.36.2`**.  `scripts/kernel_image_report.py` is `build_rpi5_image.sh`'s last step, so the `Lean aarch64 Archive` job — which builds the Lean-linked image and its boot files — publishes, on every run, the size of `kernel8.img` read from the file and required to equal the image's loaded extent `[_start, __image_load_end)` (a file that is not the image is refused, not reported), the loaded section bytes and their padding, the text bytes, the `NOLOAD` bytes, how much of the kernel's reserved extent the image uses to `__dtb_window_end`, and the section map (every allocated section's extent, size and kind).  The Markdown is appended to the run's step summary and written as `kernel-image-report.json` beside the boot files; the job uploads the ELF, `kernel8.img`, `config.txt` and the JSON as the `rpi5-kernel-image` artifact.  *As registered:* Build the image in CI, and publish its size and section map so a regression in either is visible in the run rather than on the board | `.github/workflows/`, `scripts/kernel_image_report.py`, `scripts/build_rpi5_image.sh` | S |
| BP5.5 | **LANDED `v0.36.2`**.  Both entries call `.L_enter_el1` as their first item, ahead of the FP-trap prologue — the `v0.36.2` audit reordered the two, because `HCR_EL2.E2H` is UNKNOWN at reset and with it set a `cpacr_el1` write at EL2 names `CPTR_EL2`, so the trap is written once the PE is at EL1 (`_start`, `secondary_entry` — PSCI `CPU_ON` enters at the caller's EL, EL1 once the boot core has dropped, and every PE takes the routine regardless).  It masks DAIF, reads `CurrentEL`, returns at EL1, halts at any level but EL1 or EL2, and at EL2 programs `HCR_EL2 = RW` (EL1 is AArch64; `TSC = 0`, so an EL1 `smc` reaches the EL3 firmware) then an `isb`, `CPTR_EL2 = 0x33FF` (`TFP = 0`: FP/SIMD is **not** trapped to EL2, so the EL1 trap `CPACR_EL1` sets is the one that fires), `CNTHCTL_EL2 = 0x3` / `CNTVOFF_EL2 = 0` (EL1 owns the physical counter and timer), and — beyond the row as written, each for a stated reason at the routine — `VPIDR_EL2` / `VMPIDR_EL2` = the real `MIDR_EL1` / `MPIDR_EL1` (an EL1 read returns these and their reset values are UNKNOWN), `MDCR_EL2` = `HPMN` only (no PMU or debug trap), and a known MMU-off little-endian `SCTLR_EL1`; then `SPSR_EL2 = 0x3C5` / `ELR_EL2 = x30` for an `eret` to EL1h with DAIF masked.  It returns the entry level in `x9`, which `_start` passes to `rust_boot_main` as `entry_el`.  `build.rs`'s `scan_el1_entry`, beside `scan_fp_trap_prologue`, pins the call position, the entry-level hand-off and the routine item for item (`EL1_ENTRY_ROUTINE`), refuses a write to any EL2 register — by name or by an `S3_4_…` encoding — anywhere else in assembly or Rust, and carries token-preserving mutation self-tests.  **Found while landing it**: every PSCI wrapper hard-coded `hvc #0`, which nothing at EL2 can service on a board entered at EL2, so `CPU_ON` could not have reached the firmware; the conduit now follows the entry level (`psci::select_conduit`: EL2 → `smc`, EL1 → `hvc`), and reading it from the device tree's `/psci` `method` on an EL1 entry is registered debt.  QEMU's `virt` machine enters at EL1 unless `virtualization=on`, so no current harness reaches the EL2 path; the first-boot phase runs it both ways.  Consumes nothing in this plan | `rust/sele4n-hal/src/boot.S`, `rust/sele4n-hal/build.rs`, `rust/sele4n-hal/src/psci.rs`, `rust/sele4n-hal/src/boot.rs` | M |

**Acceptance**: `kernel8.img` is produced by CI on every push, its
`.text` contains `_start`, `__exception_vectors` and `lean_kernel_main`, the
linked image passes the FP/SIMD disassembly gate, and both entries reach EL1
from an EL2 entry.

### BP6 — Per-core readiness (3 sub-tasks)

Every seam behind the per-core `lean_ready` gate was wired end to end and
dormant until this phase: the IRQ vector redirect, the `.reschedule` SGI
receiver, the secondary bring-up entry, the SVC dispatch and the classifier.
A core that is not ready halts on a syscall rather than serving it, because
the timer seam consults the same mask and a thread on a not-ready core would
never be preempted again.  Flipping the mask is what made the kernel run.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| BP6.1 | **LANDED `v0.36.2`**.  The per-image half of the handshake — the library initializer and the install — ran once on the boot core, and `enter_lean_kernel` now publishes it (`lean_ready::publish_kernel_installed`, `Release`) before it mints the release permit.  The kernel's runtime has no per-thread heap, task manager or stack guard, so what is per-PE is the PE's own posture, decided by `lean_ready::initialise_core_runtime_with` in order: the call runs on the core it names (`TPIDR_EL1`), once per core; the install happened-before (`Acquire`); the PE translates (`SCTLR_EL1.M`, since the heap lock is an exclusive-monitor atomic); it runs on its own stack slot (`own_stack_extent`: the boot stack, or the `c`-th 64 KiB slot below `__smp_secondary_stack_top`); and the kernel heap serves an allocation and a free from it.  Success mints a `LeanRuntimeReadyOnCore`, neither `Clone` nor `Copy`.  The boot core runs it too, after Phase 5.  Consumes BP2.3 | `rust/sele4n-hal/src/smp.rs`, `rust/sele4n-hal/src/lean_ready.rs`, `rust/sele4n-hal/src/lean_entry.rs`, `rust/sele4n-hal/src/boot.rs` | M |
| BP6.2 | **LANDED `v0.36.2`**.  `mark_lean_ready` is safe and consumes the token; the `unsafe fn mark_lean_ready(core_id)` whose contract was the promise is retired (`LeanRuntimeReadyOnCore::assume_initialised` is the unsafe host-test form).  `lean_ready::become_ready_or_halt` is the one caller: `rust_secondary_main` calls it after the timer arm and before its bring-up entry and `enable_irq`, parking the PE on a refusal; `rust_boot_main` calls it after the install, halting the system on a refusal, and its `enable_irq` moved from Phase 4 to after the mark, so no PE takes an interrupt in the degraded Rust-only mode once the kernel exists.  Consumes BP6.1 | `rust/sele4n-hal/src/lean_ready.rs`, `rust/sele4n-hal/src/smp.rs`, `rust/sele4n-hal/src/boot.rs` | S |
| BP6.3 | **LANDED `v0.36.2`**.  The Phase-7 refusal waits for cores that *serve the kernel* — `smp::core_serves`, IRQ-ready **and** Lean-ready — through `serving_core_count_within`, bounded, and halts the system (`gic::halt_all`) unless every declared PE does; the retired `irq_ready_core_count_within` counted the IRQ flag alone, which a PE with every seam dormant satisfies.  `build.rs`'s `readiness_publication_status` holds both marks (hardware-only top-level statements, after their dependencies, before their PE's one `enable_irq`, with the pinned halts), the refusal (after the bring-up; the wait then an `if` on its shortfall whose block ends in the system halt, no `else`), and — derived — that nothing else calls `mark_lean_ready` or `become_ready_or_halt`; fourteen token-preserving mutations and ten mutations of the checker are refused.  Consumes BP6.2 | `rust/sele4n-hal/src/boot.rs`, `rust/sele4n-hal/src/smp.rs`, `rust/sele4n-hal/build.rs` | M |

**Acceptance**: all four PEs publish readiness under QEMU, and a PE that
does not makes the boot fail rather than hang.

### BP7 — The context restore (11 sub-tasks)

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
| BP7.8 | **`MR4` onward reach the handler's IPC buffer** (WS-RR RR7's registered residual, re-homed here at `v0.35.203`).  The WS-RA return frame carries four message registers in `x2`-`x5` and no receive path writes `MR4` onward into the receiver's IPC buffer, so on hardware an `unknownSyscall` (13 words) or `userException` (5 words) handler sees its first four — the model delivers every word (`decodeFault_encodeFault`), which is what makes this a delivery gap rather than a model one.  `Architecture.IpcBufferRead` gains a write twin through the receiver's VSpace, which is why it consumes BP7.2: writing through a VSpace needs the root install.  The fault path and the `.receive` / `.replyRecv` arms take it together, as RR7 staged it.  Consumes BP7.2 and BP7.6 | `SeLe4n/Kernel/Architecture/IpcBufferRead.lean`, `SeLe4n/Kernel/Architecture/Fault.lean`, `SeLe4n/Kernel/IPC/Operations/` | M |
| BP7.9 | **Per-thread FP/SIMD state.**  Since `v0.36.2` `boot.S` traps FP/SIMD at EL0 as well as EL1 (the architecture has no encoding that traps EL1 alone), so a user FP instruction raises EC `0x07`, which the classifier delivers as a `userException` fault: fail-closed, and no user thread can use floating point.  Give each thread an FP context — `v0`–`v31`, `FPCR`, `FPSR` — in the model (`TCB`, erased by `projectKernelObject` like the register context) and switch it **lazily**, as seL4's `CONFIG_HAVE_FPU` does: a per-core FP owner; on EC `0x07` from EL0, lift the trap, save the previous owner's state to its TCB, load the faulting thread's, record it as owner and restart the instruction; on a context switch away from the owner, re-arm the trap.  The save/restore routines are the only kernel code that may name an FP register, so they are hand-written assembly in a named section the disassembly gate exempts **by symbol**, reconciled both ways, and `scan_fp_trap_prologue`'s one-writer rule gains exactly their `CPACR_EL1` writes.  Information flow: the FP context is per-thread state the lazy switch must never let a different thread read, which is the property the owner/trap pair exists for and what the witness exercises.  Consumes BP7.3 (the frame the switch saves beside) and BP7.6 (the restore that resumes the faulting instruction) | `SeLe4n/Model/Object/Types.lean`, `SeLe4n/Kernel/Architecture/Fault.lean`, `rust/sele4n-hal/src/trap.S`, `rust/sele4n-hal/src/trap.rs`, `rust/sele4n-hal/build.rs`, `scripts/check_fp_simd_free_objects.py` | L |
| BP7.10 | **LANDED `v0.36.3`.**  The first gigabyte's RAM is read off the account: `BCM2712Config.lowRamTop` (default the gigabyte's top, so every uncut member is unchanged) is the end of the first RAM region `rpi5MemoryMapForConfig` declares, and `rpi5LowRamTopFor` derives it — the account's RAM prefix from `0` (`ramPrefixTop`, the union reading's own cursor), capped at the gigabyte and rounded **down** to the 2 MiB granule the HAL extends by, or the admissible floor (the kernel's extent plus one granule) when the account reaches less.  `rpi5VariantFor` is the covered member cut to that top, so the real account binds the 8 GiB member at `0x3FC00000` (`rpi5VariantFor_rpi5_firmware_account`) and a CM5 4 GiB's at `0x3FA00000`.  Every gate is re-proved over every **admissible** configuration (`BCM2712Config.Admissible`: the uncut form a member, the top admissible) — the extent-independent gates by `decide` through the extent-erasure projection `PlatformConfig.withoutExtents`, the placement symbolically, the machine config's well-formedness by `MachineConfig.wellFormed_of_within`.  **Deviation from the text above, recorded:** the row said `GUARANTEED_RAM_TOP` "becomes an upper bound"; it is **retired** instead, because the HAL's constant boot map was the defect — it described `[0, 1 GiB)` as the kernel's own writable RAM, the firmware's withheld top included, before any account was read.  The constant Normal window is now the kernel's reserved extent `[0, KERNEL_RESERVED_END)` and nothing else; everything past it, the first gigabyte's reported part included, is an extension the verified parse derives (`bootRamExtensionsOf`, clipped at the extent), which `extend_boot_tables` writes into the first gigabyte's own level-2 table in 2 MiB blocks (`level2_table`), and the root task's untypeds are one per extension (`rpi5RootTaskUntypeds`, ids `6 + i`, slots `5 + i`), so the RAM mapped, declared and owned is one list; `link.ld`'s RAM region ends at the extent.  The retired refusal witness is `realFirmwareAccountBindsTheReportedRam`; the shared boot-map fixture carries three firmware-cut configurations beside the five variants.  *The row as registered:* **The deployment's RAM is derived from the firmware's account** (the `v0.36.2` audit, register table B).  A Raspberry Pi 5's firmware writes `/memory@0` as three ranges — `[0, 0x80000)`, `[0x80000, 0x3FC00000)` and `[0x40000000, top)` on a Pi 5 8 GiB Rev 1.1, `[0x80000, 0x3FB00000)` on a CM5 4 GiB Rev 1.0 (accounts read 2026-09-25) — withholding the top few MiB of the first gigabyte for itself, and the amount varies by board and firmware.  `rpi5MemoryMapForConfig` declares `[0, ramSize)` whole and `machineConfigCovers` requires every declared RAM byte to be in the account, so **no variant is covered, `rpi5PlatformConfigFromDtb` answers `.boardDoesNotMatchBinding` and the boot halts on every real board** (`Ak9PlatformSuite`'s `realFirmwareAccountIsRefusedUntilDerived` and the corpus's `eight_gib_rpi5_firmware` pin the account and the refusal; fail-closed, so the first board boot cannot pass without this row).  The remedy is not a smaller constant — the withheld extent is the firmware's to choose — but the account itself: the first-gigabyte RAM the deployment declares, maps (`GUARANTEED_RAM_TOP` becomes an upper bound, the bound variant's map the firmware's ranges clipped to it) and hands the root task (BP3.2's `[256 MiB, 1 GiB)` untypeds must stop at the account's end, since an untyped over the firmware's withheld memory would let the root task retype VideoCore memory) are read from the parsed tree, with `bootRamExtensionsOf` — already stated over an arbitrary map — unchanged.  What must stay: the kernel's reserved extent `[0, KERNEL_RESERVED_END)` inside the account's first range, the variant selection by RAM *above* the gigabyte, and every BP3–BP4 theorem re-stated over the account rather than the constant.  **Order** (decided at the audit's review, 2026-09-26): this row depends on nothing in BP7 and nothing in BP7 depends on it — its one input is BP4.7 — so the next PR takes it **first**, before the context-restore rows; its id stays, because §8 freezes an id once a CHANGELOG entry or a commit message cites it, and BP7.1–BP7.9 are cited.  Consumes BP4.7 | `SeLe4n/Platform/RPi5/Board.lean`, `SeLe4n/Platform/RPi5/Deployment.lean`, `SeLe4n/Platform/FFI.lean`, `SeLe4n/Platform/Boot/MemoryCoverage.lean`, `rust/sele4n-hal/src/mmu.rs`, `tests/Ak9PlatformSuite.lean` | L |
| BP7.11 | **The root task starts** (the `v0.36.2` audit).  Both initial threads are `.Inactive` — `bootSafeTcbCheck` requires it — and nothing resumes them: the root task's only TCB capability is in its own CNode and the untrusted thread's in its own, so no live authority ever names either, the root task never runs, and the upper separation witness (`0x10_0000`) satisfies the labeling's non-triviality guard with a thread that can never originate or receive a flow — the vacuity `separationWitnessAdmissible` excludes for idle threads, one object over.  **Decided at the audit's review (2026-09-26): the boot starts BOTH initial threads, one per domain** — the root task on the boot core and the untrusted thread on its own core, the way a Microkit-style loader starts every protection domain — so no capability crosses the confinement boundary.  The two alternatives were weighed and refused: a TCB capability to the upper-domain thread in the root task's CNode is control authority across the boundary and would have to be argued against `confinedDeploymentLabeling`, and leaving the witness inert is precisely the vacuity this row names.  Mechanism: `PlatformConfig` names the designated initial threads; the checked boot admits exactly that set `.Ready` and enqueues each on its home core after the idle enqueue, through the kernel model's own `enqueueRunnableOnCore` (as the idle install goes through `enqueueIdleThreadOnCore`, `v0.35.68`), with `bootSafeTcbCheck`'s `.Inactive` clause carved out for that set alone, the boot queue characterisation (`…_runQueueOnCore_eq`) and the proof-layer bundle (`bootFromPlatformCheckedWithIdleThreadsFor_proofLayerInvariantBundle`) re-proved over the enqueues, and `separationWitnessAdmissible`'s witnesses then threads that run.  Each core's first scheduling point dispatches the designated thread ahead of idle by priority, which is what makes the restore (BP7.6) the row this consumes: until it is live a dispatched thread has nowhere to return to.  Consumes BP7.6 | `SeLe4n/Platform/RPi5/Deployment.lean`, `SeLe4n/Platform/Boot.lean`, `SeLe4n/Platform/FFI.lean` | M |

**Acceptance**: a thread blocked in `seL4_Recv` is resumed by its partner
with the frame the kernel staged, on hardware, no path in the image still
installs a sentinel, and a wait-before-signal declassified badge reaches the
waiter's `x0` with its audit record, and two threads on one core each
keep their own FP/SIMD state across preemption.

### BP8 — First boot and bring-up (5 sub-tasks)

Sixteen QEMU scripts exist in `scripts/` and every one of them has always
reported SKIP for want of an image.  This phase is the first time any of
them executes a line of kernel code.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| BP8.1 | Single-core boot under QEMU to the first idle dispatch — the first execution of `BP4.5`'s boot clean-to-PoU, whose emission is a boot-seam instruction sequence and whose *observation* is here.  Run **twice**, once at QEMU's default EL1 entry and once with `-machine virtualization=on`, so `BP5.5`'s EL2-to-EL1 drop executes before the board, which enters at EL2, is the first thing to run it.  *Recorded at the BCM2712 address-map correction (`v0.36.2`):* QEMU has no BCM2712 machine — `raspi4b` is the BCM2711 and `virt` puts its PL011 at `0x0900_0000` and its GIC at `0x0800_0000` — so the image's device map, which is the BCM2712's and a constant of the HAL, meets no device under QEMU; this row therefore owes either a QEMU device map taken from a platform binding or the board itself, and must say which.  Since the `v0.36.2` audit `scripts/test_qemu.sh` builds the real image (`sele4n-kernel`, `kernel_image`) and SKIPs unless `QEMU_MACHINE` names a machine, so the lane can no longer report a pass on a binary that does not exist — it waits on this row's answer.  Consumes BP7.10 (the deployment's RAM derived from the firmware's account, without which the bridge refuses every real board) | `scripts/` | L |
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
  The lane landed at `v0.36.2` and ran green locally
  (`scripts/test_lean_aarch64_archive.sh`); this box is ticked by its first
  green CI run, not by the job existing.
- [x] `check_kernel_entry_exports.py` reads the cross archive (BP1.4).
  Executed at BP1.4 (`v0.36.2`, before the entry existed): 8 declarations
  defined in both archives and `lean_kernel_main` reconciled as
  expected-unresolved; since BP4.1 the reconciliation reports 10 defined and 0
  expected-unresolved (next box).
- [ ] A Lean `IO` action that allocates completes on the target (BP2.5).
- [ ] The Lean runtime's failure path halts rather than continues (BP2.4).
- [x] `bootAndInitialiseRPi5OrHalt (rpi5PlatformConfigFor board)` evaluates to
      `.ok` for every board account, every refusal arm unreachable (BP3.3,
      BP3.4; generalised at BP4.4 —
      `bootAndInitialiseRPi5OrHalt_rpi5PlatformConfigFor`).
- [x] `lean_kernel_main` is defined by the archive; the `EXPECTED_UNRESOLVED`
      entry is removed rather than retained (BP4.1).  Executed at `v0.36.2`:
      `scripts/test_lean_aarch64_archive.sh` reports all 10 HAL kernel-entry
      declarations defined in both archives, 0 expected unresolved.
- [ ] The kernel-state install precedes the release of any secondary (BP4.2).
      Enforced by type at `v0.36.2` (`SecondaryReleasePermit`); the box is
      ticked by a boot trace showing the order, which is BP8's.
- [ ] The device tree reaches Lean, and a foreign board is refused (BP4.3).
      Implemented at `v0.36.2` and run on the host over fixture boards
      (`kernelEntry_boots_the_deployment_on_every_variant`); the box is ticked
      by the target run that reads a real firmware blob, which is BP8's.
- [ ] `kernel8.img` is built by CI and contains `_start`,
      `__exception_vectors` and `lean_kernel_main` (BP5.3, BP5.4).
- [ ] Every declared PE publishes readiness within the bounded window, and a
      PE that does not fails the boot (BP6.3).  Implemented at `v0.36.2` and
      pinned by `build.rs`; the box is ticked by the QEMU run with four PEs,
      and by one with a PE withheld, which the first-boot phase runs.
- [ ] `contextRestoreSeamLive` is `true`, and no path installs a sentinel
      frame or halts pending SM10.1 (BP7.6).
- [ ] A blocked caller is resumed with the frame the kernel staged, on
      hardware (BP7.6).
- [ ] A wait-before-signal declassified badge reaches the waiter's `x0`
      through the live restore, with the matching audit record (BP7.7).
- [ ] A handler of an `unknownSyscall` fault reads all thirteen message
      words, so the delivery matches what the model encodes (BP7.8).
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
| Bare-metal Lean runtime hosting is larger than 2–4 weeks | MED | HIGH | BP2.2 derived the runtime's surface from the *measured* reachable link of BP1.3's archive rather than from a guess (144 symbols, 118 of them the runtime's; 145 since BP4.6), so the size was known before the work was done |
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
  and BP4.4 re-pointed.

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
