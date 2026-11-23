<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="assets/logo_dark.png" />
    <img src="assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.37.37-blue" alt="Version" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="License" /></a>
</p>

<p align="center">
  A microkernel written in Lean 4 with machine-checked proofs, inspired by the
  <a href="https://sel4.systems">seL4</a> architecture. First hardware target:
  <strong>Raspberry Pi 5</strong>.
</p>
<p align="center">
  <div align="center">
    Created thoughtfully with the help of:
  </div>
  <div align="center">
    claude :robot: :heart: :robot: codex
  </div>
  <div align="center">
    <strong>TREAT THIS KERNEL ACCORDINGLY</strong>
  </div>
</p>

<p align="center">
  <a href="docs/i18n/zh-CN/README.md">简体中文</a> ·
  <a href="docs/i18n/es/README.md">Español</a> ·
  <a href="docs/i18n/ja/README.md">日本語</a> ·
  <a href="docs/i18n/ko/README.md">한국어</a> ·
  <a href="docs/i18n/ar/README.md">العربية</a> ·
  <a href="docs/i18n/fr/README.md">Français</a> ·
  <a href="docs/i18n/pt-BR/README.md">Português</a> ·
  <a href="docs/i18n/ru/README.md">Русский</a> ·
  <a href="docs/i18n/de/README.md">Deutsch</a> ·
  <a href="docs/i18n/hi/README.md">हिन्दी</a> ·
  <a href="docs/i18n/uk/README.md">Українська</a>
</p>

---

## What is seLe4n?

seLe4n is a microkernel built from the ground up in Lean 4. Every kernel
transition is an executable pure function, and every invariant is checked by
the Lean kernel: the production proof surface has zero `sorry` and zero
`axiom`. The same Lean code is compiled to native code and linked, with a
small Rust hardware layer, into the kernel image that boots on the target.

The project keeps seL4's capability-based security model and, increasingly,
seL4's user-visible ABI, while using Lean to prove more about it and to harden
it where seL4 leaves a gap. The full specification is
[`docs/spec/SELE4N_SPEC.md`](docs/spec/SELE4N_SPEC.md); the items below are
pointers into it.

### seL4's ABI

- **seL4-MCS's syscall set** — the eleven MCS syscalls (`Call` … `Yield`),
  numbered as seL4 numbers them in `x7`; the operation is chosen from the
  syscall, the invoked capability's type and the message label
  (`Syscall.selectOperation`), as in seL4
- **seL4's error and fault payloads** — `LookupFault`, the error frame in
  seL4's message-register order, receive-side capability faults, the
  `Restart` thread state, capability arguments passed as extra capabilities,
  and the guard held in the capability with one `resolveAddressBits`
- The rest of the seL4 ABI work (the remaining invocations, timeout faults,
  per-invocation rights, the Running state per core) is the active WS-SX
  workstream; its rows are in
  [`docs/planning/SEL4_ABI_FIDELITY_PLAN.md`](docs/planning/SEL4_ABI_FIDELITY_PLAN.md)

### Scheduling and real-time

- **Scheduling contexts as capabilities** — CPU time is a kernel object.
  A `SchedContext` holds seL4-MCS's budget, period and refills, is configured
  through the core's `SchedControl` authority, and is bound to threads through
  capabilities; its invariants (`budgetWithinBounds`, `refillsConserved`) are
  part of the top-level bundle. Bandwidth isolation is `refill_window_bound`:
  a context runs at most its budget in any window of one period, seL4-MCS's
  sliding-window guarantee. A hierarchical constant-bandwidth scheduler with
  an EDF root, which adds the converse (an admitted server receives its
  budget every window), is the planned WS-CB workstream
  ([`docs/planning/HIERARCHICAL_CBS_PLAN.md`](docs/planning/HIERARCHICAL_CBS_PLAN.md))
- **Passive servers** — a server runs on the scheduling context its client
  donates during IPC; `donationChainAcyclic` rules out circular donation
- **Budget-driven IPC timeouts** — a blocked thread whose budget is exhausted
  is removed from its endpoint queue (`timeoutThread`)
- **Priority inheritance** — transitive propagation with machine-checked
  freedom from blocking cycles (`blockingAcyclic`) and a bounded inversion
  theorem (`pip_bounded_inversion`)
- **Bounded latency** — a parametric worst-case response-time bound,
  `wcrtBound D L_max N B P = D × L_max + N × (B + P)`
  (`bounded_scheduling_latency_exists`, with a per-core form), proven over the
  modules in `SeLe4n/Kernel/Scheduler/Liveness/`

### Kernel objects and memory

- **Objects carved from untyped memory** — retype carves an object from an
  untyped capability's region, and an untyped reset is seL4's. Moving each
  carved object's cells into its untyped's own memory is the active WS-UC
  workstream
- **A kernel entry allocates nothing** — the compiled syscall, fault and
  interrupt entries make no heap allocation; a retype's carve allocates only
  the new object's own cells. The QEMU heap gate
  (`scripts/test_qemu_heap_allocations_per_syscall.sh`) reads every entry on
  the booted image and fails on any other count
- **Data structures** — the object store and VSpace mappings are verified
  Robin Hood hash tables (`RHTable`, with `distCorrect`, `noDupKeys` and
  `probeChainDominant`); a CNode is a flat array of `2^radix` slots, as in
  seL4; run queues, endpoint and notification queues and reply waiters are
  linked through the TCBs, each with a ghost abstract queue the links are
  proven to agree with
- **Capability derivation tree linked through the slots** — each slot holds
  its parent, first-child and sibling links (seL4's mapping database), proven
  to agree with the tree; delete, revoke (seL4's `cteRevoke` loop) and slot
  transfer walk the links
- **VSpace** — ARMv8 page tables with W^X enforced per frame and memory-type
  checks that refuse an uncached alias of RAM

### Security and verification

- **N-domain information flow** — parameterised flow policies generalising
  seL4's two-domain partition; an enforcement boundary whose length is pinned
  by `enforcementBoundaryExtended_count` (and by
  `enforcementBoundaryPerCore_count` for the per-core boundary); a
  non-interference theorem for every `NonInterferenceStep` constructor; and a
  bounded, fail-closed declassification audit trail read through an
  `auditTrail` capability
- **Composed proof layer** — `proofLayerInvariantBundle`
  (`SeLe4n/Kernel/Architecture/Invariant.lean`) conjoins every subsystem's
  invariant bundle (scheduler, capability, IPC and its scheduler coupling,
  lifecycle, service registry, VSpace, cross-subsystem, TLB and I-cache
  coherence, TLB shootdown, the declassification audit log, and the
  agreement of every linked structure with its ghost) into one obligation
  carried from boot through every operation
- **Multi-core** — four cores with per-core scheduling, cross-core IPC and
  wake, and TLB shootdown; the SMP completion workstream (WS-SM) is in flight
- **Three-phase state** — a builder phase with invariant witnesses freezes to
  an immutable representation with proven lookup equivalence; the frozen
  operations cover the syscalls `frozenOpCoverage` lists, pinned by
  `frozenOpCoverage_count`
- **Service registry** — a seLe4n extension, not in seL4: services are
  registered and looked up through a `serviceRegistry` capability and recorded
  on the serving endpoint; dependency policy is left, as in seL4, to a
  user-level service manager

## Current state

<!-- Metrics below are synced from docs/codebase_map.json → readme_sync section.
     Regenerate with: ./scripts/generate_codebase_map.py --pretty
     Source of truth: docs/codebase_map.json (readme_sync) -->

| Attribute | Value |
|-----------|-------|
| **Version** | `0.37.37` |
| **Lean toolchain** | `v4.28.0` |
| **Production Lean LoC** | 680,393 across 687 files |
| **Test Lean LoC** | 92,469 across 71 test suites |
| **Proved declarations** | 25,997 theorem/lemma declarations (zero sorry/axiom) |
| **Rust crates** | `sele4n-types`, `sele4n-abi`, `sele4n-sys` (user-space wrappers), `sele4n-hal` (the kernel's hardware layer), and the host test `sele4n-lean-boundary` |
| **Target hardware** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Boot lanes** | Every QEMU lane boots the Raspberry Pi 5 image on [rpi5_machine](https://github.com/hatter6822/rpi5_machine)'s `raspi5b` machine first, then the `virt` image on QEMU's `virt` |
| **Workstreams** | Status of every open workstream: [`docs/agent_guide/WORKSTREAM_CONTEXT.md`](docs/agent_guide/WORKSTREAM_CONTEXT.md); index and debt register: [`docs/REGISTERED_DEBT.md`](docs/REGISTERED_DEBT.md) |
| **Audits** | [`docs/audits/`](docs/audits/README.md) — the active audit's artefacts; earlier audits are archived |
| **Codebase map** | [`docs/codebase_map.json`](docs/codebase_map.json) — machine-readable declaration inventory |

Metrics are derived from the codebase by `./scripts/generate_codebase_map.py`
and stored in [`docs/codebase_map.json`](docs/codebase_map.json) under the
`readme_sync` key. Update all documentation together with
`./scripts/sync_documentation_metrics.sh` (verify-only: `--check`);
`./scripts/report_current_state.py` remains a manual cross-check.

## Quick start

```bash
./scripts/setup_lean_env.sh    # install the Lean toolchain and test dependencies
source ~/.elan/env
lake build                     # build the default targets
lake exe sele4n                # run the trace harness
./scripts/test_smoke.sh        # hygiene + build + trace + negative-state
```

`lake build` builds only what `Main.lean` and the test executables reach;
before committing a `.lean` file, build its module by name
(`lake build <Module.Path>`). The full workflow is in
[`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md), and the rules every contributor
follows are in [`CLAUDE.md`](CLAUDE.md).

## Documentation

| Start here | Then |
|------------|------|
| [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md) — workflow, validation, PR checklist | [`docs/spec/SELE4N_SPEC.md`](docs/spec/SELE4N_SPEC.md) — specification and milestones |
| [`docs/gitbook/README.md`](docs/gitbook/README.md) — full handbook | [`docs/spec/SEL4_SPEC.md`](docs/spec/SEL4_SPEC.md) — seL4 reference semantics |
| [`docs/codebase_map.json`](docs/codebase_map.json) — machine-readable inventory | [`docs/REGISTERED_DEBT.md`](docs/REGISTERED_DEBT.md) — every deferred item, with an owner |
| [`CONTRIBUTING.md`](CONTRIBUTING.md) — contribution mechanics | [`CHANGELOG.md`](CHANGELOG.md) — version history |

[`docs/codebase_map.json`](docs/codebase_map.json) is the source of truth for
project metrics. It feeds [seLe4n.org](https://github.com/hatter6822/hatter6822.github.io)
and is checked against the tree on every merge by CI. Regenerate with
`./scripts/generate_codebase_map.py --pretty`.

## Validation commands

```bash
./scripts/test_fast.sh      # Tier 0+1: hygiene + build
./scripts/test_smoke.sh     # + Tier 2: trace + negative-state
./scripts/test_full.sh      # + Tier 3: invariant surface anchors + Lean #check
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Tier 4: nightly determinism

./scripts/test_rust.sh                 # host Rust: build, tests, fmt, clippy
./scripts/test_aarch64_cross_build.sh  # the kernel HAL's real target

./scripts/test_qemu.sh                 # boot the image on raspi5b, then on virt
./scripts/test_qemu.sh --lean-kernel   # the Lean-linked images, on four cores
```

Run at least `test_smoke.sh` before any PR, and `test_full.sh` when changing
theorems, invariants, or Tier 3 anchors. A tier stops at its first failing
check; pass `--continue` to collect every failure in one pass.

After any change under `rust/`, run **both** Rust lanes. They cover disjoint
halves of the same crate: on the host every `#[cfg(target_arch = "aarch64")]`
block is removed before rustc or clippy sees it, so the host lane cannot see
the cfg-gated blocks, `asm!` sites and `.S` sources that make up most of the
HAL. The cross lane builds `sele4n-hal` for `aarch64-unknown-none-softfloat`
in both profiles, verifies the assembly sources really assembled, lints the
cross target, and disassembles the release objects to prove they use no
FP/SIMD register (the kernel traps FP/SIMD at EL1 from its first
instruction). It is a build rather than a `cargo check`, because `check` stops
before code generation and never reaches an assembler.

The QEMU lanes build rpi5_machine at the commit pinned in
`scripts/setup_rpi5_machine.sh` on first use. A lane whose prerequisite is
missing reports NOT RUN rather than passing. The full list of QEMU gates is
in [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md).

## Architecture

seLe4n is organized as layered contracts, each with executable transitions and
machine-checked invariant preservation proofs:

```
┌──────────────────────────────────────────────────────────────────────┐
│   Kernel entries  (syscall, fault, interrupt, per-core timer tick)   │
│                 Kernel API  (SeLe4n/Kernel/API.lean)                 │
├──────────────┬─────────────┬────────────┬───────────┬────────────────┤
│  Scheduler   │  Capability │    IPC     │ Lifecycle │  Service (ext) │
│   RunQueue   │  CSpace/CDT │  DualQueue │  Untyped  │    Registry    │
│ SchedContext │             │  Donation  │  Retype   │                │
├──────────────┴─────────────┴────────────┴───────────┴────────────────┤
│         Information Flow  (Policy, Projection, Enforcement)          │
├──────────────────────────────────────────────────────────────────────┤
│  Architecture  (VSpace, page tables, TLB/cache, decode, trap frame)  │
├──────────────────────────────────────────────────────────────────────┤
│         Concurrency  (locks, memory model, per-core state)           │
├──────────────────────────────────────────────────────────────────────┤
│                     Model  (Object, State, CDT)                      │
├──────────────────────────────────────────────────────────────────────┤
│             Foundations  (Prelude, Machine, MachineConfig)           │
├──────────────────────────────────────────────────────────────────────┤
│    Platform  (Contract, Boot, Sim, RPi5, QemuVirt)  ← bindings       │
├──────────────────────────────────────────────────────────────────────┤
│        Rust HAL  (rust/sele4n-hal: boot, traps, GIC, MMU, SMP)       │
└──────────────────────────────────────────────────────────────────────┘
```

## Source layout

```
SeLe4n/
├── Prelude.lean                 Typed identifiers, KernelM monad
├── Machine.lean                 Register file, memory, timer
├── Model/                       Object types, SystemState, slot links, builder/freeze phases
├── Kernel/
│   ├── API.lean                 Unified public API + apiInvariantBundle
│   ├── *Entry.lean              Compiled syscall, fault, interrupt and per-core timer entries
│   ├── Scheduler/               Run queues, selection, priority inheritance, liveness (WCRT)
│   ├── SchedContext/            Scheduling contexts, seL4-MCS refills, SchedControl
│   ├── Capability/              CSpace operations, derivation tree, authority proofs
│   ├── IPC/                     Dual-queue endpoints, donation, timeouts, cross-core IPC
│   ├── Lifecycle/               Untyped retype and reset, thread suspend/resume
│   ├── Service/                 Service registry and its invariants
│   ├── Architecture/            VSpace (W^X), page tables, TLB/cache models, decode, trap frame
│   ├── InformationFlow/         N-domain policy, projection, enforcement, NI proofs
│   ├── Concurrency/             Lock model, memory model, per-core runtime
│   ├── RobinHood/               Verified Robin Hood hash table (RHTable/RHSet)
│   ├── RadixTree/               CNode radix view and its bridge to the slot array
│   ├── FrozenOps/               Frozen-state operations + commutativity proofs
│   └── CrossSubsystem.lean      Cross-subsystem invariant composition
├── Platform/
│   ├── Contract.lean            PlatformBinding typeclass and boundary contracts
│   ├── Boot.lean, Boot/         Boot sequence: root server, initial threads, IRQ nodes
│   ├── FFI.lean                 The Lean side of the HAL boundary
│   ├── Sim/                     Simulation platform (permissive contracts for testing)
│   ├── RPi5/                    Raspberry Pi 5 (BCM2712, GIC-400, MMIO, boot VSpace)
│   └── QemuVirt/                QEMU `virt` binding and boot entry
├── Testing/                     Test harness, state builder, invariant checks, censuses
Main.lean                        Executable entry point
tests/                           Executable test suites + fixtures
rust/                            sele4n-types, sele4n-abi, sele4n-sys, sele4n-hal, sele4n-lean-boundary
```

Each subsystem follows the **Operations/Invariant split**: transitions in
`Operations.lean`, proofs in `Invariant.lean`. The unified `apiInvariantBundle`
aggregates all subsystem invariants into a single proof obligation. The
subsystem map is [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md) §5; for the full
per-file inventory, see [`docs/codebase_map.json`](docs/codebase_map.json).

## Comparison with seL4

| Feature | seL4 | seLe4n |
|---------|------|--------|
| **Syscall ABI** | MCS syscall set, invocation labels, error and fault payloads | The same: seL4-MCS's eleven syscalls and seL4's numbering, label-selected invocations and seL4's error payloads; the remaining invocations are WS-SX rows |
| **Scheduling** | MCS scheduling contexts with sporadic-server refills | The same refill engine, with its conservation invariant and the one-budget-per-window bound (`refill_window_bound`) proven; a hierarchical CBS with an EDF root is planned (WS-CB) |
| **Passive servers** | SchedContext donation | Verified donation with the `donationChainAcyclic` invariant |
| **IPC** | One queue per endpoint, linked through the TCBs | A send queue and a receive queue per endpoint, both linked through the TCBs with O(1) removal from any position; budget-driven timeouts |
| **Information flow** | Binary high/low partition | N-domain configurable policy, an enforcement boundary pinned by `enforcementBoundaryExtended_count`, a non-interference theorem per step, and a capability-gated audit trail for every authorized declassification |
| **Priority inheritance** | Not in the kernel | Machine-checked transitive PIP with freedom from blocking cycles and a bounded-inversion theorem |
| **Bounded latency** | No formal WCRT bound | `wcrtBound D L_max N B P = D × L_max + N × (B + P)`, proven over the liveness modules |
| **Object store** | Objects at physical addresses | Verified Robin Hood hash tables (`RHTable`/`RHSet`); CNodes are flat slot arrays as in seL4 |
| **Memory mapping** | W^X not enforced by the kernel | W^X enforced per frame as an invariant; memory-type checks refuse an uncached alias of RAM |
| **Service management** | Not in kernel | Capability-gated service registry on the endpoint; dependency policy in user space |
| **Proofs** | Isabelle/HOL, over C via refinement | Lean 4, co-located with the executable transitions; zero sorry/axiom (count in the [Current state](#current-state) table) |
| **Platform** | C-level HAL | `PlatformBinding` typeclass with typed boundary contracts and a Rust HAL |


## License and third-party attributions

seLe4n itself is licensed under the GNU General Public License v3.0 or later
(GPLv3+); see [`LICENSE`](LICENSE) for the full text. Third-party build
dependencies (`cc`, `find-msvc-tools`, `shlex`, all dual-licensed
`MIT OR Apache-2.0`) are used under the MIT option; their upstream copyright
and permission notices are reproduced verbatim in
[`THIRD_PARTY_LICENSES.md`](THIRD_PARTY_LICENSES.md). No runtime-linked
third-party code is present in the kernel binary — the HAL is `#![no_std]`
and uses only `core::*`.
