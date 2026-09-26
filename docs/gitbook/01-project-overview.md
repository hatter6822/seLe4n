# Project Overview

## 1. What is seLe4n?

seLe4n is a **production-oriented microkernel** built from the ground up in Lean 4.
Every kernel transition is an executable pure function. Every invariant is
machine-checked — zero `sorry`, zero `axiom` across the entire production proof surface.

The project began as a formalization of seL4 semantics and is now a novel kernel
that preserves seL4's capability-based security model while introducing improvements
that the Lean 4 proof framework enables.

**First hardware target: Raspberry Pi 5 (ARM64).**

## 2. Why this project matters

Most kernel verification efforts work backward — write C, then verify it. seLe4n
works forward: executable semantics and proofs are developed together, and the
kernel *is* the specification. This eliminates the verification gap between
specification and implementation.

Current state (as of v0.36.6): 423,960 lines of production Lean across 344 files, 86,280 lines across 71 Lean test suites,
14,056 theorem/lemma declarations, zero unsound constructs.
Metrics source: [`docs/codebase_map.json`](../../docs/codebase_map.json) (`readme_sync` key).

## 3. Architectural improvements over seL4

| Area | seL4 | seLe4n |
|------|------|--------|
| **Service lifecycle** | No kernel-level concept | Dependency graphs with acyclic enforcement |
| **CDT** | Mutable doubly-linked list | Node-stable with O(1) slot transfer |
| **IPC queuing** | Intrusive linked list | Dual-queue with O(1) arbitrary removal |
| **Information flow** | Binary partition | Parameterized N-domain labels |
| **Scheduling** | Priority round-robin | Priority + EDF with domain partitioning |
| **Revocation** | Silent error handling | Strict variant with failure context reporting |

## 4. What is implemented today

### Completed milestone slices

Bootstrap, M1 (scheduler), M2 (capability), M3/M3.5 (IPC + coherence),
M4-A/M4-B (lifecycle), M5 (service graph), M6 (architecture boundary),
M7 (audit remediation).

### Where the project is

Phases SM0–SM9 of the SMP multi-core workstream have landed: foundational SMP
types and the lock hierarchy, the Rust HAL bring-up, verified lock primitives,
per-object locks, per-core scheduler state and scheduling, cross-core IPC, TLB
shootdown and cache maintenance, SMP information flow, and declassification.
The syscall return ABI is complete.

**WS-RR — the pre-1.0 remediation phase — is complete at v0.35.203**
([`SMP_RELEASE_READINESS_PLAN.md`](../planning/SMP_RELEASE_READINESS_PLAN.md)):
198 sub-tasks across nine phases, all landed — the boot-path fail-open closure
(v0.34.48), the verified lock primitives (v0.34.50), which made the deployed
reader-writer lock the ticket-FIFO one the Lean spec describes and refined it
to that spec before the switch, the forty-one-sub-task medium-severity sweep
(v0.34.47 → v0.34.92), and **RR8**, the closure phase, which grew from five
rows to sixteen at v0.35.56 once its gate walk measured that eight register
rows gate the closure and none of them is bookkeeping (v0.35.55 → v0.35.203).
Its last act was to read the debt register against the tree rather than against
its own CHANGELOG, which is what found two rows recording work already
done — one discharged 276 versions earlier, one whose claim the cut that closed
it had made false.

**SM10 — release closure at v1.0.0 — is blocked on WS-BP**, the bare-metal boot
path ([`SMP_BOOT_PATH_PLAN.md`](../planning/SMP_BOOT_PATH_PLAN.md)), which
became SM10.1's content at v0.34.59 and is unblocked as of v0.35.203: 50
sub-tasks across nine phases.  **BP0 landed at v0.36.2**: the three Lean/Rust
pairs — the device-tree readers, the ABI encoder and decoder, the boot map and
the Lean memory map — are driven through shared fixtures, so a divergence fails
a gate rather than waiting for a reviewer.  In the same version the kernel became
**FP-free**: the HAL builds for `aarch64-unknown-none-softfloat`, both boot
entries trap FP/SIMD at EL0 and EL1 from their first instruction, and the cross
gate disassembles the release objects to prove it; user FP/SIMD traps until
threads carry an FP context (BP7.9).  **BP1 landed at v0.36.2 as well**: the
kernel's Lean object code is built for the target as `libsele4n.a` from the
elaborator's closure of `SeLe4n`, compiled freestanding and soft-float, with
every unresolved symbol attributed to its provider and the kernel-entry gate
deciding on both archives (the `Lean aarch64 Archive` CI lane).  **BP2.1** gave
the Lean runtime its heap: one arena the linker script places (64 MiB, asserted
to fit the smallest board) and an allocator in the HAL behind `lean.h`'s
small-object API, whose state is all out of band so it never touches the memory
it serves and refuses every invalid free.  **BP2.2** gave the kernel its own
Lean runtime, written in Rust so the image carries no C++: every symbol the
archive's reachable link needs (144, 118 of them the runtime's; 145 since BP4.6) is provided, each
one faithful to upstream, answering for a machine with no operating system, or
halting; 9 215 results computed on upstream's runtime are recomputed by the
kernel's, and a Tier 1 census proves no kernel entry reaches the environmental
answers.  **BP2.3/BP2.4** run the Lean library initializer before the kernel
is entered — the entry takes a token only a successful initialization
constructs, so the order is checked by the compiler — and halt the whole
system if it fails.  **BP2.6** builds the boot map from linker symbols and
board constants — the image's text read-only and executable at EL1 alone, its
read-only data and everything else never executable, the kernel's reserved extent (the first
GiB until BP7.10) and the device window — so nothing parses the device tree before the MMU is on.
**BP3.1–BP3.4** give the hardware boot a deployment to install: a root task
with its own address space, an interrupt notification and untypeds over the
board's RAM outside the kernel's reserved extent, and an untrusted
initial thread, with no capability between them.  The boot now admits a
thread's VSpace root (registering its ASID), refuses an untyped over memory it
may not describe, and every gate of the checked boot on this configuration is
decided by evaluation, so the hardware entry provably boots it.  **BP3.5**
proves the proof-layer invariant bundle of the state that boot installs — for
every configuration the checked boot accepts, the RPi5 deployment an instance —
through one argument the unchecked boot now shares, and made the checked boot
refuse a CNode holding a reply capability or an out-of-range badge, which it
had admitted.  **BP4.1** writes the hardware boot entry, `lean_kernel_main`,
and **BP4.2** runs it before any secondary core is released — enforced by a
permit type the bring-up consumes and only the install returns.  **BP4.3**
copies the firmware's device tree into a Lean `ByteArray`, and **BP4.4** makes
the entry the device-tree boot on it: a board that is not a Raspberry Pi 5
halts every core, and an accepted one boots the deployment on its own RAM
variant, which is proved for all five.  **BP4.5** cleans the image's loaded
bytes to the Point of Unification before any thread can fetch, so an initial
task's code is fetched as the firmware loaded it.  **BP4.6** maps the RAM a
board has outside the kernel's reserved extent, once the verified parse has
chosen the variant, and seals the boot map before any secondary is released,
and **BP4.7** hands that RAM to the root task as untypeds, so on every board no
RAM outside the kernel's reserved extent is left unowned.  **BP5.1** makes the
kernel one bare-metal binary, `sele4n-kernel`, entered at `_start` under
`link.ld` and checked as an image by `scripts/check_kernel_image.py`; its panic
handler halts the system.  **BP5.2** links the Lean kernel into that image with
`--gc-sections`, rooted at the same symbols as the archive lane's reachable
link, and runs the FP/SIMD gate over the linked image.  **BP5.3** packages it
for the firmware: `scripts/build_rpi5_image.sh` writes `kernel8.img` and a
`config.txt` pinning the load address to the image's entry and the device tree
to a window `link.ld` places inside the kernel's reserved extent, and checks
both against the image.  **BP5.4** publishes the image's size and section map
with every CI run.  **BP5.5** handles the firmware's EL2 entry: both boot entries
drop to EL1 through one routine `build.rs` pins item for item, with FP/SIMD left
untrapped at EL2 so the EL1 trap fires, and the PSCI conduit follows the entry
level (`smc` after an EL2 entry, where nothing is left to take an `hvc`).
**BP6** makes the dormant seams live: every PE runs a per-PE runtime handshake
and marks itself ready before it unmasks IRQs, and the boot halts unless every
declared PE serves the kernel (IRQ-ready and Lean-ready) within a bounded
window.  **BP7.10** (v0.36.3) reads the first gigabyte's RAM off the firmware's
account — a real Raspberry Pi 5 withholds the gigabyte's top — so a real board
boots, and the boot map's constant RAM is the kernel's reserved extent alone.
The rest of BP7, and BP8, have not started.

**WS-LC** ran ahead of RR7 and closed the two lock **datatype** residuals
RR6 re-registered rather than absorbed — complete at v0.34.55. A queued core
may take its request back in the abstract lock, in the ticket-FIFO refinement
and in the deployed `QueuedRwLock`; all five reader-writer invariants are
preserved and the liveness results that conclude "becomes the holder" are
restated under an explicit no-withdrawal window; both two-phase-locking unwinds
withdraw before they release; and the lock-delay bounds are denominated — in
lock operations unconditionally, in cycles under a stated per-critical-section
ceiling, and in hardware ticks only where a board's counter frequency is
named.

**The kernel does not boot yet.** Producing a bootable image is SM10.1's work;
until it lands, every runtime seam behind the per-core readiness gate is wired
and dormant. What the project does and does not claim is enumerated in
[`CLAIM_EVIDENCE_INDEX.md`](../CLAIM_EVIDENCE_INDEX.md), including a table of
what is *not* claimed and who owns each gap.

| For | Read |
|-----|------|
| What changed in a version | [`CHANGELOG.md`](../../CHANGELOG.md) |
| What is deferred, and who owns it | [`REGISTERED_DEBT.md`](../REGISTERED_DEBT.md) |
| What a phase is scheduled to do | [`docs/planning/`](../planning/) |
| How to build, test and contribute | [`DEVELOPMENT.md`](../DEVELOPMENT.md) |

## 5. Architecture mental model

```
┌─────────────────────────────────────────────────────┐
│  Kernel API  (SeLe4n/Kernel/API.lean)               │
├────────┬────────┬──────┬───────────┬────────────────┤
│Sched   │Capabil │ IPC  │ Lifecycle │ Service (ext)  │
│ uler   │  ity   │      │           │                │
├────────┴────────┴──────┴───────────┴────────────────┤
│  Information Flow  (Policy, Projection, Enforcement) │
├─────────────────────────────────────────────────────┤
│  Architecture  (VSpace, Adapter, Assumptions)        │
├─────────────────────────────────────────────────────┤
│  Model  (Object, State, CDT)                         │
├─────────────────────────────────────────────────────┤
│  Foundations  (Prelude, Machine)                      │
└─────────────────────────────────────────────────────┘
```

Each subsystem follows the **Operations/Invariant split**: executable transitions
in `Operations.lean`, machine-checked proofs in `Invariant.lean`.

## 6. Contributor definition-of-done loop

For milestone-moving changes:

1. implement transition semantics,
2. add/refine invariant components,
3. prove local preservation,
4. prove composed preservation,
5. expose behavior in executable traces,
6. add symbol/fixture anchors in tests,
7. synchronize spec, README, and GitBook docs.

## 7. Key links

- Project specification: [`docs/spec/SELE4N_SPEC.md`](../spec/SELE4N_SPEC.md)
- seL4 reference: [`docs/spec/SEL4_SPEC.md`](../spec/SEL4_SPEC.md)
- Performance optimization: [Kernel Performance Optimization (WS-G)](08-kernel-performance-optimization.md)
- Registered debt: [`docs/REGISTERED_DEBT.md`](../REGISTERED_DEBT.md)
- Hardware path: [Path to Real Hardware (Raspberry Pi 5)](10-path-to-real-hardware-mobile-first.md)
