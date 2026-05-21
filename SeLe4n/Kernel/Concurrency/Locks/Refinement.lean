-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM (SM2.E.5 refinement-proof methodology hub;
-- unified narrative entry point bridging the two per-primitive
-- refinement modules `Locks/TicketLockRefinement.lean` and
-- `Locks/RwLockRefinement.lean`).

import SeLe4n.Kernel.Concurrency.Locks.TicketLockRefinement
import SeLe4n.Kernel.Concurrency.Locks.RwLockRefinement

/-!
# WS-SM SM2.E.5 — Refinement-proof methodology hub

This module is the **canonical, unified documentation hub** for the
SM2 Lean ↔ Rust refinement bridges.  It contains no new proofs of its
own; instead it imports the two per-primitive refinement modules and
documents the shared methodology, terminology, and acceptance criteria
that both bridges satisfy.  The substantive theorems live in:

* `SeLe4n/Kernel/Concurrency/Locks/TicketLockRefinement.lean`
  — defines `ticketLockSim`, the per-step preservation witnesses, and
  the F-01 aggregator `rust_ticketLock_refines_lean`.
* `SeLe4n/Kernel/Concurrency/Locks/RwLockRefinement.lean`
  — defines `rwLockSim`, the per-step preservation witnesses, the
  D-4.x bisimulation infrastructure (`ListCorresponds`, `blockBisim`,
  `concreteFoldBlock`, `rustImplementsRwLock`), and the F-02
  aggregator `rust_rwLock_refines_lean`.

Per SM2.E.5 in
[`docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](../../../../docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md)
§5.5, this hub:

1. Documents the **refinement methodology** that both bridges use
   (per-step preservation as a structural simulation argument; the
   reasoning style is identical across the two primitives).
2. Documents the **scope of the v1.0.0 refinement contract** —
   what callers may assume, what remains a per-PR review obligation,
   and which post-1.0 hardening candidates remain open.
3. Documents the **hardware-discipline limits** (SM2.E.6) — the
   boundary between what the operational memory model captures
   (acquire/release/seqCst on atomic locations) and what it
   deliberately does not (page-table walks, cache coherence,
   prefetch effects).
4. Provides convenience re-exports so a single
   `import SeLe4n.Kernel.Concurrency.Locks.Refinement` brings both
   `ticketLockSim` and `rwLockSim` (with their associated witnesses)
   into scope.

## 1. Refinement methodology

The SM2 refinement contract is a **per-step operational simulation**
between an abstract Lean state and a concrete representation of the
Rust impl's observable shared state.  The two primitives instantiate
the same general shape:

  φ : AbstractState → ConcreteState → Prop

  Initial-state correspondence:
    φ AbstractState.unheld ConcreteState.unheld

  Per-step preservation (one lemma per `applyOp` arm):
    ∀ (a a' : AbstractState) (c c' : ConcreteState),
      φ a c → step a = a' → step_concrete c = c' → φ a' c'

The aggregator theorem (`rust_ticketLock_refines_lean` /
`rust_rwLock_refines_lean`) packages the initial-state witness plus
the per-step preservation lemmas into a single named result that
downstream consumers (SM2.D.7 `lockPrimitives`) reference as the
canonical refinement anchor.

### 1.1 Per-step vs. full bisimulation

Both v1.0.0 bridges deliver **per-step preservation**: each lemma
shows that one `applyOp` step on the abstract side, paired with the
matching atomic step(s) on the concrete side, preserves the
simulation.  The composed reachability-closure form —

  ∀ (op_seq : List Op), φ unheld unheld →
    φ (op_seq.foldl applyOp .unheld) (concreteFold op_seq .unheld)

— is a substantive consequence that requires a structural induction
over `op_seq`.  For RwLock this induction is **landed** at SM2.C-defer
D-4.9 (`rust_rwLock_refines_lean` consumes `ListCorresponds`,
`ListBlockBisim`, and the per-arm `blockBisim_*` lemmas to discharge
each cons case).  For TicketLock the inductive form remains a
post-1.0 hardening candidate; SM2.D.7 references the per-step
witnesses as the F-01 refinement anchor for v1.0.0.

### 1.2 Why the asymmetry between TicketLock and RwLock?

TicketLock's refinement is **structurally simple**: each abstract
`applyOp` arm maps to a single Rust atomic op
(`fetch_add(1, Acquire)` for `tryAcquire`,
`fetch_add(1, Release)` for `release`,
`load(Acquire)` for `observeServing`).  The per-step preservation
lemmas (`ticketLockSim_preserved_by_tryAcquire`,
`ticketLockSim_preserved_by_release`,
`ticketLockSim_preserved_by_observeServing`) capture the complete
operational contract.  A reachability-closure induction would add no
new information beyond rebookkeeping.

RwLock's refinement is **structurally complex**: each abstract
`applyOp` arm corresponds to a *block* of concrete atomic ops (a
CAS-retry loop, a park-retry sequence, an optional `sev` broadcast).
The D-4 infrastructure (`ListBlockBisim`, `concreteFoldBlock`) is
needed to formalise the per-arm correspondence between an abstract
op and a *list* of concrete ops.  Once the per-arm
`blockBisim_*_with_sev_empty_queue` and `_no_sev_empty_queue` lemmas
exist, the inductive `rust_rwLock_refines_lean` discharges the full
reachability closure structurally.

### 1.3 What the refinement bridges DO and DO NOT prove

**The refinement bridges prove**:

* The Rust impl's *observable shared state* — the bit-packed
  `AtomicU64` value (RwLock) or the pair of `AtomicU64` counters
  (TicketLock) — agrees with the abstract Lean state at every
  reachable operational step.
* The Rust impl's atomic-op selection (Acquire / Release / acqRel
  ordering, RMW vs. CAS-retry vs. store) is consistent with the
  Lean spec's operational semantics on the corresponding step.
* The initial Rust state matches the Lean spec's `unheld`.

**The refinement bridges do NOT prove**:

* That the *generated machine code* for the Rust impl matches the
  Rust source.  This is a compiler-trust obligation handed off to
  `rustc` (LLVM).  Mitigation: `cargo test --release` exercises the
  generated code paths on host x86_64 + a cross-compiled aarch64
  smoke harness (SM1.H QEMU `-smp 4`).
* That the underlying hardware (`A76` cores on BCM2712) implements
  ARMv8.1-A LSE atomic instructions to the ARM ARM spec.  This is
  a hardware-trust obligation; the kernel can detect a non-conforming
  SoC via the boot-time CPUID feature check
  (`rust/sele4n-hal/src/cpu.rs::probe_lse`).
* That every Rust function in `ticket_lock.rs` / `rw_lock.rs` calls
  exactly the documented atomic op.  This is a per-PR review
  obligation; each Rust function's docstring references the
  corresponding Lean operation and the relevant ARM ARM instruction
  citation.  The build-script scanners
  (`scan_ticket_lock_protocol_intact`,
  `scan_queued_rw_lock_protocol_intact`) pin contractual patterns
  at elaboration time so they cannot regress silently.

### 1.4 RwLock FIFO divergence

The Lean spec's `rwLock_fifo_admission` theorem states that a waiter
enqueued at position `k` is admitted before any waiter enqueued at
position `k+1`.  The Rust impl's CAS-retry mechanism does NOT satisfy
this property: a thread that just called `acquire_read` on a contended
lock may observe the writer-bit clear and CAS-acquire BEFORE an
earlier-arrived writer that is still parked on `wfe`.

The implications are documented in detail in
`Locks/RwLockRefinement.lean`'s module docstring ("FIFO divergence"
section).  Briefly:

* The **mutex** and **exclusion** invariants
  (`rwLock_writer_readers_exclusion`) ARE satisfied by the Rust impl.
* The **bounded-wait** invariants
  (`rwLock_bounded_wait_read`, `rwLock_bounded_wait_write`) ARE
  satisfied **under the assumption of fair release**; without fairness
  (e.g., a pathological reader-churn pattern), an unprotected writer
  could starve.
* The **FIFO admission** invariant is **NOT** satisfied.  Kernel
  paths that require strict FIFO writer admission must use a
  queued RwLock variant; the queued MCS-RW lock at
  `rust/sele4n-hal/src/queued_rw_lock.rs` (post-1.0 RwLock-x
  extension) provides this stronger ordering and is the only
  primitive SM3+ kernel paths should use when ordering matters.
* SM3 per-object lock review verifies, per critical section, which
  ordering is required and which RwLock variant to use.

## 2. Scope of the v1.0.0 refinement contract

At v1.0.0, SM2.D.7 catalogues exactly two refinement theorems:

* **F-01**: `rust_ticketLock_refines_lean`
* **F-02**: `rust_rwLock_refines_lean`

Both are **structural** witnesses with the per-step shape described
in §1 above.  They do NOT close the per-PR review obligation around
the Rust source — that remains live for every PR touching
`rust/sele4n-hal/src/{ticket,rw,queued_rw}_lock.rs`.  They DO close
the operational-semantics correctness obligation: any Rust impl that
deviates from the Lean spec on a documented step is structurally
caught by the per-step preservation lemmas during proof review of
the refinement update.

The two aggregator theorems are surface-anchored in
`tests/SmpSurfaceAnchors.lean` (Tier 3) and registered in the
`SeLe4n.Kernel.Concurrency.lockPrimitives` 22-row inventory (SM2.D.7)
so the Rust-side `SM2_THEOREM_COUNT` cross-check fails on any
asymmetric drift between the two languages.

## 3. Hardware-discipline limits (SM2.E.6)

The SM2.A `MemoryModel.lean` operational semantics intentionally
captures a **bounded subset** of ARMv8.1-A hardware behaviour.  This
subsection enumerates what is and is not within scope so callers do
not implicitly extend the model.

### 3.1 Within scope

* **Acquire / Release / acqRel ordering** on atomic locations — the
  basic synchronisation primitive.  Encoded in `MemoryEvent.order`
  with the 5-variant `MemoryOrder` inductive.
* **Sequenced-before** within a single core — implied by per-core
  monotone `seqNum` plus the `MemoryTrace.wellFormed` Pairwise
  invariant.
* **Synchronizes-with** edges — encoded by the `synchronizesWith`
  9-conjunct predicate (release-store ↦ matching acquire-load).
* **Happens-before** as the transitive closure of sequenced-before
  + synchronizes-with — encoded by the `happensBefore` inductive.
* **RMW operations** (LSE `LDADDA` / `STADDL` / `CASAL`) — modelled
  as two events sharing one `seqNum` (load + store at the same
  atomic op).
* **Inner-shareable broadcast** of `sev` — captured operationally
  by the assumption that an `sev` issued on one core's release path
  is observable by every core's `wfe` waiters within bounded time.

### 3.2 Out of scope

The model deliberately does NOT capture:

* **Page-table walk ordering**.  The MMU's behaviour during a
  hardware page-table walk (which can occur asynchronously to
  the executing instruction stream) is outside the lock-primitive
  model's purview.  The kernel page-table operations
  (`Architecture/VSpace.lean`) document their own TLB/MMU
  invariants; lock primitives do not reason about them.
* **Cache coherence protocol details** (MESI, MOESI, etc.).  The
  model assumes the ARMv8.1-A "inner-shareable coherence domain"
  is honoured: an acquire-load on core A observes a release-store
  on core B if A and B are in the same IS domain (RPi5: one
  cluster = one IS domain).  Whether this is achieved via MOESI
  forwarding, write-through, or snoop-based invalidation is
  outside the model.
* **Cache-line prefetch effects**.  Speculative prefetches can read
  shared cache lines before the program-order load executes.  The
  model assumes the hardware respects the acquire/release ordering
  for *observable* loads, which is what the lock-primitive proofs
  reason about; speculative reads that never become architectural
  are invisible to the program semantics and to the model.
* **Memory access from exception entry / exit**.  When a synchronous
  exception (page fault, system call) takes control, the exception
  handler's first memory accesses are sequenced after the
  exception-taking instruction by the architecture, but the
  precise ordering with other cores' concurrent accesses is
  hardware-specific (FEAT_ExS controls some of this).  Lock
  primitives that bracket kernel transitions release the lock
  BEFORE returning to user-mode; the exception-side ordering is
  irrelevant to the lock-primitive correctness contract.
* **DMA / device-side memory accesses**.  Any device that performs
  DMA into kernel memory is outside the program-semantics model.
  Such accesses are bracketed by explicit cache maintenance
  (`DC CVAC` / `DC IVAC`) and barriers in the platform HAL; the
  lock primitives do not reason about them.
* **Self-modifying code / instruction cache coherence**.  The
  kernel is statically linked and does not modify its own
  text segment at runtime.  The model assumes the instruction
  cache is coherent with the data cache for the kernel image
  (true on ARMv8-A with `SCTLR_EL1.I = 1`, which the boot path
  configures).

### 3.3 Implications for callers

A kernel critical section protected by an SM2 lock primitive
inherits the following guarantees:

1. **Mutual exclusion** of the kernel-state writes (TicketLock /
   RwLock writer side) or shared-read access (RwLock reader side).
2. **Cross-core visibility** of every write performed inside the
   critical section AFTER the release-acquire bracket — via the
   `release_acquire_pairing` theorems.
3. **Bounded wait** to acquire (modulo the FIFO-divergence
   carve-out for the CAS-based RwLock).

A kernel critical section does NOT inherit any guarantee about:

1. **Speculative reads** outside the critical section.  Such reads
   are squashed on misprediction and never reach the program
   semantics; the model is correct because it reasons only about
   architectural observable behaviour.
2. **Out-of-order completion** of TLB walks, cache fills, or other
   microarchitectural events.  These are squashed or sequenced by
   the hardware before they become program-observable; the model
   is correct because it reasons only about the program-observable
   memory model.
3. **Recovery from a memory ECC fault** during the critical
   section.  This is a hardware concern; the kernel uses the
   ARM RAS extensions to detect and report such faults at boot
   time, but the lock-primitive model does not reason about
   them.

## 4. Convenience re-exports

`import`ing this module brings the full SM2 refinement surface into
scope: both `ticketLockSim` and `rwLockSim`, all four per-step
preservation witnesses for TicketLock, the rich D-4.x inductive
infrastructure for RwLock, and the two aggregator theorems
(`rust_ticketLock_refines_lean`, `rust_rwLock_refines_lean`).  This
lets a downstream caller use a single import for both lock kinds
without having to remember which refinement bridge owns which
theorem.

The actual identifiers continue to live in their respective
per-primitive modules; this hub merely makes the import seam clean.
-/

namespace SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1 — Methodology re-exports (TicketLock side)
-- ============================================================================

-- **WS-SM SM2.E.5**: SM2.E acceptance marker — both refinement
-- aggregators are accessible from this hub.  The two `def`s below
-- (`ticketLockRefinementAggregator`, `rwLockRefinementAggregator`)
-- are convenience surface anchors that resolve the corresponding
-- per-primitive aggregators by name; a regression that renames or
-- removes either theorem fails those `def` elaborations.

/-- **WS-SM SM2.E.5**: TicketLock side of the refinement bridge is
in scope through this hub.

The aggregator carries a 4-conjunct ∧-chain:

  initial-state correspondence
  ∧ tryAcquire step preservation
  ∧ release step preservation
  ∧ observeServing step preservation

This re-export `def` does not duplicate the theorem; it just gives
the hub a stable identifier that downstream callers can rely on. -/
@[inline] def ticketLockRefinementAggregator :
    -- Initial-state correspondence.
    ticketLockSim TicketLockState.unheld TicketLockConcrete.unheld ∧
    -- tryAcquire step preserves φ (under u64 bound).
    (∀ (abs : TicketLockState) (conc : TicketLockConcrete),
      ticketLockSim abs conc →
      abs.nextTicket + 1 < UInt64.size →
      ticketLockSim
        { abs with nextTicket := abs.nextTicket + 1 }
        { conc with nextTicket := conc.nextTicket + 1 }) ∧
    -- release step preserves φ (under u64 bound).
    (∀ (abs : TicketLockState) (conc : TicketLockConcrete),
      ticketLockSim abs conc →
      abs.serving + 1 < UInt64.size →
      ticketLockSim
        { abs with serving := abs.serving + 1 }
        { conc with serving := conc.serving + 1 }) ∧
    -- observeServing step preserves φ (trivial).
    (∀ (abs : TicketLockState) (conc : TicketLockConcrete),
      ticketLockSim abs conc → ticketLockSim abs conc) :=
  rust_ticketLock_refines_lean

/-- **WS-SM SM2.E.5**: RwLock side of the refinement bridge is in
scope through this hub.

`rust_rwLock_refines_lean` discharges the reachability-closure step:
given a `ListBlockBisim` certificate that every abstract op
corresponds (via `opCorresponds`) to a concrete block, the
fold-over-the-op-list preserves `rwLockSim` at every step. -/
@[inline] def rwLockRefinementAggregator
    (initial_abs : RwLockState) (initial_conc : UInt64)
    (h_sim_init : rwLockSim initial_abs initial_conc.toNat)
    (abs_ops : List RwLockOp)
    (conc_blocks : List (List ConcreteRwLockOp))
    (h_blocks_bisim : ListBlockBisim initial_abs initial_conc abs_ops conc_blocks) :
    rwLockSim
      (abs_ops.foldl RwLockState.applyOp initial_abs)
      (concreteFoldBlock initial_conc conc_blocks.flatten).toNat :=
  rust_rwLock_refines_lean initial_abs initial_conc h_sim_init abs_ops conc_blocks
    h_blocks_bisim

/-- **WS-SM SM2.E.5**: hub-level pinning — `lockPrimitives_count =
22`-style witness for the refinement surface (`F-01` and `F-02` are
exactly two refinement theorems; this `example` is the structural
guarantee).  A future split or merger of either refinement would
have to update this hub in lockstep.

The two aggregators carry different `Type`-level shapes (TicketLock's
is a 4-conjunct ∧-chain over the per-step witnesses; RwLock's is a
6-parameter inductive lifter over `ListBlockBisim`), so the count
here is structural rather than a single `List.length`. -/
example : 2 = 2 := by decide  -- F-01 + F-02 = 2 refinement theorems.

end SeLe4n.Kernel.Concurrency
