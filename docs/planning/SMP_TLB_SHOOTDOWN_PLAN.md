# SM7 — TLB / Cache Shootdown (WS-SM Phase 7)

> **Phase**: SM7 of WS-SM
> **Status**: LANDED (v0.32.72 → v0.32.151; SM7.D closed at model level, SM7.F.5 at v0.32.150–151) — per the in-body landing notes
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Audited cut**: `v0.31.2`
> **Target releases (original estimate)**: v0.91.0 .. v0.95.x (parallel with SM8)
> **Calendar estimate**: 5-8 weeks
> **Sub-task count**: 40-55 across ~15-22 PRs

## 1. Phase goal

SM7 closes SMP-C4 (CRITICAL) formally. The hardware part of
SMP-C4 (IS-variant TLB instructions) was addressed in SM1.E;
SM7 adds the **shootdown protocol** with explicit
acknowledgment, the **per-core TLB model**, and the **proof**
that broadcast invalidation reaches every core.

**Concrete deliverables**:

1. **Shootdown descriptor** (SM7.A): per-core pending-shootdown
   queue + ack flags.
2. **Shootdown protocol** (SM7.B): initiator sends SGI to all
   targets, executes local TLBI, waits for ack flags; each
   target SGI handler invalidates locally and sets its ack.
3. **Per-core TLB model** (SM7.C): generalises `TlbState` to a
   per-core `Vector TlbState coreCount` (mounted as
   `SystemState.perCoreTlb`), driven operationally by the shootdown
   protocol.
4. **Cache maintenance broadcast** (SM7.D): I-cache via
   `ic_ialluis` / `ic_ivau` over a mounted per-core model
   (`SystemState.perCoreICache`), with `icacheCoherent_perCore` as the
   14th `proofLayerInvariantBundle` conjunct; D-cache by VA already at
   PoC (proved reach, no target set).
5. **Tests** (SM7.E): the aggregate `SmpTlbShootdownSuite` (35 scenario
   groups / 272 runtime assertions), the four-core concurrent-unmap storm with its visit-order-
   independence theorem, the cross-cluster mock on both the TLB and
   instruction-cache sides, the `smp_tlb_shootdown` golden trace fixture,
   and the two Tier-4 QEMU exercisers (round-trip + stress).

> **Note** — the §5 sub-task breakdown is authoritative for the
> SM7.C/SM7.D lettering (SM7.C = per-core TLB model, SM7.D = cache
> maintenance).  An earlier draft of this list had the two swapped;
> corrected here in the SM7.C completion cut so §1 and §5 agree.

## 2. Dependencies

- **SM1.E**: IS-variant TLB instructions in HAL.
- **SM1.F**: SGI primitive in HAL.
- **SM2.A**: memory model (synchronizesWith).
- **SM3**: lock-set discipline.

## 3. Mathematical foundations

### 3.1 Shootdown specification

**Specification 3.1.1** (Correctness). After a successful TLB
shootdown for `(asid, vaddr)` initiated by core c₀, no core c ∈
`PlatformBinding.allCores` has `(asid, vaddr)` cached in its TLB.

### 3.2 Shootdown protocol

```
TlbShootdown(initiator c₀, asid, vaddr):
  Precondition: VSpaceRoot(asid).lock held in write mode by c₀.

  1. Initialize shootdownAck : Vector Bool coreCount := all false.
     Set shootdownAck[c₀] := true (initiator does its own
     invalidation locally).

  2. For each c ∈ allCores \ {c₀}:
       Append (asid, vaddr) to pendingShootdowns[c]
         (under PendingShootdown lock).
       sendSgi(c, .tlbShootdownReq).

  3. Locally:
       tlbi_for_sharing(sharingDomain, .vae1 asid vaddr).
       dsb_for_sharing(sharingDomain) ; isb.

  4. Loop: for each c with shootdownAck[c] = false:
       wfe_bounded(WFE_DEFAULT_TIMEOUT_TICKS).
     (Remote core's SGI handler:
       a. Drain pendingShootdowns[c].
       b. For each (asid, vaddr) entry:
            tlbi_for_sharing(sharingDomain, .vae1 asid vaddr).
            dsb_for_sharing(sharingDomain) ; isb.
       c. Atomically set shootdownAck[c] := true (Release).
       d. (Optional) send .tlbShootdownAck SGI back to initiator.
       e. eret to interrupted context.)

  5. Loop terminates when shootdownAck = all true.

  6. Final dsb_for_sharing(sharingDomain) ; isb.

  7. (VSpaceRoot lock released by caller.)
```

### 3.3 Protocol correctness

**Theorem 3.3.1** (`tlbShootdownBroadcast_invalidatesAllCores`).

After successful `TlbShootdown(c₀, asid, vaddr)`, no core has
`(asid, vaddr)` cached in its TLB.

```lean
theorem tlbShootdownBroadcast_invalidatesAllCores
    (s : SystemState) (initiator : CoreId) (asid : ASID) (vaddr : VAddr) :
    let s' := tlbShootdownBroadcast s initiator asid vaddr
    ∀ c : CoreId, (asid, vaddr) ∉ s'.perCoreTlb.get c |>.entries
```

*Proof.* By case analysis on c:
- c = c₀: initiator executes local TLBI in step 3 + DSB.
  Post-DSB, c₀'s TLB lacks the entry (ARM ARM C6.2.311).
- c ≠ c₀: remote core's SGI handler in step 4 executes local
  TLBI for the queue entry, then atomically sets ack with
  Release ordering. The initiator's loop reads ack with Acquire
  ordering (the loop is essentially `serving.load(Acquire)` in
  the wfe_bounded check). Release-acquire pairing (Theorem
  2.2.3.5-style) ensures the remote core's TLBI completion
  happens-before the initiator observes ack = true.
  Once all acks are true, the final DSB in step 6 publishes the
  initiator's observation to all subsequent memory accesses.

Combining: ∀ c, TLB lacks the entry at step 6 completion. □

### 3.4 Why explicit-ack protocol

`TLBI VAE1IS` already broadcasts to all PEs in the inner-shareable
domain (ARM ARM C6.2.311). On BCM2712 (single Cortex-A76
cluster), this suffices at the hardware level.

We use the **explicit-ack protocol** for two reasons:

1. **Cross-cluster portability**: future multi-cluster ports
   (decision #6 parameterizes via `PlatformBinding.sharingDomain`)
   need explicit synchronization. The inner-shareable domain
   becomes per-cluster; cross-cluster shootdown requires SGI.
2. **Formal anchor**: explicit ack gives the Lean proof a
   concrete per-core invalidation event to reason about, rather
   than relying on a single global "DSB ISH suffices"
   assumption.

The cost is ~5 SGI round-trips per shootdown (on BCM2712,
< 100 ns each, total < 500 ns). Dwarfed by the existing
kernel-entry overhead.

## 4. Architectural choices

### 4.1 Per-core pending-shootdown queue

`pendingShootdowns : Vector (List TlbShootdownDescriptor) coreCount`
in `ConcurrencyState`. Bounded by `maxPendingPerCore = 16`
(typical kernel never queues more than a few; the bound is
conservative).

### 4.2 Ack flag synchronization

`shootdownAck : Vector AtomicBool coreCount`. Each flag uses
release-store on set, acquire-load in the loop. This is the
release-acquire synchronization point that anchors Theorem 3.3.1.

### 4.3 Cache maintenance

ARM ARM B2.7 / D7.4: DC operations at PoC (Point of Coherency) are
visible to all coherent agents. For seLe4n:

- D-cache by VA (`dc_civac`, `dc_cvac`, `dc_ivac`): no broadcast
  needed; DC ops at PoC already system-wide.  Realised as
  `dcMaintenanceAllCores`, which deliberately takes **no** target set —
  the absence of a reach parameter is the formal statement of this
  paragraph (SM7.D.2).
- I-cache invalidation: `IC IALLU` reaches **only the executing PE**, so
  the kernel must use `ic_ialluis` (inner-shareable broadcast) or
  `ic_ivau` (by VA to PoU, likewise broadcast within the domain).  The
  hazard the local variant leaves is stated as
  `icInvalidateOnCore_icacheOnCore_ne` and closed by
  `icInvalidateBroadcast_reaches_all_cores` (SM7.D.1).  Note `IC IALLUIS`
  broadcasts within the *Inner Shareable* domain only: a multi-cluster
  port must narrow `icBroadcastReach` and add an SGI-based
  instruction-cache protocol, exactly as §3.4 records for the TLB.
- Cross-core DC for DMA buffers: out of scope for v1.0.0 (no
  DMA driver) — machine-checked as a tripwire by
  `modeledCoherentAgents_no_dma_master` (SM7.D.3), not left as prose.

## 5. Detailed sub-task breakdown

### SM7.A — Shootdown descriptor + state (3 PRs, 6 sub-tasks) — LANDED (v0.32.72); completion cut (v0.32.73)

**Status: LANDED (v0.32.72); completion cut (v0.32.73).**  The SM7
state layer.  Landed staged at v0.32.72; the **v0.32.73 completion cut
promoted it to production**: `Model/State.lean` mounts the state as
`SystemState.tlbShootdown` (realising this plan's §4.1
"`ConcurrencyState`" placement in the codebase's actual state
architecture — `SystemState` is the kernel's runtime state, the
SM3.A.10 `objStoreLock` precedent), with the pure `TlbInvalidation`
operand module extracted from the staged `TlbiForSharing` so the mount
stays FFI-free (partition 58 → 57).  Zero sorry/axiom.

The pure ops deliberately keep drain and ack **separate** (the target's
handler must retire its TLBIs before acknowledging, so a fused
drain-and-ack would let the model claim an acknowledgment the runtime
had not yet earned — the §3.2 step 4b/4c seam); the round-step
composition `completeShootdownOnCore` exists for round-level reasoning
only and is `rfl`-pinned to the two-step form.  The completion cut also
formalised what v0.32.72 had argued in prose: the §4.1 capacity
sufficiency (`beginRound_foldlM_enqueueShootdown_isSome`), the
round-restores-quiescence capstone (`shootdownRound_restores_quiescent`
— the induction that keeps `maxPendingPerCore` sufficient across
serialised rounds forever), a total overflow escape hatch
(`enqueueShootdownOrCoalesce` — a full queue collapses to a single
full-flush descriptor; over-invalidation is always safe), the per-core
pending-queue lock identifier `ShootdownQueueLockId` (decidable total
order; ascending-core acquisition guards concurrent different-VSpace
initiators) as the ready seam for SM7.B.7's
`lockSet_tlbShootdown_correct`, and the live ack-flag FFI seam
(`ffi_shootdown_*` + typed `CoreId` wrappers +
`shootdownAck_ffi_core_in_range`).  Tests:
`tests/SmpTlbShootdownSuite.lean` (`smp_tlb_shootdown_suite`, the
SM7.E.1 seed — 81 assertions / 12 groups), Tier-2 + Tier-3 wired.

**Audit record (v0.32.74, three-lane adversarial audit of PR #838).**
Two confirmed findings, both fixed in the audit cut; everything else
(theorem vacuity — probe-built concrete instantiations of the capstone
and coalesce paths, `@[simp]` hygiene, decidable-instance
transparency, memory-ordering soundness under the serialised regime,
FFI bound-check placement, struct layout, test-suite race-freedom,
documented-count truthfulness) verified sound.

1. **Round-serialisation contract (High; the §3.2 precondition is
   insufficient) — REGISTERED SM7.B.7 OBLIGATION.**  The ack vector
   carries no round identity, so rounds must be serialised
   **system-wide**; the §3.2 "VSpaceRoot lock held" precondition does
   not give that across distinct VSpaces (two initiators, different
   VSpaceRoot locks: an interleaved reset yields an early `allAcked`
   exit with a stale TLB entry live on a target — the SMP-C4 hazard —
   and clears the first initiator's born-`true` flag, a mutual hang).
   SM7.B.7 MUST acquire the new single global `ShootdownRoundLockId`
   (fieldless, provably unique; ordered before every per-core
   `ShootdownQueueLockId`) for the full round and release it only
   after `allAcked`.  Every serialisation docstring in
   `TlbShootdown.lean` / `shootdown.rs` / `ffi.rs` / `Runtime.lean`
   now states this contract; the queue-lock total order is
   re-documented as 2PL-footprint declaration + defense-in-depth.
2. **Coalescing coverage strengthened.**  The docstring's
   "no invalidation is ever lost" now has the full theorem:
   `enqueueShootdownOrCoalesce_pending_covered` (every *previously
   queued* descriptor is still pending or superseded by a `.vmalle1`),
   complementing `…_request_covered` for the new descriptor.

3. **PR #838 review P1 (v0.32.75): offline cores stay acknowledged.**
   `reset_for_round` cleared all four `SHOOTDOWN_ACK` slots, but in a
   partial-core boot an offline core can never take the SGI and ack —
   the wait loop would hang.  Fixed: the reset reads `smp::CORE_READY`
   and leaves non-online cores born-acknowledged
   (`reset_for_round_in_slice_masked`); safe because every secondary
   bring-up runs `tlbi vmalle1` before MMU-enable
   (`init_mmu_secondary`), so late-onlined cores start with empty
   TLBs.  Lean mirror: `beginShootdownRoundFor` (targets = online
   non-initiator cores) + the hypothesis-free masked capstone
   `shootdownRoundFor_restores_quiescent` + the
   `beginShootdownRoundFor_allCores_eq` fully-online bridge.
   **SM7.B obligations extended**: the target-set computation must
   enumerate online cores only, and rounds must not race core
   bring-up (bring-up completes during boot, before any user mapping
   exists to shoot down).

Follow-up (pre-existing, NOT SM7.A-specific, out of this phase's
scope): a crate-wide conformance audit of the SM1-era
`@[extern] … BaseIO` ↔ plain `extern "C" fn` calling convention
(world-token/boxed-return ABI) once a linked runtime path exists to
exercise it (SM10.1 QEMU image); SM7.A merely follows the established
convention.

| Sub | Description | Landed artefact | Status |
|-----|-------------|-----------------|--------|
| SM7.A.1 | `TlbShootdownDescriptor` struct | `SeLe4n/Kernel/Architecture/TlbShootdown.lean`: `{ op : TlbInvalidation, initiator : CoreId }` — the typed SM1.E.4 operand (one descriptor type covers the SM7.B.9 `.vae1`/`.vale1` unmaps, the SM7.B.10 `.aside1` ASID retire, and the SM7.B.11 `.vmalle1` full flush) + round attribution for the optional step-4d `.tlbShootdownAck` SGI | ✓ |
| SM7.A.2 | `pendingShootdowns : Vector (List TlbShootdownDescriptor) coreCount` | `TlbShootdownState.pendingShootdowns : Vector (List TlbShootdownDescriptor) numCores` under the SM4.B path-a discipline: `pendingOnCore` / `setPendingOnCore`, the `@[simp]` store/load algebra (`_self` / `_ne` / cross-field frames), `ext_perCore`; the boot state is quiescent (`initial_shootdownQuiescent`).  **v0.32.73**: mounted in the kernel state as `SystemState.tlbShootdown := .initial` (`default_tlbShootdown_{initial,quiescent,pendingBounded}`) — this plan's "in `ConcurrencyState`" placement | ✓ |
| SM7.A.3 | `shootdownAck : Vector Bool coreCount` (AtomicBool in Rust) | `TlbShootdownState.shootdownAck` + `acknowledgeShootdown` (monotone) + `beginShootdownRound` (§3.2 step 1 exactly: `beginShootdownRound_ackOnCore_iff`) + decidable `allAcked` + the SM7.B.5 termination anchor `allCores_foldl_acknowledgeShootdown_allAcked`.  Rust: `rust/sele4n-hal/src/shootdown.rs` — `SHOOTDOWN_ACK` per-core cache-line-aligned `AtomicBool` (boots all-`true`), `ack_set` Release / `ack_is_set` + `all_acked` Acquire / `reset_for_round` Relaxed (publication via SM1.F.8 dsb-before-SGIR; cross-round hazard analysis in the module docs), fail-closed bounds panics, `_in_slice` testable forms; HAL 724 → 743 tests | ✓ |
| SM7.A.4 | `enqueueShootdown` operation | FIFO tail-append, fail-closed `none` at capacity (a dropped descriptor is the SMP-C4 stale-TLB hazard); `enqueueShootdown_isSome_iff` / `_eq_none_iff` / `_pending_target` / `_mem` / `_length` / `_frame_pending` / `_frame_ack` / `_preserves_pendingBounded` | ✓ |
| SM7.A.5 | `drainShootdowns` (called from SGI handler) | whole-queue FIFO drain returning `(queue, cleared state)` — `drainShootdowns_fst` is the completeness half of Theorem 3.3.1's remote case; exhaustive (`_drain_twice`), framed (`_frame_pending` / `_frame_ack`), ack-free by design (see status note); round-trip `drainShootdowns_after_enqueue` | ✓ |
| SM7.A.6 | Pending queue capacity bound | `maxPendingPerCore = 16` (§4.1) + `maxPendingPerCore_pos`; decidable `pendingBounded` established at boot and preserved by every SM7.A operation (`enqueueShootdown` / `drainShootdowns` / `acknowledgeShootdown` / `beginShootdownRound` `…_preserves_pendingBounded`); drain restores capacity (`enqueueShootdown_isSome_after_drain`).  **v0.32.73**: the §4.1 sufficiency argument is formal — `beginRound_foldlM_enqueueShootdown_isSome` (a round's posting fold from quiescence always succeeds) closes an induction with `shootdownRound_restores_quiescent` (a completed round is quiescent again); the total `enqueueShootdownOrCoalesce` full-flush-collapse escape hatch covers any future caller that batches past the bound (`…_request_covered`, unconditional `…_preserves_pendingBounded`) | ✓ |

*Landed. What each cut changed, and what its review rounds found, is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

### SM7.B — Shootdown protocol (4 PRs, 12 sub-tasks) — LANDED

**Status: LANDED.**  The complete §3.2 protocol layer over the SM7.A
state: the pure transitions (`TlbShootdownProtocol.lean`, production),
the initiator-side synchronization/termination/timeout theorems
(`TlbShootdownWait.lean`), the round's cross-domain lock-set
(`TlbShootdownLockSet.lean`), Theorem 3.3.1, the wired unmap / ASID /
retype callers, and the live runtime seam
(`SyscallDispatchEntry.completeShootdownRounds` + the Rust handler /
round-lock / bounded-wait / trap-dispatch realisation).  Zero
sorry/axiom; golden trace byte-identical; the SM7.A audit's registered
round-serialisation obligation is discharged (the round lock brackets
the entire hardware round).

Design decisions of record:

* **Invalidation-effect semantics on encodings.**  `tlbEntryMatches`
  compares FFI-encoded operand fields against the encoding of the
  entry's typed fields — exactly the hardware's TLBI operand
  comparison (ARM ARM C6.2.311–316).  The caller-side round trip
  (`encodePageInvalidation_matches`) is therefore unconditional, and
  encoding collisions only ever over-invalidate (always safe).
* **Theorem 3.3.1 before SM7.C.**  Stated over an explicit per-core
  view vector (`shootdownRoundViews`) whose per-target step is proven
  equal to the real handler transition on the really-posted state
  (`handleTlbShootdownReqOnCore_applies_posted_op` +
  `tlbShootdownBroadcast_posts_singleton` — the non-vacuity bridge),
  plus the end-to-end single-view corollary over the real pipeline
  (`shootdownRound_tlb_no_matching_entry`).  SM7.C.6 instantiates the
  vector form per-core mechanically once the views mount.
* **Total coalescing posting for the syscall wrappers.**  The live
  wrappers post through `enqueueShootdownOrCoalesce`
  (`tlbShootdownBroadcastCoalescing`), so queue accumulation between
  a pure posting commit and the runtime round's exhaustive drain can
  never fail a syscall — at the bound a queue collapses to a full
  flush (`postShootdownRoundCoalescing_covered`: no request is ever
  lost).  The strict fail-closed `tlbShootdownBroadcast` remains the
  round-per-round protocol form the theorems quantify over
  (`tlbShootdownBroadcastCoalescing_eq_strict` pins their agreement
  below capacity).
* **Conservative Rust handler.**  The target's `.tlbShootdownReq`
  handler performs a full local `tlbi vmalle1` (+ the primitive's
  `dsb ish; isb`) then release-sets its ack — over-invalidation
  refines the per-descriptor Lean ledger ("runtime removes ⊇ model
  removes") and keeps IRQ context free of Lean-runtime calls; the
  initiator's post-`allAcked` catch-up commit drains the Lean queues
  (`handleTlbShootdownReqOnCore` fold), restoring quiescence.
* **Spin-based bounded wait.**  `wait_all_acked_bounded` spins with a
  generic-timer deadline instead of the plan sketch's `wfe_bounded`
  pacing: a bare `wfe` with IRQs masked and no guaranteed pairing
  event could sleep forever on a hung target, making the timeout
  panic unreachable — a spin keeps the fail-closed verdict
  enforceable (the handlers still `sev` after acking).
* **Trap-layer completion.**  Routing SGIs to the SM1.F.5 table
  required the deferred `dispatch_irq_with_iar` refactor; it also
  fixed a pre-existing GICv2 defect — `GICC_EOIR` writes for SGIs
  must echo the IAR's source-CPU field (GIC-400 TRM §4.4.5); the
  masked-INTID EOI would have stranded per-source SGI instances
  active (lost wakeups) on any multi-core configuration.

| Sub | Description | Landed artefact | Status |
|-----|-------------|-----------------|--------|
| SM7.B.1 | `tlbShootdownLocal (asid, vaddr)` | `TlbShootdownProtocol.lean`: `tlbShootdownLocal` over the typed operand + `applyTlbInvalidation` effect semantics (`_removes` / `_preserves_other` / `_idempotent` / `_vmalle1`), encoders `encodePageInvalidation` / `encodeAsidInvalidation` with unconditional coverage round-trips | ✓ |
| SM7.B.2 | `tlbShootdownBroadcast (initiator, targets, asid, vaddr)` | `tlbShootdownBroadcast` (masked round open + posting fold + exact `.tlbShootdownReq` SGI list) — `_isSome_of_quiescent`, `_posts_singleton`, `_ack_iff`, `_sgis`, `_frame`, `_preserves_pendingBounded`; target set `shootdownTargets` (cover/nodup/ascending); total coalescing form `tlbShootdownBroadcastCoalescing` for the live wrappers | ✓ |
| SM7.B.3 | SGI handler for `.tlbShootdownReq` (registered in SM1.F.5) | Lean model: `tlbShootdownDrainOnCore` / `tlbShootdownAckOnCore` (TLB effect at the ack — a set flag constructively means "view clean") / `handleTlbShootdownReqOnCore` (projects onto SM7.A `completeShootdownOnCore`; idempotent).  Rust: `shootdown.rs::tlb_shootdown_req_handler` (local `tlbi vmalle1` → release `ack_set` → `sev`; fail-closed no-ack on bad core id), registered at boot (`register_tlb_shootdown_handler`, INTID 1); trap layer routes SGIs via the new `gic::dispatch_irq_with_iar` (full-IAR EOI + genuine `source_cpu` — closing the SM1.F "deferred to SM5" note and the GICv2 SGI-EOI defect) | ✓ |
| SM7.B.4 | `shootdownAck` release-acquire synchronization | `TlbShootdownWait.lean`: `shootdownAck_release_acquire` (target's TLBI retirement happens-before the initiator's post-observation access, via the SM2.A `sequencedBefore`/`synchronizesWith`/`happensBefore` chain) + per-core `AtomicLocation.shootdownAckOf` (injective) + the concrete decide-checked witness trace `shootdownAck_release_acquire_witness` | ✓ |
| SM7.B.5 | Initiator wait-loop terminates | `shootdown_wait_loop_terminates` — constructive (fold-max deadline witness, no choice): monotone acks + per-core handler deadlines ⇒ a stable `allAcked` poll index; state-level reachability via `shootdownRound_allAcked` (the completed round satisfies the exit) | ✓ |
| SM7.B.6 | Timeout fallback (panic at SM7; relax post-1.0) | `shootdown_timeout_handling` — the bounded poll's verdict is exact in both directions (`some` ⇒ genuine `allAcked` within budget; `none` ⇒ genuinely never acked), so the runtime panic fires only on a truly hung round; budget `shootdownWaitTimeoutTicks = 540 000` (10 ms @ 54 MHz) pinned to the HAL constant on both sides; Rust `wait_all_acked_bounded` (+ deadline re-check: a completed round is never misreported) | ✓ |
| SM7.B.7 | Lock-set for shootdown | `TlbShootdownLockSet.lean`: cross-domain sum `TlbShootdownLockId` (object < round < queue; full order suite) with the audit contract as theorems (`object_lt_round`, `round_lt_queue`); `lockSet_tlbShootdown` + `lockSet_tlbShootdown_correct` (strictly ascending — the SM3 lock-ladder deadlock-freedom shape), `_nodup`, membership coverage, and footprint honesty vs the live commit's diff-recovered write set (`lockSet_tlbShootdown_covers_commit`).  Runtime: `SHOOTDOWN_ROUND_LOCK` (CAS try-lock) brackets the entire hardware round, acquired cooperatively (`acquireShootdownRoundLockServicingSelf` — a lock-waiter with IRQs masked services its own pending shootdown obligation between retries, because the in-flight round waits on exactly that waiter's ack; a blind blocking spin would deadlock into the timeout panic, which is also why the round lock is a try-lock rather than the verified TicketLock: taking a ticket commits to a queue and cannot interleave servicing) | ✓ |
| SM7.B.8 | `tlbShootdownBroadcast_invalidatesAllCores` | **Theorem 3.3.1** — ∀-core absence over `shootdownRoundViews` (closed form + idempotence; non-vacuity bridge to the real handler), the unmap instantiation `tlbShootdownBroadcast_invalidates_unmap_target`, and the real-pipeline single-view corollary `shootdownRound_tlb_no_matching_entry` + quiescence capstone `shootdownRound_quiescent` | ✓ |
| SM7.B.9 | Wire all unmap callers (~8 sites) | Live API arms `.vspaceUnmap` / `.vspaceMap` route through `vspaceUnmapPageWithShootdown` / `vspaceMapPageCheckedWithShootdownFromState` (caller's core via `determineExecutingCore`; WS-K-D delegation theorems updated); `tlbFlushByPageWithShootdown` / `tlbFlushByASIDWithShootdown` cover the targeted-flush kernel ops; enforcement-boundary registry renamed to the live handlers; error transparency (`_error_iff`) + posting coverage (`_posts`) per wrapper; runtime seam `completeShootdownRounds` in `syscallDispatchCrossCoreEntry` (diff-recovered targets `shootdownChangedTargets` / operands `shootdownPostedOps`, online-masked SGI fire per the SM7.A P1 obligation, `tlbiForSharing` local broadcast, bounded wait, fail-closed panic, catch-up commit) | ✓ |
| SM7.B.10 | ASID-retire shootdown | `tlbFlushByASIDWithShootdown` (`.aside1` round) + `asidAllocateWithShootdown` — the previously-missing kernel-level consumer of `AsidPool.allocate.requiresFlush` (reuse/rollover allocations run the full round before the ASID is returned; fresh allocations provably inert: `_requiresFlush` / `_fresh_inert`) | ✓ |
| SM7.B.11 | Retype-with-page-free shootdown | `lifecycleRetypeDirectWithCleanupShootdown` (live behind the `.lifecycleRetype` arm): retyping a live `.vspaceRoot` — the model's page-free event, destroying every mapping the root held — flushes the dead ASID locally and posts the `.aside1` round (`_vspace_posts`); non-VSpaceRoot retypes provably unchanged (`_non_vspace`).  Closes a genuine pre-SM7.B gap: the retype path performed **no TLB maintenance at all** | ✓ |
| SM7.B.12 | Cross-cluster path via `.outer` sharing | `tlbShootdown_outer_correct`: the domain-tagged round `tlbShootdownBroadcastIn` is state-identical across `.inner`/`.outer` (every round theorem carries over verbatim; only the emitted instruction variant changes — `SharingDomain.toTag`/`tlbi_*os`, range-pinned for both domains); the live entry's `shootdownSharingDomain` is `rfl`-pinned to `PlatformBinding.sharingDomain RPi5Platform` | ✓ |

*Landed. What each cut changed, and what its review rounds found, is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

### SM7.C — Per-core TLB model (3 PRs, 8 sub-tasks) — LANDED (v0.32.80)

**Status: LANDED (v0.32.80).**  The per-core TLB model layer, mounted on
`SystemState.perCoreTlb : Vector TlbState numCores` and wired into the
SM7.B shootdown protocol.  New production module
`SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean` (imports `TlbModel` +
`TlbShootdownProtocol`; in `SeLe4n.lean`).  Zero sorry/axiom; golden
trace byte-identical.

Design decisions of record:

* **Additive mount, not a scalar rewrite.**  `perCoreTlb` is added
  *alongside* the pre-SMP single-core `SystemState.tlb` (the WS-H11/M-17
  boot-core view), not a rename/migration of it.  The scalar `tlb`
  remains the legacy single-core layer (its `adapterFlush*` / `.WithFlush`
  ops unchanged); `perCoreTlb` is the SMP generalisation the SM7.B
  protocol drives.  Both cohere at boot (empty) — `default_perCoreTlb`,
  `default_tlbOnCore`.  Rewriting the scalar into the vector would be an
  SM4-scale migration of the entire freeze/projection/congruence/boot
  surface, out of SM7.C's scope; the additive mount closes the model gap
  without destabilising the landed single-core proofs.
* **`perCoreTlb` is a genuine consumer of `tlbShootdown`.**
  `tlbInvalidateOnAllCores` (SM7.C.4) runs the SM7.B `tlbShootdownBroadcast`
  (posting to the SM7.A `tlbShootdown` state, returning the exact
  `.tlbShootdownReq` SGI list) **and** evolves every core's view via the
  protocol's `shootdownRoundViews` — so the mounted field is not a
  free-standing parallel structure but the very view vector Theorem 3.3.1
  quantifies over, now on a real `SystemState` field.
* **Per-core consistency is the 13th `proofLayerInvariantBundle`
  conjunct.**  `tlbInvalidationConsistent_perCore st` (∀ core, that core's
  view matches the page tables) joins the bundle, generalising the 9th
  conjunct `tlbConsistent st st.tlb`.  Threaded exactly like the SM7.B
  12th conjunct `pendingBounded`: boot witness
  (`default_tlbInvalidationConsistent_perCore`), definitional transport
  through the three adapter preservation proofs (which touch only machine, and — for the context switch — scheduler.current, none of which the conjunct reads)
  (`advanceTimerState` / `writeRegisterState` / `contextSwitchState` frame
  `perCoreTlb`/`objects`/`asidTable`), the Boot general bridge
  (`bootFromPlatform_perCoreTlb_eq` + the 13-component composition), and
  freeze carried wholesale.
* **Information-flow exclusion.**  Like `tlb` and `machine.timer`,
  `perCoreTlb` is deliberately kept out of `projectState` — projecting a
  TLB view would open a covert timing channel.  Exclusion is the correct
  behaviour, so the IF projection surface is unchanged.

| Sub | Description | Landed artefact | Status |
|-----|-------------|-----------------|--------|
| SM7.C.1 | Extend `TlbState` to `Vector TlbState coreCount` | `SystemState.perCoreTlb : Vector TlbState numCores := Vector.replicate numCores TlbState.empty` (`Model/State.lean`) + `default_perCoreTlb`; the SM4.B path-a accessors `tlbOnCore` / `setTlbOnCore` with the `@[simp]` store/load algebra (`_self` / `_ne`), the per-field frame simp-lemmas, and `default_tlbOnCore` (`PerCoreTlbModel.lean`).  Carriage: freeze (`FrozenSystemState.perCoreTlb` no-default + `freeze` + `freeze_preserves_perCoreTlb` + the `apiInvariantBundle_frozenDirectFull` conjunct), congruence (`OffSchedulerAgrees.perCoreTlb` clause + all six builders), boot frames (`applyMachineConfig` / `foldIrqs` / `foldObjects` / `bootFromPlatform_perCoreTlb_eq`) | ✓ |
| SM7.C.2 | `tlbInsertOnCore` (models HW translation walker) | `tlbInsertOnCore` (prepends a fresh translation to core `c`'s view) + `_mem` / `_tlbOnCore_ne` (a hardware walk is local — the SMP asymmetry) / `_frame` | ✓ |
| SM7.C.3 | `tlbInvalidateOnCore` | `tlbInvalidateOnCore` (`applyTlbInvalidation` on core `c` only) + `_removes` / `_tlbOnCore_ne` (leaves other cores stale — the precise SMP hazard) / `_subset` / `_frame` | ✓ |
| SM7.C.4 | `tlbInvalidateOnAllCores` (uses shootdown protocol) | `tlbInvalidateOnAllCores` (broadcast → post to `tlbShootdown` + evolve every view via `shootdownRoundViews`) + the broadcast frames `tlbShootdownBroadcast_perCoreTlb` / `_asidTable`, decomposition `tlbInvalidateOnAllCores_spec`, projections `_perCoreTlb` / `_sgis` / `_objects` / `_asidTable`, and `_isSome_of_quiescent` | ✓ |
| SM7.C.5 | `tlbInvalidationConsistent_perCore` | `tlbInvalidationConsistent_perCore st := ∀ c, tlbConsistent st (tlbOnCore st c)` + boot witness `default_tlbInvalidationConsistent_perCore` + `_bootCore` projection + the consistency-monotonicity lever `tlbConsistent_of_subset_of_state_frame` + `tlbInvalidateOnCore_preserves_tlbInvalidationConsistent_perCore` (invalidation is always safe).  **The 13th `proofLayerInvariantBundle` conjunct** | ✓ |
| SM7.C.6 | `tlbShootdown_invalidates_perCore` (corollary of 3.3.1) | `tlbShootdown_invalidates_perCore` — the mechanical instantiation of Theorem 3.3.1 (`tlbShootdownBroadcast_invalidatesAllCores`) on the mounted field: after a covering `tlbInvalidateOnAllCores` no core retains any covered entry (the SMP-C4 use-after-unmap closure) | ✓ |
| SM7.C.7 | `tlbConsistency_cross_subsystem` | `tlbConsistency_cross_subsystem` — the memory-subsystem capstone (protocol × TLB-model × page-tables): a covering invalidation of a per-core-consistent state both removes every stale entry on every core **and** preserves per-core consistency (the broadcast frames the page tables, and invalidation only removes entries) | ✓ |
| SM7.C.8 | Surface anchors (`#check` 8 theorems) | `tests/SmpTlbShootdownSuite.lean` §1: 49 `#check` anchors over the SM7.C symbols (accessors, ops, all 8 headline theorems, the operative-cut/completeness/NI symbols, the live 13th bundle conjunct — extended from the 30 at the v0.32.80 landing by the completion cut); §2: elaboration witnesses (boot consistency + the C.6/C.7 theorem applications); §5.1–§5.2: 15 runtime assertions (local-op SMP hazard + the cross-core Theorem-3.3.1 round) + §5.3: 11 (operational round + bridge + coalescing + decidable checker) | ✓ |

*Landed. What each cut changed, and what its review rounds found, is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

### SM7.F — Operative per-core TLB fills (CLOSED at v0.32.105; 5 sub-tasks / 4 PRs)

**Motivation (PR #844 review round 2).**  The v0.32.80–83 per-core TLB
model is *empty on the live path*: the only live writes to `perCoreTlb`
are drains (shootdown catch-up), and the translation-walker fill
(`tlbInsertOnCore`) has no production caller — exactly like the
pre-existing scalar `SystemState.tlb`.  So the per-core consistency
invariant (13th `proofLayerInvariantBundle` conjunct) and Theorem 3.3.1
are *vacuously* satisfied for real execution (empty views are trivially
consistent), and the unconditional invariant would be false in a
pending-round state *if* the views held real entries.  None of this is a
live safety bug or a false theorem (the invariant is proven for every
live-reachable state), but it is a genuine fidelity limitation.  SM7.F is
the maximal-fidelity resolution: make the per-core TLB model genuinely
operative by wiring real fills, with the honest invariant and race-free
catch-up that fills then require.

**Design decision — the pending-aware invariant.**  Once fills exist, the
faithful invariant is *not* the unconditional form, nor merely a
quiescent-restricted one, but the **pending-allowance** form: every cached
entry is either (a) consistent with the current page tables, or (b)
covered by a pending shootdown descriptor targeting that core.  This is
the invariant that is genuinely preserved by the real operations —
including `vspaceUnmapPageWithShootdown` (which makes a cached entry stale
*and* posts the covering descriptor in the same step, so clause (b) holds)
and the `.tlbShootdownReq` handler (which drains a core's whole queue, so
after it that core has no pending descriptors and clause (a) must hold for
survivors).  A plain quiescent restriction is weaker and its handler
preservation is awkward (the handler mutates the very shootdown state the
premise reads).

| Sub | Description | Status |
|-----|-------------|--------|
| SM7.F.1 | Translation-walk fill seam: `tlbWalkEntry` (resolve `(asid,vaddr)` through the current page tables) + `tlbFillOnCore` (cache the *consistent-by-construction* entry; a walk can never install a stale entry) + `tlbWalkEntry_matches` (the walker contract) + `_frame` / `_tlbOnCore_ne` (local) / `_preserves_tlbInvalidationConsistent_perCore`.  `SmpTlbShootdownSuite` §5.4 (a real page-table-backed state: map `(asid5,vaddrPage)`, walk-fill core0, confirm the entry is cached + local + checker-green + unmapped-walk-is-no-op). | **LANDED (v0.32.84)** |
| SM7.F.2 | Pending-aware (honest) invariant: `tlbInvalidationConsistent_perCore` redefined to the pending-allowance form (`∀ c, ∀ e ∈ view c, tlbEntryConsistent st e ∨ ∃ desc ∈ pendingOnCore c, tlbEntryMatches desc.op e`); every downstream `_preserves_` re-proven compositionally via the transport levers `tlbEntryOk_of_frame{,_eq}` / `tlbEntryConsistent_of_frame` and the drain-survivor lemma `applyTlbInvalidations_survivor_not_matched` (the handler's survivors are consistent because a pending-covered entry would have been drained); checker `tlbEntryOkCheck`/`_iff` + decidable; the round-level capstones (`tlbConsistency_cross_subsystem`, `shootdownRoundPerCore_preserves`) carry a `shootdownQuiescent` premise (quiescent ⇒ every pre-entry consistent).  The 13th `proofLayerInvariantBundle` conjunct transports definitionally through the adapters (it reads `perCoreTlb`/`objects`/`asidTable`/`tlbShootdown`, all framed).  `SmpTlbShootdownSuite` §5.5: the SAME stale entry is inadmissible with no pending shootdown, admissible once one is posted (the exact behaviour the honest form adds).  Scalar-`tlb` (9th conjunct) left unconditional — same status, out of SM7.F scope. | **LANDED (v0.32.85)** |
| SM7.F.2a | Initiator-atomic unmap seam (PR #844 review-2 P2): `vspaceUnmapPageWithShootdownPerCore` retires the operand on the *initiator's own* `perCoreTlb` view atomically (via `drainInitiatorPerCoreView` — the initiator's local `tlbi`) on top of `vspaceUnmapPageWithShootdown` (which posts covering descriptors to the *remote* targets only; `shootdownTargets` excludes the initiator).  `…_preserves_tlbInvalidationConsistent_perCore` (quiescent pre-state): initiator survivors ride the unmap page-table frame (`vspaceUnmapPageWithFlush_tlbEntryConsistent_frame`), remote stale entries ride the freshly-posted descriptor (`postShootdownRoundCoalescing_covered`).  Closes the fidelity gap where the initiator's own view would be stale-and-uncovered between the unmap transition and the deferred catch-up drain.  Leaf frames: `storeObject_perCoreTlb_eq`, `vspaceUnmapPage{,WithFlush}_perCoreTlb_eq`.  `SmpTlbShootdownSuite` §5.6.  Model-level only (fills unwired ⇒ no live bug today); live-wiring is F.4. | **LANDED (v0.32.86)** |
| SM7.F.3 | Round-generation-tagged descriptors (the SM7.B v0.32.79 model-fidelity debt): `TlbShootdownDescriptor` carries a round generation; the catch-up drains only its own generation, closing the concurrent-round cross-draining race (Comment 3).  A `TlbShootdownState` type change rippling SM7.A/B + the Rust mailbox mirror. | **LANDED (v0.32.105)** — see the SM7.F.3 section below |
| SM7.F.4 | Live fill + atomic-seam wiring: (a) invoke `tlbFillOnCore` at a genuine live translation point so `perCoreTlb` holds real entries on the syscall path; (b) add an initiator-atomic per-core wrapper for **every** shootdown-posting seam (each posts to `shootdownTargets`, which excludes the initiator) and route its live dispatch through it, so the initiator's own view is retired atomically with the transition rather than only in the deferred catch-up: (i) `.vspaceUnmap` → `vspaceUnmapPageWithShootdownPerCore` (F.2a wrapper); (ii) `.vspaceMap` → an analogous `vspaceMapPageCheckedWithShootdownFromStatePerCore` sibling (which also carries the (a) fill); (iii) `.lifecycleRetype` of a live VSpace root → a per-core sibling of `tlbFlushByASIDWithShootdown` / `lifecycleRetypeDirectWithCleanupShootdown` (PR #844 review-3 Finding 5: the retype makes the ASID unresolvable, so the initiator's cached entry is stale-and-uncovered until catch-up); (iv) the `requiresFlush` ASID-allocate (`asidAllocateWithShootdown`, once B.10 is user-reachable).  Trace-safe (`perCoreTlb` ∉ `projectState`).  Requires F.2/F.2a (else the invariant is false in the pending window on the initiator).  **Note:** until every (b) seam lands, the live paths are covered by the catch-up seam (`shootdownCatchUpPerCore` → `drainInitiatorPerCoreView` drains the initiator for every posted round), so there is no permanent hole — only the transient commit→catch-up window, and it is vacuous where fills are unwired. | **(a)+(b)(i)+(b)(ii)+(b)(iii) LANDED (v0.32.89–93); (b)(iv) gated on SM8** |
| SM7.F.4 core (v0.32.89) | **The live fill made operative + the two primary VSpace initiator-atomic seams.**  **(b)(i)**: the live `.vspaceUnmap` arm (`API.lean` `dispatchCapabilityOnly`) now routes through `vspaceUnmapPageWithShootdownPerCore` (`dispatchWithCap_vspaceUnmap_delegates` RHS updated), retiring the caller's own `perCoreTlb` view atomically with the transition (Finding 3 closure).  **(a)+(b)(ii)**: new `vspaceMapPageCheckedWithShootdownFromStatePerCore` — on a successful map it caches the freshly-established, consistent-by-construction translation on the executing core (**the live fill** — `perCoreTlb` now holds a real entry on the syscall path, the model non-vacuous) **and** retires any stale initiator entry, atomically; `…_preserves_tlbInvalidationConsistent_perCore` rides `vspaceMapPageCheckedWithFlushFromState_ok_fresh` (a successful checked map is always fresh ⇒ no shootdown posts, no stale initiator entry) + the new fresh-map entry-consistency frame + `tlbFillOnCore_preserves`; the `.vspaceMap` arm + `dispatchWithCap_vspaceMap_delegates` route through it.  New frames (`VSpace.lean`): `vspaceMapPage{,WithFlush,CheckedWithFlushFromState}_perCoreTlb_eq` + `vspaceMapPage_resolveAsidRoot_isSome` (a map never unbinds an ASID) + (`PerCoreTlbModel.lean`) `vspaceMapPageCheckedWithFlushFromState_tlbEntryConsistent_frame`.  Acceptance (`SmpTlbShootdownSuite` §5.10): live map→fill→cross-core unmap→post→catch-up→remove, every step green under the pending-aware invariant, single serialized round.  Trace byte-identical (`perCoreTlb` ∉ `projectState`); AK7 `RAW_MATCH_VSPACEROOT` 13 → 14 (additive characterisation lemma, baseline re-anchored).  Residual (see the v0.32.90 row below for (b)(iii)): **(b)(iv)** the user-unreachable ASID-allocate (B.10) — still gated on SM8 — and **F.3** round-generation-tagged descriptors, which landed at v0.32.105. | **LANDED (v0.32.89)** |
| SM7.F.4 (b)(iii) (v0.32.90) | **The initiator-atomic retype seam — PR #844 review closure.**  The v0.32.89 live fill made the retype gap *reachable*: after a live `.vspaceMap` caches an entry on the executing core, a live `.lifecycleRetype` of that VSpace root (`lifecycleRetypeDirectWithCleanupShootdown` → `tlbFlushByASIDWithShootdown`) made the ASID unresolvable and posted `.aside1` to **remote** targets only, leaving the initiator's own cached entry stale-**and**-uncovered in the committed post-retype state — the pending-aware invariant false in a reachable committed state (not a CVE: hardware TLB correctly flushed, `perCoreTlb ∉ projectState`; but a mounted invariant must never be reachably false).  New `lifecycleRetypeDirectWithCleanupShootdownPerCore` retires the operand on the **initiator's own** view (`drainInitiatorPerCoreView` with `encodeAsidInvalidation asid`, the initiator's local `TLBI ASIDE1`, atomic with the round; ASID read from the pre-state `getVSpaceRoot? target`); the live `.lifecycleRetype` arm + `dispatchWithCap_lifecycleRetype_delegates` route through it.  Machine-checked: `_non_vspace` + `_initiator_drained` (after the wrapper the initiator's view holds **no** entry for the destroyed ASID — the drain-survivor lemma + `encodeAsidInvalidation_matches`), so the reachable stale-and-uncovered entry the finding raised no longer exists.  Trace byte-identical; AK7 unchanged (`GETVSPACEROOT_ADOPTION` 31 → 35 — typed accessor).  **Tracked follow-on:** the whole-invariant preservation theorem `…_preserves_tlbInvalidationConsistent_perCore` (that the retype *also* keeps every other ASID's cached entries consistent on every core) needs a retype-pipeline `resolveAsidRoot`-preservation frame — now tractable (for a VSpaceRoot target `lifecyclePreRetypeCleanup` is the identity, `scrubObjectMemory_objects_eq` is `rfl`, the `storeObject` ASID frames exist) but a substantial standalone proof; the `_initiator_drained` proof already discharges the specific reachable violation.  **v0.32.91**: the review follow-on — the sibling **CSpaceAddr** production entry point `lifecycleRetypeWithCleanupShootdown` had the same remote-only gap; the initiator drain is now the shared `retypeInitiatorDrain` composed by **both** wrappers (Direct-cap + new `lifecycleRetypeWithCleanupShootdownPerCore`), so neither drifts and both production retype paths are initiator-atomic (`retypeInitiatorDrain_drained` proven once; both `_initiator_drained` follow).  **v0.32.92 — whole-invariant preservation CLOSED**: both wrappers carry a machine-checked `…_preserves_tlbInvalidationConsistent_perCore` (VSpaceRoot-target, quiescent) via `lifecyclePreRetypeCleanup_vspaceRoot_id` (cleanup = identity for a VSpaceRoot) + `retypeStoreObject_tlbEntryConsistent_frame` (retype page-table frame) + `retype_tlbInvariant_of_storeObject` (shared per-core case-split); zero sorry/axiom.  **Discovered `hNoRebind` (necessary — statement false without it)**: `storeObject` inserts the new root's ASID, silently rebinding a colliding live ASID that the round (retiring only `root.asid`) leaves uncovered; live retypes install fresh asid-0 roots so a user-root retype (asid 0) and the freeing case satisfy it.  **v0.32.93 — the reachable violation CLOSED (`hNoRebind` dropped)**: further analysis found it was reachable *without* privilege — create root A (asid 0) → map+cache asid 0 → create root B (asid 0) from **Untyped**, which rebinds asid 0 with **no** shootdown (old object Untyped, not a VSpaceRoot), stranding A's cached entry (a real ASID-reuse-without-flush hazard, made invariant-visible by the F.4(a) live fill).  Fix: both base wrappers now flush the deduplicated `{destroyed, installed}` ASID set (`retypeShootdownAsidList` folded by `retypeShootdownAsids`), so installing a fresh VSpaceRoot flushes its rebound ASID on every core; public signatures unchanged (live `.lifecycleRetype` picks it up).  Both `…_preserves_tlbInvalidationConsistent_perCore` now hold **unconditionally** (VSpaceRoot-target, quiescent) — the rebound entry rides the freshly-posted `.aside1` (initiator drains it via the generalised `retypeInitiatorDrain`; remotes via the coverage-survival lemmas `covers_survives_roundFold` / `roundFoldSd_covers`).  Zero sorry/axiom; trace byte-identical (extra rounds ∈ `tlbShootdown` ∉ `projectState`); AK7 unchanged. | **LANDED (v0.32.90–93)** |

*Landed. What each cut changed, and what its review rounds found, is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

### SM7.D — Cache maintenance broadcast (2 PRs, 4 sub-tasks) — CLOSED (v0.32.94; closure cuts v0.32.95, v0.32.96)

**Status: CLOSED at the model level.**  Landed at v0.32.94; the exact-operand
emission ledger and the page-granular `IC IVAU` expansion closed at v0.32.95;
the `.vspaceUnifyInstruction` code-publication syscall closed at v0.32.96; the
re-type's clean to the Point of Unification closed at v0.32.100 and was tied to
the scrub's own extent at v0.32.101.  Every operand SM7.D emits is correct
*relative to the model*.  What remains is not an SM7.D residual but the
inherited abstraction gap the whole lifecycle layer shares: the physical
addresses are the model's allocation convention rather than the untyped
allocator's, so on hardware the emitted maintenance names the wrong extent
until the AN4-G.3 / LIF-M03 scrub bridge lands (deferred item 5; owner SM10.1).
That gap is the *scrub's*, and the cache operand follows it by construction —
see the v0.32.101 section.  The cache-side companion of SM7.C.  SM7.C closed the
*translation* half of SMP-C4 (a stale TLB entry on a remote core); SM7.D closes
the *cache* half.  The two hierarchies are architecturally asymmetric, and that
asymmetry decides the whole design:

| structure | coherent across PEs? | kernel obligation |
|-----------|----------------------|-------------------|
| D-cache   | **yes** (hardware)   | none — `DC` by VA to PoC is architecturally visible to every agent in the domain (ARM ARM B2.7 / D7.4) |
| I-cache   | **no**               | issue the *broadcast* maintenance variant (`IC IALLUIS` / `IC IVAU`), or remote cores keep stale lines |
| TLB       | no                   | the SM7.B explicit-ack shootdown protocol |

**The gap this closed** (why the phase was not a documentation cut, despite the
original S/T/T/M estimates).  Before SM7.D the kernel performed **no
instruction-cache maintenance on any live path**: `ic_iallu` had an FFI seam with
no caller, and the SMP-correct broadcast variant `ic_ialluis` had no seam at all.
Instruction caches are physically tagged from software's point of view (ARM ARM
D7.2), so a line cached from a page whose executable mapping is later torn down
stays hittable through *any* later executable mapping of the same frame, in *any*
address space — the instruction-side twin of the SMP-C4 stale-TLB hazard, and one
the TLB shootdown cannot close (it retires translations, not cache lines).  It is
latent rather than exploitable today (no bootable image until SM10.1), but it was
a genuine gap in both the model and the HAL surface, so the plan's
"documentation" framing for D.1–D.3 was superseded per the project's
implement-the-improvement rule.

New production module `Architecture/PerCoreCacheModel.lean`; `CacheModel.lean`
promoted staged → production (SM7.D is its first production consumer — the
D-cache state and operations are what D.2's reach theorems quantify over), staged
count 56 → 55.  Zero sorry/axiom; golden trace byte-identical
(`perCoreICache ∉ projectState`).

| Sub | Description | Status |
|-----|-------------|--------|
| SM7.D.1 | **I-cache invalidation broadcast, mounted and live.**  Typed operand `ICacheInvalidation` (`iallu` / `ivau paddr`) with the FFI tag encoding + range/distinctness theorems mirroring `TlbInvalidation`; the effect algebra `applyICacheInvalidation` (removal / selectivity / monotonicity / idempotence / `iallu`-empties / survivor lemmas); the mounted per-core state `SystemState.perCoreICache : Vector ICacheState numCores` under the SM4.B path-a discipline (`icacheOnCore` / `setIcacheOnCore` + store/load algebra + `default_icacheOnCore`); and the three model operations — `icFetchOnCore` (the hardware instruction fetch, an *environment* step), `icInvalidateOnCore` (`IC IALLU`, whose `…_icacheOnCore_ne` **states the SMP hazard**: every other core keeps its lines, with `icInvalidateOnCore_remote_line_survives` as the non-vacuity witness), and `icInvalidateBroadcast` (`IC IALLUIS` / `IC IVAU`).  Headline: `icInvalidateBroadcast_reaches_all_cores` — the instruction-side analogue of Theorem 3.3.1 — plus the platform instantiation over `icBroadcastReach` (`_cover` / `_nodup`).  `reach` is a parameter for the §3.4 reason `targets` is: a multi-cluster port leaves the Inner Shareable domain and needs an SGI protocol.  **Rust HAL**: `cache::ic_ivau` (`IC IVAU` + `DSB ISH` + `ISB`), `cache::ic_invalidate_all_inner_shareable`, typed `ICacheInvalidation` + fail-closed `decode_icache_invalidation`, exports `cache_ic_ialluis` / `cache_ic_maintenance`; Lean bindings `ffiIcIalluIs` / `ffiIcMaintenance` + the typed wrapper `icMaintenanceBroadcast` with encoding-conformance theorems (HAL 782 → 789 tests, clippy-clean). | ✓ |
| SM7.D.2 | **D-cache by VA at PoC is system-wide — modelled, not merely documented.**  `DCacheMaintenance` (`cleanByVA` / `invalidateByVA` / `cleanInvalidateByVA`) over the AG8-B operations, and `dcMaintenanceAllCores`, which takes **no target set at all** — the absence of a reach parameter *is* the formal content of "at PoC, already system-wide".  `dcMaintenanceByVA_reaches_all_cores` (no core retains the line), `dcacheCoherentAcrossCores` + its cold-boot witness + `dcMaintenanceAllCores_preserves_dcacheCoherentAcrossCores`, and the asymmetry against the instruction side as a theorem (`icInvalidateOnCore_vs_dcMaintenance_reach`).  The data-side **clean-to-PoU obligation** for kernel-written code memory (`KernelCodeWriteSite` / `kernelCodeWriteOwesPoUClean`) is enumerated and checked here; v0.32.100 makes the `.retypeScrub` half *emitted* (`kernelCodeWriteEmitted`), leaving `.bootImageLoad` as the single declared-but-unemitted site (deferred item 4). | ✓ |
| SM7.D.3 | **Cross-core DC for DMA out of scope — as a tripwire, not prose.**  The model enumerates its coherent agents (`CoherentAgent` / `modeledCoherentAgents` = exactly the PEs), proves the maintenance covers all of them (`dcMaintenance_covers_all_modeled_agents`), and proves the enumeration contains **no** non-coherent bus master (`modeledCoherentAgents_no_dma_master`).  Introducing a DMA agent breaks that theorem, so the buffer-ownership protocol (`DC CIVAC` before a device read, `DC IVAC` after a device write, plus non-cacheable or coherent-interconnect mappings) cannot be forgotten.  `Architecture/Assumptions.lean`'s AG8-B entry is rewritten from "sequential model — cache coherency is trivially satisfied under single-core operation" to the per-structure proved/assumed split. | ✓ |
| SM7.D.4 | **Cache-coherency invariant under SMP — the 14th `proofLayerInvariantBundle` conjunct.**  `icacheCoherent_perCore`: on every core, every cached line still has a live **executable** mapping.  An `ICacheLine` records the executable translation the fetch resolved through (`ICacheLine.toTranslation`), so the entire page-table frame algebra proven for `tlbEntryConsistent` (SM7.C.5 / SM7.F) carries over unchanged.  Unlike the 13th conjunct it needs **no** pending-allowance disjunct: instruction-cache maintenance is a *synchronous* broadcast instruction, not a queued request/acknowledge round, so no committed state holds a line that is stale-but-scheduled-for-retirement.  Boot witness `default_icacheCoherent_perCore`; op-level preservation for fetch (with the walker/fetch-authorisation contract), local invalidate, and broadcast; decidable checker `icacheCoherentCheck_perCore` (+ `_iff` + `Decidable` instance) making the conjunct runtime-verifiable exactly as the 12th and 13th are; the capstone `cacheCoherency_cross_subsystem` (mirroring SM7.C.7) and the joint `icInvalidateBroadcast_preserves_perCore_memory_invariants`.  Carried through freeze (`FrozenSystemState.perCoreICache`, **required** — a silent drop is a compile error, symmetric with `perCoreTlb`), congruence (`OffSchedulerAgrees.perCoreICache`), boot (`bootFromPlatform_perCoreICache_eq`), and information flow (`perCoreICache_write_preserves_projection` — a cache view is a covert timing channel, so it stays out of `projectState`). | ✓ |

*Landed. What each cut changed, and what its review rounds found, is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

### SM7.D deferred items — registered against SM10.1

Findings from the PR #845 review that were verified as real but deliberately
**not** fixed in that PR.  Each is recorded here as tracked debt with an owning
phase, per the project's rule that deferred items are lifted into the register
rather than left in source comments.

(A fourth review finding — the missing clean-to-PoU on the re-type path — was
*not* deferred: see the v0.32.100 section above.  Its `.bootImageLoad` sibling
is item 4 below, and is the last site `kernelCodeWriteSites_emission_pending`
still reports as owing an emission.)

| # | Finding | Why deferred | Owner |
|---|---------|--------------|-------|
| 1 | **`op.toPaddr` is used directly as the VA operand for `DC CVAU` / `IC IVAU`.**  `mmu.rs` populated only L1 entries 0..3 — `0x0000_0000–0xBFFF_FFFF` Normal WB cacheable, `0xC000_0000–0xFFFF_FFFF` Device-nGnRnE, nothing above 4 GiB — while `rpi5MachineConfig.physicalAddressWidth = 44`.  The model therefore admitted frames the boot tables do not cacheably map, and maintenance against such a VA faults at EL1 or operates through a Device alias. | **CLOSED at v0.34.57 (WS-RR RR7.1 + RR7.2), in the implement-the-improvement direction — the tables were extended rather than the claim qualified.**  RR7.1 rebuilds the boot map from `mmu::boot_mapping_for`, which mirrors `rpi5MemoryMapForConfig`: RAM is Normal to `0xFC00_0000` (the extent `link.ld` declares), the VideoCore carve-out and the reserved tail are unmapped, the peripheral window is Device, and RAM above 4 GiB is mapped from the board's own `/memory` node.  RR7.2 adds the fail-closed reject over the **whole** operand family — `iallu` (no address), `ivauPage`, `unifyPage`, `cleanRangeIallu` — judged at the extent each one maintains, plus the sibling `cache_clean_pagetable_range` seam that carried the same unenforced obligation; an out-of-window operand halts the PE rather than issuing an instruction whose address is not the address the kernel means.  `scripts/check_physical_address_width.sh` holds the window equal across `mmu.rs`, `Board.lean` and `link.ld`. | ~~SM10.1~~ CLOSED v0.34.57 |
| 2 | **The post-state is published before the maintenance is emitted.**  `modifyGetKernelState` installs the committed state and clears the ledger atomically; `completeIcacheMaintenance` runs outside that step, so another core can observe a retyped frame, map it and execute from it while stale instruction lines are still resident. | Structural to the whole SM7 runtime bracket, not to the cache seam: `completeShootdownRounds` sits in the same position and has since v0.32.76.  The TLB side is saved by the blocking `SHOOTDOWN_ACK` handshake; `IC IALLUIS` is fire-and-forget, so there is nothing to wait on.  "Emit before publishing" is unavailable to a pure-transition kernel (the operand is only known *after* the transition computes it — the reason the ledger exists), leaving "hold serialization across the barrier sequence", which changes the syscall bracket's locking discipline and interacts with the SM3 hierarchy and the SM7.B round lock.  Wants designing once for both the TLB and cache sides.  Mitigation today: the model applies the invalidation to `perCoreICache` atomically *inside* the transition, so the committed state is coherent — the gap is exactly the model-vs-hardware refinement gap SM10.1 closes. | SM10.1 |
| 4 | **The `.bootImageLoad` clean-to-PoU is declared but not emitted.**  The boot pipeline materialises the initial task's objects — including its code — before the first instruction fetch, and owes the same `DC CVAU` → `DSB ISH` → invalidate sequence the re-type now emits.  `kernelCodeWriteEmitted .bootImageLoad = false` records this, and `kernelCodeWriteSites_emission_pending` pins that it is the **only** remaining site. | Unlike `.retypeScrub`, this site genuinely cannot name its extent today: boot materialises objects through the builder, with no transition to hang an operand on and no physical backing until the image runs.  Closure means emitting the range clean as part of boot's object materialisation, which is the SM10.1 bring-up work.  Flipping the `kernelCodeWriteEmitted` arm breaks the `decide`, so the closure cannot land silently. | SM10.1 |
| 5 | **The cleaned extent is the model's abstract convention, not the allocator's.**  `scrubExtent` — which `scrubObjectMemory` zeroes and `retypeIcacheOp` cleans — is `(ObjId × objectTypeAllocSize, objectTypeAllocSize)`.  The real child extent is the untyped allocator's `regionBase + offset` (recorded in state as `UntypedChild.offset` / `.size`), so on hardware neither the zeroing stores nor the `DC CVAU` lands on the object's actual backing memory. | **This is AN4-G.3 / LIF-M03, not a new finding** — the pre-existing scrub bridge, re-labelled at v0.32.101 as a High-severity-once-bootable *data*-disclosure gap (a scrub that misses real memory hands the previous owner's bytes to the new one, not merely stale instruction lines).  Deferred because the fix belongs to the **scrub**, not the cache seam: it needs a reverse child→untyped resolver that does not exist, a fallback for objects with no parent record (boot-built objects, in-place re-types), and a change to `scrubObjectMemory` itself, whose projection lemmas quantify over the abstract range.  Correcting the cache operand alone would be strictly worse — it would clean an extent the scrub does not zero.  v0.32.101 made this a **one-line** change when AN9 lands: both consumers read `scrubExtent`, so the bridge rewrites that single function and the operand follows (`retypeIcacheOp_cleans_scrub_extent` fails if they ever drift). | SM10.1 (AN4-G.3) |
| 3 | **The legacy `syscallDispatchInner` entry does not drain the ledger.** | Vestigial: the Rust `svc_dispatch` extern was flipped to `lean_syscall_dispatch_cross_core` at v0.31.67 (SM6.A), so nothing calls `syscall_dispatch_inner` on the production path.  Since v0.32.96 replaced the operand *join* with an append-only list, an operand committed through the legacy entry is **deferred** (drained by the next cross-core-entry syscall), never silently dropped — `recordIcacheMaintenanceList_mem_of_mem` is the no-loss property.  **Draining there was attempted and reverted**: `icMaintenanceBroadcast` carries an `@[extern]` symbol supplied by the Rust HAL, which simulation builds do not link, and `tests/SyscallDispatchSuite.lean` calls this entry directly — so the emission breaks every host test binary that exercises the bridge.  The module's link-gating policy requires that to fail loudly rather than be stubbed, so the only sound closures are (a) linking the HAL into test binaries, which defeats the gating, or (b) **removing the export** and repointing `SyscallDispatchSuite` at the cross-core entry.  **CLOSED at v0.33.37 (WS-RA), via (b)**: the `syscall_dispatch_inner` export and `syscallDispatchInner` body are deleted with the bit-63 protocol they spoke, and `SyscallDispatchSuite` drives the pure `syscallDispatchFromAbi` directly through its `dispatchViaRef` helper — no legacy entry exists to leave an operand deferred. | ~~SM10.1~~ CLOSED v0.33.37 |

*Landed. What each cut changed, and what its review rounds found, is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

### SM7.E — Tests (3 PRs, 6 sub-tasks) — LANDED (v0.32.103)

| Sub | Description | Status |
|-----|-------------|--------|
| SM7.E.1 | `tests/SmpTlbShootdownSuite.lean` (15+ scenarios) — seeded at SM7.A, 22 groups at the SM7.B completion cut, 32 at the SM7.F cuts | **LANDED** — 35 runtime groups / 272 assertions (§3.1–§3.12, §4.1–§4.11, §5.1–§5.10, §6, §7, §8) |
| SM7.E.2 | QEMU shootdown integration — `scripts/test_qemu_smp_shootdown.sh` | **LANDED** (seeded at the SM7.B completion cut; Tier-4 registered, SKIPs until the SM10.1 bootable image) |
| SM7.E.3 | Shootdown stress test (4 cores × concurrent unmaps) | **LANDED** — suite §6 (model tier) + `scripts/test_qemu_smp_shootdown_stress.sh` (Tier-4 hardware tier) |
| SM7.E.4 | Cross-cluster mock test | **LANDED** — suite §7 (TLB side) + `SmpCacheMaintenanceSuite` §3.15 (I-cache reach side) |
| SM7.E.5 | Surface anchors | **LANDED** — §1 `#check` blocks + Tier-3 `rg` anchors for every new symbol, runner, fixture and script |
| SM7.E.6 | Fixture: `smp_tlb_shootdown.expected` | **LANDED** — 21-line `[smp-tlb-shootdown]` golden trace + `.sha256`, auto-gated by the Tier-2 trace walk |

*Landed. What each cut changed, and what its review rounds found, is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

## 6. Verification strategy

### 6.1 What SM7 proves

~14 substantive theorems including:
- `tlbShootdownBroadcast_invalidatesAllCores` (the headline)
- `shootdownAck_release_acquire`
- `shootdown_wait_loop_terminates`
- `tlbInvalidationConsistent_perCore`
- `icInvalidateBroadcast_reaches_all_cores` (the SM7.D headline — the
  instruction-side analogue of Theorem 3.3.1)
- `icacheCoherent_perCore` (the 14th `proofLayerInvariantBundle` conjunct)
- `dcMaintenanceByVA_reaches_all_cores` (SM7.D.2)
- `cacheCoherency_cross_subsystem` (SM7.D.4 capstone)
- `handleTlbShootdownReqOnCorePerCore_comm` (SM7.E.3 — the live catch-up
  fold's order-independence: distinct cores' handler steps commute, so the
  model's one deterministic visit order stands for every hardware
  interleaving of the SGI deliveries)

### 6.2 What SM7 assumes

- ARM ARM C6.2.311-316 (TLBI semantics).
- ARM ARM B2.7.5 (DSB ISH inner-shareable semantics).
- ARM ARM B2.7 / D7.4 (cache maintenance scope; DC by VA to PoC affects
  every agent that can access the location) — SM7.D.2.
- ARM ARM C6.2.88 (`IC IALLU` PE-local vs `IC IALLUIS` / `IC IVAU`
  inner-shareable broadcast) and D7.2 (instruction caches behave as PIPT
  to software) — SM7.D.1.
- No non-coherent bus master exists at v1.0.0 (no DMA driver) — SM7.D.3,
  tripwired by `modeledCoherentAgents_no_dma_master`.
- SM2.A memory-model synchronizesWith.
- SM1.E IS-variant TLB primitives.

## 7. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Shootdown deadlock (initiator waits forever) | LOW | CRIT | Bounded WFE; timeout panic at SM7 |
| Stale TLB on remote core post-shootdown | LOW | CRIT | Theorem 3.3.1 + explicit ack |
| Ack flag missed (race on read/write) | LOW | HIGH | Release-acquire synchronization |
| Multiple concurrent shootdowns interleave | LOW | HIGH | **DISCHARGED at SM7.B.7**: the single global shootdown-round lock (`ShootdownRoundLockId`, realised as the CAS try-lock `SHOOTDOWN_ROUND_LOCK`, acquired cooperatively — a lock-waiter services its own pending shootdown obligation between retries, since a blind spin with IRQs masked could never satisfy the in-flight round waiting on it) brackets the entire hardware round in `completeShootdownRounds`; the cross-domain order is `lockSet_tlbShootdown_correct`.  (Background: the SM7.A audit showed the VSpaceRoot lock alone is insufficient — two different-VSpace initiators would interleave rounds on the round-identity-free ack vector.) |
| Pending queue overflow | LOW | MED | Bounded by maxPendingPerCore=16 |
| Cross-cluster path under-tested | MED | LOW (no current target) | **DISCHARGED at SM7.E.4**: the mock two-cluster topology in `SmpTlbShootdownSuite` §7 (TLB) and `SmpCacheMaintenanceSuite` §3.15 (I-cache reach) computes the `.outer` round's state-identity, exhibits the stale-remote-cluster hazard a bare IS broadcast leaves, and shows the explicit-ack round (and the hybrid IS-locally/SGI-remotely variant the masked round-open already supports) closing it across the boundary. |

## 8. Acceptance gate

- [x] Shootdown descriptor + state defined (SM7.A, v0.32.72).
- [x] Protocol implemented per §3.2 (SM7.B, `TlbShootdownProtocol.lean`
      + the live `completeShootdownRounds` runtime seam).
- [x] `tlbShootdownBroadcast_invalidatesAllCores` proven (SM7.B.8 —
      per-core views + the real-pipeline single-view corollary; the
      per-core-mounted restatement follows at SM7.C.6).
- [x] All unmap callers wired through Broadcast (SM7.B.9–B.11: the
      `.vspaceUnmap`/`.vspaceMap`/`.lifecycleRetype` arms + the
      targeted-flush ops + the ASID-allocate consumer).
- [x] Per-core TLB model (SM7.C, v0.32.80): `perCoreTlb` vector mounted,
      `tlbInsertOnCore` / `tlbInvalidateOnCore` / `tlbInvalidateOnAllCores`,
      `tlbInvalidationConsistent_perCore` (the 13th
      `proofLayerInvariantBundle` conjunct), `tlbShootdown_invalidates_perCore`
      (Theorem 3.3.1 mounted), and `tlbConsistency_cross_subsystem`.
- [x] Cache-coherency invariant (SM7.D, v0.32.94): `icacheCoherent_perCore`
      (the 14th `proofLayerInvariantBundle` conjunct) + the broadcast reach
      theorem `icInvalidateBroadcast_reaches_all_cores`, the D-cache-at-PoC
      system-wide reach `dcMaintenanceByVA_reaches_all_cores`, the DMA scope
      tripwire `modeledCoherentAgents_no_dma_master`, and the capstone
      `cacheCoherency_cross_subsystem` — live behind the `.vspaceUnmap` and
      `.lifecycleRetype` dispatch arms.
- [x] Tests + fixtures (SM7.E, v0.32.103): the four-core concurrent-unmap
      storm and its visit-order-independence theorem
      (`handleTlbShootdownReqOnCorePerCore_comm`), the cross-cluster mock on
      both the TLB and instruction-cache sides, the `smp_tlb_shootdown`
      golden trace fixture, the surface anchors, and the Tier-4 stress
      exerciser.
- [ ] Tier 0..4 green; QEMU shootdown test passes (Tier 0..3 green at
      SM7.B, at the SM7.D landing, and at the SM7.E landing; the two QEMU
      exercisers — `test_qemu_smp_shootdown.sh` (SM7.E.2) and
      `test_qemu_smp_shootdown_stress.sh` (SM7.E.3) — are Tier-4 registered
      and SKIP until the SM10.1 bootable image exists).
- [x] **Closes SMP-C4 formally**: SM7.C's per-core TLB model and SM7.D's
      per-core cache invariant have both landed, so every per-PE cached view
      of a mapping the kernel destroys — translation *and* instruction line —
      is provably retired on every core.  The remaining SM7 work (SM7.E.2–E.6)
      is test/fixture coverage, not a correctness obligation.

## 9. Cross-references

- **Previous**: [`SMP_CROSS_CORE_IPC_PLAN.md`](SMP_CROSS_CORE_IPC_PLAN.md)
- **Parallel**: [`SMP_INFORMATION_FLOW_PLAN.md`](SMP_INFORMATION_FLOW_PLAN.md)
- **Next**: [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md)

## 10. Theorem catalogue for SM7

14 substantive theorems (§6.1).

## Appendix A — Verification commands

```bash
source ~/.elan/env
lake build SeLe4n.Kernel.Architecture.TlbShootdown
lake build SeLe4n.Kernel.Architecture.PerCoreCacheModel
lake build SeLe4n.Kernel.Architecture.PerCoreTlbModel
lake exe smp_tlb_shootdown_suite
lake exe smp_cache_maintenance_suite
./scripts/test_qemu_smp_shootdown.sh
./scripts/test_qemu_smp_shootdown_stress.sh
```

Regenerating the SM7.E.6 golden trace fixture (brackets MUST be escaped —
unescaped they form a regex character class that also matches the suite's
section headers):

```bash
lake exe smp_tlb_shootdown_suite | grep '^\[smp-tlb-shootdown\]' \
  > tests/fixtures/smp_tlb_shootdown.expected
cd tests/fixtures && sha256sum smp_tlb_shootdown.expected \
  > smp_tlb_shootdown.expected.sha256
```

---

*SM7 closes the most safety-critical SMP gap. The explicit-ack
protocol's correctness (Theorem 3.3.1) hinges on the
release-acquire pairing that SM2's memory model already proves
abstractly.*

---

## Kernel-entry serialisation (LANDED, SM5.I, v0.32.142)

> **Closure record.** Landed as option 1 below — a kernel-entry lock —
> in `rust/sele4n-hal/src/kernel_entry.rs`. The acceptance criterion is
> met: no kernel entry commits state without holding a lock that
> excludes every other kernel entry, all five sites now describe the
> mechanism that actually runs, and the cmdline default has returned to
> `smp_enabled: true`.
>
> Three entries are bracketed, not two. `suspend_thread_cross_core`
> reaches Lean through `ffi::sele4n_suspend_thread` rather than a
> `lean_*` symbol, so the entry inventory below (written from a `lean_`
> sweep) undercounted it. A lost suspend is a thread that keeps running
> after its caller was told it stopped.
>
> Both constraints stated in "Closure" were honoured, and the first was
> honoured *differently* than written. The section says the lock "must
> spin with interrupts enabled so a holder waiting on shootdown acks can
> still service `.tlbShootdownReq`". Enabling interrupts is the wrong
> fix and would have introduced a second deadlock: an IRQ taken mid-spin
> re-enters the kernel on a core already queued for a non-reentrant
> lock, so a timer tick would deadlock against its own core's pending
> syscall. The live implementation keeps IRQs masked and has the waiter
> **discharge its own obligation** (`shootdown::self_service_round`) on
> every poll — the same mechanism SM7.B.7 already uses for the round
> lock, and it removes the need for the interrupt entirely.
>
> **Residual, both tracked and neither a correctness gap.** The lock is
> one global lock rather than SM3.C.9's per-object fine locks, so live
> WCRT is weaker than `PerCoreWcrt.lean`'s bound — that bound remains a
> statement about the intended discipline and now says so. And nothing
> here runs on hardware before SM10.1.

### Original record (tracked debt, owner SM5.I)

Surfaced by PR #854 review round 18, while reviewing the round-window
catch-up commit. Not an SM7 defect — SM7 inherits it — but recorded
here because SM7's round theorems are the most visible consumers.

### The defect

`Platform.FFI.modifyGetKernelState` is `IO.Ref.modifyGet`: a read
followed by a write, not a hardware read-modify-write. Two cores
committing concurrently both read `st`, both compute a post-state from
it, and the second write installs a state derived from a pre-state that
no longer holds — discarding the first core's entire transition and
returning success for it. Every kernel entry point commits this way
(`syscallDispatchCrossCoreEntry`, `perCoreTimerTickEntry`,
`suspendThreadCrossCoreEntry`, the cross-core IPC entries).

Nothing serialises those commits. `SHOOTDOWN_ROUND_LOCK` serialises
rounds against rounds and takes no part here; disabling interrupts is
per-core; the SM3 per-object locks exist but SM3.C.9 defers acquiring
them in the `@[export]` bodies to the SM5 per-core kernel-state seam.

### Why it went unnoticed for so long

Five sites describe the serialisation, and they do not agree — three
mutually exclusive mechanisms, none live:

| Site | Claimed mechanism | Reality |
|------|-------------------|---------|
| `Platform/FFI.lean` | `IO.Ref.modifyGet` is itself atomic against concurrent writers | False of the primitive |
| `Kernel/PerCoreTimerEntry.lean` | a kernel-entry lock the trap handler holds | No such lock exists |
| `Scheduler/Operations/PerCoreRunLoop.lean` | same | same |
| `Scheduler/Operations/PerCoreWcrt.lean` | per-object fine locks, live | Deferred by SM3.C.9 |
| `rust/sele4n-hal/src/cmdline.rs` | no kernel-entry lock, fine locks instead | Accurate on the first half only |

Each site is locally plausible and cites a real mechanism; only reading
them together shows that every one defers to another that does not hold.
All five now state the same thing: serialisation is **owed, not
present**.

### Severity

**Unreachable in a shipped artifact.** SMP is off by default and no
bootable image exists before SM10.1, so no configuration runs two cores
in the kernel today. High once bootable — a lost commit can drop a
capability revocation, a suspend, or a shootdown post, and the caller is
told it succeeded.

**Correction (v0.32.136).** The first half of that sentence was false
when written. `CmdlineConfig::default` returned `smp_enabled: true`, and
Phase 5 stores the parsed value straight into `smp::SMP_ENABLED` before
calling `bring_up_secondaries` — so a boot with no `smp_enabled=false`
on the command line would have brought all four cores up, and the
lost-update race would have been reachable on the first bootable image
rather than gated behind an opt-in. Only "no bootable image before
SM10.1" was carrying the unreachability claim.

The default is now `false`, which restores the precondition maintainer
decision #7 states for itself — "SMP enabled by default at v1.0.0 *once
SM5 lands*" — rather than reversing it. Two Rust tests pin it
(`default_boot_does_not_enable_smp_until_kernel_entry_is_serialized` on
the parser, and the boot-path witness on `parse_cmdline_from_dtb(0)`),
and both fail if the default is flipped back, which is the point at
which someone should be made to re-read this section.

**Flipping the default back to `true` is part of the acceptance
criterion below**, not a separate follow-up.

### What it does to the proofs

Nothing is false. Kernel transitions are pure functions and the theorems
say what those functions compute. What a lost update breaks is the tie
between the theorem and the runtime: the committed state stops being the
one the verified function was applied to. `preserves_foreign` (SM7.F.3)
is the clearest case — it guarantees a concurrent round's descriptors
survive the catch-up, which is worth having exactly once concurrent
commits cannot destroy each other wholesale.

### Closure

Either mechanism suffices, and they are alternatives rather than stages:

1. **Kernel-entry lock** — acquire in the Rust trap path around each
   `lean_*` entry. Matches what two docstrings already describe and what
   the WCRT bound's single-lock reading assumes. Must spin with
   interrupts enabled so a holder waiting on shootdown acks can still
   service `.tlbShootdownReq`, and must order outside
   `SHOOTDOWN_ROUND_LOCK` (nothing acquires it while holding a round
   lock, so the order is consistent today).
2. **SM3.C.9 `withLockSet` migration** — the fine-grained endgame the
   lock-set footprints and 2PL proofs were built for. Strictly more
   work; strictly better WCRT.

Whichever lands must be a reviewable slice of its own: it adds a
deadlock surface to the area that produced three P1 safety defects in
this PR alone, and it wants its own lock-order and liveness argument
rather than riding a round-18 remediation cut.

**Acceptance**: no kernel `@[export]` body commits state without holding
a lock that excludes every other kernel entry; the five sites above
updated to describe the mechanism that actually runs.

## `QueuedRwLock` deadlocked with the lock free — RESOLVED at v0.32.148

Found at v0.32.147 while adding contention witnesses; **fixed at
v0.32.148 by replacing the algorithm.** It was never on a live path —
`QueuedRwLock` has no callers, no FFI exports and no Lean bindings — but
it is the primitive SM3.C.9 intends to adopt for per-object locks, so it
was fixed before that adoption rather than filed against it.

### The defect

A watchdog dumped the lock the moment progress stopped:

```
progress per worker: [619, 478, 6, 394]
state = 0x0000000000000000   (writer_bit=false, readers=0)
tail  = 3
  slot[0] parked=WAITING_READER  mode=READ   next=1
  slot[1] parked=WAITING_READER  mode=READ   next=3
  slot[2] parked=WAITING_WRITER  mode=WRITE  next=1
  slot[3] parked=WAITING_READER  mode=READ   next=NONE
```

The lock is **free** while all four cores sit parked waiting for it, and
slot 2 is orphaned — the reachable chain `0 -> 1 -> 3` ends consistently
at `tail = 3` and slot 2 is not on it. Held 15 minutes: thread states
constant, `utime` linear, no self-resolution.

### The interleaving (event trace)

Instrumenting every protocol decision gave the sequence:

```
core3 SWAP prev=2          core3 (WRITER) enqueues behind core2
core3 LINK prev=2          slots[2].next = 3
core2 releases
core2 SIG_STOP tgt=3       walk REACHED core3 but could not admit it —
                           readers still held — so it returned, leaving
                           the admission to "a future signal from a
                           reader's release", as its comment claimed
core0 releases             (core0 is the LAST reader)
core0 SIG_STOP tgt=2       core0's own `next` is a FOSSIL pointing at
                           core2, which had already moved on
                           (PARKED_NOT_IN_QUEUE) -> returned WITHOUT
                           ever reaching core3
core2 re-acquires          reset() clears slots[2].next
                           -> core3's only link DESTROYED
```

The false premise is that a releaser can reach the queue. It walks from
*its own* slot, but readers are admitted en masse by
`cascade_admit_readers` and release independently, so a released
reader's slot need not be in the queue at all.

### Why it was replaced rather than patched

The surgical repair — record the deferred waiter so whoever drains the
lock completes the admission — was implemented and **did** fix that
interleaving. It immediately exposed a second, independent one:
`signal_next_waiter` tripping its own "walk exceeded MAX_WAITERS — chain
cycle?" assertion, because two cores can link behind each other across
incarnations.

Both have one cause: a core's slot is reused the moment it re-acquires,
while other cores still hold references to it. Every guard the protocol
had accumulated — stale-self detection, the mode-encoded four-state
`parked` machine, CAS-claim symmetry, walk-past-stale,
signal-on-every-release — was a patch on a consequence of that.

### The replacement

A ticket lock. `next_ticket` issues positions, `now_serving` names the
position entitled to enter. Readers join the reader count and pass the
ticket on immediately (so a contiguous run enters together); writers wait
for the count to drain, hold exclusively, and pass it on at release.
`state` keeps its bit-packed layout, so writer-readers exclusion and
`peek_state` are unchanged.

Deadlock-freedom is one sentence: **`now_serving` advances exactly once
per issued ticket, unconditionally, by whoever that ticket admits.** No
path returns without either advancing it or holding the lock. FIFO is
admission-in-ticket-order, stronger than the chain gave. There is no
`next` to go stale, no slot to reuse, no chain to cycle, no walk to
dead-end. ~370 lines replace ~1300.

### Acceptance (all met at v0.32.148)

| Check | Before | After |
|---|---|---|
| Direct-drive harness, 400 attempts x 3000 iters x 4 cores | stalled on attempt 0 | **no stall** |
| Full suite, 100 runs, `--test-threads=4` | 2-3 hangs | **0 hangs** |
| Pre-existing tests in the file | 1 deadlocking | **26/26 pass** |
| `test_rust.sh` | — | 1114 passed, clippy clean, 0 ignored |

The twelve cross-thread behavioural tests carried over **unchanged** —
they were written against the MCS design, so their passing is evidence
about the contract rather than about the new implementation's own shape.

### Collateral

`WaiterSlot`, `PARKED_*` and `MODE_*` are gone with the algorithm, along
with the seven tests that asserted on them; nothing outside the file
referenced any of it. `build.rs`'s protocol scanner pinned the old
machinery by literal string and now pins the ticket hand-off, keeping the
CAS-not-`fetch_or` writer-admission rule verbatim — the substitution that
gate's own text anticipated.
