# SM7 — TLB / Cache Shootdown (WS-SM Phase 7)

> **Phase**: SM7 of WS-SM
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Audited cut**: `v0.31.2`
> **Target releases**: v0.91.0 .. v0.95.x (parallel with SM8)
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
3. **Cache maintenance broadcast** (SM7.C): I-cache via
   `ic_ialluis`; D-cache by VA already at PoC.
4. **Per-core TLB model** (SM7.D): extends `TlbState` to a
   `Vector TlbState coreCount`.
5. **Tests** (SM7.E).

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

ARM ARM B2.7.5: DC operations at PoC (Point of Coherency) are
visible to all coherent agents. For seLe4n:

- D-cache by VA (`dc_civac`, `dc_cvac`, `dc_ivac`): no broadcast
  needed; DC ops at PoC already system-wide.
- I-cache invalidation on code modification: use `ic_ialluis`
  (inner-shareable broadcast variant; already in HAL).
- Cross-core DC for DMA buffers: out of scope for v1.0.0 (no
  DMA driver).

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
SM7.E.1 seed — 75 assertions / 11 groups), Tier-2 + Tier-3 wired.

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

Follow-up (pre-existing, NOT SM7.A-specific, out of this phase's
scope): a crate-wide conformance audit of the SM1-era
`@[extern] … BaseIO` ↔ plain `extern "C" fn` calling convention
(world-token/boxed-return ABI) once a linked runtime path exists to
exercise it (SM9.E QEMU image); SM7.A merely follows the established
convention.

| Sub | Description | Landed artefact | Status |
|-----|-------------|-----------------|--------|
| SM7.A.1 | `TlbShootdownDescriptor` struct | `SeLe4n/Kernel/Architecture/TlbShootdown.lean`: `{ op : TlbInvalidation, initiator : CoreId }` — the typed SM1.E.4 operand (one descriptor type covers the SM7.B.9 `.vae1`/`.vale1` unmaps, the SM7.B.10 `.aside1` ASID retire, and the SM7.B.11 `.vmalle1` full flush) + round attribution for the optional step-4d `.tlbShootdownAck` SGI | ✓ |
| SM7.A.2 | `pendingShootdowns : Vector (List TlbShootdownDescriptor) coreCount` | `TlbShootdownState.pendingShootdowns : Vector (List TlbShootdownDescriptor) numCores` under the SM4.B path-a discipline: `pendingOnCore` / `setPendingOnCore`, the `@[simp]` store/load algebra (`_self` / `_ne` / cross-field frames), `ext_perCore`; the boot state is quiescent (`initial_shootdownQuiescent`).  **v0.32.73**: mounted in the kernel state as `SystemState.tlbShootdown := .initial` (`default_tlbShootdown_{initial,quiescent,pendingBounded}`) — this plan's "in `ConcurrencyState`" placement | ✓ |
| SM7.A.3 | `shootdownAck : Vector Bool coreCount` (AtomicBool in Rust) | `TlbShootdownState.shootdownAck` + `acknowledgeShootdown` (monotone) + `beginShootdownRound` (§3.2 step 1 exactly: `beginShootdownRound_ackOnCore_iff`) + decidable `allAcked` + the SM7.B.5 termination anchor `allCores_foldl_acknowledgeShootdown_allAcked`.  Rust: `rust/sele4n-hal/src/shootdown.rs` — `SHOOTDOWN_ACK` per-core cache-line-aligned `AtomicBool` (boots all-`true`), `ack_set` Release / `ack_is_set` + `all_acked` Acquire / `reset_for_round` Relaxed (publication via SM1.F.8 dsb-before-SGIR; cross-round hazard analysis in the module docs), fail-closed bounds panics, `_in_slice` testable forms; HAL 724 → 743 tests | ✓ |
| SM7.A.4 | `enqueueShootdown` operation | FIFO tail-append, fail-closed `none` at capacity (a dropped descriptor is the SMP-C4 stale-TLB hazard); `enqueueShootdown_isSome_iff` / `_eq_none_iff` / `_pending_target` / `_mem` / `_length` / `_frame_pending` / `_frame_ack` / `_preserves_pendingBounded` | ✓ |
| SM7.A.5 | `drainShootdowns` (called from SGI handler) | whole-queue FIFO drain returning `(queue, cleared state)` — `drainShootdowns_fst` is the completeness half of Theorem 3.3.1's remote case; exhaustive (`_drain_twice`), framed (`_frame_pending` / `_frame_ack`), ack-free by design (see status note); round-trip `drainShootdowns_after_enqueue` | ✓ |
| SM7.A.6 | Pending queue capacity bound | `maxPendingPerCore = 16` (§4.1) + `maxPendingPerCore_pos`; decidable `pendingBounded` established at boot and preserved by every SM7.A operation (`enqueueShootdown` / `drainShootdowns` / `acknowledgeShootdown` / `beginShootdownRound` `…_preserves_pendingBounded`); drain restores capacity (`enqueueShootdown_isSome_after_drain`).  **v0.32.73**: the §4.1 sufficiency argument is formal — `beginRound_foldlM_enqueueShootdown_isSome` (a round's posting fold from quiescence always succeeds) closes an induction with `shootdownRound_restores_quiescent` (a completed round is quiescent again); the total `enqueueShootdownOrCoalesce` full-flush-collapse escape hatch covers any future caller that batches past the bound (`…_request_covered`, unconditional `…_preserves_pendingBounded`) | ✓ |

### SM7.B — Shootdown protocol (4 PRs, 12 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM7.B.1 | `tlbShootdownLocal (asid, vaddr)` | (def) | M |
| SM7.B.2 | `tlbShootdownBroadcast (initiator, targets, asid, vaddr)` | (def) | L |
| SM7.B.3 | SGI handler for `.tlbShootdownReq` (registered in SM1.F.5) | (def) | L |
| SM7.B.4 | `shootdownAck` release-acquire synchronization | `shootdownAck_release_acquire` | M |
| SM7.B.5 | Initiator wait-loop terminates | `shootdown_wait_loop_terminates` | M |
| SM7.B.6 | Timeout fallback (panic at SM7; relax post-1.0) | `shootdown_timeout_handling` | M |
| SM7.B.7 | Lock-set for shootdown | `lockSet_tlbShootdown_correct` | M |
| SM7.B.8 | `tlbShootdownBroadcast_invalidatesAllCores` | Theorem 3.3.1 | XL |
| SM7.B.9 | Wire all unmap callers (~8 sites) | (refactor) | M |
| SM7.B.10 | ASID-retire shootdown | (def + theorem) | M |
| SM7.B.11 | Retype-with-page-free shootdown | (theorem) | M |
| SM7.B.12 | Cross-cluster path via `.outer` sharing | `tlbShootdown_outer_correct` | M |

### SM7.C — Per-core TLB model (3 PRs, 8 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM7.C.1 | Extend `TlbState` to `Vector TlbState coreCount` | (def) | M |
| SM7.C.2 | `tlbInsertOnCore` (models HW translation walker) | (def) | M |
| SM7.C.3 | `tlbInvalidateOnCore` | (def) | M |
| SM7.C.4 | `tlbInvalidateOnAllCores` (uses shootdown protocol) | (def) | M |
| SM7.C.5 | `tlbInvalidationConsistent_perCore` | Theorem | L |
| SM7.C.6 | `tlbShootdown_invalidates_perCore` (corollary of 3.3.1) | Corollary | M |
| SM7.C.7 | `tlbConsistency_cross_subsystem` | Theorem | M |
| SM7.C.8 | Surface anchors (`#check` 8 theorems) | S |

### SM7.D — Cache maintenance broadcast (2 PRs, 4 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM7.D.1 | I-cache invalidation: `ic_ialluis` (exists from HAL) | `Architecture/CacheModel.lean` doc | S |
| SM7.D.2 | D-cache by VA at PoC documented system-wide | docstring | T |
| SM7.D.3 | Cross-core DC for DMA out-of-scope documentation | docstring | T |
| SM7.D.4 | Cache-coherency invariant under SMP | Theorem | M |

### SM7.E — Tests (3 PRs, 6 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM7.E.1 | `tests/SmpTlbShootdownSuite.lean` (15+ scenarios) | XL |
| SM7.E.2 | QEMU shootdown integration | `scripts/test_qemu_smp_shootdown.sh` | M |
| SM7.E.3 | Shootdown stress test (4 cores × concurrent unmaps) | M |
| SM7.E.4 | Cross-cluster mock test | M |
| SM7.E.5 | Surface anchors | S |
| SM7.E.6 | Fixture: `smp_tlb_shootdown.expected` | S |

## 6. Verification strategy

### 6.1 What SM7 proves

~14 substantive theorems including:
- `tlbShootdownBroadcast_invalidatesAllCores` (the headline)
- `shootdownAck_release_acquire`
- `shootdown_wait_loop_terminates`
- `tlbInvalidationConsistent_perCore`

### 6.2 What SM7 assumes

- ARM ARM C6.2.311-316 (TLBI semantics).
- ARM ARM B2.7.5 (DSB ISH inner-shareable semantics).
- SM2.A memory-model synchronizesWith.
- SM1.E IS-variant TLB primitives.

## 7. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Shootdown deadlock (initiator waits forever) | LOW | CRIT | Bounded WFE; timeout panic at SM7 |
| Stale TLB on remote core post-shootdown | LOW | CRIT | Theorem 3.3.1 + explicit ack |
| Ack flag missed (race on read/write) | LOW | HIGH | Release-acquire synchronization |
| Multiple concurrent shootdowns interleave | LOW | HIGH | **Single global shootdown-round lock** (`ShootdownRoundLockId`, SM7.B.7).  The SM7.A audit showed the VSpaceRoot lock alone is insufficient: two different-VSpace initiators would interleave rounds on the round-identity-free ack vector (early `allAcked` exit with a stale TLB live — the SMP-C4 hazard — plus a mutual-hang mode); see the SM7.A completion record |
| Pending queue overflow | LOW | MED | Bounded by maxPendingPerCore=16 |
| Cross-cluster path under-tested | MED | LOW (no current target) | Mock test in SM7.E.4 |

## 8. Acceptance gate

- [x] Shootdown descriptor + state defined (SM7.A, v0.32.72).
- [ ] Protocol implemented per §3.2.
- [ ] `tlbShootdownBroadcast_invalidatesAllCores` proven.
- [ ] All unmap callers wired through Broadcast.
- [ ] Per-core TLB model.
- [ ] Cache-coherency invariant.
- [ ] Tier 0..4 green; QEMU shootdown test passes.
- [ ] **Closes SMP-C4 formally.**

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
lake build SmpTlbShootdownSuite
./scripts/test_qemu_smp_shootdown.sh
```

---

*SM7 closes the most safety-critical SMP gap. The explicit-ack
protocol's correctness (Theorem 3.3.1) hinges on the
release-acquire pairing that SM2's memory model already proves
abstractly.*
