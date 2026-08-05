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

Tests: `tests/SmpTlbShootdownSuite.lean` §4.1–§4.8 (the SM7.E.1 suite
grows 81 → 150 assertions / 20 groups): invalidation-effect semantics,
broadcast/handler transitions, the full protocol round with
Theorem 3.3.1 computed over per-core views, the live map → unmap →
shootdown pipeline on a built VSpace state, ASID-allocate rounds,
17-round coalescing, wait/timeout verdicts, the lock-set, and the
diff-recovery seam.  Rust HAL 755 → 769 (round lock, bounded wait
incl. deadline-exactness, handler + registration/dispatch, online
mask, full-IAR dispatch + EOI conformance).

#### SM7.B completion cut (v0.32.77)

A follow-on cut closing every depth item the landing deferred:

* **Invariant-bundle carriage (the plan's "join a SystemState-level
  invariant bundle" deferral, CLOSED)**: `pendingBounded
  st.tlbShootdown` is the **12th conjunct of
  `proofLayerInvariantBundle`** (`Architecture/Invariant.lean`) — boot
  witness via `default_tlbShootdown_pendingBounded`, the three adapter
  preservation proofs extended, the Boot general bridge
  (`bootFromPlatform_tlbShootdown_eq` + the 12-component composition),
  and freeze carried wholesale.  The carriage is proven through every
  live shootdown-aware transition (`…_preserves_pendingBounded` for
  the handler, `withShootdownRound`, all five syscall wrappers, and
  both retype wrappers), resting on a new `…_tlbShootdown_eq` frame
  family covering the entire retype-cleanup pipeline and the VSpace
  base ops (`storeObject` / splice / sweeps / `detachCNodeSlots` /
  `returnDonatedSchedContext` / registry / scrub / `cspaceLookupSlot`).
* **Handler commutativity**: distinct-core round steps commute at both
  layers (`completeShootdownOnCore_comm`,
  `handleTlbShootdownReqOnCore_comm` via the retire-filter algebra
  `applyTlbInvalidation(s)_comm`) + the fold-swap corollary — the
  catch-up fold's visit order is a convention, not a correctness
  requirement.
* **Coalescing-round capstones**: `coalescingRound_restores_quiescent`
  / `coalescingRound_allAcked` (the round the runtime *actually* runs,
  via `tlbShootdownBroadcastCoalescing_eq_strict`), the positive diff
  characterization `shootdownChangedTargets_coalescing_of_quiescent`
  (the seam pokes *exactly* the round's targets), and the total-posting
  remote case of Theorem 3.3.1 (`coveredQueueRetire_removes` →
  `vspaceUnmapPageWithShootdown_remote_retire_removes`).
* **Remap-only map rounds + a model fact**: the `.vspaceMap` wrapper
  now posts only on the remap direction (`vspaceHasTranslation`
  pre-state detector; `_fresh_inert`) — and the model fact
  `vspaceMapPageCheckedWithFlushFromState_ok_fresh` pins that a
  *successful* map is always fresh (`VSpaceRoot.mapPage` rejects an
  occupied vaddr with `.mappingConflict`), so the map path owes no
  round today (`…_never_posts`); the posting branch stays as a
  defense-in-depth seam (`_remap_posts`) should `mapPage` ever gain
  replace semantics.  The round rides the unmap of the
  unmap-then-map discipline.
* **Least-index wait + round-lock model**: `waitAllAckedFrom_first` /
  `waitAllAckedBounded_least` (the bounded wait returns the least
  all-acked snapshot; `shootdown_wait_loop_terminates_least` extracts
  the least witness constructively, no choice), the round-lock CAS
  state machine (`roundLockTryAcquire` — success-iff-free, mutex,
  release-liveness) matching the Rust `compare_exchange` exactly, the
  cross-round publication chain `shootdownRoundLock_release_acquire`
  (+ decide-checked witness) — the formal reason the ack vector needs
  no round identity under serialisation — and the 4-core multi-pair
  B.4 witness (`shootdownAck_release_acquire_multi_pair_witness`).
* **Entry hardening**: named fuel constant
  `shootdownRoundLockAcquireFuel` (pinned), `completeShootdownRounds_nil`
  (the no-op path is `pure ()` by rfl — trace safety at the definition
  level), one `CORE_READY` snapshot per round (`shootdownOnlineMask` +
  pure `coreOnlineInMask`), the `vmalle1`-dominance operand collapse
  (`collapseShootdownOps`, effect-exact), `shootdownSharingDomain` now
  *derived* from `PlatformBinding.sharingDomain` (B.12 binding read;
  `shootdownSharingDomain_rpi5` pins `.inner`), and the cooperative
  self-service arm flipped to the **local** `tlbi vmalle1`
  (`Concurrency.tlbiLocalFullFlush` — the waiter cleans exactly its own
  view, as the Rust handler does; `ffi_tlbi_all`'s usage contract
  updated).
* **storeObject sweep (SM7.B.11 closure)**: audit of every
  vspaceRoot-destroying path found one further production entry point
  owing TLB work — the CSpaceAddr wrapper `lifecycleRetypeWithCleanup`;
  closed by the shootdown-aware sibling
  `lifecycleRetypeWithCleanupShootdown` (+ `_non_vspace` /
  `_vspace_posts` / `_preserves_pendingBounded`).  Remaining paths are
  clean by construction: `Internal.lifecycleRetypeObject` /
  `lifecycleRevokeDeleteRetype` are documented proof-chain internals
  (unreachable from dispatch), the non-shootdown `WithFlush` map/unmap
  forms are proof-decomposition helpers superseded on the live path,
  `installBootVSpaceRoot` runs pre-secondaries (TLBs empty by the
  bring-up contract), and `FrozenOps.frozenStoreObject` is staged
  experimental.
* **Typed-flush bridge**: the encoded operands are at least as strong
  as the typed local flushes
  (`mem_adapterFlushTlbBy{VAddr,Asid}_of_mem_applyTlbInvalidation_…`) —
  collisions only ever widen removal.
* **Test hardening**: Rust handler `_in` slice form with **genuine**
  `false → true` ack-transition tests (the boot-all-`true` global made
  the prior assertions vacuous), `round_lock_try_acquire_in` /
  `_release_in` + an 8-thread CAS **mutex stress** (at-most-one-holder
  observed at every instant); HAL 769 → 772.  Suite §4.9 (completion
  cut) + §4.10 (the **live `.vspaceUnmap` through `dispatchSyscall`**:
  CSpace resolution + authority gate + posting + fail-closed no-cap /
  read-only-cap) — 22 scenario groups, 160 runtime assertions.
  SM7.E.2 seeded: `scripts/test_qemu_smp_shootdown.sh` (Tier-4,
  registered in `test_tier4_smp_bootcheck.sh`; SKIPs until the SM9.E
  bootable image, as its SM5/SM6 siblings).
* **Testing note**: `Testing/InvariantChecks.lean` mirrors
  `crossSubsystemInvariant` only; the new bundle conjunct is
  runtime-checked by the suite's decidable `pendingBounded` probes, so
  the executable checker needs no change (golden trace byte-identical
  by construction).

#### SM7.B debt-closure cut (v0.32.78)

Every debt item either CLOSED or narrowed to a precisely-scoped
residual with an explicit target.

* **Per-descriptor Rust handler TLBIs — CLOSED.**  The
  `.tlbShootdownReq` handler now retires the round's EXACT operands on
  the local PE (one `tlbi` per descriptor via the new
  `tlb::tlbi_local`) instead of a blanket `tlbi vmalle1`, matching the
  Lean model's per-descriptor `applyTlbInvalidations`
  (`handleTlbShootdownReqOnCore`).  The initiator publishes the round's
  collapsed operands — under the round lock, BEFORE the SGIs, so the
  `dsb ish` in `send_sgi` orders the publish ahead of any SGI — into a
  **seqlock-guarded fixed-capacity mailbox** (`ShootdownOpMailbox`);
  the handler reads a stable snapshot and retires per-descriptor,
  falling back to the conservative local `tlbi vmalle1` on ANY torn
  read, empty round, over-capacity length, or undecodable operand.
  Over-invalidation is always safe; the fallback can never
  under-invalidate.  Lean: `publishShootdownOps` in the live seam +
  the `ffiShootdownPublish{Begin,Slot,Commit}` FFI + typed wrappers;
  Rust: the mailbox + `publish_*`/`snapshot_*`/`retire_round_ops_in`
  primitives + `decode_tlb_invalidation` (shared with the FFI
  dispatcher) + 8 genuine unit tests (round-trip, torn-read fallback,
  overflow collapse, per-descriptor count, op-tag conformance);
  HAL 772 → 780.  Trace byte-identical.
* **Rust-handler formal refinement — NARROWED.**  The per-descriptor
  handler now REFINES the Lean `handleTlbShootdownReqOnCore` TLB effect
  *operand-for-operand* (was "⊇, full flush"): the op-tag decode is
  pinned identical on both sides (`op_tag_decode_conformance`
  ↔ `TlbInvalidation.toOpTag`/`toAsid`/`toVaddr`, exercised in suite
  §4.11), and the retire path is unit-tested to issue exactly the
  published operands.  Residual: the end-to-end machine-checked
  refinement of the *linked* Rust↔Lean runtime still needs the SM9.E
  bootable image (unchanged target — it is the linked-runtime proof,
  not the effect correspondence, that remains).
* **B.10 syscall-level reachability — deferred, NO safety gap
  (sharpened target).**  `asidAllocateWithShootdown` is the correct,
  complete, proven kernel-level `requiresFlush` consumer, but has **no
  consumer** and no syscall route.  Audit confirms there is **no
  runtime ASID-reuse path at all**: `lifecycleRetype` creates a *fresh*
  ASID-0 empty `vspaceRoot` (`objectOfKernelType .vspaceRoot`), and
  `asidTable` is populated only at boot from the builder's initial
  roots — so no live transition reuses an ASID without the round.  The
  gap is therefore pure *completeness* (user-facing reachability), not
  a correctness/safety hole.  Closing it requires an
  ASIDControl/ASIDPool **object family** + an `asidPoolAssign` syscall
  + mounting the pool as `SystemState` — a coherent VSpace/ASID
  subsystem PR, **explicit closure target: SM8**.  Building an unwired
  assign primitive here would violate the wire-it-into-the-consumer
  rule, so it is deliberately not added.
* **Step-4d direct-ack SGI (`.tlbShootdownAck`) — CLOSED by design
  decision (won't implement).**  Under the B.6 spin-based bounded wait
  (a bare `wfe` was rejected as unsound: it could sleep past a hung
  target) the initiator polls the shared ack flags directly, and the
  SVC path runs IRQs-masked — so a direct-ack SGI can neither preempt
  the initiator nor deliver information the acquire-poll does not
  already read.  The optional optimisation adds a whole SGI round-trip
  for zero latency benefit under the chosen wait model; recorded as a
  closed design decision, not deferred work.
* **`withLockSet` bundle carriage — shootdown slice CLOSED.**  The 2PL
  bracket provably frames `tlbShootdown` (`acquire`/`releaseLockOnObject`
  /`acquireAll`/`releaseAll`/`withLockSet_tlbShootdown_eq`), so
  `withLockSet_preserves_pendingBounded` carries the 12th
  `proofLayerInvariantBundle` conjunct through any 2PL-guarded
  transition that preserves it (`WithLockSet.lean`; suite §4.11
  witness).  Residual: the full twenty-conjunct
  `withLockSet_preserves_ipcInvariantFull_perCore` generalisation stays
  with the SM6.D campaign (unchanged target).
* **SM7.C.6** — the plan-literal per-core restatement of Theorem 3.3.1
  lands with the per-core TLB mount (mechanical instantiation of the
  vector form; unchanged target).
* **Host-test starvation livelock (pre-existing, SM2-era) — CLOSED.**
  Audit shows the yields already exist: every FIFO spin routes through
  `cpu::wfe()`, which under `#[cfg(test)]` calls `std::thread::yield_now`
  (the SM2.E host-livelock fix), and the authoritative Rust gate
  (`scripts/test_rust.sh`) **builds all crates before running any test**,
  so the compile-contention window that produced the observed hang does
  not exist in the real test flow — it was an artifact of an ad-hoc
  combined `cargo test --workspace`.  Hardening: the SM7.B round-lock
  mutex-stress test now caps its contenders at
  `std::thread::available_parallelism()` so it cannot pathologically
  oversubscribe a small-core CI host.  Not a target defect (per-core
  PEs never oversubscribe) and not reachable from the SM7.B path (the
  round lock is try-acquire — never blocks).

#### SM7.B PR #839 review-P1 cut (v0.32.79)

Two P1 review findings on PR #839.

* **Comment 1 — shootdown targets keyed on the release handshake, not
  IRQ-readiness — CLOSED (real bug fix).**  Both the round reset mask
  (`reset_for_round`) and the SGI target mask (`online_mask`) read
  `smp::CORE_READY`, which the *primary* sets the instant `CPU_ON`
  succeeds (`smp.rs` `bring_up_secondaries_inner`) — i.e. **before** the
  secondary initialises its GIC CPU interface, arms its timer, or
  unmasks IRQs.  A round issued while a secondary is mid-bring-up (or
  targeting a core whose timer init *failed* and is parked forever in
  the fatal WFE halt loop, `CORE_READY` still `true`) resets that core's
  ack flag and fires it an SGI it cannot service → the initiator's
  `all_acked` wait deterministically reaches the SM7.B.6 10 ms
  fail-closed panic.  The permanent variant (timer-dead core) wedges
  *every subsequent* round, not just one.  **Fix**: a separate
  per-core `smp::CORE_IRQ_READY` flag the secondary publishes **itself**
  after `enable_irq` (Release), read (Acquire) by both masks via the
  shared `irq_ready_online()` snapshot; boot core born `true`.
  Excluding a not-IRQ-ready core is safe — it holds no invalidatable
  TLB entry (pre-MMU ⇒ empty after the boot `tlbi vmalle1`; between
  MMU-enable and `enable_irq`, or halted, ⇒ only fixed boot/halt-loop
  mappings that are never unmapped).  Lean side is FFI-backed
  (`ffiShootdownOnlineMask` / `shootdownOnlineMask`), so only docstring
  prose changed there.  Rust: `online_mask_of` (testable fold) +
  `irq_ready_online` + 2 new unit tests (`online_mask_of_*`,
  `sm7b2_reset_and_target_masks_agree_*`); HAL 780 → 782.
* **Comment 2 — model posting/catch-up not round-lock-serialised —
  TRACKED DEBT (model-fidelity, NOT a hardware hazard).**  The model
  *posting* (pending-queue enqueue) rides the syscall's own atomic
  `modifyGetKernelState` and the model *catch-up* rides a second atomic
  step; neither is under `SHOOTDOWN_ROUND_LOCK`, which serialises only
  the **hardware** round.  So under concurrent rounds one core's
  catch-up fold can drain another core's freshly-posted descriptors,
  making the model transiently quiescent before that round's hardware
  SGIs fire.  **Why this is fidelity-only, not a safety bug**: each
  round's hardware TLB maintenance is driven entirely by *that round's
  own* `(pre, post)` diff (`shootdownPostedOps` /
  `shootdownChangedTargets`), fires its own SGIs to the online targets,
  and blocks on its own `SHOOTDOWN_ACK` channel before the initiating
  syscall returns — so no round under-invalidates, and cross-round model
  over-draining is safe over-application (`handleTlbShootdownReqOnCore`
  is idempotent).  Model quiescence gates only capacity / `pendingBounded`
  bookkeeping, never a hardware-cleanliness decision.  Documented at the
  site (`completeShootdownRounds` docstring §"Model-vs-hardware catch-up
  fidelity").  **CLOSED at v0.32.105 (SM7.F.3)**: pending descriptors
  now carry the generation of the round that posted them, and a
  commit's catch-up drains only the generations its own commit opened
  (`shootdownCatchUpPerCoreInWindow_preserves_foreign`).  The Rust
  mirror of that change also closed a genuine **security** hazard the
  Boolean acknowledgment vector carried — a stale `.tlbShootdownReq`
  SGI acknowledging into a later round — see the §SM7.F.3 section.

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

Tests: `tests/SmpTlbShootdownSuite.lean` §5.1 (accessors + local ops:
`tlbInsertOnCore` fill locality, `tlbInvalidateOnCore` leaving other
cores stale — the SMP hazard) + §5.2 (the cross-core
`tlbInvalidateOnAllCores` round: no core retains the unmapped
translation, selectivity, exact SGI list, `tlbShootdown` posting,
capacity-conjunct + object-store framing, quiescent success) — the suite
now covers SM7.A + SM7.B + SM7.C.

**Round-generation-tagged descriptors (the SM7.B v0.32.79 model-fidelity
debt) was a separately-scoped follow-on**, deliberately not folded into
this cut: it is a `TlbShootdownState` *descriptor-type* change (rippling
the entire SM7.A/B `pendingBounded` / `shootdownRound_quiescent` /
Theorem 3.3.1 / `_preserves_*` surface + the Rust mailbox), orthogonal to
the per-core TLB *view* model SM7.C delivers.  It **landed at v0.32.105
as SM7.F.3** — see that section, which also records the security hazard
the Rust half of the change closed.

#### SM7.C completion cut (v0.32.81) — the model made operative + completeness

A follow-on cut turning the SM7.C model from a faithful-but-parallel
spec into the **operative** one the live shootdown path runs, and closing
every completeness gap the landing left.  Zero sorry/axiom; golden trace
**byte-identical** (verified); Tier 0–3 green.

* **The per-core model is now LIVE on the shootdown path (A1/A5).**  New
  operational per-core handler `handleTlbShootdownReqOnCorePerCore` drains
  *each core's own* posted queue onto *its own* `perCoreTlb` view (the real
  per-descriptor drain), with the initiator's `tlbShootdownLocalPerCore`
  local step; `shootdownRoundPerCore` composes them.  The live
  `SyscallDispatchEntry.completeShootdownRounds` catch-up commit now folds
  `handleTlbShootdownReqOnCorePerCore` (was the single-view
  `handleTlbShootdownReqOnCore`), so a live shootdown's model post-state
  carries the correct per-core views.  **Trace-safe by proof**: the
  per-core handler's `tlb` / `tlbShootdown` effects are *definitionally* the
  SM7.B single-view handler's (`…_tlb_eq` / `…_tlbShootdown_eq`), and the
  two folds agree on those fields
  (`foldl_handleTlbShootdownReqOnCorePerCore_agrees`); only the
  projection-invisible `perCoreTlb` additionally evolves.
* **Operative Theorem 3.3.1 via the real drain (A5).**
  `foldl_handleTlbShootdownReqOnCorePerCore_perCoreTlb` proves the real
  per-core drain **equals** the abstract `shootdownRoundViews` vector
  step-for-step (not by shared arguments), bridged by
  `handleTlbShootdownReqOnCorePerCore_applies_posted_op` +
  `tlbShootdownBroadcast_posts_singleton`; `shootdownRoundPerCore_perCoreTlb`
  and `shootdownRoundPerCore_invalidates_perCore` then give Theorem 3.3.1
  on the *live* round: after a covering per-core round no core retains a
  covered entry.
* **The two-model bridge (A4).**  `shootdownRoundPerCore_tlb_eq`: the
  per-core round's `tlb` / `tlbShootdown` effect equals the SM7.B
  single-view `shootdownRound`'s — the scalar `tlb` stays the (imprecise,
  all-cores-conflated) single view, `perCoreTlb` is the per-core
  refinement; they are related for every round, not just at boot, and are
  deliberately *not* forced pointwise-equal (the single view conflates
  what the per-core model keeps distinct).
* **Model completeness (B1/B2/B3).**  `tlbInsertOnCore_preserves_…` (the
  walker half of the safety story: a page-table-matching fill preserves
  per-core consistency); `tlbInvalidateOnAllCoresCoalescing` (the total,
  never-fails form mirroring SM7.B's, `…_eq_strict`); and the
  runtime-decidable checker `tlbConsistentCheck` /
  `tlbInvalidationConsistentCheck_perCore` (`…_iff` + `Decidable`
  instances) making the 13th `proofLayerInvariantBundle` conjunct
  executable, exactly as the 12th (`pendingBounded`) is.
* **Robustness + hygiene (D1–D4).**  `FrozenSystemState.perCoreTlb` is now
  **required** (no default), symmetric with the scalar `tlb` it
  generalises — a silent per-core drop is a compile error at the freeze
  site (six frozen test fixtures updated).  Explicit non-interference
  witness `perCoreTlb_write_preserves_projection` (a per-core TLB write is
  projection-invisible — no covert channel).  Dead `perCoreTlb_vector_ext`
  helper removed.  Plan §1 SM7.C/SM7.D lettering corrected to agree with
  §5.
* **Tests + anchors.**  `tests/SmpTlbShootdownSuite.lean` §5.3 (the
  operational round, the bridge to the single-view round computed, the
  coalescing form, the runtime checker, the walker fill) + the §1 `#check`
  anchors over the operational/completeness/NI symbols; Tier-3 anchors for
  the operational theorems and the live-seam per-core wiring.

#### SM7.C PR #844 review cut (v0.32.83) — initiator drain + view-outcome demotion

Two Codex review findings on PR #844, both verified valid against the code
and fixed faithfully (neither was a live safety bug — `perCoreTlb` is always
empty on the live path — but both were genuine per-core-model fidelity gaps).
Zero sorry/axiom; golden trace **byte-identical** (verified).

* **P1 — apply the local invalidation to the initiator (live seam).**  The
  live `completeShootdownRounds` catch-up folded the per-core handler only
  over `shootdownTargets execCore` (which *excludes* the initiator), so the
  initiator's own `perCoreTlb` view was left stale even though its
  inner-shareable `tlbiForSharing` broadcast reaches the issuing PE.  New
  `drainInitiatorPerCoreView` (perCoreTlb-only — the scalar `st.tlb` was
  already retired in the dispatch, so it is trace-safe) + `shootdownCatchUpPerCore`
  (the complete live catch-up: the non-initiator target fold **and** the
  initiator drain); the seam now runs `shootdownCatchUpPerCore st execCore
  collapsed`.  Trace-safety proven by `shootdownCatchUpPerCore_agrees_singleView`
  (the `tlb`/`tlbShootdown` effect is exactly the SM7.B single-view target
  fold's); faithfulness by `shootdownCatchUpPerCore_initiator_view`
  (+ `_preserves_tlbInvalidationConsistent_perCore`).
* **P2 — the eager `tlbInvalidateOnAllCores` is a view-outcome abstraction,
  not a completed round.**  It posts the broadcast (targets pending, acks
  down) while eagerly evolving the views; its docstring is corrected to say
  so explicitly and to point at the operative drains-at-ack round
  `shootdownRoundPerCore` (which the live seam realises), and the new
  `shootdownRoundPerCore_cross_subsystem` gives the C.7 capstone on the
  faithful completed round.

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

**Review-3 hardening (v0.32.87–88, PR #844 review-3).**  Three P2
soundness/fidelity findings on the per-core invariant closed (per-core scoped;
the scalar `tlbConsistent` shares the vacuity but stays out of SM7.F scope):
- **Finding 1 — no ASID vacuity.**  `tlbEntryConsistent` was an implication,
  vacuously true when the ASID no longer resolves, so a use-after-retype entry
  (`lifecycleRetype` replaced the VSpace root ⇒ `resolveAsidRoot = none`) was
  accepted as consistent.  Redefined to the existential conjunction (resolve
  **and** match); an unresolvable ASID now fails the consistent branch and must
  ride a pending descriptor.  New VSpace lemma
  `vspaceUnmapPage_resolveAsidRoot_isSome` (an unmap never unbinds an ASID) lets
  the F.2a frame carry the conjunction; every consumer re-proven; the unused
  bridge `tlbEntryOk_of_tlbConsistent` dropped.  §5.3/§5.7.
- **Finding 2 — faithful coalescing view.**  `tlbInvalidateOnAllCoresCoalescing`
  now drives its views with `shootdownRoundViewsCoalescing`: an overflowed
  target (queue at `maxPendingPerCore`, posting coalesced to `.vmalle1`) is
  **full-flushed**, matching the coalesced descriptor rather than merely
  `op`-invalidated.  `_eq_strict` preserved (agrees on non-overflowing states).
  §5.8.
- **Finding 4 (v0.32.88) — duplicate coalescing targets.**  The Finding-2 view
  consulted the fixed pre-round state on every visit, so a *duplicate* target
  reaching capacity only on its second visit was under-invalidated (`op` twice,
  not the coalesced full flush).  `shootdownRoundViewsCoalescing` now **threads
  the evolving shootdown state** (keyed on `beginShootdownRoundFor`), mirroring
  `postShootdownRoundCoalescing` operand-for-operand; `_eq_strict` re-proven via
  the foldlM-success agreement form.  §5.9.  (Finding 3 — live `.vspaceUnmap`
  wiring — is the tracked SM7.F.4(b) obligation; the catch-up already drains the
  initiator on the live path, so no correctness hole today.)

#### SM7.F.5 (v0.32.150) — the access-time fill

**The gap.**  `tlbFillOnCore` was invoked from exactly one site (the F.4(a)
mapping seam), so `perCoreTlb` modelled only translations a core established
itself.  The acceptance criterion's "access (fill)" step therefore had nothing
to run, and the per-core TLB invariant plus Theorem 3.3.1 stayed vacuous for
any core that had not done the mapping.

**The seam.**  The kernel performs exactly one translation of a *user* virtual
address on the syscall path: reading the caller's IPC buffer for the overflow
message registers, when a syscall carries more than the four the ABI passes in
registers (`RegisterDecode.decodeSyscallArgsFromState` →
`IpcBufferRead.ipcBufferReadMr`, which resolves through the caller's VSpace).
On hardware that walk fills the executing core's TLB.  New production module
`Architecture/IpcBufferTlbFill.lean` makes it fill `perCoreTlb`:
`ipcBufferWalkPlan` (what the walk resolves — the read's own route, TCB then
VSpace root), `ipcBufferOverflowPages` (the *distinct* pages walked;
`tlbInsertOnCore` prepends without deduplicating and a TLB caches one entry
per page), and `tlbFillIpcBufferOnCore` folding `tlbFillOnCore` over them.
**Live** in `API.syscallEntryChecked` — the per-core entry the SMP dispatch
runs — applied to the state passed to `dispatchSyscallChecked`, so the fill
precedes the transition exactly as the hardware walk precedes the operation.

**Keyed on the page, deliberately.**  `tlbEntryMatches` compares virtual
addresses for *equality*, not containment, so an entry keyed at a byte offset
would not be matched by the page invalidation a later unmap posts — it would
survive the shootdown meant to evict it and make the invariant reachably
false.  The fill caches `ipcBufferSlotPage`, the same page base the read
resolves through: one definition with two consumers, so "cache what the read
walked" holds by construction rather than by a theorem that could rot.

**Theorems.**  `_frame` (objects / ASID table / shootdown state untouched),
`_tlbOnCore_ne` (a walk is a this-core event — the SMP asymmetry, now on the
live path), `_preserves_tlbInvalidationConsistent_perCore` (substantive: every
entry added is one a real walk resolved, hence consistent by construction),
`_eq_setPerCoreTlb` (the fill writes that field and nothing else),
`ipcBufferOverflowPages_aligned`, and the correspondence
`tlbFillIpcBufferOnCore_caches_read_translation` — the load-bearing one, since
the read resolves `tid → tcb.vspaceRoot → root` while the fill resolves
`asid → resolveAsidRoot`; its `hResolve` premise is exactly the statement that
those two routes agree, which the ASID-rebind hazard can falsify.  Zero
sorry/axiom (`propext`, `Quot.sound`).  Trace byte-identical.

**Prerequisite defect fixed (pre-existing).**  `ipcBufferReadMr` passed the
slot's *byte* address to `VSpaceRoot.lookup`, which is an exact-key table
whose keys are page bases — so every slot but the zeroth missed, and any
syscall carrying two or more overflow message registers failed with
`invalidMessageInfo` against a correctly mapped buffer.  Slot 0 worked only
because its offset is zero.  Existing coverage exercised `overflowCount` 0 and
1 only, which is why it survived; the module's own docstring already described
the per-slot, page-crossing behaviour the code did not implement.  Fixed by
splitting the address (`VAddr.pageBase` / `VAddr.pageOffset`, new in
`Prelude.lean` beside `pageBytes`): resolve the containing page, carry the
intra-page offset through to the physical address.  Fail-closed, so no
security exposure — a fidelity defect.  Regression gates in `DecodingSuite`
(two overflow slots; a non-page-aligned buffer; a slot crossing into an
unmapped page still failing closed), and the fixture now keys its mapping on
the page base as `mapPage` does.

**Disclosed, not implemented.**  Two neighbouring limitations, stated here
rather than silently carried:

* The **scalar `tlb`** (9th conjunct) remains unconditional and empty-live.
  It is the pre-SMP single-view model that `perCoreTlb` refines, and
  `syscallEntry` — the boot-pinned entry — is deliberately left unfilled so
  the two models do not mix.  Out of SM7.F scope, unchanged by this cut.
* There is **no TLB capacity or eviction model**: a modelled view retains
  every entry ever filled.  This is the safe direction (the invariant carries
  a strictly stronger obligation than hardware imposes, since a real TLB may
  drop entries at will), but it was undisclosed and is now on the record.

**Whole-bundle carriage — CLOSED at v0.32.151.**  The landing cut could not
prove `proofLayerInvariantBundle` carriage across the fill and recorded it as
debt.  Investigating *why* found two structural causes, neither of which is
term size or proof budget (raising `maxHeartbeats` changes nothing), and both
of which already had congruence lemmas in the codebase — so the closure is
composition, not new proof.

Of the fifteen conjuncts, twelve transport **definitionally**: a structure
update to a field a predicate never projects is invisible to it.  Exactly
three atomic predicates block the other two, for two distinct reasons:

* **A `match` stuck on a symbolic `Nat`.**
  `PriorityInheritance.blockingChain` recurses on a fuel argument defaulting to
  `st.objectIndex.length`.  With a symbolic fuel the match never reduces, so
  `isDefEq` never reaches the field projections in the body and falls back to
  comparing the two *unreduced* applications — whose state arguments differ.
  The diagnosis is decidable by experiment: with a **literal** fuel the very
  same `rfl` succeeds.  The same shape reaches the bundle a second time through
  `dualQueueSystemInvariant` (fuel-recursive queue-chain acyclicity).
* **An `inductive` family parameterised by the state.**
  `serviceNontrivialPath (st : SystemState) : ServiceId → ServiceId → Prop`
  applied to two different states is two different *types*; definitional
  equality of the applications requires definitional equality of the
  parameters, which is exactly what fails.  Unfolding can never bridge this.

The landing cut's note said "three wrap the twenty-conjunct `ipcInvariantFull`"
— that was wrong.  Only `dualQueueSystemInvariant` sits inside
`ipcInvariantFull`; the other two arrive through `crossSubsystemInvariant`
(`serviceGraphInvariant` and `blockingAcyclic`).

**The fix** is one reusable carriage lemma,
`proofLayerInvariantBundle_setPerCoreTlb` (`Architecture/Invariant.lean`),
composed from lemmas that already existed —
`dualQueueSystemInvariant_of_getElem_eq` (`IPC/Invariant/LookupCongruence.lean`),
`PriorityInheritance.blockingAcyclic_frame` + `blockingServer_congr_objects`,
and the file-local `serviceNontrivialPath_of_services_eq`.  The reason the
bundle had no carriage before is that those congruences were **private and
bound to specific transitions** (the adapter preservation proofs) rather than
exposed as a reusable field-agreement layer.

The lemma is stated as **carriage, not an `iff`**: the thirteenth conjunct
genuinely reads `perCoreTlb`, so a writer must supply it.  That obligation is
load-bearing rather than decorative — substituting the *pre*-state's own
thirteenth conjunct fails to typecheck, which is the adversarial check that
the statement pins something.  `tlbFillIpcBufferOnCore_preserves_proofLayerInvariantBundle`
discharges it from the substantive per-core proof.  Zero sorry/axiom.

**Acceptance.**  A live map → access (fill) → cross-core unmap (shootdown)
→ catch-up sequence in which a real remote cached entry is created and then
provably removed, under the pending-aware invariant, with no cross-round
draining.  Zero sorry/axiom; golden trace byte-identical (`perCoreTlb` is
projection-invisible).  **Structurally met at v0.32.105** —
`SmpTlbShootdownSuite` §5.10 (the live single-round lifecycle) and §8 (the
four-round concurrent case, in which each commit's catch-up drains only its
own rounds) — but with one word of the criterion unrealised until v0.32.150:
the **access**.

Through v0.32.105 `tlbFillOnCore` had exactly one caller, inside
`vspaceMapPageCheckedWithShootdownFromStatePerCore`, so every entry in the
model was cached by the core that *mapped* it.  A core that merely accessed a
page another core had mapped cached nothing, and for that core Theorem 3.3.1
and the 13th bundle conjunct remained vacuous — satisfied by an empty view
rather than by a maintained one.  That is the common case on hardware, and
precisely the case a shootdown exists to handle.  No theorem was false and no
live defect followed (an empty view is trivially consistent), but the
acceptance criterion's "access (fill)" step was not exercised because the
model had no access-time fill to exercise.  **Genuinely met at v0.32.150** —
see SM7.F.5 below and `SmpTlbShootdownSuite` §5.11, where core1 maps, **core0
accesses**, and the cross-core unmap's catch-up removes the entry core0
acquired purely by access.

#### SM7.F.3 (v0.32.112) — generations allocated in hardware execution order

**SECURITY, the premature-acknowledgment dual.**  PR #854 review (Codex P1,
valid).  v0.32.105 closed the *stale*-acknowledgment hazard — an old SGI
satisfying a later round.  Its dual survived: a *newer* round's
acknowledgments satisfying an earlier round that no target had serviced,
leaving that initiator's operands live in every remote TLB while it returned
believing them retired.  The SMP-C4 under-invalidation again, from the
opposite direction.

The acknowledgment test is monotone (`acked_gen >= gen`, `fetch_max` slots),
so a round's generation has to order it against the rounds whose
acknowledgments could satisfy its wait — hardware execution order.  It did
not: `completeShootdownRounds` keyed on `window.2`, the model generation the
pure transition advances inside the atomic commit, while the hardware round
is bracketed by `SHOOTDOWN_ROUND_LOCK` acquired afterwards.  The two orders
are unrelated, so a core could commit generation N, stall before the lock,
and acquire it to find every target already acknowledging a later
generation — its wait passing before any target read its mailbox.

Two concurrent rounds cannot reach it: a round's initiator never
acknowledges its own slot, so the second round always leaves its own
initiator behind and the stalled core still blocks there.  It takes a third
round, one whose targets include the second's initiator, to lift every
target at or above the stalled generation — the steady state on a busy
system, the shootdown-bearing syscalls being the whole unmap family.

**Fix.** Separate the two identities.  The model generation keys the window
drain (which descriptors belong to this commit) and is unchanged.  The
runtime generation keys the acknowledgment channel and is allocated by
`shootdown::allocate_round_generation` — a `fetch_add` on
`SHOOTDOWN_ROUND_SEQ` performed **under the round lock**, so allocation
order is execution order by construction.  0-based, returning
pre-increment + 1, so no round carries the vacuously-satisfied generation 0.
Regression witness `newer_round_acks_cannot_satisfy_an_older_unexecuted_round`
runs the three-round interleaving under both schemes and asserts the old one
passes with nothing serviced.

**Generation overflow** (Codex P2, valid, closed in the same cut): the
runtime generation is now read *from* a `u64`, so the `UInt64.ofNat`
narrowing round-trips exactly and the `Nat` identity cannot alias at the FFI
boundary; the allocator additionally fails closed on wrap.

**TRACKED DEBT — model acknowledgments as a discharged-generation set**
(PR #854 review P2, v0.32.115).  The model's per-core acknowledgment is a
high-water mark, so reading it as "every round up to `roundGeneration` has
been serviced" is a prefix claim — and since v0.32.112 that does not hold of
the model, because commit generations and hardware execution order are
deliberately independent.  Round A commits generation 1 and stalls before the
round lock while round B commits 2 and runs first; B's catch-up records
`hi = 2` on every target, so `allAcked` reads true with A's descriptors still
queued.  `SmpTlbShootdownSuite` §8.5 computes that state, so the limitation is
machine-checked rather than asserted.

**No hardware hazard and no false theorem.**  The runtime consults the Rust
`acked_gen`, where the prefix reading *is* valid — runtime generations are
allocated under the round lock, so allocation order is execution order.  The
model's sound completion predicate is `shootdownQuiescent`, which conjoins the
pending queues and is correctly false in the scenario above; every round
capstone concludes it, and `shootdownRound_allAcked` derives `allAcked` from a
*quiescent* pre-state, which recovers the prefix reading.

**Closure**: represent the discharged generations per core as a set rather
than a high-water mark, making the model independently sound instead of
sound-relative-to-quiescence.  That is a third change to this field's
representation (`Vector Bool` → `Vector Nat` → set) plus another pass over the
SM7.A/B acknowledgment surface, so it is scoped out of this PR rather than
taken as a fourth in-flight rewrite.  **Closure target: the SM8 mount**,
alongside the other SM7.F.3 model-fidelity items.

**`ackBounded` carried in the global invariant — CLOSED at v0.32.114**
(Codex P2).  v0.32.113 introduced the predicate and left it an optional
hypothesis, so reasoning from `proofLayerInvariantBundle` could admit
`ackedGenOnCore c > roundGeneration` and defeat the acknowledgment-shape
lemmas even though the bundle held.  No production transition reaches such a
state, but the fact lived in the proofs rather than the invariant — the
project's "enforce it structurally" rule, applied to a predicate this
workstream had just introduced.  Now the **15th `proofLayerInvariantBundle`
conjunct**, threaded exactly as SM7.B threaded the 12th (`pendingBounded`):
boot witness, definitional adapter transport, Boot general bridge, freeze,
and a preservation chain across the drains, both enqueue forms, the round
steps, the posting folds, both broadcasts, the handler in both forms, the
per-core catch-up the live seam runs, and the six live wrappers.  The window
forms take `hi ≤ roundGeneration` as a hypothesis because unconditionally it
is false — a window claiming to discharge an unopened round is the state the
invariant excludes — and the live seam supplies it.

**Generation-aware model acknowledgment — CLOSED at v0.32.113** (Codex P2).
Registered as tracked debt when the P1 landed, then taken in the following
cut.  `completeShootdownOnCoreInWindow` acknowledged unconditionally, so a
catch-up that drained only its own window still wrote the target's flag
`true` and the model's `allAcked` could read true with a foreign round's
descriptors pending: SM7.F.3 made the queues generation-selective and left
the acknowledgment a bare flag.  Model-fidelity only — the runtime consults
the Rust `acked_gen`, never the model's vector, and the round capstones are
stated per-round so none was false.

`TlbShootdownState.shootdownAck` is now `Vector Nat` (the highest generation
each core has acknowledged, mirroring `ShootdownAckSlot.acked_gen`), with
`ackedGenOnCore` the raw slot and `ackOnCore` a *derived* `Bool`
(`roundGeneration ≤ ackedGenOnCore c`) so the SM7.A/B theorem shapes
survive.  `acknowledgeShootdown` takes the generation and joins with `max`
(the `fetch_max` mirror); the window catch-up passes `hi`, the whole-queue
form passes `roundGeneration`.  There is no ack reset on either side any
more — a round open writes the new generation to the born-acknowledged
cores, and a target is unacknowledged because its slot names an earlier
round.  That needs the new well-formedness predicate `ackBounded` (no core
has acknowledged an unopened round), which the `_ackOnCore_iff`
characterisations take as a hypothesis and every transition preserves.

Headline `completeShootdownOnCoreInWindow_not_acks_foreign`: a catch-up
whose window stops below a foreign round's generation does not acknowledge
it — the acknowledgment dual of `…_preserves_foreign`.  The four
window↔whole-queue bridges gained an `hi = roundGeneration` hypothesis:
under round serialisation the two coincide, and dropping it would re-assert
the identity the fix denies.  Suite §8.4 runs the interleaving.

#### SM7.F.3 (v0.32.105) — round-generation-tagged descriptors

**The model-fidelity gap.**  A syscall's shootdown work spans *two* atomic
commits: the pure transition posts the descriptors, and
`completeShootdownRounds` commits the catch-up afterwards.  Only the
**hardware** round runs under `SHOOTDOWN_ROUND_LOCK`, so a concurrently
committed round can post between them.  The catch-up drained each target's
*whole* queue, so it swallowed that round's freshly-queued descriptors and
declared the model quiescent before its `.tlbShootdownReq` SGIs had fired —
the model claiming a core clean of an invalidation the hardware had not yet
performed.  Recorded at v0.32.79 as fidelity-only (each round's hardware
maintenance is self-contained and over-application is idempotent), and closed
here.

**The model change.**  `TlbShootdownDescriptor` gains `generation : Nat` and
`TlbShootdownState` a monotone `roundGeneration : Nat` counter that
`beginShootdownRound{,For}` advances; `roundDescriptor` stamps every posted
descriptor with the opened round's value
(`roundDescriptor_generation_eq_opened`).  A commit's own rounds are exactly
the generations in `shootdownRoundWindow pre post = (pre.gen, post.gen]` — a
*window* rather than a single generation because the retype wrappers open one
round per flushed ASID.  `drainShootdownsInWindow` /
`completeShootdownOnCoreInWindow` /
`handleTlbShootdownReqOnCore{,PerCore}InWindow` /
`shootdownCatchUpPerCoreInWindow` are the selective forms the live seam runs;
the headline property is
`shootdownCatchUpPerCoreInWindow_preserves_foreign` (a concurrently posted
round's descriptors survive) and its dual `…_drains_own`.  Every landed SM7.A/B
round theorem carries across unchanged through the exactness bridges
(`drainShootdownsInWindow_eq_drainShootdowns`,
`handleTlbShootdownReqOnCore{,PerCore}InWindow_eq_handle`,
`shootdownCatchUpPerCoreInWindow_eq_catchUp`): under round serialisation a
core's queue holds only this commit's work, so the window drain **is** the
whole-queue drain.  `shootdownPostedOps` is likewise window-restricted, so the
runtime broadcasts and publishes exactly its own round's operands — with
`mem_shootdownPostedOps_iff` pinning both directions, including that the
deduplication never drops an operand (the unsafe direction).

**SECURITY — the Rust mirror closed a genuine hazard.**  Mirroring the
generation onto the acknowledgment channel was not cosmetic.  Under the SM7.A
Boolean `SHOOTDOWN_ACK` vector a round opened by *clearing* every online
target's flag, and the handler set its flag unconditionally after retiring
whatever the mailbox held.  A `.tlbShootdownReq` SGI left pending by an
**earlier** round — the cooperative round-lock acquire self-acknowledges
without consuming the interrupt, and IRQs are masked on the SVC path — could
be delivered inside a later round's `reset → publish` window.  Its handler
then retired the *previous* round's operands and acknowledged, satisfying the
new round's `all_acked` wait with that target's TLB still holding the
translation the round was supposed to retire: an under-invalidation, the
SMP-C4 stale-TLB hazard.  High severity once bootable (SM9.E); latent today.

The fix makes an acknowledgment *name the round it discharged*:
`ShootdownAckSlot` holds a monotone `acked_gen : AtomicU64` advanced by
`fetch_max`, the mailbox publishes the round's generation, and the handler
(`tlb_shootdown_req_service_in`) latches that generation **before** any TLB
work and acknowledges exactly it — so every branch it can take, precise
per-descriptor retire or conservative `tlbi vmalle1` fallback, provably
discharges the generation acknowledged.  The initiator waits for
`acked_gen[c] >= gen` over the IRQ-serviceable non-initiator cores.  With the
round identified by its generation there is nothing to clear before it opens,
so `reset_for_round*` is **gone** — the window the hazard lived in no longer
exists (Tier-3 anchors negatively pin its absence, since a reset would erase
the monotonicity the mechanism rests on).  The PR #838-P1 online mask moves
from the reset to the wait, which is where it belongs.  The cooperative
self-service arm becomes one Rust call (`self_service_round`) so the
generation read, the local flush and the acknowledgment cannot be split by a
newer round's publish.

**Tests.**  `SmpTlbShootdownSuite` §8 (`runRoundGenerationChecks`, 29
assertions) drives the closure on the same real page-table-backed four-round
storm §6 builds: generation allocation and stamping, the window predicate and
its diff recovery, core 0's catch-up draining only generation 1 while cores
2–3 keep the concurrent rounds' work, the explicit contrast that the
whole-queue catch-up *would* have swallowed them, every commit's own catch-up
run in turn ending quiescent with no page left cached, the
single-round bridge (window catch-up = whole-queue catch-up), diff-recovery
precision, and empty-window inertness.  Rust: the generation-tagging
group in `shootdown.rs` (the
`stale_acknowledgment_cannot_satisfy_a_later_round` regression test is
the security fix's direct witness, with
`wait_times_out_on_stale_acknowledgments_only` its wait-loop
companion), the exhaustive 2⁴ × 4-initiator wait-predicate conformance, the
handler/self-service generation tests, and the mailbox generation round-trip
plus its mismatch fallback.  HAL 798 → 800; golden trace byte-identical.

**Residual.**  SM7.F.4(b)(iv) — the `requiresFlush` ASID-allocate
(`asidAllocateWithShootdown`) — stays gated on SM8: the wrapper is complete
and proven but user-unreachable, because no ASID object family or assign
syscall exists yet (`lifecycleRetype` makes fresh ASID-0 roots and `asidTable`
is boot-only).  It is a completeness gap, not a safety hole; closure target
SM8.

##### v0.32.110 audit cut — the 12th conjunct carried across the live catch-up

A deep audit of the v0.32.105–109 cut, verified against the code rather than
the documentation describing it.  No live safety defect; every finding was a
claim that had stopped being true, a proof obligation the live seam did not
carry, or a gate reporting more coverage than it had.

**The invariant gap.**  SM7.B carried `pendingBounded` — the 12th
`proofLayerInvariantBundle` conjunct — through the *single-view* handler.
v0.32.81 swapped the live catch-up fold to the **per-core** handler and
v0.32.105 restricted it to the round window, and neither cut carried the
conjunct forward, so the transition `completeShootdownRounds` actually runs
had no bound proof.  Closed by five theorems in `PerCoreTlbModel.lean`:
`handleTlbShootdownReqOnCorePerCore{,InWindow}_preserves_pendingBounded`, the
fold, and `shootdownCatchUpPerCore{,InWindow}_preserves_pendingBounded`.  Each
is definitional on `tlbShootdown` — the per-core handlers write only
`perCoreTlb` on top of their single-view counterparts, and
`drainInitiatorPerCoreView` only the initiator's view — so the bound rides the
SM7.B lemmas rather than being re-derived.  It mattered because a window drain
*deliberately* leaves foreign descriptors queued: unlike a whole-queue drain it
does not empty the queues, so the bound does not fall out.

**The capacity-bound justification was false.**  Both `TlbShootdown.lean` sites
(module header, `maxPendingPerCore`) argued that the global round lock
serialises rounds, so "at most one round's descriptors are in flight per
target".  SM7.F.3 exists because that is wrong, and the counterexample needs no
concurrency: the retype wrappers open one round per flushed ASID, so a single
two-ASID commit queues generations 1 and 2 on every remote core before any
drain.  The constant is fine — the bound is maintained by construction
(`enqueueShootdown` fails closed, `enqueueShootdownOrCoalesce` collapses to a
covering `.vmalle1`), not by that counting argument — so the prose was
corrected, not the constant.  The round-serialisation section now also states
what the runtime refines and why the model does not need it: a
`.tlbShootdownReq` SGI can stay pending across the cooperative round-lock
acquire and be taken inside a later round, a delivery shape the model — where a
handler application is an explicit function call — cannot represent.

**Five dangling symbol references.**  SM7.F.3 removed the ack reset;
`reset_for_round_in_slice_masked`,
`sm7a3_masked_reset_all_online_equals_unmasked_reset` and three prose mentions
of `reset_for_round` survived it across `TlbShootdown.lean`,
`TlbShootdownProtocol.lean`, `TlbShootdownWait.lean`, `smp.rs` and `lib.rs`.
Each now names the live symbol, and where the reset carried an argument (the
PR #838 online mask, the PR #839 `CORE_IRQ_READY` snapshot) the replacement
records that it moved onto the wait.  The dead global `publish_round_ops`
wrapper is removed.

**Tests.**  §8 gains 15 assertions (29 → 44; suite 303 → 318).  Nine check the
conjunct where the drain is weakest — mid-storm, with three concurrent rounds'
work pending, asserted non-empty so the check cannot pass vacuously.  Six cover
a window **wider than one generation**, which no prior group did: a live
`lifecycleRetypeWithCleanupShootdownPerCore` into a different-ASID
`.vspaceRoot` opens two rounds, the recovered window is `(0, 2]`, and the
commit's own catch-up drains both — with the load-bearing negative that a
width-1 window strands the first round on every remote core.  Six `#check`
anchors, three Tier-3 anchors.

**Gate honesty.**  `test_rust.sh` printed the cargo log tail, summarising a
1093-test run as "1 passed"; it now aggregates the per-binary `test result:`
lines and flags skipped tests.  That surfaced two ```` ```ignore ```` doctests
against the standing "zero `#[ignore]`'d" claim — fences that are never
compiled and so rot silently.  Converting them found a real defect: all four
print macros are `#[macro_export]`ed but expanded to the `pub(crate)`
`with_boot_uart`, so every one failed to compile for any consumer of the crate.
The seam is now `#[doc(hidden)] pub`, and the `kprintln_core!` doctest — which
compiles as an external crate — is the regression gate.  Rust 1093 → 1095
passing, 0 ignored, HAL still 800.

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
until the AN4-G.3 / LIF-M03 scrub bridge lands (deferred item 5; owner SM9.E).
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
latent rather than exploitable today (no bootable image until SM9.E), but it was
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

#### SM7.D live wiring

The two production paths that can falsify a cached line's witness now perform
the maintenance **atomically with the transition**, and both carry
machine-checked preservation of *both* per-core memory invariants (the 13th and
the 14th):

* **`.vspaceUnmap`** → `vspaceUnmapPageWithShootdownAndIcacheBroadcast`
  (layered on SM7.F's `vspaceUnmapPageWithShootdownPerCore`).  Broadcasts a
  **targeted** `IC IVAU` at the retired page's physical address when — and only
  when — the mapping was executable (`unmapExecutablePaddr`, read from the
  *pre*-state, before the descriptor is erased).  A data-page unmap owes nothing
  and is provably inert (`…_non_executable_inert`).  The key step is
  `unmapSurvivor_not_target`: a line that survives the maintenance cannot be a
  line for the unmapped pair, in *both* the `none` branch (a line for it would
  have carried `perms.execute = true`, contradicting `VSpaceRoot.lookup`'s
  functionality) and the `ivau` branch (a survivor has a different physical
  address).
* **`.lifecycleRetype`** → `lifecycleRetype{Direct,}WithCleanupShootdownPerCoreIcache`
  (both authority forms, so they cannot drift).  Broadcasts `IC IALLUIS`
  **unconditionally**: a retype scrubs and re-purposes the target's backing
  memory, and the abstract state cannot enumerate which *mappings* alias that
  frame, so the sound choice is the full invalidate — over-invalidation costs
  re-fetches, under-invalidation is the hazard.  (**v0.32.100 amends this**:
  the invalidate alone is not enough.  The scrub's stores must first be cleaned
  to the Point of Unification, so the operand is `cleanRangeIallu` over exactly
  the scrubbed extent — see the v0.32.100 section below.  Everything the rest of
  this bullet says about the *invalidation* half still holds.)  The payoff is that the
  hardest transition in the kernel for cache reasoning becomes the easiest to
  discharge: the post-state has every core's cache **cold**, so
  `…_preserves_icacheCoherent_perCore` holds with *no* page-table side
  conditions.
* **Runtime seam** — `SyscallDispatchEntry.completeIcacheMaintenance`, keyed on
  the same `(pre, post)` shootdown diff the TLB round uses and ordered *after*
  it (translations retired everywhere before the caches are dropped), inert when
  no round was posted (`completeIcacheMaintenance_nil`).  It emits
  `IC IALLUIS` rather than the model's targeted `IC IVAU` because the runtime
  recovers its work from the state diff, which carries the round's *TLB*
  operands, not the physical address the model resolved from the pre-state page
  tables; reconstructing that address from the encoded `.vae1` operand would be
  a lossy round-trip whose failure mode is **under**-invalidation.  Emitting the
  targeted operand at runtime needs the round's operands carried in a form the
  diff preserves — the same descriptor-ledger work tracked as SM7.F.3.

Tests: new `tests/SmpCacheMaintenanceSuite.lean` (`smp_cache_maintenance_suite`,
Tier-2 registered, Tier-3 anchored) — 100+ `#check` surface anchors, 8
elaboration witnesses, and **56 runtime assertions across 9 groups**: operand
encoding + effect algebra, per-core accessors + cold boot cache, the broadcast
reach vs the PE-local hazard (all four cores), the D-cache-at-PoC reach, the DMA
tripwire, the invariant on a real page-table-backed state — including the
**non-vacuity witness** that a cached line whose mapping was removed *fails* the
checker while the domain broadcast restores it and a PE-local invalidate on
another core does *not* — and the two live seams end to end.

#### SM7.D closure cut (v0.32.95) — exact runtime operand, page-granular emission

The v0.32.94 landing recorded two mechanical residuals; both are closed here,
along with a granularity defect found while analysing them.

* **`IC IVAU` is line-granular, not page-granular — the emission was wrong.**
  `IC IVAU` invalidates one 64-byte cache line (ARM ARM C6.2.88), while the
  model's operand is a *page* (a `VSpaceRoot.lookup` yields a page base, and
  mappings are created and destroyed per page).  One instruction per page
  operand would leave 63 of a page's 64 lines valid — a silent
  **under**-invalidation, the one direction that is unsafe.  The Lean
  constructor is renamed `ivau` → `ivauPage` so a reader cannot infer
  single-line semantics from the model; `cache::ic_ivau` becomes the bare
  single-line primitive (no barriers); and `cache::ic_invalidate_page_inner_shareable`
  issues `ICACHE_LINES_PER_PAGE` (= 64) of them followed by one `DSB ISH` +
  `ISB` — seL4's `invalidateCacheRange_I` shape.  The expansion factor is pinned
  on both sides (`icacheLinesPerPage_covers_page`,
  `test_ic_invalidate_page_line_count`).  Not live-wrong at v0.32.94 (the seam
  emitted `IC IALLUIS`), but the HAL primitive was.
* **Residuals 1 and 3 — the runtime now emits the model's exact operand.**  The
  landing's seam keyed on the shootdown diff, so it fired the strongest operand
  for **every** unmap (including the common non-executable one, which owes
  nothing) and missed a retype that posted no round.  Both close with a proper
  emission ledger, mirroring how `tlbShootdown` makes the TLB round
  recoverable: `SystemState.pendingIcacheMaintenance : Option ICacheInvalidation`,
  written by `recordIcacheMaintenance` inside the shared `withIcacheBroadcast`
  combinator (so both live seams get it) and read **and cleared** by
  `syscallDispatchCrossCoreEntry` in the *same* atomic step that commits the
  transition — emitted exactly once, never stranded, and every state at a
  syscall boundary owes nothing.  Accumulation is the total join
  (`ICacheInvalidation.join`, `iallu` as top), so there is no capacity bound to
  thread and no new bundle conjunct; `recordIcacheMaintenance_of_none` is the
  exactness property.  Outcome: an executable unmap emits a targeted 64-line
  page loop, a **data-page unmap emits nothing at all**, and a retype emits
  `IC IALLUIS` whether or not it posted a round.  The alternative — recovering
  the operand from the round's encoded `.vae1` — was rejected: the
  `ASID`/`VAddr` round-trip is faithful only under a reachability argument
  about every caller, and its failure mode is under-invalidation.
* **The data-side dual, registered as a checked obligation.**  Nothing cleans
  the D-cache to the Point of Unification after the kernel writes memory a
  subject may later execute (`scrubObjectMemory` during a re-type, the boot
  image load); an instruction fetch reads at PoU, so a store not yet pushed
  there can be fetched stale even on the storing PE.  The *emission* needs each
  object's physical extent, which the model does not carry (only
  `UntypedObject` has `regionBase`/`regionSize`), so it is scoped to SM9.E —
  also the first point at which memory is physically backed and the omission
  could bite.  What lands now is the obligation as an object:
  `KernelCodeWriteSite` enumerates the two sites,
  `kernelCodeWriteSites_owe_pou_clean` states that each owes
  `armv8DCacheToICacheSequence`, and `kernelCodeWriteSites_complete` is the
  tripwire that fails if a third site appears without an entry.
  `Architecture.TlbCacheComposition` is promoted staged → production as SM7.D.2's
  consumer (staged-only 55 → 54).

Structure: `ICacheInvalidation` moves to the new pure
`Architecture/CacheInvalidation.lean` — the same extraction, for the same
reason, as SM7.A's `TlbInvalidation.lean` (`Model/State.lean` mounts the ledger
and must not pull the architecture layer's import closure).  The ledger is
carried through freeze (required), congruence and boot, and stays out of the IF
projection (`pendingIcacheMaintenance_write_preserves_projection` — the operand
names a physical page).  Rust HAL 789 → 792; suite 56 → 72 runtime assertions /
11 groups.  Trace byte-identical; zero sorry/axiom; Tier 0–3 green.

**Remaining residual.**  Content coherency in the *other* direction — a thread
writing new instructions through the data side (self-modifying code, JIT) — is
user software's obligation on ARMv8-A (`DC CVAU` → `DSB` → `IC IVAU` → `DSB` →
`ISB`).  seL4 exposes it as an explicit `Page_Unify_Instruction` operation
rather than performing it implicitly; seLe4n has no equivalent syscall yet, so
the obligation is currently unfulfillable by user code.  Closed by the
`vspaceUnifyInstruction` syscall (see below).

#### SM7.D residual closure (v0.32.96) — `.vspaceUnifyInstruction`, the code-publication syscall

The v0.32.95 cut left exactly one residual: instruction-cache maintenance was
wired to the paths that **destroy** an executable mapping, but nothing served
the dual — a subject that *writes* instructions.  On ARMv8-A those stores land
in the D-cache while the instruction fetch reads at the Point of Unification,
so without a kernel operation a JIT, loader, or dynamic linker had **no way**
to make its own writes fetchable.  The obligation was stated (v0.32.95's
`kernelCodeWriteSites_owe_pou_clean` names the canonical sequence for the
kernel's own writes) but unfulfillable by user code.  This cut closes it.

* **The transition.**  `Architecture.vspaceUnifyInstructionPage asid vaddr` —
  a **pure cache** operation that touches no page table
  (`vspaceUnifyInstructionPage_frame`: object store, page tables, TLB, and
  shootdown state all provably unchanged).  Fail-closed on both authority
  legs: `.asidNotBound` when the ASID is unbound and `.translationFault` when
  the address is unmapped in that address space, so a caller can only maintain
  memory it already holds a translation for.  Deliberately **not** gated on
  the mapping being executable — the writer holds the *data* mapping, so an
  execute gate would make the operation useless for its only purpose.

* **A distinct operand, not a reused one.**  The third `ICacheInvalidation`
  constructor `.unifyPage paddr` exists because the sequence is asymmetric:
  the data side must be cleaned to PoU **before** the instruction side is
  invalidated, and folding it into `.ivauPage` would silently drop the clean.
  `join` gives `.unifyPage` dominance over `.ivauPage` on the same page —
  upgrading is sound, downgrading is not — so an accumulated round can never
  weaken a unify into a bare invalidate.

* **Reach and preservation.**
  `vspaceUnifyInstructionPage_invalidates_all_cores` (after the transition no
  core retains a line for the page — the instruction-side reach property on
  the mounted field), `_records_unify`, and preservation of both per-core
  memory conjuncts (`_preserves_icacheCoherent_perCore`,
  `_preserves_tlbInvalidationConsistent_perCore`).

* **Live.**  `API.dispatchWithCap` gains the `.vspaceUnifyInstruction` arm
  (`dispatchWithCap_vspaceUnifyInstruction_delegates`), so the operand rides
  the v0.32.95 emission ledger into `syscallDispatchCrossCoreEntry`'s drain
  and out through `cache_ic_maintenance` like any other.  The HAL realises it
  as `cache::unify_instruction_page_inner_shareable`: a 64-line `DC CVAU` loop
  → `DSB ISH` → a 64-line `IC IVAU` loop → `DSB ISH` → `ISB`.

* **Ledger soundness correction (found while reviewing this cut).**  Adding
  `.unifyPage` exposed a defect in v0.32.95's single-operand *join*: `iallu`
  was the lattice top, but `IC IALLUIS` invalidates instruction caches and
  issues **no** `DC CVAU`, so `join (.unifyPage p) .iallu = .iallu` would have
  dropped that operand's clean to the Point of Unification — under-maintenance,
  the unsafe direction.  Nor does any single operand cover two distinct
  `unifyPage`s, so no join over one operand is sound once the constructor
  exists.  Not reachable at v0.32.95 (one maintenance-bearing transition per
  syscall, drained atomically with the commit, so every record started from an
  empty ledger and the binary arms were dead code) but a latent trap.  The join
  is replaced by a **coverage preorder over a list**:
  `pendingIcacheMaintenance : List ICacheInvalidation`, appended in record
  order and drained wholesale (`completeIcacheMaintenance_cons` pins that every
  entry is emitted), reducing only where one entry provably **covers** another.
  `covers` is grounded in the model's own effect
  (`icacheLineMatches_of_covers`, `applyICacheInvalidation_subset_of_covers`)
  rather than asserted, and `ICacheInvalidation.iallu_not_covers_unifyPage`
  states the exclusion as a theorem so a future "simplification" that restores
  `iallu` as a top fails there instead of silently under-maintaining.
  `recordIcacheMaintenanceList_covered` / `_mem_of_mem` are the no-loss
  properties and `_length_le` bounds each record at one entry, so the live
  ledger stays a singleton — still no capacity invariant, still no bundle
  conjunct.

* **ABI + registries.**  `SyscallId.vspaceUnifyInstruction = 29`, count
  29 → 30, threaded through the Lean encodings/`ofNat?`/`all`/`ToString`, the
  `sele4n-types` + `sele4n-hal` Rust mirrors (min inline args 2), ABI
  conformance (boundary 29 valid / 30 invalid + round-trip), the frozen-ops
  classifier, the argument decoder, the information-flow enforcement registry
  (`enforcementBoundaryExtended` 37 → 38, capability-only 22 → 23), and the
  lock-set inventory — `lockSet_vspaceUnifyInstruction` takes the VSpaceRoot
  in **read** mode (it modifies no page table) with
  `lockSet_consistent_vspaceUnifyInstruction`; inventory 99 → 101,
  lockSet/consistency categories 29 → 30.  Authority: `.write`, so a
  read-only VSpace capability is refused with `.illegalAuthority`.

Rust HAL 792 → 795 tests, clippy-clean.  `SmpCacheMaintenanceSuite` 72 → 93
runtime assertions / 12 groups (§3.12 covers the encoding, the operand tag and
coverage dominance, both fail-closed arms, the four-core success path on a real
page-table-backed state, and live `dispatchSyscall` authority; §3.10 gains the
coverage preorder, its semantic grounding, and the two ledger cases that would
previously have lost work).  The golden
trace's `[XVAL-002]` line moves 29 → 30 variants (it enumerates the syscall
surface); everything else byte-identical.  Zero sorry/axiom; Tier 0–3 green.

**SM7.D is CLOSED at the model level** — every operand it emits is correct
relative to the model.  The one thing still outstanding is the lifecycle
layer's shared abstraction gap (deferred item 5 / AN4-G.3): the addresses are
the model's allocation convention, not the allocator's.

### SM7.D (v0.32.102) — page alignment at the mapping boundary (PR #845 review, Codex P2)

v0.32.98/99 guarded the four *checked* map wrappers against an unaligned
physical address, but `VSpaceRoot.mapPage` and `Builder.mapPage` insert into
the mapping table directly and bypassed all four, and no VSpace invariant
carried an alignment clause.  Since the SM7.D operands name a *page* and both
HAL loops round down to the containing page, such a mapping would make the
model record maintenance against an address the machine never acts on.

Fidelity rather than under-maintenance (hardware invalidates a superset), but
an implicit invariant held only by convention — so it is enforced structurally:
one granule (`SeLe4n.pageBytes`, below both layers, with
`Kernel.Architecture.pageBytes` reading it), a constructor-level rejection in
`VSpaceRoot.mapPage` mirroring the existing W^X layer (+
`mapPage_pageAligned`), an `_hAligned` proof obligation on `Builder.mapPage`
mirroring `_hWxSafe`, and an `.alignmentError` arm in `vspaceMapPage` so the
error code stays honest.  20 downstream proof sites gained the branch.

### SM7.D (v0.32.101) — the clean and the scrub read one extent (PR #845 review, Codex P1)

A follow-up review on `cb1481f` observed that v0.32.100's `.cleanRangeIallu`
targets `ObjId × objectTypeAllocSize`, an abstract model convention, while the
real child extent is `regionBase + offset` — so on hardware the `DC CVAU`
sweeps memory the allocation does not occupy.

**Valid, and narrower and wider than it reads.**  *Narrower*: the operand
deliberately mirrors the scrub, and the scrub's own hardware gap is
pre-existing and registered (AN4-G.3).  Retargeting the operand alone would be
strictly worse — the clean would name an extent `scrubObjectMemory` does not
zero.  *Wider*: a scrub that misses real memory leaks the previous owner's
**data**, not just stale instruction lines; that is the more serious half, it
lives in the scrub bridge, and AN4-G.3 is re-labelled accordingly.

**The genuine weakness in v0.32.100.**  `retypeIcacheOp_cleans_scrub_extent`
was described as an equality between two computations.  It was not: the
right-hand side restated `retypeIcacheOp`'s own definition and never mentioned
`scrubObjectMemory`, so it held for any extent and pinned nothing.  The section
comment claimed both sides "read the same convention"; they read two identical
*copies* of it.

**The fix.**  One `scrubExtent`, two consumers — `scrubObjectMemory` zeroes it,
`retypeIcacheOp` cleans it, neither recomputes the arithmetic.  The theorem is
restated against `scrubExtent`, so it now relates two different functions and
fails if either moves; `scrubObjectMemory_cleaned_by_retype` closes the loop
from the scrub's side.  The new body is definitionally the old one, so the
other 80 references are untouched.  Tier-3 anchors pin the single source
negatively: neither body may mention `objectTypeAllocSize`.

### SECURITY (v0.32.97) — VSpace capability binding (PR #845 review, P1)

A confused deputy in the syscall gate, found while addressing a review comment
on `.vspaceUnifyInstruction` and confirmed **pre-existing and wider**:
`.vspaceMap` and `.vspaceUnmap` had carried it since long before that syscall.

`syscallLookupCap` verifies only that the caller holds *a* capability carrying
the syscall's required right; it never tied that capability's **target** to the
operand.  The three VSpace arms matched `| .object _ =>`, discarding the object
id, then acted on an **ASID the caller supplied in a message register**,
resolved through the global `asidTable` — so authority flowed from a name the
caller chose rather than from the capability it held.

Confirmed exploitable against the live dispatch path: an attacker thread holding
only a writable capability to *its own TCB*, with no VSpace capability at all,
unmapped an executable page belonging to a different address space.  Full
VSpace-isolation breach and a denial-of-service primitive against any address
space.  Severity **High**.

Closed by `SeLe4n.Kernel.vspaceCapAuthorizesAsid`: the capability must name the
VSpace root `resolveAsidRoot` yields for the operand ASID, checked in each arm
before the transition runs.  Two properties are load-bearing — it is stated
against the **resolved root** rather than the capability object's own `asid`
field (the two diverge under the SM7.F.4 ASID-rebind hazard, and only the former
is sound), and it **fails closed** on an unbound ASID, which also removes an
ASID-existence oracle.  The three `dispatchWithCap_vspace*_delegates` theorems
gain an authorization premise — without it they are now false — plus fail-closed
duals `…_unauthorized` that state the rejection itself, since a regression
dropping the gate would still satisfy the delegations.

Coverage: `tests/VSpaceCapabilityBindingSuite.lean` (26 assertions / 5 groups,
Tier-2 + Tier-3 wired), every scenario through the live `dispatchSyscall` path.
`OperationChainSuite` chain28 — the project's only `syscallEntry`-level VSpace
coverage — was additionally found **silently vacuous** (it added a second
VSpaceRoot at an ASID the builder already used, so the uniqueness check panicked
to `default : SystemState` and dispatch failed with `illegalState` before
reaching the VSpace arms, an error both branches printed as "dispatch reached");
it is repaired, now throws on error, and gains the cross-address-space refusal.

No passing test changed behaviour; the golden trace is byte-identical.


### SECURITY (v0.32.100) — the re-type's clean to the Point of Unification (PR #845 review, P1)

The SM7.D wiring gave the re-type an unconditional `IC IALLUIS` and nothing else.
That closes only half of the hazard it was written to close.

`scrubObjectMemory` zeroes the target's backing memory before the new object is
installed.  Those stores land in the **data** cache.  Instruction fetches read at
the **Point of Unification**, so until a `DC CVAU` pushes the stores out, the PoU
still holds the previous owner's content — and `IC IALLUIS`, which issues no
clean, does not merely fail to help: by dropping every cached instruction line it
*guarantees* the next fetch goes back to the stale PoU copy.  Instruction caches
are physically tagged (ARM ARM D7.2), so that fetch is reachable through any
later executable mapping of the frame, in any address space.  seL4's
`clearMemory` is `memzero` followed by `cleanCacheRange_PoU` for exactly this
reason.

Severity **High** once the kernel boots on hardware; not exploitable at v0.32.99
(no bootable image — SM9.E).  No Lean theorem was false: `ICacheState` models no
data-cache content, so the model could not see the omission.  What was wrong was
the emitted hardware sequence.

**The deferral premise was false.**  v0.32.94 and v0.32.99 both justified
deferring the data-side emission on the grounds that "the model does not carry
each written object's physical extent."  For this site that is simply untrue and
always was: `scrubObjectMemory` derives `(base, size)` from
`(ObjId, KernelObjectType)` by the model's own allocation convention.  The claim
was inherited from the `.bootImageLoad` site, where it does hold, and never
re-checked for `.retypeScrub`.

**The fix.**  A fourth operand, `ICacheInvalidation.cleanRangeIallu base size` —
clean `[base, base+size)` to the PoU, `DSB ISH`, then `IC IALLUIS`, `DSB ISH`,
`ISB`.  Both production re-type seams emit it, keyed on the pre-state object's
type so the cleaned extent is *exactly* the scrubbed one
(`retypeIcacheOp_cleans_scrub_extent`, an equality between the two computations;
`retypeIcacheOp_discharges_scrub_obligation` for the obligation link).  An empty
target slot has nothing to scrub and keeps the bare `.iallu`.

The clean and the invalidate are **one** operand, not two ledger entries, so the
ordering cannot be lost to accumulation order: bundling makes it the HAL
routine's internal `DSB ISH`.  Same reasoning that keeps `unifyPage` distinct
from `ivauPage`.

`covers` gains the range arms over interval containment (`byteRangeContains`,
whose `_trans` carries `covers_trans`).  The two exclusions are stated as
theorems so a future "simplification" fails there rather than silently dropping
a clean: `iallu_not_covers_cleanRangeIallu` (no `DC CVAU`) and
`unifyPage_not_covers_cleanRangeIallu` (one page, not the domain).
`isDomainWide` factors out "ends in `IC IALLUIS`" so the seams' 14th-conjunct
proofs carry for both operands without case-splitting.

`kernelCodeWriteSites_emission_pending` previously asserted that *every*
code-write site's obligation was a placeholder.  That is no longer true, so it
became the **partition**: `kernelCodeWriteEmitted` marks `.retypeScrub` emitted
and `.bootImageLoad` still pending, and the theorem pins that exactly one site
remains.  Wiring the boot emission breaks the `decide`.

`Model/State.lean` gains `getObjectType?`, the kind-agnostic member of the
AL2-A / AN10-B typed-accessor family, so the operand reads the store through an
accessor rather than open-coding a raw match (AK7 `RAW_MATCH_TOTAL` unchanged
at 136).

FFI: `ffiIcMaintenance` / `cache_ic_maintenance` take a third word (`size`, RES0
for tags 0–2), tag 3 routing to
`cache::clean_range_pou_then_invalidate_all_inner_shareable`.  The stale ffi.rs
header comment (two tags, `[0, 2)`) is corrected to four.

Coverage: `SmpCacheMaintenanceSuite` §3.13 (18 assertions, plus three in §3.11 for the
emission partition; 93 → 114 / 13 groups),
including the load-bearing negative that the pre-fix `.iallu` provably does *not*
discharge the obligation.  Rust HAL 795 → 798: `test_clean_range_pou_line_coverage`
computes the `DC CVAU` loop the HAL runs and checks it covers every line of
`[base, base+size)` for each allocation size and for a line-straddling base.
Trace byte-identical; zero sorry/axiom; Tier 0–3 green.

### SM7.D deferred items — registered against SM9.E

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
| 1 | **`op.toPaddr` is used directly as the VA operand for `DC CVAU` / `IC IVAU`.**  `mmu.rs` populates only L1 entries 0..3 — `0x0000_0000–0xBFFF_FFFF` Normal WB cacheable, `0xC000_0000–0xFFFF_FFFF` Device-nGnRnE, nothing above 4 GiB — while `rpi5MachineConfig.physicalAddressWidth = 44`.  The model therefore admits frames the boot tables do not cacheably map, and maintenance against such a VA faults at EL1 or operates through a Device alias. | Pre-existing since v0.32.94 (`.ivauPage` carries the same convention; `.unifyPage` inherits it).  Not reachable today — no bootable image until SM9.E and no allocator path hands out frames above 3 GiB — but live the moment the image boots on a 4 GB or 8 GB Pi 5.  The fix is a PA→kernel-VA translation with a fail-closed reject for frames outside the cacheable window, which belongs with the runtime mapping work.  **Must cover the whole operand family, not just `.unifyPage`.** | SM9.E |
| 2 | **The post-state is published before the maintenance is emitted.**  `modifyGetKernelState` installs the committed state and clears the ledger atomically; `completeIcacheMaintenance` runs outside that step, so another core can observe a retyped frame, map it and execute from it while stale instruction lines are still resident. | Structural to the whole SM7 runtime bracket, not to the cache seam: `completeShootdownRounds` sits in the same position and has since v0.32.76.  The TLB side is saved by the blocking `SHOOTDOWN_ACK` handshake; `IC IALLUIS` is fire-and-forget, so there is nothing to wait on.  "Emit before publishing" is unavailable to a pure-transition kernel (the operand is only known *after* the transition computes it — the reason the ledger exists), leaving "hold serialization across the barrier sequence", which changes the syscall bracket's locking discipline and interacts with the SM3 hierarchy and the SM7.B round lock.  Wants designing once for both the TLB and cache sides.  Mitigation today: the model applies the invalidation to `perCoreICache` atomically *inside* the transition, so the committed state is coherent — the gap is exactly the model-vs-hardware refinement gap SM9.E closes. | SM9.E |
| 4 | **The `.bootImageLoad` clean-to-PoU is declared but not emitted.**  The boot pipeline materialises the initial task's objects — including its code — before the first instruction fetch, and owes the same `DC CVAU` → `DSB ISH` → invalidate sequence the re-type now emits.  `kernelCodeWriteEmitted .bootImageLoad = false` records this, and `kernelCodeWriteSites_emission_pending` pins that it is the **only** remaining site. | Unlike `.retypeScrub`, this site genuinely cannot name its extent today: boot materialises objects through the builder, with no transition to hang an operand on and no physical backing until the image runs.  Closure means emitting the range clean as part of boot's object materialisation, which is the SM9.E bring-up work.  Flipping the `kernelCodeWriteEmitted` arm breaks the `decide`, so the closure cannot land silently. | SM9.E |
| 5 | **The cleaned extent is the model's abstract convention, not the allocator's.**  `scrubExtent` — which `scrubObjectMemory` zeroes and `retypeIcacheOp` cleans — is `(ObjId × objectTypeAllocSize, objectTypeAllocSize)`.  The real child extent is the untyped allocator's `regionBase + offset` (recorded in state as `UntypedChild.offset` / `.size`), so on hardware neither the zeroing stores nor the `DC CVAU` lands on the object's actual backing memory. | **This is AN4-G.3 / LIF-M03, not a new finding** — the pre-existing scrub bridge, re-labelled at v0.32.101 as a High-severity-once-bootable *data*-disclosure gap (a scrub that misses real memory hands the previous owner's bytes to the new one, not merely stale instruction lines).  Deferred because the fix belongs to the **scrub**, not the cache seam: it needs a reverse child→untyped resolver that does not exist, a fallback for objects with no parent record (boot-built objects, in-place re-types), and a change to `scrubObjectMemory` itself, whose projection lemmas quantify over the abstract range.  Correcting the cache operand alone would be strictly worse — it would clean an extent the scrub does not zero.  v0.32.101 made this a **one-line** change when AN9 lands: both consumers read `scrubExtent`, so the bridge rewrites that single function and the operand follows (`retypeIcacheOp_cleans_scrub_extent` fails if they ever drift). | SM9.E (AN4-G.3) |
| 3 | **The legacy `syscallDispatchInner` entry does not drain the ledger.** | Vestigial: the Rust `svc_dispatch` extern was flipped to `lean_syscall_dispatch_cross_core` at v0.31.67 (SM6.A), so nothing calls `syscall_dispatch_inner` on the production path.  Since v0.32.96 replaced the operand *join* with an append-only list, an operand committed through the legacy entry is **deferred** (drained by the next cross-core-entry syscall), never silently dropped — `recordIcacheMaintenanceList_mem_of_mem` is the no-loss property.  **Draining there was attempted and reverted**: `icMaintenanceBroadcast` carries an `@[extern]` symbol supplied by the Rust HAL, which simulation builds do not link, and `tests/SyscallDispatchSuite.lean` calls this entry directly — so the emission breaks every host test binary that exercises the bridge.  The module's link-gating policy requires that to fail loudly rather than be stubbed, so the only sound closures are (a) linking the HAL into test binaries, which defeats the gating, or (b) **removing the export** and repointing `SyscallDispatchSuite` at the cross-core entry.  (b) is the intended closure. | SM9.E |

### SM7.E — Tests (3 PRs, 6 sub-tasks) — LANDED (v0.32.103)

| Sub | Description | Status |
|-----|-------------|--------|
| SM7.E.1 | `tests/SmpTlbShootdownSuite.lean` (15+ scenarios) — seeded at SM7.A, 22 groups at the SM7.B completion cut, 32 at the SM7.F cuts | **LANDED** — 35 runtime groups / 272 assertions (§3.1–§3.12, §4.1–§4.11, §5.1–§5.10, §6, §7, §8) |
| SM7.E.2 | QEMU shootdown integration — `scripts/test_qemu_smp_shootdown.sh` | **LANDED** (seeded at the SM7.B completion cut; Tier-4 registered, SKIPs until the SM9.E bootable image) |
| SM7.E.3 | Shootdown stress test (4 cores × concurrent unmaps) | **LANDED** — suite §6 (model tier) + `scripts/test_qemu_smp_shootdown_stress.sh` (Tier-4 hardware tier) |
| SM7.E.4 | Cross-cluster mock test | **LANDED** — suite §7 (TLB side) + `SmpCacheMaintenanceSuite` §3.15 (I-cache reach side) |
| SM7.E.5 | Surface anchors | **LANDED** — §1 `#check` blocks + Tier-3 `rg` anchors for every new symbol, runner, fixture and script |
| SM7.E.6 | Fixture: `smp_tlb_shootdown.expected` | **LANDED** — 21-line `[smp-tlb-shootdown]` golden trace + `.sha256`, auto-gated by the Tier-2 trace walk |

#### SM7.E landing cut (v0.32.103)

**SM7.E.3 — the concurrent-unmap storm** (`SmpTlbShootdownSuite` §6, 28
runtime assertions).  The model is deterministic and sequential, so genuine concurrency
surfaces in exactly two places, and the group drives both on a **real
page-table-backed state with real cached translations** (four pages mapped,
sixteen SM7.F walk fills, then four live `vspaceUnmapPageWithShootdownPerCore`
rounds with no catch-up in between):

* **Rounds in flight at once.**  Each core's queue holds exactly the three
  descriptors the *other* three initiators posted (never its own — the
  initiator is never a target), the capacity conjunct never breaks, every
  initiator retired its own operand atomically with its own unmap, and the
  three pages it did *not* initiate are stale on it — but covered, so the
  pending-aware invariant is **GREEN mid-storm**.  The deferred catch-ups then
  drain in the order the runtime runs them: round 0's leaves every *remote*
  core clean while the initiator's own queue waits for round 1's catch-up
  (which the group checks, rather than assuming a single catch-up suffices),
  after which the state is quiescent, every view clean, and the remaining
  rounds' catch-ups provably inert.
* **Visit-order independence.**  On hardware the four targets take their
  `.tlbShootdownReq` SGIs and retire in whatever order the GIC delivers them,
  while the model commits **one** fold order.  Three different visit orders are
  computed and pinned to the identical per-core views, shootdown state and
  single-view TLB.
* **Backpressure**: sixteen un-drained rounds fill each remote queue exactly to
  `maxPendingPerCore`, the strict posting then fails closed (never silently
  drops), the seventeenth coalescing round collapses each full queue to one
  `.vmalle1`, the bound holds throughout, and draining the collapsed queue
  empties every remote view.
* **Mixed operands**: a page unmap and an ASID retirement in flight together —
  each core's drain retires exactly *its* queue, so the ASID round's initiator
  keeps the three translations it never queued.  A blanket-flush regression in
  the handler fails right there.

**The theorem the order-independence claim rests on** — `handleTlbShootdown
ReqOnCorePerCore_comm` (+ `setTlbOnCore_comm`,
`handleTlbShootdownReqOnCore_setTlbOnCore_comm`, and the adjacent-transposition
`foldl_handleTlbShootdownReqOnCorePerCore_swap`), new in `PerCoreTlbModel.lean`.
SM7.B proved commutativity for the **single-view** handler and documented it as
"the fold order in `completeShootdownRounds` is a convention, not a correctness
requirement"; v0.32.81 then swapped that live fold to the **per-core** handler
without carrying the theorem forward, so the documented claim no longer covered
the handler the live seam runs.  Closed here rather than weakened: distinct
cores' per-core handler steps commute (each drains only its own queue,
acknowledges only its own flag, writes only its own view, and the shared `tlb`
retire-filters intersect commutatively), so one deterministic model fold order
is a faithful representative of every hardware interleaving.  Axiom-clean
(`propext`, `Quot.sound`).

**SM7.E.4 — the cross-cluster mock** (suite §7, 17 runtime assertions;
cache-suite §3.15, 9).  §3.4's portability argument, made executable over a mock
two-cluster topology on the same four PEs (A = {0,1}, B = {2,3}):

* The sharing domain changes the emitted instruction variant and the completing
  barrier (`.inner` ↦ tag 0 / `DSB ISH`, `.outer` ↦ tag 1 / `DSB OSH`) and
  **nothing else** — the `.outer` round posts the identical shootdown state,
  emits the identical SGI list and evolves the identical per-core views
  (`tlbShootdown_outer_correct`, computed).
* **The hazard**: a bare Inner Shareable broadcast modelled as the per-core
  invalidation applied to the initiator's cluster alone leaves the *remote*
  cluster holding the stale translation — the SMP-C4 window that would reopen
  if a multi-cluster port dropped the explicit-ack round.  The round does not:
  it retires the entry on every PE of both clusters, from either cluster.
* **The hybrid a real port would run** — IS locally, SGIs remotely — already
  works without a protocol change: the masked round-open takes the narrowed
  target set, fires SGIs only at the remote cluster, and leaves the
  initiator's cluster-mate born-acknowledged for the local broadcast to clean.
* Instruction-cache side: `icBroadcastReach` narrowed to one mock cluster leaves
  the other cluster's lines resident for **every** operand kind (`iallu`,
  `ivauPage`, `unifyPage`) — the executable statement of the module docs'
  "a multi-cluster port must narrow this list and add an SGI-based protocol" —
  while the composed per-cluster broadcasts equal the single full-reach one.
* Both groups pin that the mock **is** a mock: today's binding is
  `shootdownSharingDomain = .inner`, `icBroadcastReach` is the whole topology,
  and the real target set spans both mock clusters.

**SM7.E.6 — the golden trace** (`tests/fixtures/smp_tlb_shootdown.expected`,
21 lines + `.sha256`).  Every line is computed from the live
`vspaceMapPageCheckedWithShootdownFromStatePerCore` /
`vspaceUnmapPageWithShootdownPerCore` / `shootdownCatchUpPerCore` /
`handleTlbShootdownReqOnCorePerCore` decisions on a real page-table-backed
state, reporting per-core observables (cached entries, pending descriptors, ack
flags) at each stage plus the pending-aware invariant verdict, the raw FFI
operand encoding, the storm's per-core profile and the cross-cluster identity.
Auto-gated by the Tier-2 trace walk (which discovers every
`*.expected.sha256` in `tests/fixtures/`), so a fixture edit without a hash
refresh fails CI.

**SM7.E.3 hardware tier** — `scripts/test_qemu_smp_shootdown_stress.sh`
(Tier-4-registered, SKIPs until SM9.E) drives the one thing the pure model
cannot: the real interleaving of the global round lock, the SGI delivery order
and the `SHOOTDOWN_ACK` handshake under contention.  It hunts the two §7 risks
by name — a round-serialisation break (an initiator observing someone else's
`allAcked` and returning with a stale TLB live) and a round-lock deadlock (the
SM7.B.6 fail-closed timeout, or a hang) — with a distinct diagnostic for each.

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
      and SKIP until the SM9.E bootable image exists).
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
> here runs on hardware before SM9.E.

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
bootable image exists before SM9.E, so no configuration runs two cores
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
SM9.E" was carrying the unreachability claim.

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
