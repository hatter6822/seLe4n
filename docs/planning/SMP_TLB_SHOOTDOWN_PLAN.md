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
   `ic_ialluis`; D-cache by VA already at PoC.
5. **Tests** (SM7.E).

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
  pinned identical on both sides (`sm7b_op_tag_decode_conformance`
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
  `irq_ready_online` + 2 new unit tests (`sm7b2_online_mask_of_*`,
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
  fidelity").  **Closure target**: round-generation-tagged pending
  descriptors so catch-up drains only its own round — a verified-model-
  type change (`TlbShootdownState` + the SM7.A/B proof surface
  `pendingBounded`/`shootdownRound_quiescent`/Theorem 3.3.1/all
  `_preserves_*` + the Rust mailbox mirror).  Scoped as a follow-on cut
  (candidate: SM7.C, alongside the per-core TLB mount that will already
  reshape the shootdown-state surface); not undertaken in this
  review-response cut to keep it a coherent bug fix.

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
debt) remains a separately-scoped follow-on**, not folded into this cut:
it is a `TlbShootdownState` *descriptor-type* change (rippling the entire
SM7.A/B `pendingBounded` / `shootdownRound_quiescent` / Theorem 3.3.1 /
`_preserves_*` surface + the Rust mailbox), orthogonal to the per-core
TLB *view* model SM7.C delivers, and — as the SM7.B audit recorded — a
model-fidelity item with **no hardware hazard** (each round's hardware
maintenance is self-contained; catch-up over-application is idempotent).
Bundling it here would violate the one-coherent-slice rule.

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

### SM7.F — Operative per-core TLB fills (IN FLIGHT; 4 sub-tasks / ~3 PRs; F.1+F.2 LANDED)

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
| SM7.F.3 | Round-generation-tagged descriptors (the SM7.B v0.32.79 model-fidelity debt): `TlbShootdownDescriptor` carries a round generation; the catch-up drains only its own generation, closing the concurrent-round cross-draining race (Comment 3).  A `TlbShootdownState` type change rippling SM7.A/B + the Rust mailbox mirror. | PENDING |
| SM7.F.4 | Live fill wiring: invoke `tlbFillOnCore` at a genuine live translation point (e.g. the IPC-buffer / mapped-access seam) so `perCoreTlb` holds real entries on the syscall path.  Trace-safe (`perCoreTlb` ∉ `projectState`).  Requires F.2 (else the invariant is false in the pending window) and rides F.3 for race-free catch-up. | PENDING |

**Acceptance.**  A live map → access (fill) → cross-core unmap (shootdown)
→ catch-up sequence in which a real remote cached entry is created and then
provably removed, under the pending-aware invariant, with no cross-round
draining.  Zero sorry/axiom; golden trace byte-identical (`perCoreTlb` is
projection-invisible).

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
| SM7.E.1 | `tests/SmpTlbShootdownSuite.lean` (15+ scenarios) — seeded at SM7.A, 22 groups at the SM7.B completion cut | XL |
| SM7.E.2 | QEMU shootdown integration | `scripts/test_qemu_smp_shootdown.sh` — **seeded** at the SM7.B completion cut (Tier-4 registered; SKIPs until the SM9.E bootable image) | M |
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
| Multiple concurrent shootdowns interleave | LOW | HIGH | **DISCHARGED at SM7.B.7**: the single global shootdown-round lock (`ShootdownRoundLockId`, realised as the CAS try-lock `SHOOTDOWN_ROUND_LOCK`, acquired cooperatively — a lock-waiter services its own pending shootdown obligation between retries, since a blind spin with IRQs masked could never satisfy the in-flight round waiting on it) brackets the entire hardware round in `completeShootdownRounds`; the cross-domain order is `lockSet_tlbShootdown_correct`.  (Background: the SM7.A audit showed the VSpaceRoot lock alone is insufficient — two different-VSpace initiators would interleave rounds on the round-identity-free ack vector.) |
| Pending queue overflow | LOW | MED | Bounded by maxPendingPerCore=16 |
| Cross-cluster path under-tested | MED | LOW (no current target) | Mock test in SM7.E.4 |

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
- [ ] Cache-coherency invariant (SM7.D).
- [ ] Tier 0..4 green; QEMU shootdown test passes (Tier 0..3 green at
      SM7.B; the QEMU exerciser lands with SM7.E.2 and runs once the
      SM9.E bootable image exists).
- [ ] **Closes SMP-C4 formally** (at SM7 completion: SM7.C's per-core
      model + SM7.D's cache invariant remain).

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
