-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM6.A: PRODUCTION (LANDED).  The cross-core-aware syscall dispatch entry
-- `syscallDispatchCrossCoreEntry` (`@[export lean_syscall_dispatch_cross_core]`)
-- is the live seam the Rust SVC handler resolves against; it runs the verified
-- `syscallDispatchFromAbi` (per-core caller via the threaded `executingCore`) and
-- fires the diff-recovered cross-core `.reschedule` SGIs.  (Former "STATUS:
-- staged" marker replaced with this landing note per the implement-the-improvement
-- rule; see docs/planning/SMP_CROSS_CORE_IPC_PLAN.md.)

import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore
import SeLe4n.Kernel.Concurrency.Runtime
import SeLe4n.Kernel.Concurrency.Locks.LockSetForSyscall
-- WS-SM SM6.E: the per-core suspend behind `suspendThreadCrossCoreEntry`.
import SeLe4n.Kernel.IPC.CrossCore.Cancellation
-- WS-SM SM7.B: the shootdown round's pure transitions + diff recovery
-- (`shootdownChangedTargets` / `shootdownPostedOps` /
-- `handleTlbShootdownReqOnCore`), the wait budget, and the typed
-- broadcast-TLBI dispatcher behind `completeShootdownRounds`.
import SeLe4n.Kernel.Architecture.TlbShootdownProtocol
-- WS-SM SM7.C: the catch-up commit drains each target's queue onto its own
-- per-core `perCoreTlb` view (`handleTlbShootdownReqOnCorePerCore`), making
-- the mounted per-core TLB model operative on the live shootdown path.
import SeLe4n.Kernel.Architecture.PerCoreTlbModel
import SeLe4n.Kernel.Architecture.TlbShootdownWait
import SeLe4n.Kernel.Architecture.TlbiForSharing
-- WS-SM SM7.B.12: the RPi5 platform binding — `shootdownSharingDomain`
-- reads `PlatformBinding.sharingDomain` directly, so a multi-cluster
-- port that changes the binding flips the live round's TLBI domain
-- without touching this module.
import SeLe4n.Platform.RPi5.Contract
import SeLe4n.Platform.FFI

/-!
# WS-SM SM6.A — Cross-core syscall dispatch entry (the live SGI-dispatch seam)

The C-callable seam the Rust SVC trap handler (`svc_dispatch::dispatch_svc`)
invokes for every syscall, in its cross-core-aware form.  It is the syscall
analogue of `perCoreTimerTickEntry` (the per-core timer ISR seam): it runs the
verified pure dispatch (`Platform.FFI.syscallDispatchFromAbi`) atomically against
the live kernel state, then **fires the cross-core `.reschedule` SGIs that the
state transition warrants** — recovered purely from the `(pre, post)` diff by
the SM5.F.4 dispatch `computeCrossCoreSgis`.

This closes the live half of the SM5.F.4 diff-based cross-core SGI dispatch for
the syscall path: the existing `Platform.FFI.syscallDispatchInner` commits the
post-state but never pokes a remote core, so a syscall whose effect makes a remote
thread newly runnable (an endpoint-call receiver or notification waiter / bound TCB
woken on another core — WS-SM SM6.A/SM6.B) or migrates its run-queue bucket (a
`.call`'s donation boosting a passive server pinned to another core) would leave
that core unscheduled until its next local timer tick.  This entry fires the IPI
immediately after the commit.  (The `computeCrossCoreSgis` diff recovers *both*
cases — see `crossCoreSgiBody_remote_wake` for the wake direction.)

**Single-core inertness (trace safety).** On the boot core,
`PriorityInheritance.computeCrossCoreSgis pre post bootCoreId = []` whenever every
thread's home core is the boot core (`computeCrossCoreSgis_nil_single_core`), and
`Concurrency.fireCrossCoreSgis [] = pure ()`.  So on the single-core
configuration the entry is observably identical to the boot-pinned
`syscallDispatchInner` — it commits the same state and performs no IPI.  The
model-layer trace harness exercises the pure `syscallEntry`, not this BaseIO
seam, so the golden trace is unaffected.

The `@[export lean_syscall_dispatch_cross_core]` keeps the symbol live for the
Rust extern.  The live switchover (the trap handler calling this instead of the
boot-pinned `syscall_dispatch_inner`) lands with the per-core dispatch seam,
when the executing core is threaded into `syscallDispatchFromAbi` so the calling
thread is identified and descheduled on its own core rather than the boot core.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)

/-- **WS-SM SM7.B.12**: the sharing domain the live shootdown round's
TLBIs are issued in — read **directly from the platform binding**
(`PlatformBinding.sharingDomain`), so the entry follows the platform:
`.inner` on the single-cluster BCM2712 (the test suite `rfl`-pins the
computed value), `.outer` on a multi-cluster port that changes the
binding — and only this changes: the state protocol is
domain-invariant (`Architecture.tlbShootdown_outer_correct`), so every
SM7.B round theorem carries over unchanged. -/
def shootdownSharingDomain : Concurrency.SharingDomain :=
  Platform.PlatformBinding.sharingDomain
    (platform := Platform.RPi5.RPi5Platform)

/-- **WS-SM SM7.B.12**: the RPi5 binding computes `.inner` — the
single-cluster BCM2712 pin, now derived rather than hardcoded. -/
theorem shootdownSharingDomain_rpi5 :
    shootdownSharingDomain = .inner := rfl

/-- **WS-SM SM7.B.6 + SM7.B.7**: report a fail-closed barrier violation
and then genuinely stop.  **Never returns.**

Lean's `panic!` is a diagnostic, not a barrier.  It requires
`[Inhabited α]` precisely because the runtime prints the message and
then returns the default value — in `BaseIO Unit`, `()` — so a bare
`panic!` reports the violation and lets the caller carry on into the
commit it was meant to prevent (PR #854 review; the process even exits
`0`).  Both shootdown barriers were written that way and were therefore
fail-*open*: the round-lock acquire returned as though it held the lock,
and the acknowledgment timeout fell through to the catch-up commit.

So the two roles are split.  `panic!` still emits the message, because
it is the only thing here that produces one.  `Concurrency.fatalHaltAll`
(Rust `ffi_fatal_halt_all`, `-> !`) is the stop.  The trailing recursion
is unreachable — it exists so that this function is non-returning in
*Lean's* semantics rather than only by the FFI's promise, which is the
distinction the barriers got wrong in the first place.

**The halt is system-wide, not per-PE** (PR #854 review).  Parking only
the core that detected the fault is not a barrier: the mapping change
is already committed, so every other core carries on against a TLB this
one has just declared it could not clean, and the target that never
acknowledged can resume with the stale translation — the very hazard
the barrier exists to stop.  `fatalHaltAll` broadcasts the SM0.H
`haltAll` SGI (INTID 4) before parking; that INTID had been reserved
and documented since SM0.H with **no handler registered**, so this is
also where that declaration finally becomes functional. -/
partial def haltFailClosed (msg : String) : BaseIO Unit := do
  panic! msg
  Concurrency.fatalHaltAll
  haltFailClosed msg

/-- **WS-SM SM7.B.7**: the cooperative round-lock acquire's retry
budget.  Covers > 10⁵ round-lengths of retries (a round completes in
< 1 µs on the 4-core BCM2712, plan §3.4) — exhaustion means a
genuinely wedged round holder. -/
def shootdownRoundLockAcquireFuel : Nat := 1000000

/-- **WS-SM SM7.B.7**: the budget literal, pinned. -/
theorem shootdownRoundLockAcquireFuel_value :
    shootdownRoundLockAcquireFuel = 1000000 := rfl

/-- **WS-SM SM7.B.7**: the cooperative round-lock acquire — spin on the
try-lock, and on every failed attempt **service this core's own
pending shootdown obligation** (its acknowledged generation is below
the round currently published ⇒ an in-flight round is waiting on this
core: invalidate the local TLB and acknowledge that round, exactly the
`.tlbShootdownReq` handler's effect).

Without the servicing arm this loop would deadlock into the holder's
wait-timeout panic: the holder's round waits on THIS core's ack, and
with IRQs masked in the SVC path the `.tlbShootdownReq` SGI can never
preempt the spin.  With it, a lock-waiter discharges the in-flight
round's obligation itself (over-invalidation-safe full local flush —
the same conservative effect as the Rust handler; the holder's
catch-up commit drains the Lean-side queue), so the holder always
completes and releases.

Fuel-bounded fail-closed (the SM7.B.6 discipline): the fuel covers
> 10⁵ round-lengths of retries — exhaustion means a genuinely wedged
round holder, and halting is the safe verdict (proceeding without the
round would be the SMP-C4 hazard). -/
def acquireShootdownRoundLockServicingSelf
    (execCore : Concurrency.CoreId) : BaseIO Unit := do
  let rec go : Nat → BaseIO Unit
    | 0 => haltFailClosed "WS-SM SM7.B.7: shootdown round-lock acquire \
        exhausted its fuel — the in-flight round's holder is wedged; \
        halting fail-closed"
    | fuel + 1 => do
        if (← Concurrency.shootdownRoundLockTryAcquire) then
          pure ()
        else
          -- Self-service is a LOCAL obligation: clean exactly this
          -- core's view (the Rust handler's `tlbi vmalle1`), then
          -- acknowledge the round that flush discharged.  The in-flight
          -- round's initiator owns the broadcast step — no IS-broadcast
          -- here.  The generation read, the flush and the
          -- acknowledgment are ONE Rust call so a newer round cannot
          -- publish between them and make the acknowledgment name a
          -- round this core never serviced (WS-SM SM7.F.3).
          let _ ← Concurrency.shootdownSelfServiceRound execCore
          go fuel
  go shootdownRoundLockAcquireFuel

/-- **WS-SM SM7.B (debt (1))**: publish a round's collapsed operand list
into the Rust per-descriptor mailbox under the seqlock discipline —
`begin`, one `slot` per operand (index-addressed), then `commit len`.
Each `TlbInvalidation` is transmitted as its raw
`(toOpTag, toAsid, toVaddr)` encoding, matching the Rust
`decode_tlb_invalidation` decode (SM7.B op-tag conformance).  Called by
the initiator under the round lock, before the SGIs fire.

**WS-SM SM7.F.3**: the publish also carries the round's *generation*
(`gen`), which each target's handler latches before any TLB work and
acknowledges afterwards.  That is what makes an acknowledgment name the
round it discharged, so a `.tlbShootdownReq` SGI left pending by an
earlier round can never satisfy this one's wait. -/
def publishShootdownOps (ops : List Architecture.TlbInvalidation)
    (gen : Nat) : BaseIO Unit := do
  Concurrency.shootdownPublishBegin
  let mut i : Nat := 0
  for op in ops do
    Concurrency.shootdownPublishSlot i op.toOpTag op.toAsid op.toVaddr
    i := i + 1
  Concurrency.shootdownPublishCommit ops.length gen

/-- **WS-SM SM7.B (the live round runtime)**: complete the shootdown
round(s) a syscall commit posted — the runtime realisation of plan
§3.2 steps 1–6 around the already-committed pure posting.

`changed` is the diff-recovered posted-target set
(`Architecture.shootdownChangedTargets pre post`), `ops` the
deduplicated posted operands (`Architecture.shootdownPostedOps`), and
`(lo, hi)` the diff-recovered **round-generation window** this commit
opened (`Architecture.shootdownRoundWindow pre post`); when no round was
posted this is `pure ()` (single-syscall inertness — no existing
syscall's runtime behaviour changes).

Sequence, under THE global round lock (the SM7.B.7 hardware-round
serialiser; acquired cooperatively,
`acquireShootdownRoundLockServicingSelf`):

1. **Publish the collapsed operands together with the round's
   generation** (`publishShootdownOps`), BEFORE the SGIs — so each
   target's handler latches the generation, retires just this round's
   operands locally (matching the Lean `handleTlbShootdownReqOnCore`
   per-descriptor effect) instead of a blanket `vmalle1`, and then
   acknowledges exactly that generation.  The `dsb ish` in
   `sendSgiToCore` orders the publish before any target can take the SGI
   (SM7.B debt (1)).

   There is deliberately **no ack reset** (WS-SM SM7.F.3, closing a
   stale-SGI hazard).  Under the SM7.A Boolean flag vector a round
   opened by clearing every online target's flag, and a
   `.tlbShootdownReq` SGI left pending by an *earlier* round — the
   cooperative acquire above self-acknowledges without consuming the
   interrupt — could be delivered in the window between that clear and
   this publish.  Its handler would then retire the *previous* round's
   operands and unconditionally set the flag, satisfying this round's
   wait with the target's TLB still holding the translation the round
   was supposed to retire.  Acknowledgments now carry the generation
   they discharged, so a stale delivery can only re-affirm an older
   round and nothing has to be cleared before a round opens.
2. One `.tlbShootdownReq` SGI per **online** non-initiator core (the
   SM7.A PR #838 P1 target-set obligation).  The full non-initiator
   set is poked — not just `changed` — because every online target owes
   this generation, and the handler is idempotent
   (`handleTlbShootdownReqOnCore_idempotent`); poking a subset could
   strand a target and hang the wait.
3. The initiator's local broadcast TLBIs — one `tlbiForSharing` per
   posted operand after the `vmalle1`-dominance collapse
   (`collapseShootdownOps`; effect-exact by
   `collapseShootdownOps_effect_eq`); each ends with the `dsb`+`isb`
   bracket.
4. Bounded wait for **this generation** acknowledged; timeout is a
   fail-closed panic (`shootdown_timeout_handling`: the verdict is
   exact, so the panic only fires on a genuinely hung round).
5. Model catch-up: fold `handleTlbShootdownReqOnCorePerCoreInWindow`
   over the targets — this commit's **own** descriptors drained on each
   target and on the initiator's own view, every model flag re-set,
   restoring quiescence (`shootdownRound_quiescent`) so the next round's
   posting succeeds.  Committed after the hardware acknowledgments
   certified that every target's TLBIs retired
   (`shootdownAck_release_acquire`).

On the v1.0.0 single-online-core boot this degenerates to: the publish,
zero SGIs, the local TLBIs, an immediately-satisfied wait, and the
catch-up commit.

**Model-vs-hardware catch-up fidelity — CLOSED at SM7.F.3.**  The model
*posting* (the pending-queue enqueue) rides the syscall's own atomic
`modifyGetKernelState` (`syscallDispatchCrossCoreEntry`), and this model
catch-up rides a *second* atomic step; neither is under the
`SHOOTDOWN_ROUND_LOCK`, which serialises only the hardware round.  A
concurrently-committed round can therefore have posted descriptors
between the two steps.  The catch-up is keyed on this commit's own
round-generation window, so it drains exactly the descriptors its own
rounds posted and leaves the other round's queued work for that round's
own catch-up
(`Architecture.shootdownCatchUpPerCoreInWindow_preserves_foreign`).  The
model can no longer report a core clean of an invalidation whose SGI has
not yet fired.

**Invariant carriage.**  Because a window drain deliberately leaves
foreign descriptors queued, it does *not* empty the pending queues the
way a whole-queue drain does, so the 12th `proofLayerInvariantBundle`
conjunct has to be carried rather than fall out:
`Architecture.shootdownCatchUpPerCoreInWindow_preserves_pendingBounded`
is the statement for this transition, resting on the per-core window
handler and its fold. -/
def completeShootdownRounds (changed : List Concurrency.CoreId)
    (ops : List Architecture.TlbInvalidation)
    (window : Nat × Nat)
    (execCore : Concurrency.CoreId) : BaseIO Unit := do
  if changed.isEmpty then
    pure ()
  else do
    -- A posted `vmalle1` supersedes every other operand — collapse to
    -- it once (`collapseShootdownOps_effect_eq`: the collapsed list's
    -- TLB effect is exactly the full list's) and reuse for both the
    -- per-descriptor mailbox publish and the initiator's broadcast.
    let collapsed := Architecture.collapseShootdownOps ops
    acquireShootdownRoundLockServicingSelf execCore
    -- WS-SM SM7.F.3 (PR #854 review P1): the round identity the HARDWARE
    -- side runs under is allocated HERE — under the round lock — and is
    -- deliberately NOT the model's commit-time `window.2`.
    --
    -- The acknowledgment test is monotone (`acked_gen >= gen`), so this
    -- generation has to order the round against the rounds whose acks
    -- could satisfy its wait: hardware execution order.  The model's
    -- generation is allocated by the pure transition inside the atomic
    -- commit above, which is a *different* order — nothing ties a
    -- commit's position to its position in the round-lock queue.  With
    -- two cores posting concurrently, core A could commit generation N,
    -- stall, watch core B commit N+1 and run B's round to completion
    -- (every target's `acked_gen` now N+1), then acquire the lock and
    -- have its own wait for `>= N` satisfied instantly — returning from
    -- a round no target ever serviced, operands still live in every
    -- remote TLB.  That is an under-invalidation: the SMP-C4 hazard,
    -- and the same failure SM7.F.3 closed for *stale* acknowledgments,
    -- arriving here as the *premature* one.
    --
    -- Allocating under the lock makes allocation order execution order
    -- by construction, so no older round can be certified by a newer
    -- round's acks.  The counter starts at 0 and returns pre-increment
    -- +1, so `roundGen ≥ 1` always: a round never carries the
    -- vacuously-satisfied generation 0 (slots initialise to 0, and
    -- `0 >= 0` would pass with nothing serviced).  The Rust side fails
    -- closed if the counter wraps.
    --
    -- The model window (`window`) keeps its own generations and still
    -- keys the catch-up drain below — the two identities answer
    -- different questions and are intentionally independent.  A commit
    -- that opened two model rounds (the retype's destroyed + installed
    -- ASID) still publishes both rounds' operands together and waits
    -- once, now under this single hardware generation.
    let roundGen ← Concurrency.shootdownAllocateRoundGeneration
    -- WS-SM SM7.B (debt (1)) + SM7.F.3: publish the round's exact operands
    -- AND its generation into the per-descriptor mailbox BEFORE firing the
    -- SGIs, so each target's handler latches the generation, retires just
    -- these operands locally (matching the Lean
    -- `handleTlbShootdownReqOnCore` per-descriptor effect) rather than a
    -- blanket `vmalle1`, and acknowledges exactly that generation.  The
    -- `dsb ish` in `sendSgiToCore` (SM1.F.8) orders this publish before any
    -- target can take the SGI.  There is no ack reset to race — see the
    -- header.
    publishShootdownOps collapsed roundGen
    -- One CORE_IRQ_READY snapshot per round (the IRQ-serviceable set,
    -- not the CORE_READY release handshake — PR #839 review P1;
    -- bring-up never overlaps a round per the SM7.A P1 contract, so the
    -- snapshot is stable).
    let onlineMask ← Concurrency.shootdownOnlineMask
    for c in Architecture.shootdownTargets execCore do
      if Concurrency.coreOnlineInMask onlineMask c then
        Concurrency.sendSgiToCore c .tlbShootdownReq
    for op in collapsed do
      Architecture.tlbiForSharing shootdownSharingDomain op
    -- PR #854 review: the wait is driven by **this round's** `onlineMask`,
    -- the same snapshot the SGI loop targeted, not by a fresh
    -- `CORE_IRQ_READY` read on the Rust side.  A secondary that publishes
    -- IRQ-readiness between the two reads would otherwise be absent from the
    -- SGI loop (never poked) yet present in the wait (required to
    -- acknowledge), so the round could only time out — and
    -- `bring_up_secondaries_inner` returns after its `CPU_ON` calls without
    -- waiting for secondaries to publish, so that window is reachable during
    -- ordinary boot.  Harmless while the timeout was fail-open; since
    -- v0.32.117 it halts the core, which is what makes carrying the snapshot
    -- load-bearing rather than tidy.
    let acked ← Concurrency.shootdownWaitAllAcked roundGen execCore onlineMask
      Architecture.shootdownWaitTimeoutTicks
    if !acked then
      -- The round lock is deliberately **not** released here.  A target
      -- never certified its invalidation, so every other core's round must
      -- block rather than proceed against a TLB this one could not clean:
      -- holding the lock quarantines the subsystem, and `haltFailClosed`
      -- broadcasts `haltAll` before parking so the cores that would have
      -- waited on it stop too.  Releasing first — as this did until the PR
      -- #854 review — let the rest of the machine run on with the stale
      -- translation the barrier exists to prevent.
      haltFailClosed "WS-SM SM7.B.6: TLB shootdown round timed out — a \
        target core is hung or deaf; halting fail-closed (a silently \
        skipped invalidation would be the SMP-C4 stale-TLB hazard)"
    -- WS-SM SM7.C + SM7.F.3: the model catch-up drains each *non-initiator*
    -- target's **own** posted descriptors — those in this commit's round-
    -- generation window — onto that core's per-core `perCoreTlb` view
    -- (`handleTlbShootdownReqOnCorePerCoreInWindow`) AND retires the round's
    -- collapsed operands on the *initiator's* own view
    -- (`drainInitiatorPerCoreView`, via `shootdownCatchUpPerCoreInWindow`).
    -- Keying on the window is the SM7.B v0.32.79 model-fidelity closure: a
    -- concurrently-committed round's freshly-posted descriptors survive for
    -- its own catch-up
    -- (`shootdownCatchUpPerCoreInWindow_preserves_foreign`), so the model
    -- never claims a core clean of an invalidation whose SGI has not fired.
    -- Under round serialisation the window drain IS the whole-queue drain
    -- (`shootdownCatchUpPerCoreInWindow_eq_catchUp`), so nothing about a
    -- single-round commit changes.  The initiator drain is the PR #844 P1 fix:
    -- the `tlbiForSharing` loop above is an inner-shareable broadcast that
    -- reaches the issuing PE too, so the initiator's own per-core view must
    -- retire the operands (`shootdownTargets execCore` explicitly excludes the
    -- initiator).  This makes the mounted per-core TLB model reflect the live
    -- round's real per-descriptor drain on **every** reached core, initiator
    -- included — the operative form of Theorem 3.3.1
    -- (`Architecture.shootdownRoundPerCore_invalidates_perCore`).  It stays
    -- **trace-safe**: the initiator drain is `perCoreTlb`-only (the scalar
    -- `st.tlb` boot-core view was already retired in the dispatch), so the
    -- catch-up's `tlb` / `tlbShootdown` effect is definitionally the SM7.B
    -- single-view target fold's (`shootdownCatchUpPerCore_agrees_singleView`);
    -- only the projection-invisible `perCoreTlb` additionally evolves, so the
    -- golden trace stays byte-identical.  The scalar `st.tlb` remains the
    -- pre-SMP single-view (all-cores-conflated) model; `perCoreTlb` is the
    -- per-core refinement.
    Platform.FFI.modifyGetKernelState (fun st =>
      ((), Architecture.shootdownCatchUpPerCoreInWindow st execCore collapsed
        window.1 window.2))
    -- PR #854 review: the release is **after** the catch-up commit, so the
    -- lock brackets every access `shootdownRoundLock_release_acquire` names
    -- as `e_crit` — the operand publication, the posted queues, and the
    -- catch-up commit.  It previously released before the commit, which left
    -- that contract naming an access the bracket did not cover and the
    -- theorem un-instantiable at the catch-up.  Extending costs a bounded
    -- queue drain inside the critical section (`modifyGetKernelState` is a
    -- plain `IO.Ref` update, so there is no lock to invert against), well
    -- within `shootdownRoundLockAcquireFuel`.
    --
    -- What that bracket does NOT buy: `SHOOTDOWN_ROUND_LOCK` serialises
    -- *rounds* against each other, and nothing else.  An ordinary syscall
    -- commit on another core takes no round lock, so it can interleave with
    -- this read-modify-write and lose one of the two transitions entirely
    -- (`Platform.FFI.modifyGetKernelState`).  That would defeat
    -- `shootdownCatchUpPerCoreInWindow_preserves_foreign` at runtime — the
    -- theorem says the *pure function* preserves a concurrent round's
    -- descriptors, which is only worth having once kernel entry is
    -- serialised.  Owed by SM5.I; unreachable today (SMP off by default —
    -- enforced by `CmdlineConfig::default`, which returned `true` until
    -- v0.32.136 — and no bootable image before SM10.1).
    Concurrency.shootdownRoundLockRelease

/-- **WS-SM SM7.D.1** (the live instruction-cache maintenance seam): emit the
instruction-cache maintenance the just-committed transition recorded.

**How the work is recovered.**  Kernel transitions are pure state functions, so
every hardware effect is emitted here, after the commit.  The TLB round is
recoverable from the `(pre, post)` diff because it *posts descriptors* into
`tlbShootdown`; the instruction-cache maintenance has no such queue, so the
model records the operand it applied in `SystemState.pendingIcacheMaintenance`
(`Architecture.recordIcacheMaintenance`) and this seam emits exactly that.  The
ledger is cleared in the same atomic step that reads it, so no operand can be
emitted twice and none can be stranded into the next syscall.

**Why not key on the shootdown diff.**  That was the SM7.D landing's
approximation, and it was doubly imprecise: it fired the *strongest* operand
(`IC IALLUIS`) for every unmap — including the common non-executable one, which
owes nothing at all — and it missed a retype that posted no round.  Recovering
the precise operand from the round's encoded `.vae1` instead would need an
`ASID`/`VAddr` round-trip whose failure mode is **under**-invalidation, the one
direction that is unsafe.  The ledger avoids both: the runtime emits the
model's operand, no reconstruction and no over-approximation.

**Why a list.**  The ledger holds the operands *in record order* rather than a
single joined operand, because the operands do not form a join-semilattice:
`iallu` (`IC IALLUIS`) invalidates instruction caches but issues no `DC CVAU`,
so it does not discharge a `unifyPage`'s clean to the Point of Unification, and
collapsing into it would silently drop that clean.  The seam therefore emits
every entry.  On the live path the list holds at most one operand (one
maintenance-bearing transition per syscall, drained here), so this is a `forM`
over a singleton or the empty list.

**Ordering.**  Called *after* `completeShootdownRounds`, so the translations a
transition retired are gone from every core's TLB before the instruction lines
fetched through them are dropped.  Inert when the transition owed nothing
(`completeIcacheMaintenance_nil`), which is every syscall that touched no
executable mapping and re-purposed no memory. -/
def completeIcacheMaintenance
    (owed : List Architecture.ICacheInvalidation) : BaseIO Unit :=
  owed.forM Platform.FFI.icMaintenanceBroadcast

/-- **WS-SM SM7.D.1** (structural marker): a commit that owed no
instruction-cache maintenance emits none — no maintenance instruction, no
barriers.  The definition-level inertness of the SM7.D runtime bracket,
mirroring `completeShootdownRounds_nil`. -/
theorem completeIcacheMaintenance_nil :
    completeIcacheMaintenance [] = pure () := rfl

/-- **WS-SM SM7.D.1**: when maintenance *was* owed the seam emits exactly the
recorded operand — pinned so a refactor that widened it back to the domain-wide
invalidate, or dropped the emission, breaks here. -/
theorem completeIcacheMaintenance_singleton (op : Architecture.ICacheInvalidation) :
    completeIcacheMaintenance [op] =
      Platform.FFI.icMaintenanceBroadcast op := rfl

/-- **WS-SM SM7.D**: the seam emits **every** recorded operand, in record order.
Pinned so a refactor that collapses the ledger to one operand — the unsound
direction, since `iallu` does not discharge a `unifyPage`'s clean-to-PoU — fails
here rather than silently under-maintaining. -/
theorem completeIcacheMaintenance_cons (op : Architecture.ICacheInvalidation)
    (rest : List Architecture.ICacheInvalidation) :
    completeIcacheMaintenance (op :: rest) =
      (do Platform.FFI.icMaintenanceBroadcast op; completeIcacheMaintenance rest) := rfl

/-- **WS-SM SM7.B** (structural marker): a commit that changed no
pending-shootdown queue runs no round — no lock traffic, no reset, no
SGIs, no TLBIs, no wait.  This is the non-shootdown-syscall inertness
of the runtime bracket at the definition level (the state-diff half is
`shootdownChangedTargets_nil_of_eq`); the trace fixture's
byte-identity across the SM7.B landing rests on it. -/
theorem completeShootdownRounds_nil
    (ops : List Architecture.TlbInvalidation) (window : Nat × Nat)
    (execCore : Concurrency.CoreId) :
    completeShootdownRounds [] ops window execCore = pure () := rfl

/-- **WS-SM SM6.A**: the cross-core-aware syscall dispatch entry — the live
SGI-dispatch seam.  Reads the deployment labeling context and the executing core
from the hardware (`currentCoreId`), runs the verified
`Platform.FFI.syscallDispatchFromAbi` atomically against the kernel state ref
(`modifyGetKernelState`, committing the post-state), then — *after* the commit —
fires the cross-core `.reschedule` SGIs recovered from the `(pre, post)` diff by
`PriorityInheritance.computeCrossCoreSgis`, then — WS-SM SM7.B — runs the TLB
shootdown round(s) the commit posted (`completeShootdownRounds`, recovered from
the `tlbShootdown` diff; inert for every non-shootdown syscall).

**WS-RA (the return convention)**: the committed outcome's return frame
(`x0`-`x5`, errors as the offset label on `x1`) is published into this core's
return-frame mailbox (`ffiSyscallReturnFrame` — the `ShootdownOpMailbox`
pattern, since a scalar export return cannot carry six words), and the export's
scalar return is the **outcome tag**: `0` = the mailbox frame is the caller's
return, `1` = the caller blocked and no frame exists for it (RA.C.9; the
staged frame is delivered by the SM10.1 context restore).  The pure dispatch
never takes the `.error` arm (`syscallDispatchFromAbi_total`); the arm is
discharged inertly with an error frame.

**WS-SM SM8.B (PR #861 review round 17): the local half of the reschedule.**
`PriorityInheritance.scheduleLocalSuccessorLive` runs *inside* the atomic step,
before the diffs are taken, and dispatches a successor when the transition
vacated this core (`localSuccessorNeeded`).  It is the inline dual of
`currentSlotChangeSgis`, which pokes every *remote* core whose `current` slot
changed and excludes the executing core by construction — correctly, since a
core does not interrupt itself, it runs the handler inline.  That inline half
did not exist: every blocking IPC leg cleared the caller's slot and nothing
selected a successor, and the periodic tick provably cannot cover for it
(`timerTickOnCore_cannot_dispatch_vacated_core`).

**Gated (round 20).**  The wrapper is `scheduleLocalSuccessorLive`, which is
the identity until `contextRestoreSeamLive` is true.  Dispatching a successor
whose context the runtime cannot install into the trap frame would be worse than
dispatching none: hardware returns through the blocked caller's frame either
way, but `currentOnCore = none` makes the caller's next syscall fail *closed*
(`.illegalState` — `vacatedCore_next_syscall_rejected` below, over the state
this entry commits) whereas a named successor **misattributes** it.  The switch
therefore turns on with the seam it depends on, not before.

Two properties of the placement are load-bearing.  It is **inside** the
`modifyGetKernelState` closure, so the successor is dispatched in the same
atomic step that commits the transition — a second `modifyGetKernelState` would
be a separate read-modify-write another core could interleave with.  And the
SGI, shootdown and I-cache diffs are taken against the **final** state `st''`
rather than the pre-reschedule `st'`, so what the hardware is told to do
describes the state that was actually committed;
`handleRescheduleSgiOnCore` writes the executing core's register bank as well as
its scheduler slots.  Inert (`st'' = st'`) for every syscall that left a thread
running on this core — including every arm of a single-core build. -/
@[export lean_syscall_dispatch_cross_core]
def syscallDispatchCrossCoreEntry
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 : UInt64)
    (ipcBufferAddr : UInt64) : BaseIO UInt64 := do
  let ctx ← Platform.FFI.getKernelLabelingContext
  let execCore ← Concurrency.currentCoreId
  let result ← Platform.FFI.modifyGetKernelState (fun st =>
    match Platform.FFI.syscallDispatchFromAbi ctx execCore syscallId msgInfo x0 x1 x2 x3 x4 x5
        ipcBufferAddr st with
    | Except.ok (outcome, st') =>
        let st'' := PriorityInheritance.scheduleLocalSuccessorLive st st' execCore
        ((outcome, PriorityInheritance.computeCrossCoreSgis st st'' execCore,
          Architecture.shootdownChangedTargets st st'',
          Architecture.shootdownPostedOps st st'',
          Architecture.shootdownRoundWindow st st'',
          st''.pendingIcacheMaintenance),
         Architecture.clearIcacheMaintenance st'')
    | Except.error e =>
        ((Architecture.SyscallOutcome.returns (Architecture.errorFrame e),
          ([] : List (CoreId × SgiKind)),
          ([] : List CoreId),
          ([] : List Architecture.TlbInvalidation),
          ((0, 0) : Nat × Nat),
          ([] : List Architecture.ICacheInvalidation)), st))
  -- WS-RA (plan §3.3): publish the return frame into this core's mailbox
  -- immediately after the commit — `dispatch_svc` reads it back inside the
  -- same `with_kernel_entry` critical section.  A `blocks` outcome publishes
  -- the zero frame, which the Rust side never reads (the tag below says no
  -- frame exists for the caller — RA.C.9).
  let frame := result.1.mailboxFrame
  Platform.FFI.ffiSyscallReturnFrame frame.x0 frame.x1 frame.x2 frame.x3 frame.x4 frame.x5
  Concurrency.fireCrossCoreSgis result.2.1
  -- WS-SM SM7.B: run the shootdown round(s) this commit posted (inert
  -- when the syscall touched no pending-shootdown queue).
  completeShootdownRounds result.2.2.1 result.2.2.2.1 result.2.2.2.2.1 execCore
  -- WS-SM SM7.D.1: emit the instruction-cache maintenance this commit
  -- recorded.  Ordered *after* the shootdown round so the translations are
  -- already retired everywhere when the instruction lines fetched through them
  -- are dropped.  The operand is the model's own — the ledger was read and
  -- cleared in the atomic step above, so it is emitted exactly once and never
  -- stranded into the next syscall.  Inert when nothing was owed.
  completeIcacheMaintenance result.2.2.2.2.2
  -- WS-RA: the export's scalar return is the outcome tag (0 = the mailbox
  -- frame is the caller's return; 1 = the caller blocked, no frame).
  pure result.1.tagWord

/-- **WS-SM SM6.A** structural marker: `syscallDispatchCrossCoreEntry` unfolds to
the read-context / read-core / commit-dispatch / fire-SGIs / return-encoded
driver.  Pins the body shape (atomic `modifyGetKernelState` over
`syscallDispatchFromAbi`, then `fireCrossCoreSgis` of the diff-recovered SGIs) so
a refactor that drops the SGI firing or the state commit breaks this marker at
elaboration; combined with `@[export]` (which the Rust extern resolves against)
the seam cannot regress silently. -/
theorem syscallDispatchCrossCoreEntry_def
    (syscallId : UInt32) (msgInfo : UInt64) (x0 x1 x2 x3 x4 x5 : UInt64)
    (ipcBufferAddr : UInt64) :
    syscallDispatchCrossCoreEntry syscallId msgInfo x0 x1 x2 x3 x4 x5 ipcBufferAddr =
      (do
        let ctx ← Platform.FFI.getKernelLabelingContext
        let execCore ← Concurrency.currentCoreId
        let result ← Platform.FFI.modifyGetKernelState (fun st =>
          match Platform.FFI.syscallDispatchFromAbi ctx execCore syscallId msgInfo x0 x1 x2 x3 x4 x5
              ipcBufferAddr st with
          | Except.ok (outcome, st') =>
              let st'' := PriorityInheritance.scheduleLocalSuccessorLive st st' execCore
              ((outcome, PriorityInheritance.computeCrossCoreSgis st st'' execCore,
                Architecture.shootdownChangedTargets st st'',
                Architecture.shootdownPostedOps st st'',
                Architecture.shootdownRoundWindow st st'',
                st''.pendingIcacheMaintenance),
               Architecture.clearIcacheMaintenance st'')
          | Except.error e =>
              ((Architecture.SyscallOutcome.returns (Architecture.errorFrame e),
                ([] : List (CoreId × SgiKind)),
                ([] : List CoreId),
                ([] : List Architecture.TlbInvalidation),
                ((0, 0) : Nat × Nat),
                ([] : List Architecture.ICacheInvalidation)), st))
        let frame := result.1.mailboxFrame
        Platform.FFI.ffiSyscallReturnFrame frame.x0 frame.x1 frame.x2 frame.x3 frame.x4 frame.x5
        Concurrency.fireCrossCoreSgis result.2.1
        completeShootdownRounds result.2.2.1 result.2.2.2.1 result.2.2.2.2.1 execCore
        completeIcacheMaintenance result.2.2.2.2.2
        pure result.1.tagWord) := rfl

/-- **WS-SM SM8.B** (PR #861 review rounds 39/41): the gating argument's
"rejection, not misattribution" half, as a theorem rather than as prose.

The gate above (`scheduleLocalSuccessorLive`, inert until the restore seam is
live) is justified by a claim about what happens *next*: a blocking transition
leaves `currentOnCore execCore = none`, and the caller's next syscall is then
**rejected** rather than attributed to some other thread.  That claim has been
challenged twice on the review — both times asserting the opposite, that the
next syscall silently falls back to `bootCoreId` — so it is stated here at the
entry, over the state the entry actually commits (the *gated* wrapper's output,
so the theorem tracks whichever side of the seam is live).

The fallback the challenge describes is real but belongs to
`determineExecutingCore`, which is reached only with a caller id already in
hand.  Resolution happens first, in `syscallDispatchFromAbi`, and it has no
fallback: no current thread on the issuing core means `.illegalState` with the
state returned unmodified.  A change that gave the entry a fallback core — the
outcome the challenge fears — breaks this theorem. -/
theorem vacatedCore_next_syscall_rejected
    (ctx : LabelingContext) (execCore : CoreId)
    (pre post : SystemState)
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr : UInt64)
    (hMsg : msgInfo = x1)
    (hVacated :
      (PriorityInheritance.scheduleLocalSuccessorLive pre post execCore).scheduler.currentOnCore
        execCore = none) :
    Platform.FFI.syscallDispatchFromAbi ctx execCore syscallId msgInfo x0 x1 x2 x3 x4 x5
        ipcBufferAddr (PriorityInheritance.scheduleLocalSuccessorLive pre post execCore)
      = Except.ok (.returns (Architecture.errorFrame .illegalState),
                   PriorityInheritance.scheduleLocalSuccessorLive pre post execCore) :=
  Platform.FFI.syscallDispatchFromAbi_illegalState_when_no_current ctx execCore syscallId msgInfo
    x0 x1 x2 x3 x4 x5 ipcBufferAddr _ hMsg hVacated

/-- **WS-SM SM6.A** trace-safety witness: on the boot core, when every thread's
home core is the boot core (the single-core configuration), the diff-recovered
SGI list the entry fires is empty.  Combined with `fireCrossCoreSgis [] = pure ()`
this is the machine-checked statement that the cross-core entry is observably
identical to a plain commit-and-return on single-core — it commits the same
post-state and performs no IPI.  Re-exports `computeCrossCoreSgis_nil_single_core`
at the entry's dispatch granularity. -/
theorem syscallDispatchCrossCoreEntry_sgis_nil_single_core
    (pre post : SystemState)
    (hAllBoot : ∀ t : SeLe4n.ThreadId,
      determineTargetCore post t = Concurrency.bootCoreId)
    (hNoRemoteCur : ∀ c : Concurrency.CoreId, c ≠ Concurrency.bootCoreId →
      pre.scheduler.currentOnCore c = none)
    (hNoRemoteCurPost : ∀ c : Concurrency.CoreId, c ≠ Concurrency.bootCoreId →
      post.scheduler.currentOnCore c = none) :
    PriorityInheritance.computeCrossCoreSgis pre post Concurrency.bootCoreId = [] :=
  PriorityInheritance.computeCrossCoreSgis_nil_single_core pre post hAllBoot hNoRemoteCur
    hNoRemoteCurPost

/-- **WS-SM SM6.E**: the cross-core-aware suspend entry — the per-core seam the
Rust `sele4n_suspend_thread` atomicity bracket resolves against (the suspend
analogue of `syscallDispatchCrossCoreEntry`, superseding the boot-pinned
`Platform.FFI.suspendThreadInner`).  Reads the executing core from the hardware
(`currentCoreId`), runs the verified per-core
`Lifecycle.Suspend.suspendThreadOnCore` atomically against the kernel state ref
(committing the post-state; the pre-state is kept on every error), then —
*after* the commit — fires the **diff-recovered** cross-core `.reschedule`
SGIs (`computeCrossCoreSgis` over the committed pre/post pair), exactly as
`syscallDispatchCrossCoreEntry`.  The diff subsumes the single SGI
`suspendThreadOnCore` surfaces (the victim-deschedule poke is re-derived by
the diff seam's SM6.E descheduled-current rule,
`crossCoreSgiBody_remote_deschedule`) and additionally recovers the G2b
PIP-revert pokes — a suspend that severs a donation chain lowers remote
chain members' effective run-queue buckets, and each such member's home
core must re-run its scheduler (PR #831 review: the pre-fix entry fired
only the surfaced victim SGI, leaving the re-bucketed cores unpoked until
their next timer tick).  Sentinel `tid`s are rejected at the boundary
Sentinel `tid`s are rejected at the boundary
exactly as `suspendThreadInner`.

**Authority obligation (audit note).**  This export performs NO capability
check — it is the *mechanism* seam below the dispatch layer.  Its only
sanctioned caller is the Rust AN9-D atomicity bracket
(`sele4n_suspend_thread`), reached from the capability-gated syscall path;
the symbol is unreachable from user mode (user code enters via SVC →
`dispatch_svc` only).  Any future in-kernel caller MUST carry its own
authority for the target thread (a `.write`-bearing TCB capability or an
equivalent kernel-internal justification) — calling this raw seam without
one is a privilege-escalation bug, not a supported use.

**Single-core inertness (trace safety).**  On an all-boot deployment every
diff-derived SGI list is empty (`computeCrossCoreSgis_nil_single_core`), so
the entry commits the same post-state with no IPI. -/
@[export suspend_thread_cross_core]
def suspendThreadCrossCoreEntry (tid : UInt64) : BaseIO UInt32 := do
  let execCore ← Concurrency.currentCoreId
  let result ← Platform.FFI.modifyGetKernelState (fun st =>
    let threadId := SeLe4n.ThreadId.ofNat tid.toNat
    match threadId.toValid? with
    | none =>
        ((Platform.FFI.KernelError.toUInt32 .invalidArgument,
          ([] : List (CoreId × SgiKind))), st)
    | some vtid =>
        -- **WS-SM SM3.C.9**: run the transition inside its declared
        -- per-object lock set.  `suspend_thread_cross_core` is the first
        -- live export to do this, which is what makes SM3's 2PL and
        -- serializability theorems statements about the path the kernel
        -- actually runs rather than about an intended discipline.
        --
        -- The caller is the thread currently on the executing core; its
        -- TCB is read-locked, the victim's is write-locked, and the
        -- optional members (blocked endpoint / notification, consumed
        -- Reply, bound or donated SchedContext, donation's original
        -- owner) are resolved from the victim's own fields — the same
        -- fields the suspend pipeline branches on.
        --
        -- `none` means no footprint has been declared for this
        -- transition, in which case the transition runs exactly as
        -- before under the SM5.I kernel-entry lock.  Falling back is
        -- always sound; claiming a footprint that does not cover a write
        -- would not be.
        --
        -- **WS-SM SM8.B (review round 17)**: the local reschedule applies here
        -- too, and is *self-disabling* on this path —
        -- `suspendThreadOnCore` runs its own scheduling point
        -- (`suspendRescheduleOnCore`), so where it dispatched a successor the
        -- post-state slot is populated and `localSuccessorNeeded` is false
        -- (`scheduleLocalSuccessor_of_post_running`).  The two mechanisms
        -- cannot both dispatch.  It is applied anyway rather than reasoned
        -- away, so that the entry seams do not disagree about who is
        -- responsible for a vacated core.
        let action : SystemState →
            SystemState × (UInt32 × List (CoreId × SgiKind)) := fun s =>
          match Lifecycle.Suspend.suspendThreadOnCore s vtid execCore with
          | Except.ok (s', _) =>
              let s'' := PriorityInheritance.scheduleLocalSuccessorLive s s' execCore
              (s'', ((0 : UInt32),
                    PriorityInheritance.computeCrossCoreSgis s s'' execCore))
          | Except.error e =>
              (s, (Platform.FFI.KernelError.toUInt32 e,
                   ([] : List (CoreId × SgiKind))))
        let callerTid := (st.scheduler.currentOnCore execCore).getD vtid
        match Concurrency.lockSetForSyscall .tcbSuspend callerTid vtid st with
        | some lockSet =>
            let (st', r) := Concurrency.withLockSet lockSet execCore action st
            (r, st')
        | none =>
            let (st', r) := action st
            (r, st'))
  Concurrency.fireCrossCoreSgis result.2
  pure result.1

-- ============================================================================
-- WS-SM SM9.B.9 — the refusal write does not disturb the runtime seam
-- ============================================================================

/-- WS-SM SM9.B.9: **the diff-recovered cross-core SGIs are unchanged by a
refusal write.**

The runtime seam commits the dispatch's post-state and then fires the SGIs
`computeCrossCoreSgis` re-derives from the `(pre, post)` diff.  SM9.B adds a
field to that post-state on the error path, and this is the statement that the
addition is invisible to the re-derivation: the SGI rule reads the object
index, the object store and the scheduler slots, all of which the refusal write
frames, so the pokes the runtime sends are exactly the pokes it sent before the
ledger existed.

Stated here rather than at the seam because this is where the two meet — and
worth stating rather than assuming, since "the write only touches one field" is
a property of `recordSyscallRefusal`, while "the seam reads no other field" is a
property of `computeCrossCoreSgis`, and only their conjunction says the runtime
is unaffected. -/
theorem computeCrossCoreSgis_recordSyscallRefusal_eq
    (ctx : LabelingContext) (executingCore : CoreId) (syscallId : UInt32)
    (tid : SeLe4n.ThreadId) (ke : KernelError) (x0 : UInt64)
    (pre post : SystemState) (execCore : CoreId) :
    PriorityInheritance.computeCrossCoreSgis pre
        (Platform.FFI.recordSyscallRefusal ctx executingCore syscallId tid ke x0 post)
        execCore
      = PriorityInheritance.computeCrossCoreSgis pre post execCore := by
  obtain ⟨L, hEq⟩ :=
    Platform.FFI.recordSyscallRefusal_frame ctx executingCore syscallId tid ke x0 post
  rw [hEq]
  rfl

end SeLe4n.Kernel
