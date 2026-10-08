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
-- rule; see WS-SM SM6.)

import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore
import SeLe4n.Kernel.Concurrency.Runtime
import SeLe4n.Kernel.Concurrency.Locks.LockSetForSyscall
-- WS-LS LS2.4: the atomic step the seam commits, the footprint the entry's own
-- decode declares for it, and the proof that the footprint covers the step's
-- writes — the three fields of the seam's `BracketSpec`.
import SeLe4n.Kernel.SyscallDispatchStep
import SeLe4n.Kernel.SyscallSchedFootprint
import SeLe4n.Kernel.SyscallSeamCoverage
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
open SeLe4n.Kernel.Concurrency (CoreId SgiKind LockSet BracketSpec)

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
    (windowFrom windowTo : Nat)
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
    -- deliberately NOT the model's commit-time `windowTo`.
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
    -- The model window (`windowFrom`, `windowTo`) keeps its own generations and still
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
        windowFrom windowTo))
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

-- **v0.36.39**: `completeIcacheMaintenance` and its three equations moved to
-- `Platform.FFI`, beside `completePhysicalWrites`, because every state-committing
-- entry drains the instruction-cache ledger now, and the timer, reschedule and
-- fault entries cannot reach this module.

-- **WS-BP BP7.8**: `completePhysicalWrites` and its two equations moved to
-- `Platform.FFI`, beside `physicalWriteApply`, because the fault entries drain the
-- same ledger now (a fault message's words past the fourth are user-word stores)
-- and `FaultEntry` cannot reach this module.

/-- **WS-SM SM7.B** (structural marker): a commit that changed no
pending-shootdown queue runs no round — no lock traffic, no reset, no
SGIs, no TLBIs, no wait.  This is the non-shootdown-syscall inertness
of the runtime bracket at the definition level (the state-diff half is
`shootdownChangedTargets_nil_of_eq`); the trace fixture's
byte-identity across the SM7.B landing rests on it. -/
theorem completeShootdownRounds_nil
    (ops : List Architecture.TlbInvalidation) (windowFrom windowTo : Nat)
    (execCore : Concurrency.CoreId) :
    completeShootdownRounds [] ops windowFrom windowTo execCore = pure () := rfl

/-- **WS-LS LS2.4: the syscall seam's bracket.**

The footprint is the entry's own decode (`declaredUnifiedLockSetForAbiEntry`,
resolved at the step's pre-state), the step is `syscallDispatchCrossCoreStep`
over the context the caller trapped with, and the proof field is
`syscallDispatchCrossCoreStep_coversWrites` (WS-LS LS2.3) under the seam's
pre-state invariant — so the record cannot be built for a footprint the step
writes outside of.  The entry runs `BracketSpec.run`, which is the step and
nothing else: no footprint is resolved, acquired, re-resolved or unwound on
the executed path.  The growing and shrinking phases exist on the ghost table
(`BracketSpec.runGhost`) alone, and `runGhost_kernel` says the executed path
is the kernel projection of the proven one.

The three arms of the word-level bracket this replaces (WS-RR RR7.12:
undeclared / committed / refused, with `syscallBracketRefusalResult` on the
third) are gone with the lock words they wrote.  The refusal arm has no
counterpart: under the entry lock the ghost table starts and ends all-free
(`BracketSpec.runGhost_locks_of_unheld`), so the guard a refusal answered
holds by construction (`BracketSpec.guard_of_unheld`), and a syscall whose
footprint is undeclared runs the same step as one whose footprint is — the
footprint is a proof obligation, not a runtime branch.

`execCore` is the core the syscall executes on.  `trapped` is the context the
caller trapped with, whole (`v0.36.47` audit): the step reads the six message
registers, the IPC buffer (`x6`) and the fault window (`pc`, `pstate`, `sp`,
`x30`) off it here, so the closure the entry hands
`Platform.FFI.modifyGetKernelState` captures one object rather than eleven
boxed `UInt64`s.  It is the core's in-flight object (WS-CV CV3.1), read here
and never kept: the state receives its words through the save's copy.  Inlined, with `BracketSpec.run`, so the executed path is the
step's own application and the record is never built at runtime. -/
@[inline] def syscallDispatchBracket (ctx : LabelingContext) (execCore : CoreId)
    (syscallId : UInt32) (trapped : Architecture.InFlightContext) :
    BracketSpec (Architecture.SyscallOutcome × List (CoreId × SgiKind) × List CoreId ×
      List Architecture.TlbInvalidation × (Nat × Nat) ×
      List Architecture.ICacheInvalidation × List Architecture.PhysicalWrite ×
      Architecture.RestoreTarget × Option SeLe4n.ThreadId) where
  declared := declaredUnifiedLockSetForAbiEntry ctx execCore syscallId
    trapped.x0 trapped.x1 trapped.x2 trapped.x3 trapped.x4 trapped.x5
  step := syscallDispatchCrossCoreStep ctx execCore syscallId
    trapped.x0 trapped.x1 trapped.x2 trapped.x3 trapped.x4 trapped.x5
    trapped.x6 trapped.pc trapped.pstate trapped.sp trapped.x30
  inv := fun st => st.objects.invExt ∧ queueHeadBlockedConsistent st
  covers := fun st S hInv hS =>
    syscallDispatchCrossCoreStep_coversWrites ctx execCore syscallId
      trapped.x0 trapped.x1 trapped.x2 trapped.x3 trapped.x4 trapped.x5
      trapped.x6 trapped.pc trapped.pstate trapped.sp trapped.x30 st S hInv hS

/-- The step the seam commits: the syscall bracket, run.  Kept under the name
the entry, its definitional marker and the suites call. -/
@[inline] def syscallDispatchCrossCoreBracketedStep (ctx : LabelingContext)
    (execCore : CoreId) (syscallId : UInt32) (trapped : Architecture.InFlightContext)
    (st : SystemState) :
    (Architecture.SyscallOutcome × List (CoreId × SgiKind) × List CoreId ×
      List Architecture.TlbInvalidation × (Nat × Nat) ×
      List Architecture.ICacheInvalidation × List Architecture.PhysicalWrite ×
      Architecture.RestoreTarget × Option SeLe4n.ThreadId) × SystemState :=
  (syscallDispatchBracket ctx execCore syscallId trapped).run st

/-- **WS-LS LS2.4**: what the syscall entry executes is the verified step —
`rfl`, because `BracketSpec.run` is the step.  This equation holding on every
pre-state, declared footprint or not, is what subsumes the old bracket's
`_undeclared` fallback and `_refused` negative: there is no arm on which the
seam commits anything but the step. -/
theorem syscallDispatchCrossCoreBracketedStep_run (ctx : LabelingContext)
    (execCore : CoreId) (syscallId : UInt32) (trapped : Architecture.InFlightContext)
    (st : SystemState) :
    syscallDispatchCrossCoreBracketedStep ctx execCore syscallId trapped st
      = syscallDispatchCrossCoreStep ctx execCore syscallId
          trapped.x0 trapped.x1 trapped.x2 trapped.x3 trapped.x4 trapped.x5
          trapped.x6 trapped.pc trapped.pstate trapped.sp trapped.x30 st := rfl

/-- **The sender's overflow words, from the batches the HAL answered**
(`v0.36.47` audit): each run's `ByteArray` decoded to its `n` words
(`IpcBufferRead.wordsOfBatches`) and zipped back onto the addresses the runs
were built from.  A batch of any other size — or a different number of batches
than runs — is a HAL defect the hardware never produces (it halts on a refused
run instead), and the answer is to fail closed exactly as
`syscallEntryContextOrFaulted` does: the `.faulted` tag, on which the entry
commits nothing and the trap layer halts the PE.  Pure, so the host suite runs
the decode and that arm (`tests/SyscallDispatchSuite.lean`).  Inlined with
`readCallerOverflowWords` into the entry, so the entry's match on the answer
is a match on the decode and no `Except` is built (WS-ZA). -/
@[inline] def overflowWordsOrFaulted (addrs : List SeLe4n.PAddr) (runs : List (SeLe4n.PAddr × Nat))
    (batches : List ByteArray) : Except UInt64 (List (SeLe4n.PAddr × UInt64)) :=
  match Architecture.IpcBufferRead.wordsOfBatches runs batches with
  | some ws => .ok (addrs.zip ws)
  | none => .error Architecture.SyscallOutcome.faulted.tagWord

/-- **Every address gets its word**: on the runs of `addrs`, a decoded answer
pairs the addresses in order with one word each — the pairs' addresses are
`addrs` itself — so `syncUserWords` writes exactly the words the loop synced. -/
theorem overflowWordsOrFaulted_addrs (addrs : List SeLe4n.PAddr) (batches : List ByteArray)
    (pairs : List (SeLe4n.PAddr × UInt64))
    (h : overflowWordsOrFaulted addrs (Architecture.IpcBufferRead.wordRuns addrs) batches
        = .ok pairs) :
    pairs.map Prod.fst = addrs := by
  unfold overflowWordsOrFaulted at h
  split at h
  · rename_i ws hws
    cases h
    have hLen := Architecture.IpcBufferRead.wordsOfBatches_length _ _ _ hws
    rw [Architecture.IpcBufferRead.expandRuns_wordRuns] at hLen
    exact List.map_fst_zip (Nat.le_of_eq hLen.symm)
  · cases h

/-- **Each run crosses as one `ByteArray`, read in order.**  The loop of
`readCallerOverflowWords`, written as a recursion over the runs rather than a
`mapM` over a lambda: a lambda that captures nothing compiles to a closure
built once at module initialisation, and that closure would keep the
`ffi_read_user_words` call — present only in the kernel archive — reachable in
every host executable linking this module. -/
def readWordRuns : List (SeLe4n.PAddr × Nat) → BaseIO (List ByteArray)
  | [] => pure []
  | run :: rest => do
      let batch ← Platform.FFI.ffiReadUserWords run.1.toNat.toUInt64 run.2.toUInt64
      let batches ← readWordRuns rest
      pure (batch :: batches)

/-- **WS-BP BP7.8: the sender's message registers past the fourth, read from
RAM.**  The decode reads a syscall's overflow message registers out of the
caller's IPC buffer (`RegisterDecode.decodeSyscallArgsFromState` →
`IpcBufferRead.ipcBufferReadMr`), and it reads them from `machine.memory` —
the model's memory, which holds no thread's writes.  So before this seam the
kernel on hardware decoded a sender's `MR4` onward as whatever the model held
for that frame (zeroes from the carve), never what the thread wrote.

This reads each word the decode will read — the caller's slots the shared
resolver answers (`IpcBufferRead.callerOverflowAddrs`) — from RAM through the
HAL, and `syncUserWords` writes them into the model in the atomic step, before
the decode runs.  The addresses are resolved on the state read here and the
words written on the state the commit closure receives; those are one state,
because the kernel-entry lock serialises every committing entry and nothing
between the two reads writes an address space.  A syscall that asks for no
overflow reads nothing (`callerOverflowAddrs` answers `[]`).

**`v0.36.47` audit: the words cross in runs, not one per call.**  The slots
are grouped into their contiguous same-page runs (`IpcBufferRead.wordRuns` —
one run for a buffer inside a page, two for one straddling a boundary; on a
116-word message that is one or two `ffiReadUserWords` calls where there were
116), each run crosses as one `ByteArray` of `8 · n` bytes, and the pure
`overflowWordsOrFaulted` decodes the batches back onto the addresses.  The
runs name exactly the addresses the loop read, in order
(`expandRuns_wordRuns`), and never leave a page
(`wordRuns_within_page`), so the HAL's run bound is never the kernel's own
refusal. -/
@[inline] def readCallerOverflowWords (execCore : CoreId) (msgInfo : UInt64) :
    BaseIO (Except UInt64 (List (SeLe4n.PAddr × UInt64))) := do
  let st ← Platform.FFI.getKernelState
  match st.scheduler.currentOnCore execCore with
  | none => pure (.ok [])
  | some tid =>
      let addrs := Architecture.IpcBufferRead.callerOverflowAddrs st tid msgInfo
      let runs := Architecture.IpcBufferRead.wordRuns addrs
      let batches ← readWordRuns runs
      pure (overflowWordsOrFaulted addrs runs batches)

/-- **The context the syscall entry dispatches on, or the outcome it answers
without one.**  An `SVC` handler always publishes its frame before it
dispatches (`rust/sele4n-hal/src/trap.rs`), so an entry the HAL hands no context
is a kernel defect, and the answer is to fail closed: `.faulted` with no state
read, no state committed and no restore staged, on which the trap layer halts
the PE (`halt_after_delivered_syscall_fault`).  Pure, so the host suite runs the
arm no hardware path reaches (`tests/SyscallDispatchSuite.lean`).  Inlined, so
the entry's match on its answer is a match on the HAL's `Option` and no
`Except` is built (WS-CV CV3.1: the HAL's `some` is persistent, so its cell
cannot be reused for one). -/
@[inline] def syscallEntryContextOrFaulted :
    Option Architecture.InFlightContext → Except UInt64 Architecture.InFlightContext
  | some trapped => .ok trapped
  | none => .error Architecture.SyscallOutcome.faulted.tagWord

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
(`x0`-`x5`, errors as the status label on `x1`) is published into this core's
return-frame mailbox (`ffiSyscallReturnFrame` — the `ShootdownOpMailbox`
pattern, since a scalar export return cannot carry six words), and the export's
scalar return is the **outcome tag**: `0` = the mailbox frame is the caller's
return, `1` = the caller blocked and no frame exists for it (RA.C.9; the
staged frame is delivered by the context restore (WS-BP BP7.6)).  The pure dispatch
never takes the `.error` arm (`syscallDispatchFromAbi_total`); the arm is
discharged inertly with an error frame.

**WS-SM SM8.B (PR #861 review round 17): the local half of the reschedule.**
`PriorityInheritance.scheduleLocalSuccessor` runs *inside* the atomic step,
before the diffs are taken, and dispatches a successor when the transition
vacated this core (`localSuccessorNeeded`).  It is the inline dual of
`currentSlotChangeSgis`, which pokes every *remote* core whose `current` slot
changed and excludes the executing core by construction — correctly, since a
core does not interrupt itself, it runs the handler inline.  That inline half
did not exist: every blocking IPC leg cleared the caller's slot and nothing
selected a successor, and the periodic tick provably cannot cover for it
(`timerTickOnCore_cannot_dispatch_vacated_core`).

**Live since WS-BP BP7.6.**  From round 20 until then the dispatch ran behind a
gate on the context-restore seam, because a successor the runtime could not
install into the trap frame would have been attributed the blocked caller's
next syscall, where `currentOnCore = none` fails it *closed*
(`vacatedCore_next_syscall_rejected` below).  The entry now hands the HAL the
context its core resumes (`Platform.FFI.restoreTrapFrame`), so the successor it
dispatches is the thread the hardware runs, and the gate is retired.

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
def syscallDispatchCrossCoreEntry (syscallId : UInt32) : BaseIO UInt64 := do
  let ctx ← Platform.FFI.getKernelLabelingContext
  let execCore ← Concurrency.currentCoreId
  -- **WS-LS LS2.4**: the atomic step is the seam's bracket, run
  -- (`syscallDispatchBracket`): the footprint this entry's own decode declares
  -- covers every write the step makes (`syscallDispatchCrossCoreStep_coversWrites`),
  -- and the executed path is the step and nothing else — the footprint lives on
  -- the ghost lock table, not in a lock word this seam acquires.
  -- **WS-BP BP7.3**: the whole context the caller trapped with is saved into
  -- this core's register bank and the caller's TCB before the step runs, so a
  -- context switch the syscall causes saves every register, not the window.
  -- PR #904 review (`v0.36.41`): on a core a remote deschedule vacated, the
  -- frame goes to the core's resident thread rewound to the `SVC`
  -- (`saveCapturedSyscallFrame`), so the interrupted syscall is re-issued.
  -- The frame is also where the syscall's arguments are read, once: the
  -- message info (`x1`), the six message registers, the IPC buffer (`x6`) and
  -- the fault window (`ELR_EL1`, `SPSR_EL1`, `SP_EL0`, `x30`).  An `SVC`
  -- handler always publishes its frame before it dispatches, so an entry with
  -- none is a kernel defect and fails closed (`syscallEntryContextOrFaulted`):
  -- `.faulted` with no restore staged, on which the trap layer halts the PE.
  let frame ← Platform.FFI.ffiTrapContext
  let trapped ← match syscallEntryContextOrFaulted frame with
    | .ok trapped => pure trapped
    | .error tag => return tag
  let msgInfo := trapped.x1
  -- **WS-BP BP7.8**: the sender's overflow message registers, read from RAM
  -- and synced into the model in the atomic step, so the decode reads what the
  -- thread wrote.
  let words ← match ← readCallerOverflowWords execCore msgInfo with
    | .ok words => pure words
    | .error tag => return tag
  let result ← Platform.FFI.modifyGetKernelState fun st =>
    syscallDispatchCrossCoreBracketedStep ctx execCore syscallId trapped
      (Architecture.IpcBufferRead.syncUserWords
        (Architecture.saveCapturedSyscallFrame st execCore frame) words)
  -- WS-RA (plan §3.3): publish the return frame into this core's mailbox
  -- immediately after the commit — `dispatch_svc` reads it back inside the
  -- same `with_kernel_entry` critical section.  A `blocks` outcome publishes
  -- the zero frame, which the Rust side never reads (the tag below says no
  -- frame exists for the caller — RA.C.9).
  let frame := result.1.mailboxFrame
  Platform.FFI.ffiSyscallReturnFrame frame.x0 frame.x1 frame.x2 frame.x3 frame.x4 frame.x5
  -- **WS-BP BP7.2**: make physical memory agree with the committed address
  -- spaces — the descriptor stores, page zeroings and ASID invalidations the
  -- transition recorded, read and cleared in the atomic step above.  First,
  -- before any core is poked and before the shootdown round: a remote core
  -- must not refill its TLB from a descriptor the model has already cleared,
  -- and a carved page must be zero before anything can name it.
  Platform.FFI.completePhysicalWrites result.2.2.2.2.2.2.1
  Concurrency.fireCrossCoreSgis result.2.1
  -- WS-SM SM7.B: run the shootdown round(s) this commit posted (inert
  -- when the syscall touched no pending-shootdown queue).
  completeShootdownRounds result.2.2.1 result.2.2.2.1 result.2.2.2.2.1.1
    result.2.2.2.2.1.2 execCore
  -- WS-SM SM7.D.1: emit the instruction-cache maintenance this commit
  -- recorded.  Ordered *after* the shootdown round so the translations are
  -- already retired everywhere when the instruction lines fetched through them
  -- are dropped.  The operand is the model's own — the ledger was read and
  -- cleared in the atomic step above, so it is emitted exactly once and never
  -- stranded into the next syscall.  Inert when nothing was owed.
  Platform.FFI.completeIcacheMaintenance result.2.2.2.2.2.1
  -- **WS-BP BP7.9**: a thread whose FP/SIMD values this core holds and which
  -- the committed state no longer runs here has them saved into its TCB first.
  Concurrency.releaseSwitchedFpOwnerOnCore execCore
  -- **WS-BP BP7.4**: install what the committed state runs on this core — the
  -- current thread's saved context and translation, or the idle wait loop —
  -- into the in-flight trap frame, last, after every memory and TLB effect the
  -- commit owed.
  Platform.FFI.restoreTrapFrame result.2.2.2.2.2.2.2.1
  -- **WS-RR RR7.26**: record on the HAL what this commit left running on the
  -- executing core, so `ffi::PER_CPU_CURRENT_THREAD` follows the verified
  -- scheduler rather than lagging it.  The value was read inside the atomic
  -- step above (after `scheduleLocalSuccessor`, so it is the successor
  -- when the syscall vacated the core), and a syscall that left the core
  -- vacated clears the mirror rather than leaving it naming a blocked caller.
  Concurrency.recordCommittedCurrentThreadHw (some (execCore, result.2.2.2.2.2.2.2.2))
  -- WS-RA: the export's scalar return is the outcome tag (0 = the mailbox
  -- frame is the caller's return; 1 = the caller blocked, no frame; 2 = the
  -- caller faulted at the seam, no frame — PR #887 review round 5; since WS-BP
  -- BP7.6 the trap layer resumes the context restore staged, and halts only
  -- when none was).
  pure result.1.tagWord

/-- **WS-SM SM6.A** structural marker: `syscallDispatchCrossCoreEntry` unfolds to
the read-context / read-core / commit-dispatch / fire-SGIs / record-current /
return-encoded driver.  Pins the body shape (atomic `modifyGetKernelState` over
`syscallDispatchFromAbi`, then `fireCrossCoreSgis` of the diff-recovered SGIs,
then — **WS-RR RR7.26** — the HAL current-thread record of the value the same
atomic step read off the committed post-state) so a refactor that drops the SGI
firing, the state commit or the record breaks this marker at elaboration;
combined with `@[export]` (which the Rust extern resolves against) the seam
cannot regress silently. -/
theorem syscallDispatchCrossCoreEntry_def (syscallId : UInt32) :
    syscallDispatchCrossCoreEntry syscallId =
      (do
        let ctx ← Platform.FFI.getKernelLabelingContext
        let execCore ← Concurrency.currentCoreId
        let frame ← Platform.FFI.ffiTrapContext
        let trapped ← match syscallEntryContextOrFaulted frame with
          | .ok trapped => pure trapped
          | .error tag => return tag
        let msgInfo := trapped.x1
        let words ← match ← readCallerOverflowWords execCore msgInfo with
          | .ok words => pure words
          | .error tag => return tag
        let result ← Platform.FFI.modifyGetKernelState fun st =>
          syscallDispatchCrossCoreBracketedStep ctx execCore syscallId trapped
            (Architecture.IpcBufferRead.syncUserWords
              (Architecture.saveCapturedSyscallFrame st execCore frame) words)
        let frame := result.1.mailboxFrame
        Platform.FFI.ffiSyscallReturnFrame frame.x0 frame.x1 frame.x2 frame.x3 frame.x4 frame.x5
        Platform.FFI.completePhysicalWrites result.2.2.2.2.2.2.1
        Concurrency.fireCrossCoreSgis result.2.1
        completeShootdownRounds result.2.2.1 result.2.2.2.1 result.2.2.2.2.1.1
          result.2.2.2.2.1.2 execCore
        Platform.FFI.completeIcacheMaintenance result.2.2.2.2.2.1
        Concurrency.releaseSwitchedFpOwnerOnCore execCore
        Platform.FFI.restoreTrapFrame result.2.2.2.2.2.2.2.1
        Concurrency.recordCommittedCurrentThreadHw (some (execCore, result.2.2.2.2.2.2.2.2))
        pure result.1.tagWord) := rfl

/-- **WS-SM SM8.B** (PR #861 review rounds 39/41): the gating argument's
"rejection, not misattribution" half, as a theorem rather than as prose.

The gate that stood above until WS-BP BP7.6 was justified by a claim about what
happens *next*: a transition that leaves `currentOnCore execCore = none` has the
caller's next syscall **rejected** rather than attributed to some other thread.
That claim was challenged twice on the review — both times asserting the
opposite, that the next syscall silently falls back to `bootCoreId` — so it is
stated here at the entry, over the state the entry commits.  With the dispatch
live it covers a core whose run queue held no successor.

The fallback the challenge describes belonged to a state-scanning
executing-core resolver that IPC-8 (`v0.36.46`) deleted: the core is now
threaded from this entry through the dispatcher, so no arm re-derives it and no
fallback exists anywhere.  Resolution happens first, in
`syscallDispatchFromAbi`, and it has no fallback: no current thread on the issuing core means `.illegalState` with the
state returned unmodified.  A change that gave the entry a fallback core — the
outcome the challenge fears — breaks this theorem. -/
theorem vacatedCore_next_syscall_rejected
    (ctx : LabelingContext) (execCore : CoreId)
    (pre post : SystemState)
    (syscallId : UInt32)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64)
    (hVacated :
      (PriorityInheritance.scheduleLocalSuccessor pre post execCore).scheduler.currentOnCore
        execCore = none) :
    Platform.FFI.syscallDispatchFromAbi ctx execCore syscallId x0 x1 x2 x3 x4 x5
        ipcBufferAddr elr spsr spEl0 x30
        (PriorityInheritance.scheduleLocalSuccessor pre post execCore)
      = Except.ok (.returns (Architecture.errorFrame .illegalState),
                   PriorityInheritance.scheduleLocalSuccessor pre post execCore) :=
  Platform.FFI.syscallDispatchFromAbi_illegalState_when_no_current ctx execCore syscallId
    x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 _ hVacated

/-- **WS-LS LS2.4: the raw suspend seam's bracket.**

The footprint is the unified suspend footprint (`unifiedLockSetForSyscall`,
WS-RR RR7.10: the resolver takes operands rather than two thread ids, because
an IPC arm's footprint names an endpoint and not a thread; a suspend is
thread-directed, so it supplies exactly that) for the thread on the executing
core — or, on a core running nothing, the victim itself — suspending `vtid`.
The step is the suspend on the executing core followed by the executing core's
local successor, with the pre-state reads captured first (KSC-1: a remote core
is poked when the step raised its reschedule flag), and the proof field is
`suspendSeamAction_coversWrites` (WS-LS LS2.3).

**WS-SM SM8.B (review round 17)**: the local reschedule is *self-disabling* on
this path — `suspendThreadOnCore` runs its own scheduling point
(`suspendRescheduleOnCore`), so where it dispatched a successor the post-state
slot is populated and `localSuccessorNeeded` is false
(`scheduleLocalSuccessor_of_post_running`).  The two mechanisms cannot both
dispatch.  It is applied anyway rather than reasoned away, so that the entry
seams do not disagree about who is responsible for a vacated core. -/
@[inline] def suspendThreadBracket (vtid : SeLe4n.ValidThreadId) (execCore : CoreId) :
    BracketSpec (UInt32 × List (CoreId × SgiKind)) where
  declared := fun s =>
    unifiedLockSetForSyscall .tcbSuspend
      (.ofThreadTarget ((s.scheduler.currentOnCore execCore).getD vtid.val) vtid.val)
      execCore s
  step := fun s =>
    let caller? := s.scheduler.currentOnCore execCore
    let pending0 := reschedulePendingSnapshot s
    match Lifecycle.Suspend.suspendThreadOnCore s vtid execCore with
    | Except.ok (s', _) =>
        let s'' := PriorityInheritance.scheduleLocalSuccessorFrom caller? s' execCore
        (((0 : UInt32), rescheduleSgisFromFlags pending0 s''.scheduler.reschedulePending), s'')
    | Except.error e =>
        ((Platform.FFI.KernelError.toUInt32 e, ([] : List (CoreId × SgiKind))), s)
  inv := fun _ => True
  covers := by
    intro s S _ hS
    have h := suspendSeamAction_coversWrites _ vtid execCore s S hS
    cases hStep : Lifecycle.Suspend.suspendThreadOnCore s vtid execCore with
    | ok p =>
        obtain ⟨s', sgi⟩ := p
        simp only [hStep] at h ⊢
        exact h
    | error e =>
        simp only [hStep] at h ⊢
        exact h

/-- **WS-LS LS2.4**: what the suspend seam executes on a valid, non-idle
thread id is the step — `rfl`. -/
theorem suspendThreadBracket_run (vtid : SeLe4n.ValidThreadId) (execCore : CoreId)
    (s : SystemState) :
    (suspendThreadBracket vtid execCore).run s =
      (match Lifecycle.Suspend.suspendThreadOnCore s vtid execCore with
       | Except.ok (s', _) =>
           let s'' := PriorityInheritance.scheduleLocalSuccessorFrom
             (s.scheduler.currentOnCore execCore) s' execCore
           (((0 : UInt32), rescheduleSgisFromFlags (reschedulePendingSnapshot s)
               s''.scheduler.reschedulePending), s'')
       | Except.error e =>
           ((Platform.FFI.KernelError.toUInt32 e, ([] : List (CoreId × SgiKind))), s)) := rfl

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
exactly as `suspendThreadInner`, and (PR #889 review round 8) so are the
kernel-reserved **idle thread ids**: the capability chokepoint refuses a
capability naming an idle object (`syscallResolveCap_ok_not_reserved`), but
this seam takes a raw id and no capability, so without its own check an
in-kernel caller could hand it `idleThreadId c` and remove core `c`'s only
guaranteed runnable thread — `suspendThreadOnCore` would dequeue the idle
TCB like any other.  The refusal is `.invalidArgument`, the sentinel's
discriminant: the id is outside the set this seam serves.  The whole step
is the pure `suspendThreadCrossCoreStep`, and
`suspendThreadCrossCoreStep_idle_refused` proves the refusal commits
nothing.

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
def suspendThreadCrossCoreStep (tid : UInt64) (execCore : CoreId) (st : SystemState) :
    (UInt32 × List (CoreId × SgiKind)) × SystemState :=
    let threadId := SeLe4n.ThreadId.ofNat tid.toNat
    match threadId.toValid? with
    | none =>
        ((Platform.FFI.KernelError.toUInt32 .invalidArgument,
          ([] : List (CoreId × SgiKind))), st)
    | some vtid =>
      -- PR #889 review round 8: a reserved idle thread id is refused before
      -- the transition runs — see the entry's docstring.
      if SeLe4n.Kernel.isIdleThreadId vtid.val then
        ((Platform.FFI.KernelError.toUInt32 .invalidArgument,
          ([] : List (CoreId × SgiKind))), st)
      else
        -- **WS-LS LS2.4**: the transition is the seam's bracket, run.  The
        -- footprint the bracket declares is the unified suspend footprint for
        -- the thread on the executing core suspending `vtid`, and
        -- `suspendSeamAction_coversWrites` is its `covers` field; the executed
        -- path is the step alone.  (The WS-SM SM3.C.9 word-level `withLockSet`
        -- this replaces made `suspend_thread_cross_core` the first live export
        -- to acquire a declared footprint; the footprint is now a proof
        -- obligation the record discharges, not a runtime acquire.)
        (suspendThreadBracket vtid execCore).run st

/-- PR #889 review round 8: the raw suspend seam **refuses a reserved idle
    thread id and commits nothing** — the status is the sentinel's
    `.invalidArgument`, no SGI is derived, and the state is returned
    untouched.  The capability chokepoint keeps user authority off the idle
    objects; this is the same guarantee for the one live seam that takes a
    raw id. -/
theorem suspendThreadCrossCoreStep_idle_refused (tid : UInt64) (execCore : CoreId)
    (st : SystemState)
    (hIdle : SeLe4n.Kernel.isIdleThreadId (SeLe4n.ThreadId.ofNat tid.toNat) = true) :
    suspendThreadCrossCoreStep tid execCore st =
      ((Platform.FFI.KernelError.toUInt32 .invalidArgument,
        ([] : List (CoreId × SgiKind))), st) := by
  unfold suspendThreadCrossCoreStep
  dsimp only
  split
  · rfl
  · rename_i vtid hSome
    rw [SeLe4n.ThreadId.toValid?_some_val_eq _ _ hSome, hIdle]
    rfl

/-- PR #889 review round 8: the sentinel is refused the same way. -/
theorem suspendThreadCrossCoreStep_sentinel_refused (execCore : CoreId) (st : SystemState) :
    suspendThreadCrossCoreStep 0 execCore st =
      ((Platform.FFI.KernelError.toUInt32 .invalidArgument,
        ([] : List (CoreId × SgiKind))), st) := by
  rfl

/-- The cross-core suspend step with both hardware ledgers drained
(`v0.36.39`): `suspendThreadCrossCoreStep`, then the recorded physical writes
and instruction-cache operands read out and cleared in the same atomic step.
Named rather than written as a lambda at the seam, so the seam still hands
`modifyGetKernelState` a named pure step and a refused suspend is refused here
exactly as there (`suspendThreadCrossCoreDrainedStep_idle_refused`). -/
def suspendThreadCrossCoreDrainedStep (tid : UInt64) (execCore : CoreId)
    (st : SystemState) :
    ((UInt32 × List (CoreId × SgiKind)) ×
      (List Architecture.PhysicalWrite × List Architecture.ICacheInvalidation))
      × SystemState :=
  let (out, st') := suspendThreadCrossCoreStep tid execCore st
  ((out, (st'.pendingPhysicalWrites, st'.pendingIcacheMaintenance)),
    Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites st'))

/-- The drained step refuses an idle thread as the bare step does, and the
state it commits is the bare step's with both ledgers cleared — the refusal
recorded nothing, so the drain performs nothing. -/
theorem suspendThreadCrossCoreDrainedStep_idle_refused (tid : UInt64)
    (execCore : CoreId) (st : SystemState)
    (hIdle : SeLe4n.Kernel.isIdleThreadId (SeLe4n.ThreadId.ofNat tid.toNat) = true) :
    (suspendThreadCrossCoreDrainedStep tid execCore st).1.1 =
      (Platform.FFI.KernelError.toUInt32 .invalidArgument,
        ([] : List (CoreId × SgiKind))) := by
  unfold suspendThreadCrossCoreDrainedStep
  rw [suspendThreadCrossCoreStep_idle_refused tid execCore st hIdle]

/-- The raw cross-core suspend seam.  **Every state-committing entry drains
both hardware ledgers** (`v0.36.39`), this one included: the drained step
reads and clears them atomically, the physical writes are performed before any
core is poked and the instruction-cache operands after the SGIs, as the syscall
and fault seams do, so a write a later transition records on this path can
neither be skipped nor be performed late by some other core's entry. -/
@[export suspend_thread_cross_core]
def suspendThreadCrossCoreEntry (tid : UInt64) : BaseIO UInt32 := do
  let execCore ← Concurrency.currentCoreId
  let result ← Platform.FFI.modifyGetKernelState
    (suspendThreadCrossCoreDrainedStep tid execCore)
  Platform.FFI.completePhysicalWrites result.2.1
  Concurrency.fireCrossCoreSgis result.1.2
  Platform.FFI.completeIcacheMaintenance result.2.2
  pure result.1.1

-- ============================================================================
-- WS-SM SM9.B.9 — the refusal write does not disturb the runtime seam
-- ============================================================================

/-- WS-SM SM9.B.9: **the cross-core SGIs are unchanged by a refusal write.**

The runtime seam commits the dispatch's post-state and then fires an SGI at each
remote core whose reschedule flag the step raised (KSC-1).  SM9.B adds a field to
that post-state on the error path, and this is the statement that the addition is
invisible to the seam: the refusal write leaves the scheduler, flags included,
alone, so the pokes the runtime sends are exactly the pokes it sent before the
ledger existed.

Stated here rather than at the seam because this is where the two meet — "the
write only touches one field" is a property of `recordSyscallRefusal`, while
"the seam reads only the flags" is a property of the seam, and only their
conjunction says the runtime is unaffected. -/
theorem rescheduleSgisFromFlags_recordSyscallRefusal_eq
    (ctx : LabelingContext) (executingCore : CoreId) (syscallId : UInt32)
    (tid : SeLe4n.ThreadId) (ke : KernelError) (x0 : UInt64)
    (pending : Vector Bool Concurrency.numCores) (post : SystemState) :
    rescheduleSgisFromFlags pending
        (Platform.FFI.recordSyscallRefusal ctx executingCore syscallId tid ke x0
          post).scheduler.reschedulePending
      = rescheduleSgisFromFlags pending post.scheduler.reschedulePending := by
  rw [Platform.FFI.recordSyscallRefusal_scheduler_eq]

end SeLe4n.Kernel
