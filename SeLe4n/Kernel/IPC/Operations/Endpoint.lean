-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-! # AN3-E.5 (IPC-M09) — `cleanupPreReceiveDonation` co-location banner.

**DO NOT MOVE `cleanupPreReceiveDonation` or `cleanupPreReceiveDonationChecked`
out of this file.**

The donation primitive graph currently flows:

  `Donation.lean` → `DualQueue/Transport.lean` → `DualQueue/Core.lean`
                 → `Operations` (hub) → `Operations/Endpoint.lean` (this file)

If the cleanup helpers are moved back to `Donation.lean`, the hub re-export
constructed in AN3-A reintroduces the `Operations -> Donation -> Transport
-> Core -> Operations` import cycle that AI4-A (v0.27.10 / M-01) closed by
relocating the functions here in the first place.  The compile-time guard
below (`an3e_cleanup_colocation_guard`) re-elaborates `cleanupPreReceiveDonation`
through its fully-qualified name in this file's namespace so that any
future relocation that bypasses this banner fails the build immediately.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId)

/-! # AK1-J (I-L1..I-L6, IPC INFO): IPC LOW-tier batch documentation

This batched docblock consolidates the LOW-tier IPC findings from the
v0.29.0 audit (AK1-J in the WS-AK plan). Each bullet references the
finding ID, the affected site, and the remediation applied.

- **I-L1 — `donateSchedContext` unproven-unreachable defensive branch.**
  `IPC/Operations/Donation.lean:80–82` routes through an error-propagating
  call to `donateSchedContext` which itself has an internal `| .error _ =>`
  branch that is unreachable under `donationOwnerValid` +
  `boundThreadConsistent`. The error propagation added in AH2-A preserves
  operational correctness; a formal unreachability lemma is tracked as
  part of the AK10 proof-engineering closure (see
  `cleanupPreReceiveDonationChecked_never_errors_under_ipcInvariantFull`
  in `IPC/Invariant/Defs.lean` for the analogous pattern).

- **I-L2 — `timeoutAwareReceive` stale `.timedOut` reachability.**
  `IPC/Operations/Timeout.lean:114–128`. The `tcb.timedOut ∧ ipcState =
  .ready` check can report a stale timeout if the scheduler ticked twice
  before the thread was rescheduled. Under the `timedOutInvariant` —
  every timedOut=true TCB must have `ipcState = .ready` and an empty
  `pendingMessage` — this is a correct fixed-point and the thread will
  observe the timeout deterministically on the next receive attempt.
  No behavior change required.

- **I-L3 — `popHead_returns_head` external composition.**
  `endpointQueuePopHead_returns_head` (defined in `IPC/Invariant/Defs.lean`) is
  referenced across more than one caller — `endpointSendDualWithCaps`
  (DualQueue/WithCaps.lean) among them — without a local composition wrapper.
  (The note named `endpointCallWithDonation` as the other until `v0.35.192`
  deleted it; the live Call path reads the same theorem through
  `endpointCallCrossCoreDispatch`.) The theorem is non-fragile (invariant-independent)
  so inlining its composition is not required; cross-file use is
  idiomatic.

- **I-L4 — Reply-path badge handling deferred-work marker.** Reply messages do not carry
  a badge per seL4 semantics (the badge is a property of the endpoint
  capability used on send, not reply). No badge field is stored on the
  reply path; the `IpcMessage.badge` field is `none` in all reply paths.
  Closed as matching seL4 spec — no deferred-work marker required.

- **I-L5 — `notificationSignal.Badge.bor` unbounded-Nat accumulation.**
  `IPC/Operations/Endpoint.lean:notificationSignal` uses `Badge.bor`
  for pending-badge accumulation. `Badge.bor` is defined in
  `Prelude.lean` and preserves the 64-bit mask via the
  `bor_valid` theorem (see AC3/I-04). Hardware-binding (AN9) masks
  the result to `2^64 - 1` at the platform boundary. Safety documented
  at the `notificationSignal` definition site.

- **I-L6 — `returnDonatedSchedContext` leaves client in replenish queue.**
  After a SchedContext is returned to the original owner, the client's
  `isActive := false` field is reset, causing the replenish-queue
  processor (`SchedContext/ReplenishQueue.lean:popDue`) to filter it out
  naturally. No explicit removal is required; this is benign.

- **IPC INFO — `ipcInvariant` rename to `notificationInvariantSystem`.**
  Deferred to AK10 as part of broader naming cleanup. The current name
  is correct in scope (notification well-formedness), but "notification
  invariant" would be clearer. Deprecation shim deferred to minimize
  cross-subsystem churn in the v1.0 release.

- **IPC INFO — `.endpointQueueEmpty` error misuse at AH2-G site.**
  `IPC/Operations/Timeout.lean:timeoutAwareReceive:138` returns
  `.endpointQueueEmpty` for a missing `pendingMessage` on a non-timed-out
  receive. Semantically this is "IPC state violation" rather than an
  empty queue; `.invalidIpcState` would be more accurate. Replaced via a
  cross-reference (no error-variant rename in AK1 scope — replaced in
  AK10 documentation closure).
-/

/-- WS-G4/F-P02: O(1) amortized remove via RunQueue. -/
def removeRunnable (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  { st with
      scheduler := (st.scheduler.setRunQueueOnCore bootCoreId
          ((st.scheduler.runQueueOnCore bootCoreId).remove tid)).setCurrentOnCore bootCoreId
          (if (st.scheduler.currentOnCore bootCoreId) = some tid then none
            else (st.scheduler.currentOnCore bootCoreId))
  }

/-- WS-SM SM8.B (PR #861 review round 17): **does core `c` hold this thread at
all** — in its run queue, or as its current thread?

The sweep's guard, and therefore the sweep's write set.  Reading it from the
pre-state is what lets the destroy path declare the cores it touches instead of
declaring all of them. -/
def threadOccupiesCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : SeLe4n.Kernel.Concurrency.CoreId) : Bool :=
  (st.scheduler.runQueueOnCore c).contains tid
    || (st.scheduler.currentOnCore c == some tid)

/-- WS-SM SM8.B: one core's share of the destroy sweep — drop the thread from
that core's run queue and clear its current slot if it holds it.

**Write-set-honest** (PR #861 review round 17): a core that holds the thread
neither way is left *literally* untouched, rather than rewritten with values
equal to the ones already there.  The unguarded form wrote
`setRunQueueOnCore c ((runQueueOnCore c).remove tid)` at every core, and while
that removal changes nothing a non-member can observe
(`RunQueue.remove_content_of_not_mem`), it is not *syntactically* the old queue
— so the sweep's write set could only ever be bounded by `allCores`, and
`.lifecycleRetype` inherited that.

Same discipline as the v0.32.65 cancellation sweeps (insert-only-on-change).
Proving the unguarded form inert instead would need "erasing an absent key from
a Robin Hood table is the identity", a real theorem about backward-shift
deletion that is not on file and that nothing else wants. -/
def removeRunnableStepOnCore (tid : SeLe4n.ThreadId) (st : SystemState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) : SystemState :=
  if threadOccupiesCore st tid c then
    { st with
        scheduler := (st.scheduler.setRunQueueOnCore c
            ((st.scheduler.runQueueOnCore c).remove tid)).setCurrentOnCore c
            (if (st.scheduler.currentOnCore c) = some tid then none
              else (st.scheduler.currentOnCore c)) }
  else st

/-- WS-SM SM8.B: the guard is exactly "this core holds the thread", so an
unoccupied core is framed by the step at it. -/
@[simp] theorem removeRunnableStepOnCore_of_not_occupies (tid : SeLe4n.ThreadId)
    (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId)
    (h : threadOccupiesCore st tid c = false) :
    removeRunnableStepOnCore tid st c = st := by
  unfold removeRunnableStepOnCore
  simp [h]

/-- WS-SM SM8.B: a step at core `d` does not change whether core `c` holds the
thread — occupancy reads only `c`'s own two slots, and a step writes only `d`'s.
This is what lets the sweep's guard be read from the pre-state even though the
fold evaluates it against the accumulator. -/
theorem removeRunnableStepOnCore_threadOccupiesCore_ne (tid : SeLe4n.ThreadId)
    (st : SystemState) (c d : SeLe4n.Kernel.Concurrency.CoreId) (hne : d ≠ c) :
    threadOccupiesCore (removeRunnableStepOnCore tid st d) tid c
      = threadOccupiesCore st tid c := by
  unfold removeRunnableStepOnCore threadOccupiesCore
  split
  · simp [SchedulerState.setCurrentOnCore_runQueueOnCore,
      SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hne,
      SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ hne,
      SchedulerState.setRunQueueOnCore_currentOnCore]
  · rfl

/-- WS-SM SM8.B: **remove a thread from every core's scheduler state.**

`removeRunnable` clears the boot core alone, which is right for a thread that is
merely blocking — it blocks where it runs — and wrong for a thread that is being
**destroyed**.  A retype of a live TCB ran the boot-core form
(`cleanupTcbReferences`), so retyping a thread queued on any other core left a
run-queue entry whose object no longer resolves to a `.tcb`; `chooseBestRunnableBy`
then failed that core's *entire* selection scan, permanently, because nothing
removes the entry on the failure path.  Found in PR #861 review round 15.

A destroy has no home core to speak of — the object is going away — so this
sweeps `allCores` rather than resolving one.  That also covers the SM6.E
review-4 divergence, where a thread is current on a core that is not the one
`determineTargetCore` names. -/
def removeRunnableFromAllCores (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  SeLe4n.Kernel.Concurrency.allCores.foldl (removeRunnableStepOnCore tid) st

/-- WS-SM SM8.B: a step at another core leaves this core's run queue alone, so a
sweep over a list omitting `c` frames `c`. -/
theorem foldl_removeRunnableStepOnCore_runQueueOnCore_not_mem
    (cs : List SeLe4n.Kernel.Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    ∀ st : SystemState, c ∉ cs →
      (cs.foldl (removeRunnableStepOnCore tid) st).scheduler.runQueueOnCore c
        = st.scheduler.runQueueOnCore c := by
  induction cs with
  | nil => intro st _; rfl
  | cons d ds ih =>
    intro st hc
    have hne : d ≠ c := fun h => hc (by simp [h])
    have hd : c ∉ ds := fun h => hc (by simp [h])
    rw [List.foldl_cons, ih _ hd]
    unfold removeRunnableStepOnCore
    split
    · simp [SchedulerState.setCurrentOnCore_runQueueOnCore,
        SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hne]
    · rfl

/-- WS-SM SM8.B: and the step at `c` itself removes the thread — so over a
duplicate-free list containing `c`, `c`'s queue comes back without it. -/
theorem foldl_removeRunnableStepOnCore_runQueueOnCore_mem
    (cs : List SeLe4n.Kernel.Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    ∀ st : SystemState, c ∈ cs → cs.Nodup →
      (cs.foldl (removeRunnableStepOnCore tid) st).scheduler.runQueueOnCore c
        = if threadOccupiesCore st tid c then (st.scheduler.runQueueOnCore c).remove tid
          else st.scheduler.runQueueOnCore c := by
  induction cs with
  | nil => intro _ hc _; exact absurd hc (by simp)
  | cons d ds ih =>
    intro st hc hnd
    rcases List.mem_cons.mp hc with hEq | hIn
    · subst hEq
      rw [List.foldl_cons,
        foldl_removeRunnableStepOnCore_runQueueOnCore_not_mem ds tid c _
          (List.nodup_cons.mp hnd).1]
      by_cases hOcc : threadOccupiesCore st tid c = true
      · rw [removeRunnableStepOnCore, if_pos hOcc, if_pos hOcc]
        simp [SchedulerState.setCurrentOnCore_runQueueOnCore,
          SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
      · rw [removeRunnableStepOnCore, if_neg hOcc, if_neg hOcc]
    · have hne : d ≠ c := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hIn)
      rw [List.foldl_cons, ih _ hIn (List.nodup_cons.mp hnd).2,
        removeRunnableStepOnCore_threadOccupiesCore_ne tid st c d hne]
      by_cases hOccD : threadOccupiesCore st tid d = true
      · rw [removeRunnableStepOnCore, if_pos hOccD]
        simp [SchedulerState.setCurrentOnCore_runQueueOnCore,
          SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hne]
      · rw [removeRunnableStepOnCore, if_neg hOccD]

/-- WS-SM SM8.B: the `current`-slot analogue of the two run-queue fold lemmas —
a step at another core leaves this core's current slot alone, and the step at
`c` itself clears it exactly when it held the thread. -/
theorem foldl_removeRunnableStepOnCore_currentOnCore
    (cs : List SeLe4n.Kernel.Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    ∀ st : SystemState, c ∈ cs → cs.Nodup →
      (cs.foldl (removeRunnableStepOnCore tid) st).scheduler.currentOnCore c
        = if st.scheduler.currentOnCore c = some tid then none
          else st.scheduler.currentOnCore c := by
  have hFrame : ∀ (ds : List SeLe4n.Kernel.Concurrency.CoreId) (st : SystemState),
      c ∉ ds →
      (ds.foldl (removeRunnableStepOnCore tid) st).scheduler.currentOnCore c
        = st.scheduler.currentOnCore c := by
    intro ds
    induction ds with
    | nil => intro _ _; rfl
    | cons d dd ih =>
      intro st hc
      have hne : d ≠ c := fun h => hc (by simp [h])
      have hd : c ∉ dd := fun h => hc (by simp [h])
      rw [List.foldl_cons, ih _ hd]
      unfold removeRunnableStepOnCore
      split
      · simp [SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ hne,
          SchedulerState.setRunQueueOnCore_currentOnCore]
      · rfl
  induction cs with
  | nil => intro _ hc _; exact absurd hc (by simp)
  | cons d ds ih =>
    intro st hc hnd
    rcases List.mem_cons.mp hc with hEq | hIn
    · subst hEq
      rw [List.foldl_cons, hFrame ds _ (List.nodup_cons.mp hnd).1]
      by_cases hOcc : threadOccupiesCore st tid c = true
      · rw [removeRunnableStepOnCore, if_pos hOcc]
        simp [SchedulerState.setCurrentOnCore_currentOnCore_self]
      · rw [removeRunnableStepOnCore, if_neg hOcc]
        -- Not occupied means the current slot does not hold `tid` either, so
        -- the conditional on the right collapses to the identity.
        have : st.scheduler.currentOnCore c ≠ some tid := by
          intro hEq'
          exact hOcc (by simp [threadOccupiesCore, hEq'])
        simp [this]
    · have hne : d ≠ c := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hIn)
      rw [List.foldl_cons, ih _ hIn (List.nodup_cons.mp hnd).2]
      by_cases hOccD : threadOccupiesCore st tid d = true
      · rw [removeRunnableStepOnCore, if_pos hOccD]
        simp [SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ hne,
          SchedulerState.setRunQueueOnCore_currentOnCore]
      · rw [removeRunnableStepOnCore, if_neg hOccD]

/-- WS-SM SM8.B: the sweep's closed form — **every** core's run queue comes back
with the thread removed. -/
@[simp] theorem removeRunnableFromAllCores_runQueueOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (removeRunnableFromAllCores st tid).scheduler.runQueueOnCore c
      = if threadOccupiesCore st tid c then (st.scheduler.runQueueOnCore c).remove tid
        else st.scheduler.runQueueOnCore c :=
  foldl_removeRunnableStepOnCore_runQueueOnCore_mem _ tid c st
    (SeLe4n.Kernel.Concurrency.mem_allCores c)
    SeLe4n.Kernel.Concurrency.allCores_nodup

/-- WS-SM SM8.B: the sweep's closed form on the **current** slot — a core running
the thread is cleared, every other core keeps whatever it was running.

The companion to the run-queue form, and the fact the round-16 SGI fix rests on:
a core whose `current` held the destroyed thread has a *changed* slot in the
post-state, which is what `currentSlotChangeSgis` keys the remote poke on. -/
@[simp] theorem removeRunnableFromAllCores_currentOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (removeRunnableFromAllCores st tid).scheduler.currentOnCore c
      = if st.scheduler.currentOnCore c = some tid then none
        else st.scheduler.currentOnCore c := by
  unfold removeRunnableFromAllCores
  exact foldl_removeRunnableStepOnCore_currentOnCore _ tid c st
    (SeLe4n.Kernel.Concurrency.mem_allCores c)
    SeLe4n.Kernel.Concurrency.allCores_nodup

/-- WS-SM SM8.B: and so the destroyed thread is in no core's run queue. -/
theorem removeRunnableFromAllCores_not_mem (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    ¬ (tid ∈ (removeRunnableFromAllCores st tid).scheduler.runQueueOnCore c) := by
  rw [removeRunnableFromAllCores_runQueueOnCore]
  -- Occupied: the removal takes it out.  Unoccupied: it was never there — the
  -- guard's `false` gives exactly that, since occupancy includes queue
  -- membership.
  split
  · exact RunQueue.not_mem_remove_self _ _
  · next hOcc =>
    intro hMem
    exact hOcc (by simp [threadOccupiesCore, RunQueue.mem_iff_contains.mp hMem])

/-- WS-SM SM8.B: the sweep only ever removes — it never introduces a thread. -/
theorem removeRunnableFromAllCores_flat_subset (st : SystemState)
    (tid x : SeLe4n.ThreadId) (c : SeLe4n.Kernel.Concurrency.CoreId)
    (h : x ∈ ((removeRunnableFromAllCores st tid).scheduler.runQueueOnCore c).flat) :
    x ∈ (st.scheduler.runQueueOnCore c).flat := by
  rw [removeRunnableFromAllCores_runQueueOnCore] at h
  split at h
  · exact (List.mem_filter.mp h).1
  · exact h

/-- WS-SM SM8.B: the sweep is scheduler-only — every other field frames, by
induction over the core list rather than by reducing it. -/
theorem foldl_removeRunnableStepOnCore_frame
    (cs : List SeLe4n.Kernel.Concurrency.CoreId) (tid : SeLe4n.ThreadId) :
    ∀ st : SystemState,
      (cs.foldl (removeRunnableStepOnCore tid) st).objects = st.objects
      ∧ (cs.foldl (removeRunnableStepOnCore tid) st).lifecycle = st.lifecycle
      ∧ (cs.foldl (removeRunnableStepOnCore tid) st).machine = st.machine
      ∧ (cs.foldl (removeRunnableStepOnCore tid) st).tlbShootdown = st.tlbShootdown := by
  induction cs with
  | nil => intro _; exact ⟨rfl, rfl, rfl, rfl⟩
  | cons d ds ih =>
    intro st
    obtain ⟨h1, h2, h3, h4⟩ := ih (removeRunnableStepOnCore tid st d)
    -- The step frames all four fields in *both* guard branches: the taken one
    -- writes only `scheduler`, the untaken one writes nothing.
    have hStep : ∀ (s : SystemState) (e : SeLe4n.Kernel.Concurrency.CoreId),
        (removeRunnableStepOnCore tid s e).objects = s.objects
        ∧ (removeRunnableStepOnCore tid s e).lifecycle = s.lifecycle
        ∧ (removeRunnableStepOnCore tid s e).machine = s.machine
        ∧ (removeRunnableStepOnCore tid s e).tlbShootdown = s.tlbShootdown := by
      intro s e
      unfold removeRunnableStepOnCore
      split <;> exact ⟨rfl, rfl, rfl, rfl⟩
    obtain ⟨g1, g2, g3, g4⟩ := hStep st d
    exact ⟨by rw [List.foldl_cons, h1, g1], by rw [List.foldl_cons, h2, g2],
           by rw [List.foldl_cons, h3, g3], by rw [List.foldl_cons, h4, g4]⟩

/-- WS-SM SM8.B (PR #861 review round 35): the sweep leaves every core's **domain**
slots alone.

The three domain slots complete the six-field observable set: the sweep's step
writes only `runQueueOnCore` and `currentOnCore`, in the taken branch, and
nothing at all in the untaken one.  Needed because `observableSlotsConfinedToCores`
quantifies over all six, and the `.lifecycleRetype` write set is the first
consumer to ask the sweep for them. -/
theorem foldl_removeRunnableStepOnCore_domain_frame
    (cs : List SeLe4n.Kernel.Concurrency.CoreId) (tid : SeLe4n.ThreadId) :
    ∀ (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId),
      (cs.foldl (removeRunnableStepOnCore tid) st).scheduler.activeDomainOnCore c
        = st.scheduler.activeDomainOnCore c
      ∧ (cs.foldl (removeRunnableStepOnCore tid) st).scheduler.domainTimeRemainingOnCore c
        = st.scheduler.domainTimeRemainingOnCore c
      ∧ (cs.foldl (removeRunnableStepOnCore tid) st).scheduler.domainScheduleIndexOnCore c
        = st.scheduler.domainScheduleIndexOnCore c := by
  induction cs with
  | nil => intro _ _; exact ⟨rfl, rfl, rfl⟩
  | cons d ds ih =>
    intro st c
    obtain ⟨h1, h2, h3⟩ := ih (removeRunnableStepOnCore tid st d) c
    have hStep : ∀ (s : SystemState) (e : SeLe4n.Kernel.Concurrency.CoreId),
        (removeRunnableStepOnCore tid s e).scheduler.activeDomainOnCore c
          = s.scheduler.activeDomainOnCore c
        ∧ (removeRunnableStepOnCore tid s e).scheduler.domainTimeRemainingOnCore c
          = s.scheduler.domainTimeRemainingOnCore c
        ∧ (removeRunnableStepOnCore tid s e).scheduler.domainScheduleIndexOnCore c
          = s.scheduler.domainScheduleIndexOnCore c := by
      intro s e
      unfold removeRunnableStepOnCore
      split <;> simp
    obtain ⟨g1, g2, g3⟩ := hStep st d
    exact ⟨by rw [List.foldl_cons, h1, g1], by rw [List.foldl_cons, h2, g2],
           by rw [List.foldl_cons, h3, g3]⟩

/-- **`v0.35.165`: the sweep leaves every core's REPLENISH queue alone.**

The seventh scheduler slot, and the one the SM5.H affinity invariant reads.  The
sweep's step writes a run queue and a current slot in its taken branch and
nothing in its untaken one, so a destroy path that removes a thread from every
core's run queue moves no scheduling context's eligibility entry — which is what
lets `cleanupTcbReferences` carry `replenishQueueAffinityConsistent_smp`. -/
theorem foldl_removeRunnableStepOnCore_replenishQueueOnCore
    (cs : List SeLe4n.Kernel.Concurrency.CoreId) (tid : SeLe4n.ThreadId) :
    ∀ (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId),
      (cs.foldl (removeRunnableStepOnCore tid) st).scheduler.replenishQueueOnCore c
        = st.scheduler.replenishQueueOnCore c := by
  induction cs with
  | nil => intro _ _; rfl
  | cons d ds ih =>
    intro st c
    have hStep : ∀ (s : SystemState) (e : SeLe4n.Kernel.Concurrency.CoreId),
        (removeRunnableStepOnCore tid s e).scheduler.replenishQueueOnCore c
          = s.scheduler.replenishQueueOnCore c := by
      intro s e
      unfold removeRunnableStepOnCore
      split <;> simp
    rw [List.foldl_cons, ih (removeRunnableStepOnCore tid st d) c, hStep st d]

@[simp] theorem removeRunnableFromAllCores_replenishQueueOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (removeRunnableFromAllCores st tid).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c :=
  foldl_removeRunnableStepOnCore_replenishQueueOnCore _ tid st c

@[simp] theorem removeRunnableFromAllCores_activeDomainOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (removeRunnableFromAllCores st tid).scheduler.activeDomainOnCore c
      = st.scheduler.activeDomainOnCore c :=
  (foldl_removeRunnableStepOnCore_domain_frame _ tid st c).1

@[simp] theorem removeRunnableFromAllCores_domainTimeRemainingOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (removeRunnableFromAllCores st tid).scheduler.domainTimeRemainingOnCore c
      = st.scheduler.domainTimeRemainingOnCore c :=
  (foldl_removeRunnableStepOnCore_domain_frame _ tid st c).2.1

@[simp] theorem removeRunnableFromAllCores_domainScheduleIndexOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : SeLe4n.Kernel.Concurrency.CoreId) :
    (removeRunnableFromAllCores st tid).scheduler.domainScheduleIndexOnCore c
      = st.scheduler.domainScheduleIndexOnCore c :=
  (foldl_removeRunnableStepOnCore_domain_frame _ tid st c).2.2

@[simp] theorem removeRunnableFromAllCores_objects (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (removeRunnableFromAllCores st tid).objects = st.objects :=
  (foldl_removeRunnableStepOnCore_frame _ tid st).1

@[simp] theorem removeRunnableFromAllCores_lifecycle (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (removeRunnableFromAllCores st tid).lifecycle = st.lifecycle :=
  (foldl_removeRunnableStepOnCore_frame _ tid st).2.1

@[simp] theorem removeRunnableFromAllCores_machine (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (removeRunnableFromAllCores st tid).machine = st.machine :=
  (foldl_removeRunnableStepOnCore_frame _ tid st).2.2.1

@[simp] theorem removeRunnableFromAllCores_tlbShootdown (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (removeRunnableFromAllCores st tid).tlbShootdown = st.tlbShootdown :=
  (foldl_removeRunnableStepOnCore_frame _ tid st).2.2.2

/-- WS-SM SM7.B: `removeRunnable` is scheduler-only — the TLB-shootdown
state is framed (`pendingBounded` bundle-carriage leaf). -/
theorem removeRunnable_tlbShootdown_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeRunnable st tid).tlbShootdown = st.tlbShootdown := rfl

/-- AN10 residual closure (H7): typed entry-point for `removeRunnable` that
documents the production-path discipline at the type system. Production
handlers that have already validated their `ThreadId` (through
`validateThreadIdArg` at the dispatch boundary, or through structural
extraction from a queue / TCB lookup) should prefer this wrapper to
make the invariant locally observable.

The underlying `removeRunnable` is sentinel-safe (the sentinel can never
be a member of any RunQueue or `scheduler.current`), so this wrapper
adds no runtime safety beyond what the function already guarantees —
its value is **type-level documentation of the dispatch-boundary contract**
and a reusable reduction lemma (`removeRunnableValid_eq`) for proofs
that want to discharge through the typed form. -/
@[inline] def removeRunnableValid (st : SystemState) (vtid : SeLe4n.ValidThreadId) : SystemState :=
  removeRunnable st vtid.val

/-- AN10 residual closure (H7): the typed wrapper reduces to the raw form,
so any proof body that established a result over `removeRunnable` can
be reused by rewriting through this equality. -/
@[simp] theorem removeRunnableValid_eq (st : SystemState) (vtid : SeLe4n.ValidThreadId) :
    removeRunnableValid st vtid = removeRunnable st vtid.val := rfl

/-- WS-G4/F-P02: O(1) amortized insert via RunQueue.
    AK1-E (I-M03): Priority is computed via `TCB.boostedPriority`
    to honor PIP boost on wake paths (notification signal, endpoint
    rendezvous, reply wake). Matches the yield/timer/switch convention
    established in AI3-A. -/
def ensureRunnable (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  if tid ∈ (st.scheduler.runQueueOnCore bootCoreId) then
    st
  else
    -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration. The
    -- pre-AN10 `_ => st` arm collapsed wrong-variant and absent into the
    -- same identity fall-through, so migration is semantics-preserving.
    match st.getTcb? tid with
    | some tcb =>
        { st with
            scheduler := st.scheduler.setRunQueueOnCore bootCoreId
              ((st.scheduler.runQueueOnCore bootCoreId).insert tid tcb.boostedPriority)
        }
    | none => st

def lookupTcb (st : SystemState) (tid : SeLe4n.ThreadId) : Option TCB :=
  if tid.isReserved then
    none
  else
    -- Composes the canonical reader rather than re-implementing it: this is
    -- `getTcb?` plus the reserved-id refusal, and spelling the store read a
    -- second time here is how the two could come to disagree.
    st.getTcb? tid

/-- WS-RR RR3.12: a successful `lookupTcb` witnesses that the tid is not reserved —
the half of `lookupTcb`'s guard that lets a lookup be *re-established* in another
state at the same tid. -/
theorem lookupTcb_some_not_reserved
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : lookupTcb st tid = some tcb) : ¬ tid.isReserved := by
  unfold lookupTcb SystemState.getTcb? at h
  intro hRes
  rw [if_pos hRes] at h
  cases h

/-- WS-RR RR3.12: the converse of `lookupTcb_some_objects` — a TCB in the object
store at a non-reserved tid resolves through `lookupTcb`. -/
theorem lookupTcb_of_objects_of_not_reserved
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hObj : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hNotReserved : ¬ tid.isReserved) :
    lookupTcb st tid = some tcb := by
  unfold lookupTcb SystemState.getTcb?
  rw [if_neg hNotReserved, hObj]

/-- **WS-RR RR8.12 Cut C1**: a thread `lookupTcb` resolves is promotable — the
reserved-id refusal `lookupTcb` performs is exactly the test `ThreadId.toValid?`
makes, so a resolved id has a `ValidThreadId` form that reads back to itself.  What
lets a statement over a resolved thread be handed to a primitive whose signature
demands the promoted form (`applyCallDonationOnCore`) without a second reserved-id
hypothesis. -/
theorem lookupTcb_some_toValid?
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : lookupTcb st tid = some tcb) :
    ∃ v : SeLe4n.ValidThreadId, tid.toValid? = some v ∧ v.val = tid := by
  have hNR : tid.isReserved = false := by
    simpa using lookupTcb_some_not_reserved st tid tcb h
  obtain ⟨v, hV⟩ :=
    Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff tid).mpr hNR)
  exact ⟨v, hV, SeLe4n.ThreadId.toValid?_some_val_eq tid v hV⟩

/-- If lookupTcb succeeds, the underlying objects map has a TCB at tid.toObjId. -/
theorem lookupTcb_some_objects
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : lookupTcb st tid = some tcb) :
    st.objects[tid.toObjId]? = some (.tcb tcb) := by
  unfold lookupTcb SystemState.getTcb? at h
  cases hRes : tid.isReserved
  · -- false
    simp [hRes] at h; revert h
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp
    | some obj => cases obj <;> simp
  · -- true: contradiction
    simp [hRes] at h

def storeTcbIpcState (st : SystemState) (tid : SeLe4n.ThreadId) (ipcState : ThreadIpcState) : Except KernelError SystemState :=
  match lookupTcb st tid with
  | none => .error .objectNotFound
  | some tcb =>
      match storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState }) st with
      | .error e => .error e
      | .ok ((), st') => .ok st'

/-- WS-L1/L1-C: Variant of `storeTcbIpcState` that accepts a pre-looked-up
TCB, bypassing the internal `lookupTcb`. Use when the caller has already
validated the TCB and no intervening operation has modified it. -/
def storeTcbIpcState_fromTcb (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (ipcState : ThreadIpcState) : Except KernelError SystemState :=
  match storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState }) st with
  | .error e => .error e
  | .ok ((), st') => .ok st'

/-- WS-L1/L1-C: Equivalence theorem — `_fromTcb` produces identical results
to the original when the provided TCB matches the state. -/
theorem storeTcbIpcState_fromTcb_eq
    (hLookup : lookupTcb st tid = some tcb) :
    storeTcbIpcState_fromTcb st tid tcb ipcState =
    storeTcbIpcState st tid ipcState := by
  unfold storeTcbIpcState_fromTcb storeTcbIpcState
  simp [hLookup]

/-- WS-F1: Store a pending IPC message in a thread's TCB.
Used during IPC send to stage the message for transfer. -/
def storeTcbPendingMessage (st : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage) : Except KernelError SystemState :=
  match lookupTcb st tid with
  | none => .error .objectNotFound
  | some tcb =>
      match storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
      | .error e => .error e
      | .ok ((), st') => .ok st'

/-- WS-F1: Combined store of IPC state and pending message in a single TCB update.
Avoids two separate storeObject calls and simplifies proof tracking. -/
def storeTcbIpcStateAndMessage (st : SystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState) (msg : Option IpcMessage) : Except KernelError SystemState :=
  match lookupTcb st tid with
  | none => .error .objectNotFound
  | some tcb =>
      match storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState, pendingMessage := msg }) st with
      | .error e => .error e
      | .ok ((), st') => .ok st'

/-- WS-L1/L1-B: Variant of `storeTcbIpcStateAndMessage` that accepts a
pre-looked-up TCB, bypassing the internal `lookupTcb`. Use when the caller
has already validated the TCB on the same state. -/
def storeTcbIpcStateAndMessage_fromTcb (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (ipcState : ThreadIpcState) (msg : Option IpcMessage)
    : Except KernelError SystemState :=
  match storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState, pendingMessage := msg }) st with
  | .error e => .error e
  | .ok ((), st') => .ok st'

/-- **WS-RR RR8.16** (`v0.35.200`): the resolving spelling of the delivery store
is a `kindPreservingWrite` too — it looks the TCB up itself, so it needs no
`hPre`.

The `.call` leg writes through this form where the reply leg writes through
`_fromTcb`, and both spellings are one store; stating the relation at each is
what keeps a chain over either a citation. -/
theorem storeTcbIpcStateAndMessage_kindPreservingWrite
    {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {ipcState : ThreadIpcState} {msg : Option IpcMessage}
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbIpcStateAndMessage st tid ipcState msg = .ok st') :
    kindPreservingWrite st st' := by
  unfold storeTcbIpcStateAndMessage at hStore
  cases hLk : lookupTcb st tid with
  | none => rw [hLk] at hStore; cases hStore
  | some tcb =>
    rw [hLk] at hStore
    simp only at hStore
    cases hS : storeObject tid.toObjId
        (.tcb { tcb with ipcState := ipcState, pendingMessage := msg }) st with
    | error e => rw [hS] at hStore; cases hStore
    | ok p =>
      obtain ⟨_, s1⟩ := p
      rw [hS] at hStore
      simp only [Except.ok.injEq] at hStore
      subst hStore
      exact storeObject_kindPreservingWrite hObjInv hS
        (lookupTcb_some_objects st tid tcb hLk) rfl (by simp [KernelObject.objectType])

/-- **WS-RR RR8.16** (`v0.35.200`): ...and it writes neither CDT table. -/
theorem storeTcbIpcStateAndMessage_cdt_eq
    {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {ipcState : ThreadIpcState} {msg : Option IpcMessage}
    (hStore : storeTcbIpcStateAndMessage st tid ipcState msg = .ok st') :
    st'.cdt = st.cdt ∧ st'.cdtNodeSlot = st.cdtNodeSlot := by
  unfold storeTcbIpcStateAndMessage at hStore
  cases hLk : lookupTcb st tid with
  | none => rw [hLk] at hStore; cases hStore
  | some tcb =>
    rw [hLk] at hStore
    simp only at hStore
    cases hS : storeObject tid.toObjId
        (.tcb { tcb with ipcState := ipcState, pendingMessage := msg }) st with
    | error e => rw [hS] at hStore; cases hStore
    | ok p =>
      obtain ⟨_, s1⟩ := p
      rw [hS] at hStore
      simp only [Except.ok.injEq] at hStore
      subst hStore
      exact ⟨storeObject_cdt_eq _ _ _ _ hS, storeObject_cdtNodeSlot_eq _ _ _ _ hS⟩

/-- **WS-RR RR8.16** (`v0.35.199`): the delivery store is a
`kindPreservingWrite` — one `storeObject` of a `.tcb` at a key the caller has
already resolved to a TCB.

The shape register row 85's two bundle frames consume.  Stated beside the
definition rather than at each IPC chain: every arm of the reply and call spines
opens with this store, and re-deriving the fact per arm is the duplication this
project retires. -/
theorem storeTcbIpcStateAndMessage_fromTcb_kindPreservingWrite
    {st st' : SystemState} {tid : SeLe4n.ThreadId} {tcb : TCB}
    {ipcState : ThreadIpcState} {msg : Option IpcMessage}
    (hObjInv : st.objects.invExt)
    (hPre : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hStore : storeTcbIpcStateAndMessage_fromTcb st tid tcb ipcState msg = .ok st') :
    kindPreservingWrite st st' := by
  unfold storeTcbIpcStateAndMessage_fromTcb at hStore
  cases hS : storeObject tid.toObjId
      (.tcb { tcb with ipcState := ipcState, pendingMessage := msg }) st with
  | error e => rw [hS] at hStore; cases hStore
  | ok p =>
    obtain ⟨_, s1⟩ := p
    rw [hS] at hStore
    simp only [Except.ok.injEq] at hStore
    subst hStore
    exact storeObject_kindPreservingWrite hObjInv hS hPre rfl
      (by simp [KernelObject.objectType])

/-- **WS-RR RR8.16** (`v0.35.199`): ...and it writes neither CDT table —
`storeObject` writes `objects`, the two indices, the lifecycle table and the ASID
table, and no more. -/
theorem storeTcbIpcStateAndMessage_fromTcb_cdt_eq
    {st st' : SystemState} {tid : SeLe4n.ThreadId} {tcb : TCB}
    {ipcState : ThreadIpcState} {msg : Option IpcMessage}
    (hStore : storeTcbIpcStateAndMessage_fromTcb st tid tcb ipcState msg = .ok st') :
    st'.cdt = st.cdt ∧ st'.cdtNodeSlot = st.cdtNodeSlot := by
  unfold storeTcbIpcStateAndMessage_fromTcb at hStore
  cases hS : storeObject tid.toObjId
      (.tcb { tcb with ipcState := ipcState, pendingMessage := msg }) st with
  | error e => rw [hS] at hStore; cases hStore
  | ok p =>
    obtain ⟨_, s1⟩ := p
    rw [hS] at hStore
    simp only [Except.ok.injEq] at hStore
    subst hStore
    exact ⟨storeObject_cdt_eq _ _ _ _ hS, storeObject_cdtNodeSlot_eq _ _ _ _ hS⟩

/-- WS-L1/L1-B: Equivalence theorem — `_fromTcb` produces identical results
to the original when the provided TCB matches the state. All existing
preservation theorems for `storeTcbIpcStateAndMessage` apply to `_fromTcb`
via rewriting with this theorem. -/
theorem storeTcbIpcStateAndMessage_fromTcb_eq
    (hLookup : lookupTcb st tid = some tcb) :
    storeTcbIpcStateAndMessage_fromTcb st tid tcb ipcState msg =
    storeTcbIpcStateAndMessage st tid ipcState msg := by
  unfold storeTcbIpcStateAndMessage_fromTcb storeTcbIpcStateAndMessage
  simp [hLookup]

/-- IPC de-threading D3 (Finding F-1): complete a receive — set the receiver `.ready`
with the delivered message **and** clear its server-first `pendingReceiveReply` stash.
Used by the **non-Call** receive-completion wakes (`endpointSendDual` rendezvous,
`notificationSignalBound{,OnCore}`): the receive completed without a `Call`, so the
stashed reply object is moot and the `pendingReceiveReplyWellFormed` discipline ("a
thread that is not `.blockedOnReceive` holds no server-first reply stash") requires it
cleared.  Distinct from `storeTcbIpcStateAndMessage`, which **preserves** the stash for
the `Call` rendezvous, where `linkServerStashedReply` consumes it. -/
def storeTcbReceiveComplete (st : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage) : Except KernelError SystemState :=
  match lookupTcb st tid with
  | none => .error .objectNotFound
  | some tcb =>
      match storeObject tid.toObjId
          (.tcb { tcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none }) st with
      | .error e => .error e
      | .ok ((), st') => .ok st'

/-- WS-L1: `lookupTcb` is preserved when `storeObject` targets a notification
(different ObjId from any TCB). Used to justify `_fromTcb` usage after an
intervening notification store. Accepts both `((), st')` and `pair` forms. -/
theorem lookupTcb_preserved_by_storeObject_notification
    {st : SystemState} {pair : Unit × SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB} {notifId : SeLe4n.ObjId} {ntfn : Notification}
    {obj : KernelObject}
    (hLookup : lookupTcb st tid = some tcb)
    (hNtfn : st.objects[notifId]? = some (.notification ntfn))
    (hObjInv : st.objects.invExt)
    (hStore : storeObject notifId obj st = .ok pair) :
    lookupTcb pair.2 tid = some tcb := by
  have hStore' : storeObject notifId obj st = .ok ((), pair.2) := by
    rw [show pair = ((), pair.2) from by cases pair; rfl] at hStore; exact hStore
  have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
  have hNe : tid.toObjId ≠ notifId := by
    intro heq; rw [← heq] at hNtfn; rw [hNtfn] at hTcbObj; cases hTcbObj
  have hPreserved := storeObject_objects_ne st pair.2 notifId tid.toObjId obj hNe hObjInv hStore'
  unfold lookupTcb SystemState.getTcb? at hLookup ⊢
  rw [hPreserved]
  exact hLookup

-- ============================================================================
-- Z7: SchedContext Donation Helpers
-- ============================================================================

/-- WS-OD OD4.1 (frame): a `storeObject` that replaces one TCB with another
leaves every SchedContext resolution unchanged.  The public form of the frame the
donation primitives' proofs need; a TCB store cannot land at a SchedContext's
key, because the two kinds cannot occupy one slot. -/
theorem storeObject_tcbAt_getSchedContext?_eq_donation
    (st st' : SystemState) (stored : SeLe4n.ThreadId) (tOld tNew : TCB)
    (hOld : st.getTcb? stored = some tOld)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject stored.toObjId (.tcb tNew) st = .ok ((), st'))
    (scId : SeLe4n.SchedContextId) :
    st'.getSchedContext? scId = st.getSchedContext? scId := by
  have hRaw := (SystemState.getTcb?_eq_some_iff st stored tOld).mp hOld
  unfold SystemState.getSchedContext?
  by_cases h : scId.toObjId = stored.toObjId
  · rw [h, storeObject_objects_eq st st' stored.toObjId _ hObjInv hStore, hRaw]
  · rw [storeObject_objects_ne st st' stored.toObjId scId.toObjId _ h hObjInv hStore]

/-- WS-OD OD4.1 (frame): the Reply half of
`storeObject_tcbAt_getSchedContext?_eq_donation`. -/
theorem storeObject_tcbAt_getReply?_eq_donation
    (st st' : SystemState) (stored : SeLe4n.ThreadId) (tOld tNew : TCB)
    (hOld : st.getTcb? stored = some tOld)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject stored.toObjId (.tcb tNew) st = .ok ((), st'))
    (rid : SeLe4n.ReplyId) :
    st'.getReply? rid = st.getReply? rid := by
  have hRaw := (SystemState.getTcb?_eq_some_iff st stored tOld).mp hOld
  unfold SystemState.getReply?
  by_cases h : rid.toObjId = stored.toObjId
  · rw [h, storeObject_objects_eq st st' stored.toObjId _ hObjInv hStore, hRaw]
  · rw [storeObject_objects_ne st st' stored.toObjId rid.toObjId _ h hObjInv hStore]

/-- WS-OD OD4.1 (frame): a `storeObject` that replaces one Reply with another
leaves every thread's TCB resolution unchanged — neither the written value nor
the previous occupant is a TCB.

Stated here, beside the two operations that write a Reply's stack links (the
donation push's frame store and the pop's `storeDonationHeadClear`), so the
donation-primitive frames and the invariant layer read one lemma rather than a
private copy each. -/
theorem storeObject_replyAt_getTcb?_eq
    (st st' : SystemState) (stored : SeLe4n.ReplyId) (rOld rNew : Reply)
    (hOld : st.getReply? stored = some rOld)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject stored.toObjId (.reply rNew) st = .ok ((), st'))
    (tid : SeLe4n.ThreadId) :
    st'.getTcb? tid = st.getTcb? tid := by
  have hRaw := (SystemState.getReply?_eq_some_iff st stored rOld).mp hOld
  unfold SystemState.getTcb?
  by_cases h : tid.toObjId = stored.toObjId
  · rw [h, storeObject_objects_eq st st' stored.toObjId _ hObjInv hStore, hRaw]
  · rw [storeObject_objects_ne st st' stored.toObjId tid.toObjId _ h hObjInv hStore]

/-- WS-OD OD4.1 (frame): the SchedContext half of
`storeObject_replyAt_getTcb?_eq`. -/
theorem storeObject_replyAt_getSchedContext?_eq
    (st st' : SystemState) (stored : SeLe4n.ReplyId) (rOld rNew : Reply)
    (hOld : st.getReply? stored = some rOld)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject stored.toObjId (.reply rNew) st = .ok ((), st'))
    (scId : SeLe4n.SchedContextId) :
    st'.getSchedContext? scId = st.getSchedContext? scId := by
  have hRaw := (SystemState.getReply?_eq_some_iff st stored rOld).mp hOld
  unfold SystemState.getSchedContext?
  by_cases h : scId.toObjId = stored.toObjId
  · rw [h, storeObject_objects_eq st st' stored.toObjId _ hObjInv hStore, hRaw]
  · rw [storeObject_objects_ne st st' stored.toObjId scId.toObjId _ h hObjInv hStore]

/-- WS-OD OD4.1 (frame): a Reply store leaves the raw TCB reading at every key
alone, in both directions.  The raw-store form the read-agreement constructors
consume, where the two typed lemmas above serve the accessor-level frames. -/
theorem storeObject_replyAt_objects_tcb_iff
    (st st' : SystemState) (stored : SeLe4n.ReplyId) (rOld rNew : Reply)
    (hOld : st.getReply? stored = some rOld)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject stored.toObjId (.reply rNew) st = .ok ((), st'))
    (oid : SeLe4n.ObjId) (t : TCB) :
    st'.objects[oid]? = some (.tcb t) ↔ st.objects[oid]? = some (.tcb t) := by
  have hRaw := (SystemState.getReply?_eq_some_iff st stored rOld).mp hOld
  by_cases h : oid = stored.toObjId
  · rw [h, storeObject_objects_eq st st' stored.toObjId _ hObjInv hStore, hRaw]
    exact ⟨fun hc => absurd hc (by simp), fun hc => absurd hc (by simp)⟩
  · rw [storeObject_objects_ne st st' stored.toObjId oid _ h hObjInv hStore]

/-- WS-OD OD4.1: **the reply-stack frame a donation pushes.**

`donateSchedContext` records the donation on the donor's own reply object: that
Reply becomes the new head of the scheduling context's stack, carrying the
context it heads (`next := .head`) and a link down to the frame the context
previously headed (`prev`).  The pop reads exactly those fields back
(`donationHeadOf?`, `replyStackOuterCaller?`), so one push must contribute one
frame — the depth of the stack *is* the depth of the donation chain, which is
what lets a pop at depth `n` hand the context to the right thread.

**Fail-closed on all three refusals, and each is a different fact.**

* `.replyCapInvalid` — the donor holds no reply object.  Recording nothing while
  minting a `.donated` binding would leave the stack one frame short of the
  chain, so the *next* pop would clear a frame belonging to an outer caller and
  settle the context on the wrong thread.  Refusing is the only answer that
  keeps the two depths equal.
* `.objectNotFound` — the donor's reply object does not resolve.
* `.invalidArgument` — the reply already carries a stack link (`prev` or
  `next`), so it is on some stack already and pushing it would make it its own
  ancestor and close a cycle in the `prev` graph — seL4's `reply_push` asserts
  exactly `replyPrev == 0 ∧ replyNext == 0` here.  `donationChainWellFormed`'s
  termination clause is what that would break, and
  `not_mem_donationChainFrom_of_unlinked` is the freshness fact the push
  consumes in its place.

**None of the three fires on a live path**, and that is a theorem rather than a
comment: a donor that is `.blockedOnReply` carries a resolvable reply object
under `replyCallerLinkage` (`ipcInvariantFull`'s sixteenth conjunct), and a
reply carrying no donation is what `donationChainWellFormed` gives for every
reply the chain does not already hold — `donationPushFrame?_ok_of_linked` states
both.  This is the same defence-in-depth posture as the pop's own head
validation and `donateSchedContext`'s AUD-3b `boundThread` guard: the guard is
O(1), commits nothing when it refuses, and turns a whole-store obligation into a
consequence of the operation succeeding. -/
def donationPushFrame? (st : SystemState) (clientTcb : TCB) :
    Except KernelError (SeLe4n.ReplyId × Reply) :=
  match clientTcb.replyObject with
  | none => .error .replyCapInvalid
  | some rid =>
    -- Read through the state's own typed accessor: it is a whole `Reply` this
    -- needs, and the AK7 cascade counts an unmigrated raw read site as debt.
    match st.getReply? rid with
    | none => .error .objectNotFound
    | some r =>
        -- Fail-closed twice over: a frame already on a stack (either link set)
        -- cannot be pushed again, and a consumed frame (no caller) is one the
        -- pop's outer-caller resolver refuses, so pushing it would build a stack
        -- that cannot unwind.  A Reply on a stack has a caller
        -- (`Reply.wellFormed`), and this is where that is enforced at the push.
        if r.prev.isSome || r.next.isSome then .error .invalidArgument
        else if r.caller.isNone then .error .illegalState
        else .ok (rid, r)

/-- WS-OD OD4.1: **what a resolved push frame is** — the donor's own reply
object, resolving in the store, on no stack yet (neither link set).  The complete
decomposition, so every consumer reads the three facts off one lemma rather than
re-running the case analysis. -/
theorem donationPushFrame?_ok (st : SystemState) (clientTcb : TCB)
    (rid : SeLe4n.ReplyId) (r : Reply)
    (h : donationPushFrame? st clientTcb = .ok (rid, r)) :
    clientTcb.replyObject = some rid ∧
      st.getReply? rid = some r ∧ r.prev = none ∧ r.next = none ∧ r.caller ≠ none := by
  unfold donationPushFrame? at h
  revert h
  cases hRO : clientTcb.replyObject with
  | none => intro h; cases h
  | some rid0 =>
    simp only []
    cases hRep : st.getReply? rid0 with
    | none => intro h; cases h
    | some r0 =>
      simp only []
      cases hLinked : (r0.prev.isSome || r0.next.isSome) with
      | true => simp only [if_true]; intro h; cases h
      | false =>
        simp only [Bool.false_eq_true, if_false]
        cases hConsumed : r0.caller.isNone with
        | true => simp only [if_true]; intro h; cases h
        | false =>
          simp only [Bool.false_eq_true, if_false]
          intro h
          have hPair := Except.ok.inj h
          have hRid : rid0 = rid := congrArg Prod.fst hPair
          have hRep' : r0 = r := congrArg Prod.snd hPair
          subst hRid; subst hRep'
          have hBoth := Bool.or_eq_false_iff.mp hLinked
          refine ⟨rfl, hRep, Option.not_isSome_iff_eq_none.mp (by simp [hBoth.1]),
            Option.not_isSome_iff_eq_none.mp (by simp [hBoth.2]), ?_⟩
          intro hC
          rw [hC] at hConsumed
          cases hConsumed

/-- WS-OD (`v0.35.4`): **the two Reply writes of the donation push.**  seL4's
`reply_push`, stack half: the pushed frame records the frame below it (`prev :=
old head`) and becomes the head (`next := .head scId`), and the old head — when
there is one — now has a frame above it (`next := .frame pushRid`).  The second
write is what a doubly-linked stack costs at the push and what buys the `O(1)`
splice: with it, taking a frame out of the middle repairs its two neighbours and
nothing else.

Fail-closed on an old head that does not resolve (`.objectNotFound`): under
`donationChainWellFormed.headLinkReciprocal` a context's head always resolves, so
the arm is unreachable on a reachable state, and a store that could not repair
the frame below would otherwise leave a head whose `prev` names a frame that does
not point back — the shape every pop validator refuses. -/
def storeDonationFramePush (scId : SeLe4n.SchedContextId) (pushRid : SeLe4n.ReplyId)
    (pushReply : Reply) (oldHead? : Option SeLe4n.ReplyId) (st : SystemState) :
    Except KernelError SystemState :=
  -- A frame cannot be pushed onto itself: the old head is a *different* Reply or
  -- there is none.  Refused rather than assumed, so the lemmas below need no
  -- distinctness hypothesis and a malformed store cannot close a one-frame cycle.
  if oldHead? == some pushRid then .error .invalidArgument else
  match storeObject pushRid.toObjId
      (.reply { pushReply with prev := oldHead?, next := some (.head scId) }) st with
  | .error e => .error e
  | .ok ((), st1) =>
    match oldHead? with
    | none => .ok st1
    | some old =>
      match st1.getReply? old with
      | none => .error .objectNotFound
      | some oldR =>
        match storeObject old.toObjId (.reply { oldR with next := some (.frame pushRid) }) st1 with
        | .error e => .error e
        | .ok ((), st2) => .ok st2

/-- The push's Reply writes, decomposed: the frame store always, the old head's
`next` store exactly when the context headed a frame. -/
theorem storeDonationFramePush_cases
    {scId : SeLe4n.SchedContextId} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    {oldHead? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeDonationFramePush scId pushRid pushReply oldHead? st = .ok st') :
    oldHead? ≠ some pushRid ∧
    ∃ s1, storeObject pushRid.toObjId
        (.reply { pushReply with prev := oldHead?, next := some (.head scId) }) st
          = .ok ((), s1) ∧
      ((oldHead? = none ∧ st' = s1) ∨
       ∃ (old : SeLe4n.ReplyId) (oldR : Reply),
         oldHead? = some old ∧ s1.getReply? old = some oldR ∧
         storeObject old.toObjId (.reply { oldR with next := some (.frame pushRid) }) s1
           = .ok ((), st')) := by
  unfold storeDonationFramePush at h
  revert h
  cases hSelf : (oldHead? == some pushRid) with
  | true => intro h; simp only [if_true] at h; cases h
  | false =>
  simp only [Bool.false_eq_true, if_false]
  have hNeSelf : oldHead? ≠ some pushRid := by
    intro hEq; rw [hEq] at hSelf; simp at hSelf
  cases hS1 : storeObject pushRid.toObjId
      (.reply { pushReply with prev := oldHead?, next := some (.head scId) }) st with
  | error _ => intro h; cases h
  | ok p1 =>
    obtain ⟨u1, s1⟩ := p1; cases u1
    simp only []
    cases hOld : oldHead? with
    | none =>
      intro h
      have hEq := Except.ok.inj h
      subst hEq
      rw [hOld] at hNeSelf
      exact ⟨hNeSelf, s1, rfl, Or.inl ⟨rfl, rfl⟩⟩
    | some old =>
      simp only []
      cases hR : s1.getReply? old with
      | none => intro h; cases h
      | some oldR =>
        simp only []
        cases hS2 : storeObject old.toObjId (.reply { oldR with next := some (.frame pushRid) }) s1 with
        | error _ => intro h; cases h
        | ok p2 =>
          obtain ⟨u2, s2⟩ := p2; cases u2
          intro h
          have hEq := Except.ok.inj h
          subst hEq
          rw [hOld] at hNeSelf
          exact ⟨hNeSelf, s1, rfl, Or.inr ⟨old, oldR, rfl, hR, hS2⟩⟩

/-- Every write of the push's Reply half lands on a Reply key, so a key holding a
non-Reply is untouched, and every TCB and SchedContext reading survives. -/
theorem storeDonationFramePush_objects_ne
    {scId : SeLe4n.SchedContextId} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    {oldHead? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationFramePush scId pushRid pushReply oldHead? st = .ok st')
    (k : SeLe4n.ObjId) (hkPush : k ≠ pushRid.toObjId)
    (hkOld : ∀ old, oldHead? = some old → k ≠ old.toObjId) :
    st'.objects[k]? = st.objects[k]? := by
  obtain ⟨_, s1, hS1, hRest⟩ := storeDonationFramePush_cases h
  have e1 := storeObject_objects_ne st s1 _ k _ hkPush hObjInv hS1
  rcases hRest with ⟨_, rfl⟩ | ⟨old, oldR, hOld, _, hS2⟩
  · exact e1
  · have hInv1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
    rw [storeObject_objects_ne s1 st' _ k _ (hkOld old hOld) hInv1 hS2, e1]

theorem storeDonationFramePush_preserves_objects_invExt
    {scId : SeLe4n.SchedContextId} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    {oldHead? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationFramePush scId pushRid pushReply oldHead? st = .ok st') :
    st'.objects.invExt := by
  obtain ⟨_, s1, hS1, hRest⟩ := storeDonationFramePush_cases h
  have hInv1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  rcases hRest with ⟨_, rfl⟩ | ⟨_, _, _, _, hS2⟩
  · exact hInv1
  · exact storeObject_preserves_objects_invExt s1 st' _ _ hInv1 hS2

/-- **WS-RR RR8.16** (`v0.35.200`): the frame push is a `kindPreservingWrite` —
a Reply for a Reply at the pushed frame, and another at the old head when the
context already headed one.

The pushed frame's pre-state record is a hypothesis rather than derived: the
push takes it as an *argument*, and `donationPushFrame?_ok` is what the donation
supplies it from. -/
theorem storeDonationFramePush_kindPreservingWrite
    {scId : SeLe4n.SchedContextId} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    {oldHead? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (hPre : st.getReply? pushRid = some pushReply)
    (h : storeDonationFramePush scId pushRid pushReply oldHead? st = .ok st') :
    kindPreservingWrite st st' := by
  obtain ⟨_, s1, hS1, hRest⟩ := storeDonationFramePush_cases h
  have hW1 : kindPreservingWrite st s1 :=
    storeObject_kindPreservingWrite hObjInv hS1
      ((SystemState.getReply?_eq_some_iff st pushRid pushReply).mp hPre) rfl
      (by simp [KernelObject.objectType])
  have hInv1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  rcases hRest with ⟨_, rfl⟩ | ⟨old, oldR, _, hR, hS2⟩
  · exact hW1
  · exact hW1.trans (storeObject_kindPreservingWrite hInv1 hS2
      ((SystemState.getReply?_eq_some_iff s1 old oldR).mp hR) rfl
      (by simp [KernelObject.objectType]))

/-- **WS-RR RR8.16** (`v0.35.200`): ...and the push writes neither CDT table. -/
theorem storeDonationFramePush_cdt_eq
    {scId : SeLe4n.SchedContextId} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    {oldHead? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeDonationFramePush scId pushRid pushReply oldHead? st = .ok st') :
    st'.cdt = st.cdt ∧ st'.cdtNodeSlot = st.cdtNodeSlot := by
  obtain ⟨_, s1, hS1, hRest⟩ := storeDonationFramePush_cases h
  have e1 : s1.cdt = st.cdt ∧ s1.cdtNodeSlot = st.cdtNodeSlot :=
    ⟨storeObject_cdt_eq _ _ _ _ hS1, storeObject_cdtNodeSlot_eq _ _ _ _ hS1⟩
  rcases hRest with ⟨_, rfl⟩ | ⟨_, _, _, _, hS2⟩
  · exact e1
  · exact ⟨(storeObject_cdt_eq _ _ _ _ hS2).trans e1.1,
      (storeObject_cdtNodeSlot_eq _ _ _ _ hS2).trans e1.2⟩

/-- The pushed frame's record afterwards. -/
theorem storeDonationFramePush_getReply?_pushed
    {scId : SeLe4n.SchedContextId} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    {oldHead? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationFramePush scId pushRid pushReply oldHead? st = .ok st') :
    st'.getReply? pushRid
      = some { pushReply with prev := oldHead?, next := some (.head scId) } := by
  obtain ⟨hNeSelf, s1, hS1, hRest⟩ := storeDonationFramePush_cases h
  have h1 : s1.getReply? pushRid
      = some { pushReply with prev := oldHead?, next := some (.head scId) } := by
    rw [SystemState.getReply?_eq_some_iff, storeObject_objects_eq st s1 _ _ hObjInv hS1]
  rcases hRest with ⟨_, rfl⟩ | ⟨old, oldR, hOld, _, hS2⟩
  · exact h1
  · have hInv1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
    have hKey : pushRid.toObjId ≠ old.toObjId := by
      intro hEq
      apply hNeSelf
      rw [hOld, SeLe4n.ReplyId.toObjId_injective _ _ hEq]
    rw [SystemState.getReply?_eq_some_iff,
      storeObject_objects_ne s1 st' _ pushRid.toObjId _ hKey hInv1 hS2]
    exact (SystemState.getReply?_eq_some_iff s1 pushRid _).mp h1

/-- The old head's record afterwards: unchanged but for the new frame above it. -/
theorem storeDonationFramePush_getReply?_old
    {scId : SeLe4n.SchedContextId} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    {old : SeLe4n.ReplyId} {oldR : Reply} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (hOldR : st.getReply? old = some oldR)
    (h : storeDonationFramePush scId pushRid pushReply (some old) st = .ok st') :
    st'.getReply? old = some { oldR with next := some (.frame pushRid) } := by
  obtain ⟨hNeSelf, s1, hS1, hRest⟩ := storeDonationFramePush_cases h
  rcases hRest with ⟨hAbs, _⟩ | ⟨old', oldR', hOld, hR1, hS2⟩
  · cases hAbs
  · have hOldEq : old' = old := (Option.some.inj hOld).symm
    subst hOldEq
    have hInv1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
    have hKey : old'.toObjId ≠ pushRid.toObjId := by
      intro hEq
      apply hNeSelf
      rw [SeLe4n.ReplyId.toObjId_injective _ _ hEq]
    have hR1' : s1.getReply? old' = some oldR := by
      rw [SystemState.getReply?_eq_some_iff,
        storeObject_objects_ne st s1 _ old'.toObjId _ hKey hObjInv hS1]
      exact (SystemState.getReply?_eq_some_iff st old' oldR).mp hOldR
    rw [hR1'] at hR1
    have hRR : oldR' = oldR := (Option.some.inj hR1).symm
    subst hRR
    rw [SystemState.getReply?_eq_some_iff, storeObject_objects_eq s1 st' _ _ hInv1 hS2]

/-- Both of the push's Reply writes land on keys that hold Replies, so every
non-Reply key is untouched: SchedContext and TCB readings survive verbatim. -/
theorem storeDonationFramePush_non_reply_eq
    {scId : SeLe4n.SchedContextId} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    {oldHead? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (hPushReply : st.getReply? pushRid = some pushReply)
    (h : storeDonationFramePush scId pushRid pushReply oldHead? st = .ok st')
    (k : SeLe4n.ObjId) (hNotReply : ∀ r : Reply, st.objects[k]? ≠ some (.reply r)) :
    st'.objects[k]? = st.objects[k]? := by
  apply storeDonationFramePush_objects_ne hObjInv h k
  · intro hEq; subst hEq
    exact hNotReply pushReply ((SystemState.getReply?_eq_some_iff _ _ _).mp hPushReply)
  · intro old hOld hEq; subst hEq
    obtain ⟨hNeSelf, s1, hS1, hRest⟩ := storeDonationFramePush_cases h
    rcases hRest with ⟨hAbs, _⟩ | ⟨old', oldR, hOld', hR1, _⟩
    · rw [hOld] at hAbs; cases hAbs
    · rw [hOld] at hOld'
      have hOldEq : old' = old := (Option.some.inj hOld').symm
      subst hOldEq
      have hKey : old'.toObjId ≠ pushRid.toObjId := by
        intro hEq
        apply hNeSelf
        rw [hOld, SeLe4n.ReplyId.toObjId_injective _ _ hEq]
      have hPre : st.getReply? old' = some oldR := by
        rw [SystemState.getReply?_eq_some_iff] at hR1 ⊢
        rw [← storeObject_objects_ne st s1 _ old'.toObjId _ hKey hObjInv hS1]; exact hR1
      exact hNotReply oldR ((SystemState.getReply?_eq_some_iff _ _ _).mp hPre)

/-- A key holding a Reply before the push's Reply writes holds a Reply after them
(the same one, or its rewritten form). -/
theorem storeDonationFramePush_reply_kind_stable
    {scId : SeLe4n.SchedContextId} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    {oldHead? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationFramePush scId pushRid pushReply oldHead? st = .ok st')
    (k : SeLe4n.ObjId) (r : Reply) (hk : st.objects[k]? = some (.reply r)) :
    ∃ r' : Reply, st'.objects[k]? = some (.reply r') := by
  obtain ⟨_, s1, hS1, hRest⟩ := storeDonationFramePush_cases h
  have hInv1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have h1 : ∃ r1 : Reply, s1.objects[k]? = some (.reply r1) := by
    by_cases hkP : k = pushRid.toObjId
    · subst hkP; exact ⟨_, storeObject_objects_eq st s1 _ _ hObjInv hS1⟩
    · exact ⟨r, by rw [storeObject_objects_ne st s1 _ k _ hkP hObjInv hS1]; exact hk⟩
  rcases hRest with ⟨_, rfl⟩ | ⟨old, oldR, _, _, hS2⟩
  · exact h1
  · obtain ⟨r1, hr1⟩ := h1
    by_cases hkO : k = old.toObjId
    · subst hkO; exact ⟨_, storeObject_objects_eq s1 st' _ _ hInv1 hS2⟩
    · exact ⟨r1, by rw [storeObject_objects_ne s1 st' _ k _ hkO hInv1 hS2]; exact hr1⟩

theorem storeDonationFramePush_getSchedContext?_eq
    {scId : SeLe4n.SchedContextId} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    {oldHead? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (hPushReply : st.getReply? pushRid = some pushReply)
    (h : storeDonationFramePush scId pushRid pushReply oldHead? st = .ok st')
    (sc : SeLe4n.SchedContextId) :
    st'.getSchedContext? sc = st.getSchedContext? sc := by
  unfold SystemState.getSchedContext?
  by_cases hRep : ∃ r : Reply, st.objects[sc.toObjId]? = some (.reply r)
  · obtain ⟨r, hr⟩ := hRep
    obtain ⟨r', hr'⟩ := storeDonationFramePush_reply_kind_stable hObjInv h sc.toObjId r hr
    rw [hr, hr']
  · rw [storeDonationFramePush_non_reply_eq hObjInv hPushReply h sc.toObjId
      (fun r hr => hRep ⟨r, hr⟩)]

theorem storeDonationFramePush_tcb_eq
    {scId : SeLe4n.SchedContextId} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    {oldHead? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (hPushReply : st.getReply? pushRid = some pushReply)
    (h : storeDonationFramePush scId pushRid pushReply oldHead? st = .ok st')
    (k : SeLe4n.ObjId) (t0 : TCB) (hk : st.objects[k]? = some (.tcb t0)) :
    st'.objects[k]? = some (.tcb t0) := by
  rw [storeDonationFramePush_non_reply_eq hObjInv hPushReply h k
    (fun r hr => by rw [hk] at hr; cases hr)]
  exact hk

theorem storeDonationFramePush_getTcb?_eq
    {scId : SeLe4n.SchedContextId} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    {oldHead? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (hPushReply : st.getReply? pushRid = some pushReply)
    (h : storeDonationFramePush scId pushRid pushReply oldHead? st = .ok st')
    (tid : SeLe4n.ThreadId) :
    st'.getTcb? tid = st.getTcb? tid := by
  unfold SystemState.getTcb?
  by_cases hRep : ∃ r : Reply, st.objects[tid.toObjId]? = some (.reply r)
  · obtain ⟨r, hr⟩ := hRep
    obtain ⟨r', hr'⟩ := storeDonationFramePush_reply_kind_stable hObjInv h tid.toObjId r hr
    rw [hr, hr']
  · rw [storeDonationFramePush_non_reply_eq hObjInv hPushReply h tid.toObjId
      (fun r hr => hRep ⟨r, hr⟩)]

theorem storeDonationFramePush_machine_eq
    {scId : SeLe4n.SchedContextId} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    {oldHead? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeDonationFramePush scId pushRid pushReply oldHead? st = .ok st') :
    st'.machine = st.machine := by
  obtain ⟨_, s1, hS1, hRest⟩ := storeDonationFramePush_cases h
  have e1 : s1.machine = st.machine := by unfold storeObject at hS1; cases hS1; rfl
  rcases hRest with ⟨_, rfl⟩ | ⟨_, _, _, _, hS2⟩
  · exact e1
  · have e2 : st'.machine = s1.machine := by unfold storeObject at hS2; cases hS2; rfl
    rw [e2, e1]

theorem storeDonationFramePush_serviceRegistry_eq
    {scId : SeLe4n.SchedContextId} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    {oldHead? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeDonationFramePush scId pushRid pushReply oldHead? st = .ok st') :
    st'.serviceRegistry = st.serviceRegistry := by
  obtain ⟨_, s1, hS1, hRest⟩ := storeDonationFramePush_cases h
  have e1 : s1.serviceRegistry = st.serviceRegistry := by unfold storeObject at hS1; cases hS1; rfl
  rcases hRest with ⟨_, rfl⟩ | ⟨_, _, _, _, hS2⟩
  · exact e1
  · have e2 : st'.serviceRegistry = s1.serviceRegistry := by
      unfold storeObject at hS2; cases hS2; rfl
    rw [e2, e1]

theorem storeDonationFramePush_tlbShootdown_eq
    {scId : SeLe4n.SchedContextId} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    {oldHead? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeDonationFramePush scId pushRid pushReply oldHead? st = .ok st') :
    st'.tlbShootdown = st.tlbShootdown := by
  obtain ⟨_, s1, hS1, hRest⟩ := storeDonationFramePush_cases h
  have e1 : s1.tlbShootdown = st.tlbShootdown := by unfold storeObject at hS1; cases hS1; rfl
  rcases hRest with ⟨_, rfl⟩ | ⟨_, _, _, _, hS2⟩
  · exact e1
  · have e2 : st'.tlbShootdown = s1.tlbShootdown := by unfold storeObject at hS2; cases hS2; rfl
    rw [e2, e1]

theorem storeDonationFramePush_preserves_objectIndexSet_invExt
    {scId : SeLe4n.SchedContextId} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    {oldHead? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hSetInv : st.objectIndexSet.table.invExt)
    (h : storeDonationFramePush scId pushRid pushReply oldHead? st = .ok st') :
    st'.objectIndexSet.table.invExt := by
  obtain ⟨_, s1, hS1, hRest⟩ := storeDonationFramePush_cases h
  have e1 := storeObject_preserves_objectIndexSet_invExt st s1 _ _ hSetInv hS1
  rcases hRest with ⟨_, rfl⟩ | ⟨_, _, _, _, hS2⟩
  · exact e1
  · exact storeObject_preserves_objectIndexSet_invExt s1 st' _ _ e1 hS2

theorem storeDonationFramePush_preserves_objectIndexSetComplete
    {scId : SeLe4n.SchedContextId} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    {oldHead? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt) (hSetInv : st.objectIndexSet.table.invExt)
    (hComplete : ∀ oid, st.objects[oid]? ≠ none → st.objectIndexSet.contains oid = true)
    (h : storeDonationFramePush scId pushRid pushReply oldHead? st = .ok st') :
    ∀ oid, st'.objects[oid]? ≠ none → st'.objectIndexSet.contains oid = true := by
  obtain ⟨_, s1, hS1, hRest⟩ := storeDonationFramePush_cases h
  have hInv1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hSet1 := storeObject_preserves_objectIndexSet_invExt st s1 _ _ hSetInv hS1
  have c1 := storeObject_preserves_objectIndexSetComplete st s1 _ _ hObjInv hSetInv hComplete hS1
  rcases hRest with ⟨_, rfl⟩ | ⟨_, _, _, _, hS2⟩
  · exact c1
  · exact storeObject_preserves_objectIndexSetComplete s1 st' _ _ hInv1 hSet1 c1 hS2

theorem storeDonationFramePush_scheduler_eq
    {scId : SeLe4n.SchedContextId} {pushRid : SeLe4n.ReplyId} {pushReply : Reply}
    {oldHead? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeDonationFramePush scId pushRid pushReply oldHead? st = .ok st') :
    st'.scheduler = st.scheduler := by
  obtain ⟨_, s1, hS1, hRest⟩ := storeDonationFramePush_cases h
  have e1 : s1.scheduler = st.scheduler := by unfold storeObject at hS1; cases hS1; rfl
  rcases hRest with ⟨_, rfl⟩ | ⟨_, _, _, _, hS2⟩
  · exact e1
  · have e2 : st'.scheduler = s1.scheduler := by unfold storeObject at hS2; cases hS2; rfl
    rw [e2, e1]

/-- **WS-HP HP10.4: is this donation the FIRST push of this reservation?**

A first push is one where the donor still *owns* the context it is lending, which
is decidable from the donor's own binding: `SchedContextBinding.ownScId?` is `some`
exactly on `.bound` and `none` on `.unbound` and `.donated` (`v0.35.3`), so
`= some scId` says "this donor owns the very context in question".  An **onward**
push — a passive server that Calls in turn, which is what makes the chain
transitive — answers `false`.

One definition rather than an inline test, because `donateSchedContext` branches on
it and every statement about that operation's write set must name the same
question; two spellings of it would be free to drift, and the store-chain
decomposition is the *only* description of the operation. -/
@[inline] def donationFirstPush (donorTcb : TCB) (scId : SeLe4n.SchedContextId) : Bool :=
  donorTcb.schedContextBinding.ownScId? == some scId

-- ============================================================================
-- The SchedContext-binding frame (IPC de-threading D6; declared here since
-- WS-RR RR8.12 Cut C1, `v0.35.160`)
-- ============================================================================

/-- IPC de-threading D6: two states have **the same SchedContext bindings** when every
post-state TCB slot pulls back to a pre-state TCB carrying an equal `schedContextBinding`.
This is the exact frame `donationBudgetTransfer` (which reads only `schedContextBinding`)
needs: it is preserved by every core IPC transition that never writes a binding (all but
the donation primitives `donateSchedContext` / `returnDonatedSchedContext`, which is why
it is declared beside them).  Stated backward (post ⟹ pre) so it composes directly with
the store-frame style used throughout the de-threading proofs.

**WS-RR RR8.12 Cut C1 (`v0.35.160`, register row 55): declared HERE, in the operations
layer, and not in `IPC/Invariant/Defs.lean` where it was born.**
`callDonationSchedContext?` (`IPC/Operations/Donation.lean`) is the resolver every
donation-carrying footprint and transition read, and the `.receive` arm's replenish
segment has to transport its pre-state answer across the receive leg — which is
exactly this frame.  `Donation.lean`'s import closure did not contain `Defs.lean`, nor
the reverse, so the bridge from the frame to the resolver had no home beside the
resolver: *when a question has one owner and an asker that cannot see it, the owner
is in the wrong layer* (`v0.35.59`).  The predicate reads two model records and
nothing of the invariant layer, so this is where it always belonged; its two
invariant consumers (`donationBudgetTransfer_of_sameSchedContextBindings`,
`donationOwnerUnique_of_sameSchedContextBindings`) stay in `Defs.lean`, and the
`SeLe4n.Kernel` namespace is kept so that no call site is renamed. -/
def sameSchedContextBindings (st st' : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
    st'.objects[tid.toObjId]? = some (.tcb tcb') →
    ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
      tcb.schedContextBinding = tcb'.schedContextBinding

namespace sameSchedContextBindings

/-- Reflexivity: a state has the same bindings as itself. -/
theorem refl (st : SystemState) : sameSchedContextBindings st st :=
  fun _ tcb' h => ⟨tcb', h, rfl⟩

/-- Transitivity: chain two binding-preserving steps. -/
theorem trans {st st' st'' : SystemState}
    (h1 : sameSchedContextBindings st st') (h2 : sameSchedContextBindings st' st'') :
    sameSchedContextBindings st st'' := by
  intro tid tcb'' hObj''
  obtain ⟨tc', hObj', hEq'⟩ := h2 tid tcb'' hObj''
  obtain ⟨tc, hObj, hEq⟩ := h1 tid tc' hObj'
  exact ⟨tc, hObj, hEq.trans hEq'⟩

/-- A transition that leaves the object store untouched (a scheduler-only step such
as `removeRunnable` / `ensureRunnable`) preserves all bindings. -/
theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    sameSchedContextBindings st st' :=
  fun _ tcb' hObj => ⟨tcb', h ▸ hObj, rfl⟩

/-- **WS-RR RR8.12 Cut C1**: the pointwise form of `of_objects_eq` — a step invisible
to every object-store lookup preserves all bindings.  The cross-core `wakeThread` of
an already-`.ready` thread is such a step (`wakeThread_objects_getElem_eq_of_ready`)
without its table being *equal* to the pre-state's, which the whole-table form cannot
see. -/
theorem of_objects_getElem_eq {st st' : SystemState}
    (h : ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]?) :
    sameSchedContextBindings st st' :=
  fun tid tcb' hObj => ⟨tcb', by rw [← h tid.toObjId]; exact hObj, rfl⟩

/-- **WS-RR RR8.12 Cut C1**: a post-state `lookupTcb` pulls back to a pre-state
`lookupTcb` at the same thread with an equal binding — the frame read through the
reader `callDonationSchedContext?` actually uses.  `lookupTcb` is `getTcb?` under the
reserved-id refusal, and the refusal is a fact about the id alone, so it carries
across states unchanged. -/
theorem lookupTcb_backward {st st' : SystemState} (h : sameSchedContextBindings st st')
    (tid : SeLe4n.ThreadId) (tcb' : TCB) (hL : lookupTcb st' tid = some tcb') :
    ∃ tcb, lookupTcb st tid = some tcb ∧
      tcb.schedContextBinding = tcb'.schedContextBinding := by
  obtain ⟨tcb, hObj, hEq⟩ := h tid tcb' (lookupTcb_some_objects st' tid tcb' hL)
  exact ⟨tcb, lookupTcb_of_objects_of_not_reserved st tid tcb hObj
    (lookupTcb_some_not_reserved st' tid tcb' hL), hEq⟩

end sameSchedContextBindings

/-- WS-RR RR2.1: the SchedContext a `.call` donation would actually transfer —
`some scId` exactly when `applyCallDonation` takes its donating arm (the
receiver is passive and the caller holds a bound SchedContext), `none` on every
no-op arm.

Single-sourced here because three consumers need the same answer and a second
copy would drift: `applyCallDonationOnCore` names the SchedContext whose
replenishments migrate, the cross-core `.call` dispatch pre-resolves the
`lockSet_endpointCall` donation footprint from it, and the affinity proof below
case-splits on it.  Reading the same function is what keeps the declared lock
footprint and the executed write the same set. -/
def callDonationSchedContext? (st : SystemState) (caller receiver : SeLe4n.ThreadId) :
    Option SeLe4n.SchedContextId :=
  match lookupTcb st receiver with
  | some receiverTcb =>
      match receiverTcb.schedContextBinding with
      | .unbound =>
          match lookupTcb st caller with
          -- **WS-OD OD4.2**: the caller's *effective* context, bound or donated
          -- (`SchedContextBinding.scId?`), so the resolver and the transition
          -- widen in the same cut and cannot disagree about whether a call
          -- donates.
          | some callerTcb => callerTcb.schedContextBinding.scId?
          | none => none
      | _ => none
  | none => none

/-- **WS-OD OD4.2/OD4.6: the guard fires at call depth ≥ 2.**

The resolver reads the caller's *effective* context, so a caller that is itself
holding a donation (`.donated scId owner` -- the intermediate server of a chain)
names `scId` exactly as a `.bound` caller names its own.  This is the fact that
makes the chain transitive at the resolver, stated rather than read off the
definition at each of its three consumers.

The receiver's `.unbound` premise is the other half of the guard and is what a
passive server *is*; without it the call is a no-op at any depth. -/
theorem callDonationSchedContext?_of_donated_caller
    (st : SystemState) (caller receiver : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (cTcb rTcb : TCB)
    (hR : lookupTcb st receiver = some rTcb)
    (hRB : rTcb.schedContextBinding = .unbound)
    (hC : lookupTcb st caller = some cTcb)
    (hCB : cTcb.schedContextBinding = .donated scId owner) :
    callDonationSchedContext? st caller receiver = some scId := by
  unfold callDonationSchedContext?
  rw [hR]
  simp only []
  rw [hRB]
  simp only []
  rw [hC]
  simp only []
  rw [hCB]
  rfl

/-- **WS-RR RR8.12 Cut C1 (register row 55): the resolver's `some` answer transports
BACKWARD across a binding-preserving step.**

`sameSchedContextBindings st st'` says every post-state TCB pulls back to a pre-state
TCB with the same binding, and `callDonationSchedContext?` reads nothing but two
threads' bindings through `lookupTcb` — so a post-state `some scId` was already the
pre-state's answer.  This is the direction a footprint needs and the only one the
backward frame gives: the `.receive` arm's replenish segment is resolved on the
syscall's PRE-state while WS-OD OD3.6's donation runs at the POST-receive-leg state,
and a footprint is sound exactly when *the transition migrates ⟹ the footprint
declares*, i.e. post `some` ⟹ pre `some`.  The forward direction (pre `some` ⟹ post
`some`) is neither given by the frame nor needed: a footprint that declares on a
pre-state `some` the transition then declines is wider than its operation, which is
sound.

Declared beside the resolver, which is why the frame moved down to
`IPC/Operations/Endpoint.lean` in the same cut: *when a question has one owner and an
asker that cannot see it, the owner is in the wrong layer* (`v0.35.59`). -/
theorem callDonationSchedContext?_some_of_sameSchedContextBindings
    {st st' : SystemState} (hSame : sameSchedContextBindings st st')
    (caller receiver : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hPost : callDonationSchedContext? st' caller receiver = some scId) :
    callDonationSchedContext? st caller receiver = some scId := by
  unfold callDonationSchedContext? at hPost ⊢
  cases hR' : lookupTcb st' receiver with
  | none => rw [hR'] at hPost; simp at hPost
  | some rTcb' =>
    rw [hR'] at hPost
    simp only [] at hPost
    obtain ⟨rTcb, hR, hRB⟩ := hSame.lookupTcb_backward receiver rTcb' hR'
    rw [hR]
    simp only []
    cases hRB' : rTcb'.schedContextBinding with
    | bound _ => rw [hRB'] at hPost; simp at hPost
    | donated _ _ => rw [hRB'] at hPost; simp at hPost
    | unbound =>
      rw [hRB'] at hPost
      simp only [] at hPost
      rw [hRB, hRB']
      simp only []
      cases hC' : lookupTcb st' caller with
      | none => rw [hC'] at hPost; simp at hPost
      | some cTcb' =>
        rw [hC'] at hPost
        simp only [] at hPost
        obtain ⟨cTcb, hC, hCB⟩ := hSame.lookupTcb_backward caller cTcb' hC'
        rw [hC]
        simp only []
        rw [hCB]
        exact hPost

/-- **WS-RR RR8.12 Cut C1**: the contrapositive, in the shape the narrowed replenish
segment consumes — a pre-state `none` is a post-state `none`, so a receive whose
pre-state resolver declines migrates nothing at the state its donation runs on. -/
theorem callDonationSchedContext?_none_of_sameSchedContextBindings
    {st st' : SystemState} (hSame : sameSchedContextBindings st st')
    (caller receiver : SeLe4n.ThreadId)
    (hPre : callDonationSchedContext? st caller receiver = none) :
    callDonationSchedContext? st' caller receiver = none := by
  cases hPost : callDonationSchedContext? st' caller receiver with
  | none => rfl
  | some scId =>
    rw [callDonationSchedContext?_some_of_sameSchedContextBindings hSame caller receiver scId
      hPost] at hPre
    cases hPre

/-- **WS-RR RR8.12 Cut C6f**: a thread donates nothing to itself.

The resolver requires the *receiver* `.unbound` and then reads the **caller's**
effective context — so with one thread in both roles the second read is of an
`.unbound` binding, whose `scId?` is `none`.  The `.receive` arm's block path hands
the hand-off the receiver's own id (it dequeued nobody), which is what makes this
the whole of that path's donation story: no guard on the post-state `ipcState` is
needed, because the resolver refuses on the pre-state shape alone. -/
@[simp] theorem callDonationSchedContext?_self (st : SystemState) (tid : SeLe4n.ThreadId) :
    callDonationSchedContext? st tid tid = none := by
  unfold callDonationSchedContext?
  cases hT : lookupTcb st tid with
  | none => rfl
  | some tcb =>
    cases hB : tcb.schedContextBinding with
    | unbound => simp only [hB, SchedContextBinding.scId?]
    | bound scId => simp only [hB]
    | donated scId owner => simp only [hB]

/-- Z7-B2: Transfer a client's SchedContext to a passive server during IPC Call.

Performs the full ownership transfer of the SchedContext from donor to server,
and records the transfer on the context's reply stack:
1. SchedContext `boundThread` updated to point to the server, and its stack head
   (`scReply`) pushed to the donor's own reply object (WS-OD OD4.1).
2. That reply becomes the head (`next := .head clientScId`) and links down to
   the frame the context headed before (`prev`); that frame, when there is one,
   now links up to the pushed one (`next := .frame pushRid`) — seL4's doubly
   linked `reply_push`, one `storeDonationFramePush`.
3. Donor (client) TCB's `schedContextBinding` cleared to `.unbound` — the donor
   gives up its SchedContext for the duration of the Call.
4. Server TCB gets `schedContextBinding := .donated(clientScId, clientTid)`.

**WS-OD OD4.1 — the push, and why it is here.**  seL4-MCS performs the donation
inside `reply_push`, which is why its stack depth and its donation depth cannot
disagree.  This kernel keeps the reply linking and the donation separate, so the
push lives here, at the one operational construction site of a `.donated`
binding: one donation, one frame.  The pop (`returnDonatedSchedContext`) clears
exactly one frame and reads the frame *below* the head to decide which thread
the context settles on, so a donation that recorded no frame would make the next
pop clear an outer caller's frame and hand the context to the wrong thread —
across a domain boundary, in a state that breaks no conjunct.  That is why
`donationPushFrame?` refuses rather than skipping.

**The `owner` of the minted binding stays the immediate donor** at every depth.
`.donated clientScId clientTid` names the thread this context came from *now*,
not the thread that owns it at the bottom of the stack, which is what keeps all
five donation conjuncts true in a chain of any length with their current
definitions: only the innermost holder carries a `.donated` binding, and the
transitive structure lives entirely in the reply stack.

**Donor-clear (Finding F-3 remediation).** Clearing the donor here is what makes
the SchedContext referenced by **exactly one** binding after donation — the
server's `.donated` — never jointly with a residual donor `.bound`.  Without it,
`donationBudgetTransfer` (no two threads share one SchedContext) and
`donationOwnerValid` (the donor is `.unbound`, awaiting the reply that returns
the SchedContext) are jointly unsatisfiable for every donated state, so
`ipcInvariantFull` would vacuously skip all donating Calls.  This mirrors seL4
MCS `sched_context_donate`, which clears the previous holder's
`tcb_sched_context` before binding the SchedContext to the new thread.  The
donor remains recoverable: the server's `.donated scId clientTid` records the
owner, and the reply object (`blockedOnReply`) links the donor to the call so
`returnDonatedSchedContext` rebinds it on reply.

**Preconditions** (enforced by caller `endpointCall` / `applyCallDonation`):
- Server has `schedContextBinding = .unbound` (passive)
- Client has `schedContextBinding = .bound clientScId`
- SchedContext `sc.boundThread = some clientTid`

Returns the updated state or error if lookups fail.

**Atomicity contract (AC3-A / I-02)**:
This function performs 4 sequential store steps (through states
`st` → `st1` → `st2` → `st3` → `st4`) with intermediate lookups — the second
step being one or two `storeObject`s (`storeDonationFramePush`):
  1. `storeObject` SchedContext with `boundThread := some serverTid` and
     `scReply := some pushRid` → `st1`.
  2. `storeDonationFramePush`: the pushed Reply with `next := .head clientScId`
     and `prev := sc.scReply` (the frame below), then that frame's
     `next := .frame pushRid` when there is one → `st2`.
  3. `storeObject` donor TCB with `schedContextBinding := .unbound` → `st3`.
  4. `storeObject` server TCB with `schedContextBinding := .donated` → `st4`.
The donor store is ordered **before** the server store so the server's
`.donated` binding is the final object write, keeping the server-binding
postcondition (`donateSchedContext_server_binding`) free of a
`clientTid ≠ serverTid` side-condition.
In the `KernelM` monad (`Except KernelError`), `.error` carries **no state** —
only the error value. If an early step succeeds but a later step fails, the
intermediate state is discarded by the monad's `bind` operation and the
caller receives `.error` with no access to the partial state. There is no
"partial state leak" risk in the pure model.
On hardware, kernel transitions execute with interrupts disabled (single-core
microkernel), so no concurrent observer can see intermediate states. -/
def donateSchedContext
    (st : SystemState)
    (clientTid : SeLe4n.ThreadId) (serverTid : SeLe4n.ThreadId)
    (clientScId : SeLe4n.SchedContextId) : Except KernelError SystemState :=
  -- Step 1: Look up the SchedContext, through the state's own typed accessor
  -- (the AK7 cascade counts an unmigrated raw store read as debt, and this one
  -- is a whole `SchedContext` the operation wants).
  match st.getSchedContext? clientScId with
  | some sc =>
    -- AUD-3b: Defense-in-depth — verify SchedContext is bound to the caller
    if sc.boundThread != some clientTid then .error .invalidArgument
    else
    -- WS-OD OD4.1: resolve the frame this donation pushes **before any store**,
    -- from the donor's own TCB, so a donation that cannot record its frame
    -- commits nothing.  The read is of the pre-state — the discipline
    -- `donationHeadOf?` follows on the pop and `recordedReplyServer?` on the
    -- reply leg; the donor's TCB is re-read below for the *value* the binding
    -- clear updates, which is a different question from *which frame* the push
    -- records.
    match lookupTcb st clientTid with
    | none => .error .objectNotFound
    | some donorTcb =>
      match donationPushFrame? st donorTcb with
      | .error e => .error e
      | .ok (pushRid, pushReply) =>
        -- Step 2: Update SchedContext to point to the server, and make the
        -- donor's reply the new head of its donation stack (WS-OD OD4.1).  One
        -- store: the rebinding and the push are the same fact about the same
        -- object, and splitting them would admit an intermediate state whose
        -- stack head and bound thread disagree.
        -- **WS-HP HP10.4: record the reservation's ORIGIN on a FIRST push.**
        --
        -- A first push is one where the donor still *owns* the context, which is
        -- decidable from its own binding: `SchedContextBinding.ownScId?` is
        -- `some` exactly on `.bound` and `none` on `.unbound` and `.donated`
        -- (`v0.35.3`), so `= some clientScId` says "this donor owns the very
        -- context it is lending".  An **onward** push -- a passive server that
        -- Calls in turn, which is what makes the chain transitive -- leaves the
        -- field alone, and that is precisely what makes it the *origin* rather
        -- than the immediate donor: the immediate donor is already recoverable
        -- from `.donated scId owner`, and a field recording it would be the
        -- duplicate this project retires.
        --
        -- A first push also *repairs* a stale origin rather than preserving it:
        -- the donor owning the context means the previous loan ended, and every
        -- step that ends one clears the field, so a `some` found here would be
        -- residue.  Writing unconditionally on this arm is therefore the
        -- fail-safe direction as well as the simple one.
        let sc' := { sc with boundThread := some serverTid,
                             scReply := some pushRid,
                             donationOrigin :=
                               if donationFirstPush donorTcb clientScId then some clientTid
                               else sc.donationOrigin }
        match storeObject clientScId.toObjId (.schedContext sc') st with
        | .error e => .error e
        | .ok ((), st1) =>
          -- Step 3 (WS-OD OD4.1 / `v0.35.4`): record the frame — it becomes the
          -- head, links down to whatever the context headed before, and that
          -- frame links back up to it.  The exact inverse of the pop's
          -- `storeDonationHeadPop`.
          match storeDonationFramePush clientScId pushRid pushReply sc.scReply st1 with
          | .error e => .error e
          | .ok st2 =>
            -- Step 4 (F-3 fix): Clear the donor's binding — the client gives up
            -- its SchedContext for the duration of the Call.  Ordered before
            -- the server store so the server's `.donated` write is the final
            -- object mutation.
            match lookupTcb st2 clientTid with
            | none => .error .objectNotFound
            | some clientTcb =>
              let clientTcb' := { clientTcb with schedContextBinding := .unbound }
              match storeObject clientTid.toObjId (.tcb clientTcb') st2 with
              | .error e => .error e
              | .ok ((), st3) =>
                -- Step 5: Look up and update server TCB with donated binding
                match lookupTcb st3 serverTid with
                | none => .error .objectNotFound
                | some serverTcb =>
                  let serverTcb' := { serverTcb with
                    schedContextBinding := .donated clientScId clientTid }
                  match storeObject serverTid.toObjId (.tcb serverTcb') st3 with
                  | .error e => .error e
                  | .ok ((), st4) =>
                    -- S-05/PERF-O1 + F-3: the SchedContext's referencing threads
                    -- change from {donor} to {server}: add the server and remove
                    -- the now-`.unbound` donor.  This keeps
                    -- `scThreadIndexConsistent` (a thread is indexed under
                    -- `scId` iff its binding references `scId`) and
                    -- `timeoutBlockedThreads` accurate — only the server (which
                    -- actually runs on the SchedContext) is iterated on budget
                    -- exhaustion, never the descheduled donor.
                    .ok { st4 with scThreadIndex :=
                      (scThreadIndexRemove
                        (scThreadIndexAdd st4.scThreadIndex clientScId serverTid)
                        clientScId clientTid) }
  | none => .error .objectNotFound

/-- WS-OD OD4.1: **the donation push *is* four store steps followed by a
`scThreadIndex` update** — three `storeObject`s and one `storeDonationFramePush`
(itself one or two Reply stores, `storeDonationFramePush_cases`).

The mirror of `returnDonatedSchedContext_ok_storeChain`, and the only description
of this operation: every field frame, every pointwise TCB reading and every
object-store fact about `donateSchedContext` is a corollary of this one
decomposition rather than a fresh case analysis over the chain.  Stated as a
**complete** decomposition — the SchedContext read and its `boundThread` guard,
the donor's TCB read, the resolved push frame, the four objects actually stored,
and `st' = { s4 with scThreadIndex := st'.scThreadIndex }` for the final step —
so a field added to `TCB`, `Reply`, `SchedContext` or `SystemState` is covered by
construction, and an incomplete description cannot license a conclusion the
operation does not earn.

It supersedes the pre-OD4 `donateSchedContext_walk`, which described three of the
four stores and was therefore a *weaker duplicate* of the same question — the
shape `returnDonatedSchedContext_walk` was retired for at OD3.2. -/
theorem donateSchedContext_ok_storeChain
    (st st' : SystemState) (clientTid serverTid : SeLe4n.ThreadId)
    (clientScId : SeLe4n.SchedContextId)
    (h : donateSchedContext st clientTid serverTid clientScId = .ok st') :
    ∃ (sc : SchedContext) (donorTcb clientTcb serverTcb : TCB)
      (pushRid : SeLe4n.ReplyId) (pushReply : Reply) (s1 s2 s3 s4 : SystemState),
      st.getSchedContext? clientScId = some sc ∧
      sc.boundThread = some clientTid ∧
      lookupTcb st clientTid = some donorTcb ∧
      donationPushFrame? st donorTcb = .ok (pushRid, pushReply) ∧
      storeObject clientScId.toObjId
        (.schedContext { sc with boundThread := some serverTid,
                                 scReply := some pushRid,
                                 -- **WS-HP HP10.4**: and the origin, on a first
                                 -- push only.  Named in the decomposition rather
                                 -- than abstracted, because this lemma is the
                                 -- *only* description of the operation and a
                                 -- component it does not mention is a write no
                                 -- consumer can reason about.
                                 donationOrigin :=
                                   if donationFirstPush donorTcb clientScId
                                   then some clientTid else sc.donationOrigin }) st
        = .ok ((), s1) ∧
      storeDonationFramePush clientScId pushRid pushReply sc.scReply s1 = .ok s2 ∧
      lookupTcb s2 clientTid = some clientTcb ∧
      storeObject clientTid.toObjId
        (.tcb { clientTcb with schedContextBinding := .unbound }) s2 = .ok ((), s3) ∧
      lookupTcb s3 serverTid = some serverTcb ∧
      storeObject serverTid.toObjId
        (.tcb { serverTcb with schedContextBinding := .donated clientScId clientTid })
        s3 = .ok ((), s4) ∧
      st' = { s4 with scThreadIndex := st'.scThreadIndex } := by
  unfold donateSchedContext at h
  revert h
  cases hObj : st.getSchedContext? clientScId with
  | none => intro h; cases h
  | some sc =>
      simp only []
      cases hBne : (sc.boundThread != some clientTid) with
      | true => simp only [if_true]; intro h; cases h
      | false =>
        simp only [Bool.false_eq_true, if_false]
        cases hDonor : lookupTcb st clientTid with
        | none => intro h; cases h
        | some donorTcb =>
          simp only []
          cases hFrame : donationPushFrame? st donorTcb with
          | error _ => intro h; cases h
          | ok frame =>
            obtain ⟨pushRid, pushReply⟩ := frame
            simp only []
            cases hS1 : storeObject clientScId.toObjId
                (.schedContext { sc with boundThread := some serverTid,
                                         scReply := some pushRid,
                                         donationOrigin :=
                                           if donationFirstPush donorTcb clientScId
                                           then some clientTid
                                           else sc.donationOrigin }) st with
            | error _ => intro h; cases h
            | ok p1 =>
              simp only []
              cases hS2 : storeDonationFramePush clientScId pushRid pushReply sc.scReply p1.2 with
              | error _ => intro h; cases h
              | ok s2 =>
                simp only []
                cases hLC : lookupTcb s2 clientTid with
                | none => intro h; cases h
                | some clientTcb =>
                  simp only []
                  cases hS3 : storeObject clientTid.toObjId
                      (.tcb { clientTcb with schedContextBinding := .unbound }) s2 with
                  | error _ => intro h; cases h
                  | ok p3 =>
                    simp only []
                    cases hL : lookupTcb p3.2 serverTid with
                    | none => intro h; cases h
                    | some serverTcb =>
                      simp only []
                      cases hS4 : storeObject serverTid.toObjId
                          (.tcb { serverTcb with
                                    schedContextBinding := .donated clientScId clientTid })
                          p3.2 with
                      | error _ => intro h; cases h
                      | ok p4 =>
                        simp only [Except.ok.injEq]
                        intro hEq; subst hEq
                        obtain ⟨u1, s1⟩ := p1; cases u1
                        obtain ⟨u3, s3⟩ := p3; cases u3
                        obtain ⟨u4, s4⟩ := p4; cases u4
                        exact ⟨sc, donorTcb, clientTcb, serverTcb, pushRid, pushReply,
                          s1, s2, s3, s4, rfl,
                          by simpa using hBne, rfl, hFrame,
                          hS1, hS2, hLC, hS3, hL, hS4, rfl⟩

/-- WS-OD OD4.1: **the pushed frame is the donor's own reply object, and it is
the context's new head.**

The three facts a consumer of the push needs about the reply stack, read off the
decomposition once: the frame is the donor's `replyObject`, it carried no
donation before the push, and the SchedContext store makes it the head.  Stated
here so the chain-preservation proof (OD4.5) and the footprint argument (OD4.7)
consume a fact rather than re-running the case analysis. -/
theorem donateSchedContext_ok_pushFrame
    (st st' : SystemState) (clientTid serverTid : SeLe4n.ThreadId)
    (clientScId : SeLe4n.SchedContextId)
    (h : donateSchedContext st clientTid serverTid clientScId = .ok st') :
    ∃ (donorTcb : TCB) (pushRid : SeLe4n.ReplyId) (pushReply : Reply),
      lookupTcb st clientTid = some donorTcb ∧
      donorTcb.replyObject = some pushRid ∧
      st.getReply? pushRid = some pushReply ∧
      pushReply.prev = none ∧ pushReply.next = none := by
  obtain ⟨_, donorTcb, _, _, pushRid, pushReply, _, _, _, _, _, _, hDonor, hFrame, _⟩ :=
    donateSchedContext_ok_storeChain st st' clientTid serverTid clientScId h
  obtain ⟨hRO, hRep, hPrev, hNext, _⟩ := donationPushFrame?_ok st donorTcb pushRid pushReply hFrame
  exact ⟨donorTcb, pushRid, pushReply, hDonor, hRO, hRep, hPrev, hNext⟩

/-- WS-OD OD4.1: **a Reply and a SchedContext never share an object-store key.**

The distinctness the push's two non-TCB stores need — the SchedContext rebinding
and the frame record land at different keys, so each frames the other.  Stated
once, over the *typed* readings, because the same three-line derivation had
started appearing at every site that composes the two stores; the shape is the
one `getTcb?_getSchedContext?_key_ne` already has for the TCB/SchedContext
pair. -/
theorem getReply?_getSchedContext?_key_ne (st : SystemState)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (r : Reply) (sc : SchedContext)
    (hR : st.getReply? rid = some r) (hSc : st.getSchedContext? scId = some sc) :
    rid.toObjId ≠ scId.toObjId := by
  intro hEq
  have hRraw := (SystemState.getReply?_eq_some_iff st rid r).mp hR
  have hScRaw := (SystemState.getSchedContext?_eq_some_iff st scId sc).mp hSc
  rw [hEq, hScRaw] at hRraw
  cases hRraw

/-- **WS-OD OD4.7: the push's write set, by key.**

`donateSchedContext` writes exactly four objects -- the scheduling context (its
`boundThread` and its new stack head), the Reply the new frame *is*, the donor's
TCB and the server's TCB -- and nothing else in the store moves.  Derived from the
store chain rather than restated, so a fifth store cannot be added without this
theorem failing.

The pushed Reply is not an argument: it is the donor's own `replyObject`, which
`donationPushFrame?` resolved and this exhibits, so a consumer that has to know
*which* Reply is written reads it off the same field the operation read.  That is
what makes the `.call` footprint's Reply member (the server-first stashed Reply
the rendezvous linked to this very caller) provably the key written here. -/
theorem donateSchedContext_objects_ne
    (st st' : SystemState) (clientTid serverTid : SeLe4n.ThreadId)
    (clientScId : SeLe4n.SchedContextId)
    (hObjInv : st.objects.invExt)
    (h : donateSchedContext st clientTid serverTid clientScId = .ok st') :
    ∃ (sc : SchedContext) (pushRid : SeLe4n.ReplyId),
      st.getSchedContext? clientScId = some sc ∧
      (∃ donorTcb, lookupTcb st clientTid = some donorTcb ∧
        donorTcb.replyObject = some pushRid) ∧
      ∀ k : SeLe4n.ObjId, k ≠ clientScId.toObjId → k ≠ pushRid.toObjId →
        (∀ old, sc.scReply = some old → k ≠ old.toObjId) →
        k ≠ clientTid.toObjId → k ≠ serverTid.toObjId →
        st'.objects[k]? = st.objects[k]? := by
  obtain ⟨sc, donorTcb, clientTcb, serverTcb, pushRid, pushReply, s1, s2, s3, s4,
      hObj, _, hDonor, hFrame, hS1, hS2, _, hS3, _, hS4, hEq⟩ :=
    donateSchedContext_ok_storeChain st st' clientTid serverTid clientScId h
  obtain ⟨hRepObj, _, _⟩ := donationPushFrame?_ok st donorTcb pushRid pushReply hFrame
  refine ⟨sc, pushRid, hObj, ⟨donorTcb, hDonor, hRepObj⟩, ?_⟩
  intro k hkSc hkRid hkOld hkC hkS
  have hInv1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 := storeDonationFramePush_preserves_objects_invExt hInv1 hS2
  have hInv3 := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  have e1 := storeObject_objects_ne st s1 _ k _ hkSc hObjInv hS1
  have e2 := storeDonationFramePush_objects_ne hInv1 hS2 k hkRid hkOld
  have e3 := storeObject_objects_ne s2 s3 _ k _ hkC hInv2 hS3
  have e4 := storeObject_objects_ne s3 s4 _ k _ hkS hInv3 hS4
  have hObjs : st'.objects = s4.objects := by rw [hEq]
  rw [hObjs, e4, e3, e2, e1]

/-- WS-OD OD4.1: **what the push does to the reply stack**, in the two readings
the chain invariant makes: the context's head *is* the pushed frame afterwards,
and the pushed frame carries this context and links down to whatever the context
headed before.

This is the operational content of "one donation contributes one frame".  It is
stated over the typed accessors because that is what `donationChainWellFormed`'s
walk consults (`replyStackLinks?` / `schedContextStackHead?` are projections of
the same objects), so OD4.5's preservation proof reads a fact rather than
re-running the store chain. -/
theorem donateSchedContext_ok_pushedHead
    (st st' : SystemState) (clientTid serverTid : SeLe4n.ThreadId)
    (clientScId : SeLe4n.SchedContextId) (hObjInv : st.objects.invExt)
    (h : donateSchedContext st clientTid serverTid clientScId = .ok st') :
    ∃ (sc : SchedContext) (donorTcb : TCB) (pushRid : SeLe4n.ReplyId) (pushReply : Reply),
      st.getSchedContext? clientScId = some sc ∧
      lookupTcb st clientTid = some donorTcb ∧
      st.getReply? pushRid = some pushReply ∧
      pushReply.prev = none ∧ pushReply.next = none ∧
      -- **WS-HP HP10.4**: the donor's TCB is exposed so the post-state record can
      -- be named in full, origin included, rather than the origin being
      -- abstracted away.  This theorem is a corollary of `_ok_storeChain` and
      -- inherits its standard: a component the description does not mention is a
      -- write no consumer can reason about.
      st'.getSchedContext? clientScId =
        some { sc with boundThread := some serverTid, scReply := some pushRid,
                       donationOrigin :=
                         if donationFirstPush donorTcb clientScId then some clientTid
                         else sc.donationOrigin } ∧
      st'.getReply? pushRid =
        some { pushReply with prev := sc.scReply, next := some (.head clientScId) } := by
  obtain ⟨sc, donorTcb, clientTcb, serverTcb, pushRid, pushReply, s1, s2, s3, s4,
      hObj, _, hDonor, hFrame, hS1, hS2, hLC, hS3, hLS, hS4, hEq⟩ :=
    donateSchedContext_ok_storeChain st st' clientTid serverTid clientScId h
  obtain ⟨_, hRepPre, hPrevNone, hNextNone, _⟩ :=
    donationPushFrame?_ok st donorTcb pushRid pushReply hFrame
  have hKeyNe := getReply?_getSchedContext?_key_ne st pushRid clientScId pushReply sc
    hRepPre hObj
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeDonationFramePush_preserves_objects_invExt hInv1 hS2
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  -- The frame's own key survives the SchedContext store.
  have hRep1 : s1.getReply? pushRid = some pushReply := by
    rw [SystemState.getReply?_eq_some_iff,
      storeObject_objects_ne st s1 clientScId.toObjId pushRid.toObjId _ hKeyNe hObjInv hS1]
    exact (SystemState.getReply?_eq_some_iff st pushRid pushReply).mp hRepPre
  -- Both readings are written by their own store and framed by the other three.
  have hSc1 : s1.getSchedContext? clientScId
      = some { sc with boundThread := some serverTid, scReply := some pushRid,
                       donationOrigin :=
                         if donationFirstPush donorTcb clientScId then some clientTid
                         else sc.donationOrigin } := by
    rw [SystemState.getSchedContext?_eq_some_iff,
      storeObject_objects_eq st s1 clientScId.toObjId _ hObjInv hS1]
  have hSc2 := storeDonationFramePush_getSchedContext?_eq hInv1 hRep1 hS2 clientScId
  have hSc3 := storeObject_tcbAt_getSchedContext?_eq_donation s2 s3 clientTid clientTcb _
    ((SystemState.getTcb?_eq_some_iff s2 clientTid clientTcb).mpr
      (lookupTcb_some_objects s2 clientTid clientTcb hLC)) hInv2 hS3 clientScId
  have hSc4 := storeObject_tcbAt_getSchedContext?_eq_donation s3 s4 serverTid serverTcb _
    ((SystemState.getTcb?_eq_some_iff s3 serverTid serverTcb).mpr
      (lookupTcb_some_objects s3 serverTid serverTcb hLS)) hInv3 hS4 clientScId
  have hRep2 : s2.getReply? pushRid
      = some { pushReply with prev := sc.scReply, next := some (.head clientScId) } :=
    storeDonationFramePush_getReply?_pushed hInv1 hS2
  have hRep3 := storeObject_tcbAt_getReply?_eq_donation s2 s3 clientTid clientTcb _
    ((SystemState.getTcb?_eq_some_iff s2 clientTid clientTcb).mpr
      (lookupTcb_some_objects s2 clientTid clientTcb hLC)) hInv2 hS3 pushRid
  have hRep4 := storeObject_tcbAt_getReply?_eq_donation s3 s4 serverTid serverTcb _
    ((SystemState.getTcb?_eq_some_iff s3 serverTid serverTcb).mpr
      (lookupTcb_some_objects s3 serverTid serverTcb hLS)) hInv3 hS4 pushRid
  refine ⟨sc, donorTcb, pushRid, pushReply, hObj, hDonor, hRepPre, hPrevNone, hNextNone, ?_, ?_⟩
  · rw [hEq]
    show s4.getSchedContext? clientScId = _
    rw [hSc4, hSc3, hSc2, hSc1]
  · rw [hEq]
    show s4.getReply? pushRid = _
    rw [hRep4, hRep3, hRep2]

/-- WS-OD OD3.1: **the binding a returned scheduling context lands in.**

`none` at the bottom of the reply stack — the thread receiving the context back
is its owner, so it becomes `.bound`.  `some outer` one level up — the thread
receiving it back is itself a *donor*, still owing the context to `outer`, so it
becomes `.donated scId outer` and the binding's `owner` stays the **immediate**
donor at every depth.  That is what keeps all five donation conjuncts true in a
chain of any length with their current definitions: only the innermost holder
carries a `.donated` binding, and the transitive structure lives in the reply
stack rather than in the binding graph. -/
@[inline] def donationReturnBinding (scId : SeLe4n.SchedContextId) :
    Option SeLe4n.ThreadId → SchedContextBinding
  | none => .bound scId
  | some outer => .donated scId outer

@[simp] theorem donationReturnBinding_none (scId : SeLe4n.SchedContextId) :
    donationReturnBinding scId none = .bound scId := rfl

@[simp] theorem donationReturnBinding_some (scId : SeLe4n.SchedContextId)
    (outer : SeLe4n.ThreadId) :
    donationReturnBinding scId (some outer) = .donated scId outer := rfl

/-- **WS-RR RR8: the SchedContext record a donation pop stores.**

`donationReturnBinding`'s counterpart on the other side of the pop's first write.
The pop rewrites a *pair* — the reservation and the recipient's binding — and
until `v0.35.100` only the binding had a name, so the reservation's record was
spelled as a literal at **eighteen** sites across four files -- eight here, eight
in `IPC/Invariant/DonationPreservation.lean`, and one each in
`IPC/Invariant/Defs.lean` and `FrozenOps/Core.lean` -- and a field added to it was
eighteen edits.  It is one definition now, which is what makes the next field a
single edit rather than a sweep, and what lets the frozen mirror store the **same**
record rather than a second copy of its shape.

Two of those files no longer name it at all.  The pop's two chain-preservation
lemmas (`donationHeadPop_preserves_donationChainWellFormed{,_of_except}`) are
statements about the STORE SURFACE the pop is built from rather than about the pop,
so they quantify over the stored record and constrain the one field their proof
reads -- which is more general than either record spelling and is what
`donationChainFrame` does for the same reason.  Stating them over this record was
measured to be strictly narrower: the depth-2 witness in
`tests/SmpCrossCoreCallSuite.lean` stores a record that KEEPS its `donationOrigin`,
which no value of `newOwner?` produces, so the named form refused it.

Three fields:

* `boundThread` names the recipient, which is what "the reservation is owned
  again" means at the bottom of a stack and what "the loan moved outward one
  frame" means above it.
* `scReply` is the frame below the head the pop clears — `nextHead?`, resolved by
  the caller from `donationHeadOf?`, because the head's own links are what the
  validation read and re-reading them here would be a second answer to that
  question.
* `donationOrigin` clears **exactly** on the bottom arm (WS-HP HP10.4): there the
  loan has ended, so a recorded origin is stale history and the thread-id-reuse
  hazard its own docstring names; above it the loan is still travelling outward
  and the origin is the fact the field exists to carry.

**What it deliberately does NOT write is `SchedContext.priority` — nor
`SchedContext.domain`, nor either of the recipient's own.**  A `.bound` thread's
band and partition are each stored twice: in its TCB, which every scheduling
decision reads, and on the reservation, which is what `schedContextBind`
propagates from and `schedContextConfigureBoundPropagate` moves in step.  This
arm installs a `.bound` binding and refreshes neither, so a reservation whose
band or domain moved while it was on loan comes back disagreeing — which is the
`boundThreadPriorityConsistent` / `boundThreadDomainConsistent` residue PR #897's
review reported and `docs/REGISTERED_DEBT.md` table C now registers.

**Refreshing either here is not the remedy, in either direction**, and that is
what makes those two predicates facts about their *writers* rather than defects
in this one:

* `tcb.priority := sc.priority` would undo a demotion by an IPC reply, and
  `tcb.domain := sc.domain` would migrate a thread's partition on one — at the
  instance of a holder of a capability on the **reservation**, which says nothing
  about the thread.  That is the authority crossing WS-OD `v0.35.3` closed from
  the other side.
* `sc.priority := tcb.priority` would silently retune a band that capability's
  holder had just set, and is projection-**visible** besides:
  `SchedContext.priority` survives `projectKernelObject` (thread priority is
  deliberately observable — see `Projection.lean` §2), so writing a possibly-high
  recipient's band into a possibly-low reservation makes
  `returnDonatedSchedContext_preserves_projection` false.

Nothing is mis-scheduled by the residue: since `v0.35.133` and `v0.35.136` every
band read is `tcb.priority` (`resolveEffectivePrioDeadline_fst_eq_boostedPriority`)
and every domain read is `tcb.domain` (`effectiveSchedParams_domain_eq`), so the
recipient resumes at its own band in its own partition.  The class fix is to stop
storing either parameter twice, which is a scheduling-model change WS-CB owns;
`tests/PriorityManagementSuite.lean`'s WS-RR-PRIO-09/10 is the executed
refutation and its control. -/
@[inline] def donationReturnSchedContext (sc : SchedContext)
    (originalOwner : SeLe4n.ThreadId) (nextHead? : Option SeLe4n.ReplyId)
    (newOwner? : Option SeLe4n.ThreadId) : SchedContext :=
  { sc with
      boundThread := some originalOwner,
      scReply := nextHead?,
      donationOrigin := if newOwner?.isNone then none else sc.donationOrigin }

@[simp] theorem donationReturnSchedContext_scReply (sc : SchedContext)
    (originalOwner : SeLe4n.ThreadId) (nextHead? : Option SeLe4n.ReplyId)
    (newOwner? : Option SeLe4n.ThreadId) :
    (donationReturnSchedContext sc originalOwner nextHead? newOwner?).scReply
      = nextHead? := rfl

/-- **WS-RR RR8**: the reservation's own configured band is untouched by a pop —
the fact the registered priority-mirror row is about, stated here rather than
left to be read off the record. -/
@[simp] theorem donationReturnSchedContext_priority (sc : SchedContext)
    (originalOwner : SeLe4n.ThreadId) (nextHead? : Option SeLe4n.ReplyId)
    (newOwner? : Option SeLe4n.ThreadId) :
    (donationReturnSchedContext sc originalOwner nextHead? newOwner?).priority
      = sc.priority := rfl

/-- **WS-RR (`v0.35.136`): and so is its configured partition.**  The sibling of
the band above, added when PR #897's review showed the two mirrors have one hole:
`schedContextConfigure` moves either field on a **donated** reservation without
propagating (the donee's `ownScId?` is `none`), and this arm then rebinds the
origin `.bound` under it.  Stated so that a cut which decides to reconcile at the
pop has to change a theorem rather than a record, and so that the two halves of
the residue are pinned symmetrically. -/
@[simp] theorem donationReturnSchedContext_domain (sc : SchedContext)
    (originalOwner : SeLe4n.ThreadId) (nextHead? : Option SeLe4n.ReplyId)
    (newOwner? : Option SeLe4n.ThreadId) :
    (donationReturnSchedContext sc originalOwner nextHead? newOwner?).domain
      = sc.domain := rfl

/-- WS-OD OD4.4: **the donor shape the pop requires of an outer caller.**

Decidable and O(1): a `none` answer (the bottom of the reply stack) demands
nothing, and a `some outer` answer demands exactly what `donationOwnerValid`
demands of a donation's owner — a stored TCB that has given up its binding and is
waiting on a reply — plus that `outer` is neither of the two threads this pop
rewrites, since a claim about their pre-state shape would not survive the step.

This is `donationReturnOuterValid`'s first three clauses, made checkable.  The
fourth (`outerUnowned`: no thread already names `outer`) is whole-store
quantified and stays a caller obligation; it reads only `schedContextBinding`,
which is what lets it travel through the reply path's `ipcState` rewrites on the
`sameSchedContextBindings` machinery that is already there. -/
def outerCallerAcceptable (st : SystemState) (serverTid originalOwner : SeLe4n.ThreadId) :
    Option SeLe4n.ThreadId → Bool
  | none => true
  | some outer =>
    outer != originalOwner && outer != serverTid &&
      (match st.getTcb? outer with
       | none => false
       | some outerTcb =>
         outerTcb.schedContextBinding == .unbound &&
           (match outerTcb.ipcState with
            | .blockedOnReply _ _ => true
            | _ => false))

@[simp] theorem outerCallerAcceptable_none (st : SystemState)
    (serverTid originalOwner : SeLe4n.ThreadId) :
    outerCallerAcceptable st serverTid originalOwner none = true := rfl

/-- WS-OD (`v0.35.4`): does this thread's reply link name a frame that is on a
live reply stack — one whose upward link is **answered** by what it names?  Such
a thread is owed a scheduling context by the pop that reaches its frame.

**The test is reciprocity, not `next.isSome`** (PR #894 review).  A stale upward
link is reachable: the splice's below side *degenerates* to the sever when the
frame below does not reciprocate (`spliceFrameBelow?` answers `none`), and the
sever leaves the frame below the cut with an upward link nothing answers — under
`severAtCut`, live until WS-HP HP6.8, cancelling the middle caller of `B → M → H`
cleared `H.prev` and consumed `M` while `B.next` still read `some (.frame M)`.
`B` is then on no live stack and is owed nothing, so refusing its bind refuses an
operation `schedContextBind` documents as supported (binding a *blocked* thread).
Presence of the link is not the property; the property is that the frame or
context above answers this frame.

That is the same question `donationChainWalk` validates on the way down — a link
is validated by the target's own upward link, never by its `caller`, because a
re-linked Reply carries no answer back — and the one `spliceReplyFrameOut`
checks before it writes.  Asking it one step is **exact** rather than
approximate: under `donationChainWellFormed`, `prevLinkReciprocal` and
`headTerminates` make a reciprocated link a link to a frame that is itself on the
stack, so no walk is needed and the guard stays `O(1)`.  A frame that really is
live still answers `true`, so the fail-closed direction is unchanged.

**Relocated here at `v0.35.157`** from `SchedContext/Operations.lean`, where
`schedContextBind` had it, because the reply pop's origin redirect asks the same
question of the reservation's recorded origin (`donationOriginRebindable`) and
the endpoint operations cannot import the SchedContext module.  Its `.head` arm
is `replyFrameHeadContext?`'s own reciprocity test (defined further down, where the
reply-stack resolvers live; `replyFrameOnLiveStack_of_head` beside it is the tie),
and its `.frame` arm is the reciprocity `spliceFrameBelow?` checks before it writes.
It sits here, ahead of `donationOriginRebindable`, because that guard reads it. -/
def replyFrameOnLiveStack (st : SystemState) (tcb : TCB) : Bool :=
  match tcb.replyObject with
  | none => false
  | some rid =>
    match st.getReply? rid with
    | none => false
    | some r =>
      match r.next with
      | none => false
      | some (.frame above) =>
        match st.getReply? above with
        | none => false
        | some a => a.prev == some rid
      | some (.head scId) =>
        match st.getSchedContext? scId with
        | none => false
        | some sc => sc.scReply == some rid

/-- A thread holding no reply object is on no live stack. -/
@[simp] theorem replyFrameOnLiveStack_of_no_reply (st : SystemState) (tcb : TCB)
    (h : tcb.replyObject = none) : replyFrameOnLiveStack st tcb = false := by
  unfold replyFrameOnLiveStack; rw [h]

/-- **WS-HP HP10.7 / `v0.35.157`: the origin may be rebound without invalidating a
live donation — the bind's own admissibility, asked of the reservation's origin.**

`donationRecipientAcceptable` asks that the recipient hold no binding of its own,
which is what the pop is about to overwrite.  That is sufficient for the
*reachability* recipient and **not** for the redirected one, and the gap is a
soundness hole rather than a tightening: `donationOwnerValid` requires the `owner`
of every live `.donated scId' owner` binding to be `.unbound`, and a thread can be
`.unbound` while named as such an owner — that is exactly what a donor awaiting its
reservation back looks like.  The redirect would then write `.bound scId` there, and
that binding's owner clause becomes false: `donationOwnerValid` broken by a
successful reply.  Reachable with ordinary syscalls: a client whose frame was
answered out of order is woken `.ready` and `.unbound`; nothing stops it binding a
*second* reservation, Calling with it, and so becoming the owner of a fresh
`.donated` binding — all while the first reservation is still parked on a server
whose stack records it as the origin.

**The question is `schedContextBind`'s, and this is its answer** (`v0.35.157`,
closing the finding PR #897's review registered at `v0.35.141`): may this thread be
handed a scheduling context now?  The bind refuses a thread whose reply frame is on
a **live** stack (`replyFrameOnLiveStack` — one-step reciprocity, exact under
`donationChainWellFormed`), because such a thread is owed a context by the pop that
reaches its frame, and a second context bound to it in the meantime would be refused
by that pop's own recipient guard or orphaned by its write.  The redirect *is* a
bind of the reservation to its origin, so it asks the same test of the origin,
through the same definition.

Two things that test decides and the retired proxy did not.  Until `v0.35.157` this
guard read the origin's `ipcState` and refused a `.blockedOnReply` thread, standing
in for "some live `.donated _ origin` binding names it" — a fact being reply-blocked
is *implied by* and does not *imply*.  It therefore **refused the re-called
client**: a client answered out of order and re-Called is `.unbound`, so its Call
donated nothing and pushed no frame — its new reply object is on no stack — and no
binding names it as owner; the pop then fell back to the answered caller and
*transferred* the reservation to the intermediate caller of the chain, erasing the
origin with it (`v0.35.141`, measured at `tests/SmpIpcSuite.lean` §3.25 — the
decline was sound and not conservative).  The structural test **admits** that client,
and it **refuses** two shapes the proxy could not tell apart from it: an origin
whose frame *heads* a context — a live owner, named by that context's holder — and
an origin whose frame sits *inside* a live stack, which is owed a pop that a
binding made here would make refuse.

**Soundness is the coherence fact, not the `ipcState`.**
`donationOriginRebindable_no_owner` derives "no live `.donated _ origin` binding
names it" from this guard under `donatedContextIsOwnerFrameHead` — a live
binding's owner has its own frame heading that context, which is exactly
`replyFrameOnLiveStack`'s `.head` arm — so the fact the proxy stood in for is what
licenses the pop's write, stated once (WS-HP HP5.2's fact, which the cancellation
reclaim already carried) and consumed by the reply path as
`redirectedOriginFrameCoherent`.  It is not derivable from `donationOwnerValid`,
which relates a donation's owner to no reply frame.

A thread that does not resolve passes, as the sibling guards' `_of_none` arms do
-- and since `v0.35.61` the resolver never consults this guard on one:
`donationOriginRecipient?` resolves the origin through `lookupTcb` first and
declines a candidate that does not resolve, so a stale origin falls back to the
reachability recipient instead of reaching the pop's own lookup as a refusal.
This guard reads `st.getTcb?` where its siblings read `lookupTcb`; on a thread the
resolver has already resolved the two readers agree (`getTcb?_of_lookupTcb`), and
the frozen mirror (`frozenDonationOriginRebindable`) reads `frozenLookupTcb` and
`frozenReplyFrameOnLiveStack`, which agree with these on every thread
`frozenDonationOriginRecipient?` hands it, since that resolver resolves first too. -/
def donationOriginRebindable (st : SystemState) (origin : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? origin with
  | none => true
  | some tcb => !replyFrameOnLiveStack st tcb

/-- An origin that does not resolve is rebindable; the pop refuses it later. -/
@[simp] theorem donationOriginRebindable_of_none (st : SystemState)
    (origin : SeLe4n.ThreadId) (h : st.getTcb? origin = none) :
    donationOriginRebindable st origin = true := by
  unfold donationOriginRebindable; rw [h]

/-- **`v0.35.157`: a rebindable origin's reply frame is on no live stack** — the
whole of what the guard reads, and the half `donatedContextIsOwnerFrameHead` turns
into "named by no live donation" (`donationOriginRebindable_no_owner`). -/
theorem donationOriginRebindable_not_onLiveStack (st : SystemState)
    {origin : SeLe4n.ThreadId} {tcb : TCB}
    (hTcb : st.getTcb? origin = some tcb)
    (h : donationOriginRebindable st origin = true) :
    replyFrameOnLiveStack st tcb = false := by
  unfold donationOriginRebindable at h
  rw [hTcb] at h
  simpa using h

/-- **`v0.35.157`: a thread holding no reply object is rebindable** -- the shape a
frame's removal leaves its owner in (`removeCallerReplyFrame_replyObject_none`), and
what makes the depth-2 payoff's rebindability a *derived* fact rather than a stated
one (`donationAccountingPreserved_atCallDepthTwo`). -/
theorem donationOriginRebindable_of_no_reply (st : SystemState)
    {origin : SeLe4n.ThreadId} {tcb : TCB}
    (hTcb : st.getTcb? origin = some tcb) (h : tcb.replyObject = none) :
    donationOriginRebindable st origin = true := by
  unfold donationOriginRebindable
  rw [hTcb]
  simp [replyFrameOnLiveStack_of_no_reply st tcb h]


/-- **WS-HP HP4.6: the thread the pop hands the context TO holds none of its
own.**

The symmetric counterpart of `outerCallerAcceptable`, and the guard the
head-driven trigger makes load-bearing.  Before WS-HP the recipient was read out
of the *holder's* `.donated scId owner` binding, and `donationOwnerValid` puts a
donation's owner `.unbound`, so the recipient was provably unbound and no check
was needed.  The head-driven pop takes its recipient from the **answered caller**
instead, and nothing the operation reads constrains that thread's binding: a
caller that acquired a reservation of its own while blocked (`schedContextBind`
binds a blocked thread, deliberately) would have it silently overwritten by
`donationReturnBinding` -- orphaning a live `SchedContext` whose `boundThread`
still names that thread, which is a `donationBudgetTransfer` violation created by
a successful reply.

O(1) and fail-closed, exactly the posture RR2.8's `boundThread` guard has, and
inert on every state this tree reaches: `donationOwnerValid` puts the recipient
`.unbound` on each of the five call sites that resolve it from a binding, and on
the reply path `replyFrameHeadHolderDonation` does the same -- but that one is a
*stated* hypothesis, and stays one: HP7 (`v0.35.46`) retired the binding-driven
coherence facts, whose content the head-driven trigger witnesses, and this is the
one it does not (the trigger answers `(context, holder)` off a `.head` link and says
nothing about `holder`'s binding).  Resting a write on a hypothesis the operation
cannot see is what this guard removes.

A recipient that does not resolve passes: the operation's own later lookup
reports `.objectNotFound` there, and shadowing that with `.invalidArgument` would
change an error code rather than refuse a write.

**WS-HP HP9.4: this guard is upstream's, in upstream's own words** — read at
seL4 `master`, `13.0.0`, `12.1.0`, `12.0.0` and `11.0.0` (every release that has
the function), and recorded here rather than only in a plan, because a claim about
an external artefact belongs beside the code it justifies.  `reply_pop` donates
only under `if (tcb->tcbSchedContext == NULL)`, commented *"only give the SC back
if our SC is NULL"*.  Two further facts that reading established, both landed:

* the pop's **trigger** is `call_stack_get_isHead(reply->replyNext)` — head-ness,
  not the recorded server's binding — which is WS-HP HP4 and HP5;
* `reply_remove`'s non-head branch writes
  `REPLY_PTR(next_ptr)->replyPrev = call_stack_new(0, false)`, under the comment
  *"not the head, remove from middle - break the chain"*.  It writes **zero**, so
  upstream **severs**, and this kernel's splice (HP6.8) is an *improvement on*
  upstream rather than parity with it.

That last point is a **retraction's retraction** and the reason the revision is
named rather than the repository: `v0.35.14` asserted that upstream splices and
quoted a line — `REPLY_PTR(call_stack_get_callStackPtr(reply->replyNext))->replyPrev
= reply->replyPrev` — that exists in **no release**, then swept that error across
nine prose sites and three docstrings that had been right.  Cite the tag you read
at, so the next reader can re-run the check instead of re-trusting the quotation. -/
def donationRecipientAcceptable (st : SystemState) (originalOwner : SeLe4n.ThreadId) : Bool :=
  match lookupTcb st originalOwner with
  | none => true
  | some tcb => tcb.schedContextBinding == .unbound

/-- A recipient that does not resolve passes the guard. -/
@[simp] theorem donationRecipientAcceptable_of_none (st : SystemState)
    (originalOwner : SeLe4n.ThreadId) (h : lookupTcb st originalOwner = none) :
    donationRecipientAcceptable st originalOwner = true := by
  unfold donationRecipientAcceptable; rw [h]

/-- And on one that does, the guard **is** the binding test. -/
theorem donationRecipientAcceptable_eq_of_some (st : SystemState)
    (originalOwner : SeLe4n.ThreadId) (tcb : TCB)
    (h : lookupTcb st originalOwner = some tcb) :
    donationRecipientAcceptable st originalOwner
      = (tcb.schedContextBinding == .unbound) := by
  unfold donationRecipientAcceptable; rw [h]

/-- WS-OD OD4.4: **neither arm of the widened binding is `.unbound`.**  The pop
hands the context *back*, so the thread it rewrites always holds it afterwards —
at the bottom of the stack as `.bound`, one level up as `.donated`.  Consumers
used to get this by `cases` on a literal `.bound scId`; with the binding a match
on the resolved owner that elimination no longer fires, and stating the fact once
is what keeps it from being re-derived by a two-way case split at each site. -/
@[simp] theorem donationReturnBinding_ne_unbound (scId : SeLe4n.SchedContextId)
    (newOwner? : Option SeLe4n.ThreadId) :
    donationReturnBinding scId newOwner? ≠ .unbound := by
  cases newOwner? <;> simp [donationReturnBinding]

/-- WS-OD OD3.1: **both arms of the return binding name the same context.**

`.bound scId` and `.donated scId outer` differ in whether the target is itself a
donor, never in *which* context it holds — so every consumer that only asks
"which scheduling context does this thread reference" is insensitive to the
stack depth, and `scThreadIndexConsistent` in particular is unchanged by the
widening. -/
@[simp] theorem donationReturnBinding_scId? (scId : SeLe4n.SchedContextId)
    (newOwner? : Option SeLe4n.ThreadId) :
    (donationReturnBinding scId newOwner?).scId? = some scId := by
  cases newOwner? <;> rfl

/-- WS-OD OD3.1: **the validated head of a scheduling context's reply stack.**

`.ok none` when the context heads no stack — the shape every state in this tree
has today, and the depth-1 shape after the push lands.  `.ok (some (rid, r))`
when it heads one *and* that reply really is on **this** context's stack.

A head that resolves to no Reply, or to one donating a different context (or
none at all), is a **refusal** rather than an empty stack: `donationChainWellFormed`
says it cannot happen, so this is defence in depth on the same reading as
`returnDonatedSchedContext`'s `boundThread` guard — and treating it as empty
would be the strictly worse failure, since the pop would then leave a Reply
naming a context that no longer names it, which is the stale-link shape the
whole chain design exists to refuse. -/
def donationHeadOf? (st : SystemState) (scId : SeLe4n.SchedContextId)
    (sc : SchedContext) : Except KernelError (Option (SeLe4n.ReplyId × Reply)) :=
  match sc.scReply with
  | none => .ok none
  | some rid =>
    -- The head is read through the state's own typed accessor rather than by a
    -- raw object-store lookup: it is a whole `Reply` this needs, and the AK7
    -- cascade counts an unmigrated read site as debt.  The wording avoids the
    -- literal the counter greps for, since a comment must not move a code
    -- metric — the project's own "gates read code, prose reads prose" rule.
    match st.getReply? rid with
    | some r =>
      if r.next != some (.head scId) then .error .invalidArgument
      else .ok (some (rid, r))
    | none => .error .objectNotFound

@[simp] theorem donationHeadOf?_of_no_stack (st : SystemState)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (h : sc.scReply = none) :
    donationHeadOf? st scId sc = .ok none := by
  unfold donationHeadOf?; rw [h]

/-- WS-OD OD3.1: **a validated head is the context's own `scReply`.**

The key half of `donationHeadOf?`: the Reply it returns is the one the context
points at, so a frame stated over "whatever the context headed" and a frame
stated over "whatever the pop cleared" are the same frame.  Without it the head
key stays existentially bound inside the store chain and every caller has to
re-derive the identification. -/
theorem donationHeadOf?_ok_key (st : SystemState) (scId : SeLe4n.SchedContextId)
    (sc : SchedContext) (head? : Option (SeLe4n.ReplyId × Reply))
    (h : donationHeadOf? st scId sc = .ok head?) :
    head?.map Prod.fst = sc.scReply := by
  unfold donationHeadOf? at h
  revert h
  cases hR : sc.scReply with
  | none => intro h; cases h; rfl
  | some rid =>
    simp only []
    cases hRep : st.getReply? rid with
    | none => intro h; cases h
    | some r =>
      simp only []
      cases hD : (r.next != some (.head scId)) with
      | true => simp only [if_true]; intro h; cases h
      | false => simp only [Bool.false_eq_true, if_false]; intro h; cases h; rfl

/-- WS-OD OD3.1: a validated head resolves to a Reply that donates **this**
context — the fact the head clear's write is sound on, and the one OD4's push
consumes to know the popped frame was its own. -/
theorem donationHeadOf?_ok_resolves (st : SystemState) (scId : SeLe4n.SchedContextId)
    (sc : SchedContext) (rid : SeLe4n.ReplyId) (r : Reply)
    (h : donationHeadOf? st scId sc = .ok (some (rid, r))) :
    st.objects[rid.toObjId]? = some (.reply r) ∧ r.next = some (.head scId) := by
  unfold donationHeadOf? at h
  revert h
  cases hR : sc.scReply with
  | none => intro h; cases h
  | some rid0 =>
    simp only []
    cases hRep : st.getReply? rid0 with
    | none => intro h; cases h
    | some r0 =>
      simp only []
      cases hD : (r0.next != some (.head scId)) with
      | true => simp only [if_true]; intro h; cases h
      | false =>
        simp only [Bool.false_eq_true, if_false]
        intro h
        have hPair := Option.some.inj (Except.ok.inj h)
        have hRid : rid0 = rid := congrArg Prod.fst hPair
        have hRep' : r0 = r := congrArg Prod.snd hPair
        subst hRid; subst hRep'
        exact ⟨(SystemState.getReply?_eq_some_iff _ _ _).mp hRep, by simpa using hD⟩

/-- WS-OD OD3.4: **who the popped context's new owner is, read off the reply
stack before anything consumes it.**

`returnDonatedSchedContext` takes its `newOwner?` as an argument rather than
resolving it internally, because the reply leg consumes the target's reply link
*before* the donation return runs (plan §3.3).  This is the resolver every call
site uses to compute that argument on its own pre-state.

**What it reads.**  The context's stack is `sc.scReply` (the head) linked down
through `Reply.prev`.  The thread the pop hands the context back to is the head's
own caller; the thread *that* caller in turn holds it from is the caller of the
frame **below** the head.  So this walks exactly one link past the head, which is
why it is `O(1)` and not a chain walk: the pop consumes one frame, so it needs one
frame's worth of lookahead and no more.

**Three answers, and `.ok none` means exactly one thing.**  `.ok none` is
"the head *is* the bottom of the stack", so the pop's target becomes `.bound`;
`.ok (some outer)` names the outer caller, so it becomes `.donated scId outer`;
`.error` means a link exists but does not validate, which is a different fact
from there being no link and must not be conflated with it — a caller that read
a corrupt link as "bottom of stack" would silently settle a scheduling context
that is still owed outward.  This is the same three-way shape `donationHeadOf?`
has, for the same reason.

**A validated frame with no caller is an `.error`, not a `none`** (`v0.35.4`,
`replyStackOuterCaller?_of_consumed_frame`).  Before the stack was doubly
linked it was the second `.ok none` state — a cancelled middle caller's frame,
which nothing could then remove — and the pop bound the target outright with
that dead frame still heading the context, pinning both objects against every
retype.  The removal is carried out by the *splice* at the cancellation
(`spliceReplyFrameOut` — `severAtCut` until WS-HP HP6.8, `spliceOutTheCut` since
`v0.35.45`), so a linked frame always has a blocked caller (`Reply.wellFormed`); a frame that validates and has none
is an invariant violation and is refused on the same fail-closed terms as a link
that does not validate.

**It validates the frame it follows** (plan §3.4, the confused deputy).  Reply
objects are re-linked to new callers by `replyIdEstablishFresh`, so a stale
`prev` over a reused Reply would name a caller that has nothing to do with this
context — handing a thread's scheduling context to an unrelated thread, in
another domain, driven by object reuse.  The frame below the head is therefore
accepted only when its own **upward** link answers the head that reached it
(`next = .frame headRid`), exactly as `donationHeadOf?` accepts the head only
when its upward link names this context.  Reciprocity is what refuses a reused
Reply: relinking clears both links, so it carries no answer back.  The plan puts
that validation in OD5.1; it is built in here instead, because OD4.4 makes this
resolver live and a live resolver whose safety check lands two phases later is
the ordering the plan's own numbering rule forbids.  OD5.1 keeps the other half
— the clears at freshening and consumption.

**The error arm is unreachable under the chain invariant**, which validates every
link of the stack; `donationChainWellFormed` is what rules it out, and a theorem
asserting this resolver *succeeds* states it. -/
def replyStackOuterCaller? (st : SystemState) (scId : SeLe4n.SchedContextId) :
    Except KernelError (Option SeLe4n.ThreadId) :=
  match st.getSchedContext? scId with
  | none => .error .objectNotFound
  | some sc =>
    match donationHeadOf? st scId sc with
    | .error e => .error e
    | .ok none => .ok none
    | .ok (some (headRid, head)) =>
      match head.prev with
      | none => .ok none
      | some below =>
        match st.getReply? below with
        | none => .error .objectNotFound
        | some b =>
          if b.next != some (.frame headRid) then .error .invalidArgument
          else
            match b.caller with
            | none => .error .illegalState
            | some outer => .ok (some outer)

/-- WS-OD OD3.4: **the resolver is inert on a context that heads no stack.**

A context with no reply stack has no outer caller, so the argument OD4.4 threads
through the six call sites is `none` there.  That was every state the tree
reached before OD4.1 (`v0.35.2`), which is what made OD4.4 a refactor rather than
a behaviour change; the answer stops being `none` exactly where the push has
written a `scReply`. -/
@[simp] theorem replyStackOuterCaller?_of_no_stack (st : SystemState)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc) (hNoHead : sc.scReply = none) :
    replyStackOuterCaller? st scId = .ok none := by
  unfold replyStackOuterCaller?
  rw [hSc]
  simp only [donationHeadOf?_of_no_stack st scId sc hNoHead]

/-- WS-OD OD3.4: **the bottom of the stack answers `none`.**

A head whose own `prev` is empty is the last frame, so the context goes back
`.bound`.  This is the depth-1 shape OD4's first push produces, and it is what
keeps `returnDonatedSchedContext_eq_legacy_of_none` reachable after the push:
the depth-1 pop still passes `none`. -/
theorem replyStackOuterCaller?_of_bottom_head (st : SystemState)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (rid : SeLe4n.ReplyId) (r : Reply)
    (hSc : st.getSchedContext? scId = some sc)
    (hHead : donationHeadOf? st scId sc = .ok (some (rid, r)))
    (hBottom : r.prev = none) :
    replyStackOuterCaller? st scId = .ok none := by
  unfold replyStackOuterCaller?
  rw [hSc]
  simp only [hHead, hBottom]

/-- WS-OD OD3.4: **what a `some` answer is.**

The resolved outer caller is the `caller` of the frame below the head, and that
frame donates this very context.  Both halves are load-bearing: the first is what
OD4's push and OD4.4's call sites consume, and the second is the validation that
stops a reused Reply from redirecting the context — a caller that only knew "the
answer came from somewhere" would have no way to state the confined-deputy
property at all. -/
theorem replyStackOuterCaller?_ok_some (st : SystemState)
    (scId : SeLe4n.SchedContextId) (outer : SeLe4n.ThreadId)
    (h : replyStackOuterCaller? st scId = .ok (some outer)) :
    ∃ sc rid head below b,
      st.getSchedContext? scId = some sc ∧
      donationHeadOf? st scId sc = .ok (some (rid, head)) ∧
      head.prev = some below ∧
      st.getReply? below = some b ∧
      b.next = some (.frame rid) ∧
      b.caller = some outer := by
  unfold replyStackOuterCaller? at h
  revert h
  cases hSc : st.getSchedContext? scId with
  | none => intro h; cases h
  | some sc =>
    simp only []
    cases hHead : donationHeadOf? st scId sc with
    | error e => intro h; cases h
    | ok head? =>
      cases head? with
      | none => intro h; cases h
      | some pair =>
        obtain ⟨rid, head⟩ := pair
        simp only []
        cases hPrev : head.prev with
        | none => intro h; cases h
        | some below =>
          simp only []
          cases hBelow : st.getReply? below with
          | none => intro h; cases h
          | some b =>
            simp only []
            cases hLink : (b.next != some (.frame rid)) with
            | true => simp only [if_true]; intro h; cases h
            | false =>
              simp only [Bool.false_eq_true, if_false]
              cases hCaller : b.caller with
              | none => intro h; cases h
              | some outer' =>
                intro h
                have hEq := Option.some.inj (Except.ok.inj h)
                subst hEq
                exact ⟨sc, rid, head, below, b, rfl, hHead, hPrev, hBelow,
                  by simpa using hLink, hCaller⟩

/-- WS-OD OD5.2 / `v0.35.4`: **a consumed frame below the head is refused, not
read as the bottom of the stack.**

Before `v0.35.4` a validated frame whose `caller` had been consumed — a cancelled
middle caller's frame, which nothing then removed from the stack — made the
resolver answer `none`, and the pop bound the target outright with that dead
frame still heading the stack: the `severAtCut` policy implemented by *leaving a
frame behind*, which pinned the frame's Reply object and the context forever
(neither could be retyped, the Reply could never be linked again).  The removal
is implemented by the splice (`spliceReplyFrameOut`; the policy it carries out was
`severAtCut` until WS-HP HP6.8 and is `spliceOutTheCut` since `v0.35.45`), which
takes the cancelled frame off the stack at the cancellation, so a linked frame
always has a blocked caller (`Reply.wellFormed`).  A frame that validates and has
none is therefore an invariant violation, and reading it as "bottom of stack"
would settle a scheduling context on a thread the stack does not name — the same
fail-closed verdict `.error` already gives a link that does not validate. -/
theorem replyStackOuterCaller?_of_consumed_frame (st : SystemState)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (rid : SeLe4n.ReplyId) (r : Reply)
    (below : SeLe4n.ReplyId) (b : Reply)
    (hSc : st.getSchedContext? scId = some sc)
    (hHead : donationHeadOf? st scId sc = .ok (some (rid, r)))
    (hPrev : r.prev = some below)
    (hBelow : st.getReply? below = some b)
    (hLink : b.next = some (.frame rid))
    (hConsumed : b.caller = none) :
    replyStackOuterCaller? st scId = .error .illegalState := by
  unfold replyStackOuterCaller?
  rw [hSc]
  simp only [hHead, hPrev, hBelow, hLink, bne_self_eq_false, Bool.false_eq_true, if_false,
    hConsumed]

/-- **WS-OD OD3.7: the two objects the pop touches *below* the stack head.**

`replyStackOuterCaller?` walks one link past the head, reading the `Reply` below
it; `outerCallerAcceptable` then reads that Reply's `caller`'s TCB to check it is
a waiting donor before the pop hands it a scheduling context.  Neither object is
covered by any other footprint member — the head Reply is the answered caller's
`replyObject`, and the outer caller is provably neither of the two threads the
pop rewrites (`outerCallerAcceptable`'s own first two conjuncts) — so at call
depth ≥ 2 a footprint that omits them is *false* of the transition.

The second read is the sharper of the two: it is a **validate-then-commit**, so
an unlocked read is a time-of-check/time-of-use window on precisely the thread
the pop is about to bind a scheduling context to.  A concurrent
`.tcbSuspend` of that thread between the check and the store would leave the
context bound to a thread the check accepted and the store found elsewhere.

**Returned as one pair because it is one question** — *what does the pop read
below the head* — and the tree has twice now paid for asking one question in two
places (`cancelArmSpliceNeighbors?`'s own docstring records the last time).  The
plan row that scheduled this work named only the first read; the second is
derived from the operation rather than from that list, which is the
enumeration-versus-derivation rule this project states for gates applied to a
footprint.

Both components were `none` on every state the tree reached when this landed,
since nothing then wrote a `scReply` (`replyStackBelowHead?_of_no_stack`),
so it widened no live footprint — it declared ahead of the code, which is the
order the plan's own numbering rule requires.  OD4.1 (`v0.35.2`) writes the
`scReply`, so the declaration is now load-bearing at depth ≥ 2 and inert below
it, exactly as intended. -/
def replyStackBelowHead? (st : SystemState) (scId : SeLe4n.SchedContextId) :
    Option SeLe4n.ReplyId × Option SeLe4n.ThreadId :=
  match st.getSchedContext? scId with
  | none => (none, none)
  | some sc =>
    match donationHeadOf? st scId sc with
    | .error _ => (none, none)
    | .ok none => (none, none)
    | .ok (some (headRid, head)) =>
      match head.prev with
      | none => (none, none)
      | some below =>
        -- The Reply below the head is read **and written** (re-headed) whether
        -- or not the validation that follows accepts it, so it is declared on
        -- the link alone.  The caller's TCB is read only when the resolver
        -- yields one, which is exactly when the call site passes a `some` for
        -- `outerCallerAcceptable` to check.
        (some below,
         match st.getReply? below with
         | none => none
         | some b => if b.next != some (.frame headRid) then none else b.caller)

/-- WS-OD OD3.7: **inert on every state this tree reaches.**

A context heading no reply stack has nothing below its head, so both members are
`none` and every footprint that gained them is definitionally the one it was
before (`lockSetExtendOpt S none = S`).  This is what makes the row a
declaration rather than a widening: the members become live exactly when OD4's
push first writes a `scReply`. -/
@[simp] theorem replyStackBelowHead?_of_no_stack (st : SystemState)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc) (hNoHead : sc.scReply = none) :
    replyStackBelowHead? st scId = (none, none) := by
  unfold replyStackBelowHead?
  rw [hSc]
  simp only [donationHeadOf?_of_no_stack st scId sc hNoHead]

/-- WS-OD OD3.7: **the bottom of the stack reads nothing below it.**

The depth-1 shape OD4's first push produces: a head with no `prev` is the last
frame, so the pop reads no further and returns the context `.bound`.  Stated
separately from `_of_no_stack` because the two are different states — no stack at
all, versus a stack exactly one frame deep — and a reader checking that this
footprint is inert at depth 1 needs the second. -/
theorem replyStackBelowHead?_of_bottom_head (st : SystemState)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (rid : SeLe4n.ReplyId) (r : Reply)
    (hSc : st.getSchedContext? scId = some sc)
    (hHead : donationHeadOf? st scId sc = .ok (some (rid, r)))
    (hBottom : r.prev = none) :
    replyStackBelowHead? st scId = (none, none) := by
  unfold replyStackBelowHead?
  rw [hSc]
  simp only [hHead, hBottom]

/-- WS-OD OD3.7: **the declared caller is the resolver's answer.**

The footprint's TCB member and `replyStackOuterCaller?`'s `some` answer are the
same thread whenever the resolver succeeds — so the lock the footprint declares
is a lock on the thread `outerCallerAcceptable` will actually read, not on one
that merely happens to sit below the head.  Without this the two could drift,
which is the shape OD3.5 spent a whole row closing on the delegated reply. -/
theorem replyStackBelowHead?_snd_eq_outerCaller (st : SystemState)
    (scId : SeLe4n.SchedContextId) (outer? : Option SeLe4n.ThreadId)
    (h : replyStackOuterCaller? st scId = .ok outer?) :
    (replyStackBelowHead? st scId).2 = outer? := by
  unfold replyStackBelowHead?
  unfold replyStackOuterCaller? at h
  revert h
  cases hSc : st.getSchedContext? scId with
  | none => intro h; cases h
  | some sc =>
    simp only []
    cases hHead : donationHeadOf? st scId sc with
    | error e => intro h; cases h
    | ok head? =>
      cases head? with
      | none => intro h; simp only []; exact Except.ok.inj h
      | some pair =>
        obtain ⟨rid, head⟩ := pair
        simp only []
        cases hPrev : head.prev with
        | none => intro h; simp only []; exact Except.ok.inj h
        | some below =>
          simp only []
          cases hBelow : st.getReply? below with
          | none => intro h; cases h
          | some b =>
            simp only []
            cases hLink : (b.next != some (.frame rid)) with
            | true => simp only [if_true]; intro h; cases h
            | false =>
              simp only [Bool.false_eq_true, if_false]
              cases hCaller : b.caller with
              | none => intro h; cases h
              | some outer' => intro h; exact Except.ok.inj h

/-- **WS-HP HP10.6: the bottom of the stack reads and writes nothing below its
head — the exclusion the origin member rests on.**

`replyStackOuterCaller?` answers `.ok none` in exactly two shapes: a context that
heads no stack at all, and one whose head has no `prev`.  In both the pop stops at
the head, so *both* components of `replyStackBelowHead?` are absent.

That is what keeps HP10.6's raise parametric.  The origin member is `some` only
where the pop is at the bottom of its stack (`donationOriginRecipient?` reads this
resolver), so it is live on exactly the states where the two below-head members
are not: a reachable footprint trades two members for one, and the reachable
`.replyRecv` figures do not move even though the declared ceiling does.  The two
sharper facts beside it — `_of_no_stack` and `_of_bottom_head` — each cover one of
the two shapes; this one is stated over the resolver so a caller that knows only
"the pop is at the bottom" has it without re-deriving which shape it is in. -/
theorem replyStackBelowHead?_of_outer_none (st : SystemState)
    (scId : SeLe4n.SchedContextId)
    (h : replyStackOuterCaller? st scId = .ok none) :
    replyStackBelowHead? st scId = (none, none) := by
  unfold replyStackBelowHead?
  unfold replyStackOuterCaller? at h
  revert h
  cases hSc : st.getSchedContext? scId with
  | none => intro hc; cases hc
  | some sc =>
    simp only []
    cases hHead : donationHeadOf? st scId sc with
    | error e => intro hc; cases hc
    | ok head? =>
      cases head? with
      | none => intro _; rfl
      | some pair =>
        obtain ⟨rid, head⟩ := pair
        simp only []
        cases hPrev : head.prev with
        | none => intro _; rfl
        | some below =>
          simp only []
          cases hBelow : st.getReply? below with
          | none => intro hc; cases hc
          | some b =>
            simp only []
            cases hLink : (b.next != some (.frame rid)) with
            | true => simp only [if_true]; intro hc; cases hc
            | false =>
              simp only [Bool.false_eq_true, if_false]
              cases hCaller : b.caller with
              | none => intro hc; cases hc
              | some outer' => intro hc; cases hc

/-- WS-OD (`v0.35.4`): **the frame a context heads**, read through the typed
accessor -- `none` for a context that heads no stack or does not resolve.

Two operations touch this object and one footprint member stands for both.  The
**push** reads it as the *old head*, which `storeDonationFramePush` rewrites
(`next := .frame pushRid`), so every footprint that declares a donation
(`.call`, `.receive`, `.replyRecv`'s re-donation) declares this Reply in write
mode beside the SchedContext it hangs off.  The **pop** clears it
(`storeDonationHeadClear`): on the reply arms it is the answered caller's own
reply object under every reachable state, but that identification is a fact the
invariants supply rather than one the operation checks, and a declared footprint
is the union over all argument values -- so the reply footprints name it through
this resolver too and let `insertOrMerge`'s key merge collapse the two where they
coincide. -/
def replyStackHead? (st : SystemState) (scId : SeLe4n.SchedContextId) :
    Option SeLe4n.ReplyId :=
  (st.getSchedContext? scId).bind (·.scReply)

@[simp] theorem replyStackHead?_of_no_stack (st : SystemState)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc) (hNoHead : sc.scReply = none) :
    replyStackHead? st scId = none := by
  unfold replyStackHead?; rw [hSc]; simp [hNoHead]

theorem replyStackHead?_eq (st : SystemState) (scId : SeLe4n.SchedContextId)
    (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc) :
    replyStackHead? st scId = sc.scReply := by
  unfold replyStackHead?; rw [hSc]; rfl

@[simp] theorem replyStackHead?_of_none (st : SystemState) (scId : SeLe4n.SchedContextId)
    (h : st.getSchedContext? scId = none) : replyStackHead? st scId = none := by
  unfold replyStackHead?; rw [h]; rfl

/-- **WS-RM (`v0.35.6`)**: a context that heads no stack has nothing below the
head either — the resolver bottoms out at `donationHeadOf?`, which answers
`.ok none` on a context with no `scReply` and is never reached when the context
does not resolve at all. -/
theorem replyStackBelowHead?_of_no_head (st : SystemState)
    (scId : SeLe4n.SchedContextId) (h : replyStackHead? st scId = none) :
    replyStackBelowHead? st scId = (none, none) := by
  unfold replyStackBelowHead?
  cases hSc : st.getSchedContext? scId with
  | none => rfl
  | some sc =>
    have hNoHead : sc.scReply = none := by
      rw [replyStackHead?_eq st scId sc hSc] at h; exact h
    simp only [donationHeadOf?_of_no_stack st scId sc hNoHead]

/-- WS-OD (`v0.35.4`): **the frame two below the head, and its caller** -- what
the *second* pop of a suspend pipeline writes and reads.

`suspendThreadOnCore` runs the cancellation's reclaim and then cancels the
victim's donation on the *post*-teardown binding (WS-OD OD5.3): at call depth
>= 2 the reclaim hands the context to the victim as `.donated scId outer`, and
the donation cancel pops once more -- clearing the frame below the original head
(a member since OD3.7, written since this cut), re-heading the frame below *that*
one, and validating that frame's caller (`outerCallerAcceptable`).  The first
component is that frame, written; the second is its caller, read, answered only
when the link validates exactly as `replyStackOuterCaller?` validates it on the
post-first-pop state, where the frame below the original head has become the
head.  Both are `none` below depth 3. -/
def replyStackSecondBelowHead? (st : SystemState) (scId : SeLe4n.SchedContextId) :
    Option SeLe4n.ReplyId × Option SeLe4n.ThreadId :=
  match (replyStackBelowHead? st scId).1 with
  | none => (none, none)
  | some below =>
    match st.getReply? below with
    | none => (none, none)
    | some b =>
      match b.prev with
      | none => (none, none)
      | some second =>
        (some second,
         match st.getReply? second with
         | none => none
         | some s => if s.next != some (.frame below) then none else s.caller)

@[simp] theorem replyStackSecondBelowHead?_of_no_stack (st : SystemState)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc) (hNoHead : sc.scReply = none) :
    replyStackSecondBelowHead? st scId = (none, none) := by
  unfold replyStackSecondBelowHead?
  rw [replyStackBelowHead?_of_no_stack st scId sc hSc hNoHead]

theorem replyStackSecondBelowHead?_of_no_below (st : SystemState)
    (scId : SeLe4n.SchedContextId) (h : (replyStackBelowHead? st scId).1 = none) :
    replyStackSecondBelowHead? st scId = (none, none) := by
  unfold replyStackSecondBelowHead?; rw [h]

/-- WS-OD OD3.1: **the head clear, as one step whether or not there is a head.**

The pop writes a Reply only when the context heads a stack, and every frame the
donation return carries has to say what happens at both.  Naming the step keeps
that a *single* extra hop in each of those proofs rather than a second arm in
each of them: `storeDonationHeadClear_of_none` is definitional, and the frames
below state what the `some` arm does once. -/
def storeDonationHeadClear :
    Option SeLe4n.ReplyId → SystemState → Except KernelError SystemState
  | none, st => .ok st
  | some rid, st =>
    match st.getReply? rid with
    | some r =>
      match storeObject rid.toObjId (.reply { r with prev := none, next := none }) st with
      | .error e => .error e
      | .ok ((), st') => .ok st'
    | none => .error .objectNotFound

@[simp] theorem storeDonationHeadClear_none (st : SystemState) :
    storeDonationHeadClear none st = .ok st := rfl

theorem storeDonationHeadClear_some (st : SystemState) (rid : SeLe4n.ReplyId) :
    storeDonationHeadClear (some rid) st =
      (match st.getReply? rid with
       | some r =>
         (match storeObject rid.toObjId
             (.reply { r with prev := none, next := none }) st with
          | .error e => .error e
          | .ok ((), st') => .ok st')
       | none => .error .objectNotFound) := rfl

/-- WS-OD OD3.1: **the head clear is the identity, or one `storeObject` of one
Reply.**

The complete decomposition of the step, on the discipline
`returnDonatedSchedContext_ok_storeChain` already follows: every frame the
donation return carries crosses this step as one extra hop with a two-line case
analysis, rather than as a second arm threaded through the whole proof. -/
theorem storeDonationHeadClear_cases
    {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeDonationHeadClear head? st = .ok st') :
    st' = st ∨ ∃ (rid : SeLe4n.ReplyId) (r : Reply),
      head? = some rid ∧
      st.objects[rid.toObjId]? = some (.reply r) ∧
      storeObject rid.toObjId (.reply { r with prev := none, next := none }) st
        = .ok ((), st') := by
  cases head? with
  | none => exact Or.inl (Except.ok.inj h).symm
  | some rid =>
    rw [storeDonationHeadClear_some] at h
    revert h
    cases hRep : st.getReply? rid with
    | none => intro h; cases h
    | some r =>
      simp only []
      cases hS : storeObject rid.toObjId
          (.reply { r with prev := none, next := none }) st with
      | error e => intro h; cases h
      | ok pr =>
        simp only []
        intro h
        cases h
        exact Or.inr ⟨rid, r, rfl,
          (SystemState.getReply?_eq_some_iff st rid r).mp hRep, by rw [← hS]⟩

/-- WS-OD OD3.8: **the head clear on a `some` head is exactly one Reply store.**

The `some` refinement of `storeDonationHeadClear_cases`, whose identity arm is
reachable only for a `none` head: a caller that already knows there *is* a head
should not have to refute "the step did nothing" before it can say what the step
wrote.  The chain-preservation proof reads the post-state's object store at the
cleared key and at every other, and both readings come from this one store.

The Reply it exposes is read back through the state's own typed accessor, which
is also how `storeDonationHeadClear` itself reads it — a raw object-store lookup
here would be a second reading of the same field and an unmigrated site the AK7
cascade counts as debt. -/
theorem storeDonationHeadClear_some_ok
    {rid : SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeDonationHeadClear (some rid) st = .ok st') :
    ∃ r : Reply, st.getReply? rid = some r ∧
      storeObject rid.toObjId (.reply { r with prev := none, next := none }) st
        = .ok ((), st') := by
  rw [storeDonationHeadClear_some] at h
  revert h
  cases hRep : st.getReply? rid with
  | none => intro h; cases h
  | some r =>
    simp only []
    cases hS : storeObject rid.toObjId
        (.reply { r with prev := none, next := none }) st with
    | error e => intro h; cases h
    | ok pr =>
      simp only []
      intro h
      cases h
      exact ⟨r, rfl, by rw [← hS]⟩

/-- WS-OD OD3.1: **the head clear succeeds when the head is a Reply.**

The only error arm is a head that does not resolve to a Reply, so the step is
total on exactly the states the pop's own head validation admits. -/
theorem storeDonationHeadClear_ok_of_reply (st : SystemState)
    (head? : Option SeLe4n.ReplyId)
    (hReply : ∀ rid, head? = some rid → ∃ r : Reply, st.objects[rid.toObjId]? = some (.reply r)) :
    ∃ st', storeDonationHeadClear head? st = .ok st' := by
  cases head? with
  | none => exact ⟨st, rfl⟩
  | some rid =>
    obtain ⟨r, hR⟩ := hReply rid rfl
    have hRep : st.getReply? rid = some r := (SystemState.getReply?_eq_some_iff st rid r).mpr hR
    -- `storeObject` is unconditionally `.ok`, so the step reduces outright.
    obtain ⟨p, hP⟩ : ∃ p, storeObject rid.toObjId
        (.reply { r with prev := none, next := none }) st = .ok p := ⟨_, rfl⟩
    obtain ⟨u, st'⟩ := p
    cases u
    refine ⟨st', ?_⟩
    rw [storeDonationHeadClear_some, hRep]
    simp only []
    rw [hP]

/-- WS-OD OD3.1: the head clear writes `objects` and nothing else — the
scheduler half. -/
theorem storeDonationHeadClear_scheduler_eq
    {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeDonationHeadClear head? st = .ok st') :
    st'.scheduler = st.scheduler := by
  rcases storeDonationHeadClear_cases h with rfl | ⟨rid, r, _, _, hS⟩
  · rfl
  · unfold storeObject at hS; cases hS; rfl

/-- WS-OD OD3.1: ...the service-registry half. -/
theorem storeDonationHeadClear_serviceRegistry_eq
    {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeDonationHeadClear head? st = .ok st') :
    st'.serviceRegistry = st.serviceRegistry := by
  rcases storeDonationHeadClear_cases h with rfl | ⟨rid, r, _, _, hS⟩
  · rfl
  · unfold storeObject at hS; cases hS; rfl

/-- WS-OD OD3.1: ...the TLB-shootdown half. -/
theorem storeDonationHeadClear_tlbShootdown_eq
    {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeDonationHeadClear head? st = .ok st') :
    st'.tlbShootdown = st.tlbShootdown := by
  rcases storeDonationHeadClear_cases h with rfl | ⟨rid, r, _, _, hS⟩
  · rfl
  · unfold storeObject at hS; cases hS; rfl

/-- WS-OD OD3.1: ...the machine half. -/
theorem storeDonationHeadClear_machine_eq
    {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeDonationHeadClear head? st = .ok st') :
    st'.machine = st.machine := by
  rcases storeDonationHeadClear_cases h with rfl | ⟨rid, r, _, _, hS⟩
  · rfl
  · unfold storeObject at hS; cases hS; rfl

/-- WS-OD OD3.1: the head clear preserves the object store's extended
invariant. -/
theorem storeDonationHeadClear_preserves_objects_invExt
    {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationHeadClear head? st = .ok st') :
    st'.objects.invExt := by
  rcases storeDonationHeadClear_cases h with rfl | ⟨rid, r, _, _, hS⟩
  · exact hObjInv
  · exact storeObject_preserves_objects_invExt st st' _ _ hObjInv hS

/-- WS-OD OD3.1: the head clear preserves the object-index set's own invariant. -/
theorem storeDonationHeadClear_preserves_objectIndexSet_invExt
    {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hSetInv : st.objectIndexSet.table.invExt)
    (h : storeDonationHeadClear head? st = .ok st') :
    st'.objectIndexSet.table.invExt := by
  rcases storeDonationHeadClear_cases h with rfl | ⟨rid, r, _, _, hS⟩
  · exact hSetInv
  · exact SeLe4n.Model.storeObject_preserves_objectIndexSet_invExt st st' _ _ hSetInv hS

/-- WS-OD OD3.1: the head clear preserves object-index completeness — the fact a
projection hop needs, since a key already in the store stays registered. -/
theorem storeDonationHeadClear_preserves_objectIndexSetComplete
    {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt) (hSetInv : st.objectIndexSet.table.invExt)
    (hComplete : ∀ oid, st.objects[oid]? ≠ none → st.objectIndexSet.contains oid = true)
    (h : storeDonationHeadClear head? st = .ok st') :
    ∀ oid, st'.objects[oid]? ≠ none → st'.objectIndexSet.contains oid = true := by
  rcases storeDonationHeadClear_cases h with rfl | ⟨rid, r, _, _, hS⟩
  · exact hComplete
  · exact SeLe4n.Model.storeObject_preserves_objectIndexSetComplete st st' _ _ hObjInv hSetInv
      hComplete hS

/-- WS-OD OD3.1: **the head clear is invisible to every TCB.**

A Reply store lands on a key that held a Reply, and no key holds both, so every
TCB in the store crosses the step unchanged — which is what lets the donation
return's TCB-shaped frames extend by a single rewrite instead of a second case
analysis. -/
theorem storeDonationHeadClear_tcb_eq
    {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationHeadClear head? st = .ok st')
    (k : SeLe4n.ObjId) (t0 : TCB) (hk : st.objects[k]? = some (.tcb t0)) :
    st'.objects[k]? = some (.tcb t0) := by
  rcases storeDonationHeadClear_cases h with rfl | ⟨rid, r, _, hRead, hS⟩
  · exact hk
  · by_cases hEq : k = rid.toObjId
    · rw [hEq, hRead] at hk; cases hk
    · rw [storeObject_objects_ne st st' rid.toObjId k _ hEq hObjInv hS]; exact hk

/-- WS-OD OD3.1: the head clear is invisible to the typed TCB accessor, for the
same reason it is invisible to the raw lookup — it writes a Reply. -/
theorem storeDonationHeadClear_getTcb?_eq
    {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationHeadClear head? st = .ok st') (tid : SeLe4n.ThreadId) :
    st'.getTcb? tid = st.getTcb? tid := by
  rcases storeDonationHeadClear_cases h with rfl | ⟨rid, r, _, hRead, hS⟩
  · rfl
  · unfold SystemState.getTcb?
    by_cases hEq : tid.toObjId = rid.toObjId
    · rw [hEq, hRead, storeObject_objects_eq' st rid.toObjId _ _ hObjInv hS]
    · rw [storeObject_objects_ne st st' rid.toObjId tid.toObjId _ hEq hObjInv hS]

/-- WS-OD OD3.1: ...and to the typed SchedContext accessor. -/
theorem storeDonationHeadClear_getSchedContext?_eq
    {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationHeadClear head? st = .ok st') (scId : SeLe4n.SchedContextId) :
    st'.getSchedContext? scId = st.getSchedContext? scId := by
  rcases storeDonationHeadClear_cases h with rfl | ⟨rid, r, _, hRead, hS⟩
  · rfl
  · unfold SystemState.getSchedContext?
    by_cases hEq : scId.toObjId = rid.toObjId
    · rw [hEq, hRead, storeObject_objects_eq' st rid.toObjId _ _ hObjInv hS]
    · rw [storeObject_objects_ne st st' rid.toObjId scId.toObjId _ hEq hObjInv hS]

/-- WS-OD OD3.1: the backward half of `storeDonationHeadClear_tcb_eq` — a TCB in
the post-state was there before, unchanged. -/
theorem storeDonationHeadClear_tcb_backward
    {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationHeadClear head? st = .ok st')
    (k : SeLe4n.ObjId) (t0 : TCB) (hk : st'.objects[k]? = some (.tcb t0)) :
    st.objects[k]? = some (.tcb t0) := by
  rcases storeDonationHeadClear_cases h with rfl | ⟨rid, r, _, hRead, hS⟩
  · exact hk
  · by_cases hEq : k = rid.toObjId
    · rw [hEq, storeObject_objects_eq' st rid.toObjId _ _ hObjInv hS] at hk
      cases hk
    · rw [← storeObject_objects_ne st st' rid.toObjId k _ hEq hObjInv hS]; exact hk


/-- **WS-RR RR7.22 (residual, remediation)**: one TCB is another with its
SchedContext binding rewritten — the complete description of what a donation
hand-off does to a thread, stated as a record update rather than as a list of
fields that agree, so a field added to `TCB` is covered by construction. -/
def tcbBindingRewrite (a b : TCB) : Prop :=
  ∃ sb, a = { b with schedContextBinding := sb }

theorem tcbBindingRewrite.refl (t : TCB) : tcbBindingRewrite t t := ⟨t.schedContextBinding, rfl⟩

theorem tcbBindingRewrite.trans {a b c : TCB}
    (h1 : tcbBindingRewrite a b) (h2 : tcbBindingRewrite b c) : tcbBindingRewrite a c := by
  obtain ⟨sb1, rfl⟩ := h1
  obtain ⟨sb2, rfl⟩ := h2
  exact ⟨sb1, rfl⟩

/-- WS-OD OD3.2: **one Reply is another with its reply-stack links rewritten** —
the complete description of what the donation return does to a Reply object,
stated as a record update rather than as a list of fields that agree, so a field
added to `Reply` is framed by construction.

The Reply counterpart of `tcbBindingRewrite`.  Before the pop existed the
donation return wrote no Reply at all and the invariant surface asserted exact
preservation; the head clear makes that false at exactly one key, and this is the
honest replacement — every field a conjunct reads other than `prev` and
`prev` still agrees by `rfl`. -/
def replyStackRewrite (a b : Reply) : Prop :=
  ∃ p n, a = { b with prev := p, next := n }

theorem replyStackRewrite.refl (r : Reply) : replyStackRewrite r r := ⟨r.prev, r.next, rfl⟩

theorem replyStackRewrite.trans {a b c : Reply}
    (h1 : replyStackRewrite a b) (h2 : replyStackRewrite b c) : replyStackRewrite a c := by
  obtain ⟨d1, p1, rfl⟩ := h1
  obtain ⟨d2, p2, rfl⟩ := h2
  exact ⟨d1, p1, rfl⟩

/-- WS-OD OD3.2: a rewritten Reply keeps its caller — the projection the
reply-freshness and stash invariants read. -/
theorem replyStackRewrite.caller_eq {a b : Reply} (h : replyStackRewrite a b) :
    a.caller = b.caller := by obtain ⟨_, _, rfl⟩ := h; rfl

/-- WS-OD OD3.2: a rewritten Reply keeps its identity. -/
theorem replyStackRewrite.replyId_eq {a b : Reply} (h : replyStackRewrite a b) :
    a.replyId = b.replyId := by obtain ⟨_, _, rfl⟩ := h; rfl


-- ----------------------------------------------------------------------------
-- WS-OD (`v0.35.4`): the re-head store — seL4's `prev->replyNext = head`
-- ----------------------------------------------------------------------------

/-! `storeReplyReHead scId below? st` marks the frame `below?` as the new head of
`scId`'s stack (`next := some (.head scId)`); the identity at `none`.  It is the
second half of the pop (`storeDonationHeadPop`), and it has exactly the shape of
the head clear — one optional Reply store on a key that already holds a Reply —
so its lemma family is that family with the record changed, generated from the
same text so the two cannot drift. -/
/-- WS-OD OD3.1: **the head clear, as one step whether or not there is a head.**

The pop writes a Reply only when the context heads a stack, and every frame the
donation return carries has to say what happens at both.  Naming the step keeps
that a *single* extra hop in each of those proofs rather than a second arm in
each of them: `storeReplyReHead_of_none` is definitional, and the frames
below state what the `some` arm does once. -/
def storeReplyReHead (scId : SeLe4n.SchedContextId) :
    Option SeLe4n.ReplyId → SystemState → Except KernelError SystemState
  | none, st => .ok st
  | some rid, st =>
    match st.getReply? rid with
    | some r =>
      match storeObject rid.toObjId (.reply { r with next := some (.head scId) }) st with
      | .error e => .error e
      | .ok ((), st') => .ok st'
    | none => .error .objectNotFound

@[simp] theorem storeReplyReHead_none (scId : SeLe4n.SchedContextId) (st : SystemState) :
    storeReplyReHead scId none st = .ok st := rfl

theorem storeReplyReHead_some (scId : SeLe4n.SchedContextId) (st : SystemState) (rid : SeLe4n.ReplyId) :
    storeReplyReHead scId (some rid) st =
      (match st.getReply? rid with
       | some r =>
         (match storeObject rid.toObjId
             (.reply { r with next := some (.head scId) }) st with
          | .error e => .error e
          | .ok ((), st') => .ok st')
       | none => .error .objectNotFound) := rfl

/-- WS-OD OD3.1: **the head clear is the identity, or one `storeObject` of one
Reply.**

The complete decomposition of the step, on the discipline
`returnDonatedSchedContext_ok_storeChain` already follows: every frame the
donation return carries crosses this step as one extra hop with a two-line case
analysis, rather than as a second arm threaded through the whole proof. -/
theorem storeReplyReHead_cases
    {scId : SeLe4n.SchedContextId} {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeReplyReHead scId head? st = .ok st') :
    st' = st ∨ ∃ (rid : SeLe4n.ReplyId) (r : Reply),
      head? = some rid ∧
      st.objects[rid.toObjId]? = some (.reply r) ∧
      storeObject rid.toObjId (.reply { r with next := some (.head scId) }) st
        = .ok ((), st') := by
  cases head? with
  | none => exact Or.inl (Except.ok.inj h).symm
  | some rid =>
    rw [storeReplyReHead_some] at h
    revert h
    cases hRep : st.getReply? rid with
    | none => intro h; cases h
    | some r =>
      simp only []
      cases hS : storeObject rid.toObjId
          (.reply { r with next := some (.head scId) }) st with
      | error e => intro h; cases h
      | ok pr =>
        simp only []
        intro h
        cases h
        exact Or.inr ⟨rid, r, rfl,
          (SystemState.getReply?_eq_some_iff st rid r).mp hRep, by rw [← hS]⟩

/-- WS-OD OD3.8: **the head clear on a `some` head is exactly one Reply store.**

The `some` refinement of `storeReplyReHead_cases`, whose identity arm is
reachable only for a `none` head: a caller that already knows there *is* a head
should not have to refute "the step did nothing" before it can say what the step
wrote.  The chain-preservation proof reads the post-state's object store at the
cleared key and at every other, and both readings come from this one store.

The Reply it exposes is read back through the state's own typed accessor, which
is also how `storeReplyReHead` itself reads it — a raw object-store lookup
here would be a second reading of the same field and an unmigrated site the AK7
cascade counts as debt. -/
theorem storeReplyReHead_some_ok
    {scId : SeLe4n.SchedContextId} {rid : SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeReplyReHead scId (some rid) st = .ok st') :
    ∃ r : Reply, st.getReply? rid = some r ∧
      storeObject rid.toObjId (.reply { r with next := some (.head scId) }) st
        = .ok ((), st') := by
  rw [storeReplyReHead_some] at h
  revert h
  cases hRep : st.getReply? rid with
  | none => intro h; cases h
  | some r =>
    simp only []
    cases hS : storeObject rid.toObjId
        (.reply { r with next := some (.head scId) }) st with
    | error e => intro h; cases h
    | ok pr =>
      simp only []
      intro h
      cases h
      exact ⟨r, rfl, by rw [← hS]⟩

/-- WS-OD OD3.1: **the head clear succeeds when the head is a Reply.**

The only error arm is a head that does not resolve to a Reply, so the step is
total on exactly the states the pop's own head validation admits. -/
theorem storeReplyReHead_ok_of_reply (scId : SeLe4n.SchedContextId) (st : SystemState)
    (head? : Option SeLe4n.ReplyId)
    (hReply : ∀ rid, head? = some rid → ∃ r : Reply, st.objects[rid.toObjId]? = some (.reply r)) :
    ∃ st', storeReplyReHead scId head? st = .ok st' := by
  cases head? with
  | none => exact ⟨st, rfl⟩
  | some rid =>
    obtain ⟨r, hR⟩ := hReply rid rfl
    have hRep : st.getReply? rid = some r := (SystemState.getReply?_eq_some_iff st rid r).mpr hR
    -- `storeObject` is unconditionally `.ok`, so the step reduces outright.
    obtain ⟨p, hP⟩ : ∃ p, storeObject rid.toObjId
        (.reply { r with next := some (.head scId) }) st = .ok p := ⟨_, rfl⟩
    obtain ⟨u, st'⟩ := p
    cases u
    refine ⟨st', ?_⟩
    rw [storeReplyReHead_some, hRep]
    simp only []
    rw [hP]

/-- WS-OD OD3.1: the head clear writes `objects` and nothing else — the
scheduler half. -/
theorem storeReplyReHead_scheduler_eq
    {scId : SeLe4n.SchedContextId} {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeReplyReHead scId head? st = .ok st') :
    st'.scheduler = st.scheduler := by
  rcases storeReplyReHead_cases h with rfl | ⟨rid, r, _, _, hS⟩
  · rfl
  · unfold storeObject at hS; cases hS; rfl

/-- WS-OD OD3.1: ...the service-registry half. -/
theorem storeReplyReHead_serviceRegistry_eq
    {scId : SeLe4n.SchedContextId} {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeReplyReHead scId head? st = .ok st') :
    st'.serviceRegistry = st.serviceRegistry := by
  rcases storeReplyReHead_cases h with rfl | ⟨rid, r, _, _, hS⟩
  · rfl
  · unfold storeObject at hS; cases hS; rfl

/-- WS-OD OD3.1: ...the TLB-shootdown half. -/
theorem storeReplyReHead_tlbShootdown_eq
    {scId : SeLe4n.SchedContextId} {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeReplyReHead scId head? st = .ok st') :
    st'.tlbShootdown = st.tlbShootdown := by
  rcases storeReplyReHead_cases h with rfl | ⟨rid, r, _, _, hS⟩
  · rfl
  · unfold storeObject at hS; cases hS; rfl

/-- WS-OD OD3.1: ...the machine half. -/
theorem storeReplyReHead_machine_eq
    {scId : SeLe4n.SchedContextId} {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeReplyReHead scId head? st = .ok st') :
    st'.machine = st.machine := by
  rcases storeReplyReHead_cases h with rfl | ⟨rid, r, _, _, hS⟩
  · rfl
  · unfold storeObject at hS; cases hS; rfl

/-- WS-OD OD3.1: the head clear preserves the object store's extended
invariant. -/
theorem storeReplyReHead_preserves_objects_invExt
    {scId : SeLe4n.SchedContextId} {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeReplyReHead scId head? st = .ok st') :
    st'.objects.invExt := by
  rcases storeReplyReHead_cases h with rfl | ⟨rid, r, _, _, hS⟩
  · exact hObjInv
  · exact storeObject_preserves_objects_invExt st st' _ _ hObjInv hS

/-- WS-OD OD3.1: the head clear preserves the object-index set's own invariant. -/
theorem storeReplyReHead_preserves_objectIndexSet_invExt
    {scId : SeLe4n.SchedContextId} {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hSetInv : st.objectIndexSet.table.invExt)
    (h : storeReplyReHead scId head? st = .ok st') :
    st'.objectIndexSet.table.invExt := by
  rcases storeReplyReHead_cases h with rfl | ⟨rid, r, _, _, hS⟩
  · exact hSetInv
  · exact SeLe4n.Model.storeObject_preserves_objectIndexSet_invExt st st' _ _ hSetInv hS

/-- WS-OD OD3.1: the head clear preserves object-index completeness — the fact a
projection hop needs, since a key already in the store stays registered. -/
theorem storeReplyReHead_preserves_objectIndexSetComplete
    {scId : SeLe4n.SchedContextId} {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt) (hSetInv : st.objectIndexSet.table.invExt)
    (hComplete : ∀ oid, st.objects[oid]? ≠ none → st.objectIndexSet.contains oid = true)
    (h : storeReplyReHead scId head? st = .ok st') :
    ∀ oid, st'.objects[oid]? ≠ none → st'.objectIndexSet.contains oid = true := by
  rcases storeReplyReHead_cases h with rfl | ⟨rid, r, _, _, hS⟩
  · exact hComplete
  · exact SeLe4n.Model.storeObject_preserves_objectIndexSetComplete st st' _ _ hObjInv hSetInv
      hComplete hS

/-- WS-OD OD3.1: **the head clear is invisible to every TCB.**

A Reply store lands on a key that held a Reply, and no key holds both, so every
TCB in the store crosses the step unchanged — which is what lets the donation
return's TCB-shaped frames extend by a single rewrite instead of a second case
analysis. -/
theorem storeReplyReHead_tcb_eq
    {scId : SeLe4n.SchedContextId} {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeReplyReHead scId head? st = .ok st')
    (k : SeLe4n.ObjId) (t0 : TCB) (hk : st.objects[k]? = some (.tcb t0)) :
    st'.objects[k]? = some (.tcb t0) := by
  rcases storeReplyReHead_cases h with rfl | ⟨rid, r, _, hRead, hS⟩
  · exact hk
  · by_cases hEq : k = rid.toObjId
    · rw [hEq, hRead] at hk; cases hk
    · rw [storeObject_objects_ne st st' rid.toObjId k _ hEq hObjInv hS]; exact hk

/-- WS-OD OD3.1: the head clear is invisible to the typed TCB accessor, for the
same reason it is invisible to the raw lookup — it writes a Reply. -/
theorem storeReplyReHead_getTcb?_eq
    {scId : SeLe4n.SchedContextId} {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeReplyReHead scId head? st = .ok st') (tid : SeLe4n.ThreadId) :
    st'.getTcb? tid = st.getTcb? tid := by
  rcases storeReplyReHead_cases h with rfl | ⟨rid, r, _, hRead, hS⟩
  · rfl
  · unfold SystemState.getTcb?
    by_cases hEq : tid.toObjId = rid.toObjId
    · rw [hEq, hRead, storeObject_objects_eq' st rid.toObjId _ _ hObjInv hS]
    · rw [storeObject_objects_ne st st' rid.toObjId tid.toObjId _ hEq hObjInv hS]

/-- WS-OD OD3.1: ...and to the typed SchedContext accessor. -/
theorem storeReplyReHead_getSchedContext?_eq
    {scId : SeLe4n.SchedContextId} {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeReplyReHead scId head? st = .ok st') (scId : SeLe4n.SchedContextId) :
    st'.getSchedContext? scId = st.getSchedContext? scId := by
  rcases storeReplyReHead_cases h with rfl | ⟨rid, r, _, hRead, hS⟩
  · rfl
  · unfold SystemState.getSchedContext?
    by_cases hEq : scId.toObjId = rid.toObjId
    · rw [hEq, hRead, storeObject_objects_eq' st rid.toObjId _ _ hObjInv hS]
    · rw [storeObject_objects_ne st st' rid.toObjId scId.toObjId _ hEq hObjInv hS]

/-- WS-OD OD3.1: the backward half of `storeReplyReHead_tcb_eq` — a TCB in
the post-state was there before, unchanged. -/
theorem storeReplyReHead_tcb_backward
    {scId : SeLe4n.SchedContextId} {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeReplyReHead scId head? st = .ok st')
    (k : SeLe4n.ObjId) (t0 : TCB) (hk : st'.objects[k]? = some (.tcb t0)) :
    st.objects[k]? = some (.tcb t0) := by
  rcases storeReplyReHead_cases h with rfl | ⟨rid, r, _, hRead, hS⟩
  · exact hk
  · by_cases hEq : k = rid.toObjId
    · rw [hEq, storeObject_objects_eq' st rid.toObjId _ _ hObjInv hS] at hk
      cases hk
    · rw [← storeObject_objects_ne st st' rid.toObjId k _ hEq hObjInv hS]; exact hk


-- ----------------------------------------------------------------------------
-- WS-OD (`v0.35.4`): the head pop — seL4's `reply_pop`, stack half
-- ----------------------------------------------------------------------------

/-- **The stack half of seL4's `reply_pop`**: unlink the head frame (both links
cleared, `storeDonationHeadClear`) and re-head the frame below it
(`storeReplyReHead`), so the context's new head points at the context and the
popped frame is on no stack.  The identity at `none`.  Fail-closed on a frame
below that does not resolve — under `donationChainWellFormed.prevLinkReciprocal`
every `prev` link resolves, so that arm is unreachable on a reachable state, and
a pop that could not re-head its new head would leave `scReply` naming a frame
that does not point back, which is what every head validator refuses. -/
def storeDonationHeadPop (scId : SeLe4n.SchedContextId) :
    Option (SeLe4n.ReplyId × Reply) → SystemState → Except KernelError SystemState
  | none, st => .ok st
  | some (rid, r), st =>
    match storeDonationHeadClear (some rid) st with
    | .error e => .error e
    | .ok st1 => storeReplyReHead scId r.prev st1

@[simp] theorem storeDonationHeadPop_none (scId : SeLe4n.SchedContextId) (st : SystemState) :
    storeDonationHeadPop scId none st = .ok st := rfl

theorem storeDonationHeadPop_some (scId : SeLe4n.SchedContextId) (st : SystemState)
    (rid : SeLe4n.ReplyId) (r : Reply) :
    storeDonationHeadPop scId (some (rid, r)) st =
      (match storeDonationHeadClear (some rid) st with
       | .error e => .error e
       | .ok st1 => storeReplyReHead scId r.prev st1) := rfl

/-- The pop's two halves, decomposed. -/
theorem storeDonationHeadPop_cases
    {scId : SeLe4n.SchedContextId} {head? : Option (SeLe4n.ReplyId × Reply)}
    {st st' : SystemState}
    (h : storeDonationHeadPop scId head? st = .ok st') :
    (head? = none ∧ st' = st) ∨
    ∃ (rid : SeLe4n.ReplyId) (r : Reply) (s1 : SystemState),
      head? = some (rid, r) ∧
      storeDonationHeadClear (some rid) st = .ok s1 ∧
      storeReplyReHead scId r.prev s1 = .ok st' := by
  cases head? with
  | none => exact Or.inl ⟨rfl, (Except.ok.inj h).symm⟩
  | some pr =>
    obtain ⟨rid, r⟩ := pr
    rw [storeDonationHeadPop_some] at h
    revert h
    cases hC : storeDonationHeadClear (some rid) st with
    | error e => intro h; cases h
    | ok s1 => intro h; exact Or.inr ⟨rid, r, s1, rfl, hC, h⟩

/-- A successful pop re-headed a frame that resolves: the frame below the head
is a Reply object of the intermediate state (and so of the pre-state, which the
unlink store only rewrote at the head's own key). -/
theorem storeDonationHeadPop_ok_below_resolves
    {scId : SeLe4n.SchedContextId} {head? : Option (SeLe4n.ReplyId × Reply)}
    {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationHeadPop scId head? st = .ok st')
    (rid : SeLe4n.ReplyId) (r : Reply) (below : SeLe4n.ReplyId)
    (hHead : head? = some (rid, r)) (hPrev : r.prev = some below) :
    ∃ b : Reply, st.objects[below.toObjId]? = some (.reply b) := by
  rcases storeDonationHeadPop_cases h with ⟨hAbs, _⟩ | ⟨rid', r', s1, hEq, hClear, hReHead⟩
  · rw [hHead] at hAbs; cases hAbs
  · rw [hHead] at hEq
    obtain ⟨hRid, hR⟩ := Prod.mk.inj (Option.some.inj hEq)
    rw [← hRid] at hClear
    rw [← hR, hPrev] at hReHead
    obtain ⟨b1, hB1, _⟩ := storeReplyReHead_some_ok hReHead
    rcases storeDonationHeadClear_cases hClear with hId | ⟨rid0, r0, hRid0, hRead0, hS0⟩
    · rw [← hId]; exact ⟨b1, (SystemState.getReply?_eq_some_iff _ _ _).mp hB1⟩
    · have hRid0' : rid0 = rid := (Option.some.inj hRid0).symm
      rw [hRid0'] at hRead0 hS0
      by_cases hk : below.toObjId = rid.toObjId
      · exact ⟨r0, by rw [hk]; exact hRead0⟩
      · refine ⟨b1, ?_⟩
        rw [← storeObject_objects_ne st s1 rid.toObjId below.toObjId _ hk hObjInv hS0]
        exact (SystemState.getReply?_eq_some_iff _ _ _).mp hB1

/-- The pop succeeds when the head is a Reply and the frame below it (if any) is
one too — the two objects it writes.  The frame below is read at the
intermediate state, where only the head's own key was rewritten and that key
still holds a Reply, so resolution in the pre-state suffices. -/
theorem storeDonationHeadPop_ok_of_reply (scId : SeLe4n.SchedContextId) (st : SystemState)
    (head? : Option (SeLe4n.ReplyId × Reply))
    (hObjInv : st.objects.invExt)
    (hHead : ∀ rid r, head? = some (rid, r) → st.objects[rid.toObjId]? = some (.reply r))
    (hBelow : ∀ rid r below, head? = some (rid, r) → r.prev = some below →
      ∃ b : Reply, st.objects[below.toObjId]? = some (.reply b)) :
    ∃ st', storeDonationHeadPop scId head? st = .ok st' := by
  cases head? with
  | none => exact ⟨st, rfl⟩
  | some pr =>
    obtain ⟨rid, r⟩ := pr
    have hR := hHead rid r rfl
    obtain ⟨s1, hClear⟩ := storeDonationHeadClear_ok_of_reply st (some rid)
      (fun rid' hEq => ⟨r, by rw [← Option.some.inj hEq]; exact hR⟩)
    obtain ⟨st', hReHead⟩ := storeReplyReHead_ok_of_reply scId s1 r.prev (by
      intro below hPrev
      obtain ⟨b, hB⟩ := hBelow rid r below rfl hPrev
      rcases storeDonationHeadClear_cases hClear with hId | ⟨rid0, r0, hRid0, hRead0, hS0⟩
      · rw [hId]; exact ⟨b, hB⟩
      · have hRid0' : rid0 = rid := (Option.some.inj hRid0).symm
        rw [hRid0'] at hS0
        by_cases hk : below.toObjId = rid.toObjId
        · refine ⟨{ r0 with prev := none, next := none }, ?_⟩
          rw [hk, storeObject_objects_eq' st rid.toObjId _ _ hObjInv hS0]
        · refine ⟨b, ?_⟩
          rw [storeObject_objects_ne st s1 rid.toObjId below.toObjId _ hk hObjInv hS0]
          exact hB)
    refine ⟨st', ?_⟩
    rw [storeDonationHeadPop_some, hClear]
    exact hReHead

theorem storeDonationHeadPop_preserves_objects_invExt
    {scId : SeLe4n.SchedContextId} {head? : Option (SeLe4n.ReplyId × Reply)}
    {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationHeadPop scId head? st = .ok st') :
    st'.objects.invExt := by
  rcases storeDonationHeadPop_cases h with ⟨_, rfl⟩ | ⟨rid, r, s1, _, hClear, hReHead⟩
  · exact hObjInv
  · exact storeReplyReHead_preserves_objects_invExt
      (storeDonationHeadClear_preserves_objects_invExt hObjInv hClear) hReHead

theorem storeDonationHeadPop_preserves_objectIndexSet_invExt
    {scId : SeLe4n.SchedContextId} {head? : Option (SeLe4n.ReplyId × Reply)}
    {st st' : SystemState}
    (hSetInv : st.objectIndexSet.table.invExt)
    (h : storeDonationHeadPop scId head? st = .ok st') :
    st'.objectIndexSet.table.invExt := by
  rcases storeDonationHeadPop_cases h with ⟨_, rfl⟩ | ⟨rid, r, s1, _, hClear, hReHead⟩
  · exact hSetInv
  · exact storeReplyReHead_preserves_objectIndexSet_invExt
      (storeDonationHeadClear_preserves_objectIndexSet_invExt hSetInv hClear) hReHead

theorem storeDonationHeadPop_preserves_objectIndexSetComplete
    {scId : SeLe4n.SchedContextId} {head? : Option (SeLe4n.ReplyId × Reply)}
    {st st' : SystemState}
    (hObjInv : st.objects.invExt) (hSetInv : st.objectIndexSet.table.invExt)
    (hComplete : ∀ oid, st.objects[oid]? ≠ none → st.objectIndexSet.contains oid = true)
    (h : storeDonationHeadPop scId head? st = .ok st') :
    ∀ oid, st'.objects[oid]? ≠ none → st'.objectIndexSet.contains oid = true := by
  rcases storeDonationHeadPop_cases h with ⟨_, rfl⟩ | ⟨rid, r, s1, _, hClear, hReHead⟩
  · exact hComplete
  · exact storeReplyReHead_preserves_objectIndexSetComplete
      (storeDonationHeadClear_preserves_objects_invExt hObjInv hClear)
      (storeDonationHeadClear_preserves_objectIndexSet_invExt hSetInv hClear)
      (storeDonationHeadClear_preserves_objectIndexSetComplete hObjInv hSetInv hComplete hClear)
      hReHead

theorem storeDonationHeadPop_scheduler_eq
    {scId : SeLe4n.SchedContextId} {head? : Option (SeLe4n.ReplyId × Reply)}
    {st st' : SystemState}
    (h : storeDonationHeadPop scId head? st = .ok st') :
    st'.scheduler = st.scheduler := by
  rcases storeDonationHeadPop_cases h with ⟨_, rfl⟩ | ⟨rid, r, s1, _, hClear, hReHead⟩
  · rfl
  · rw [storeReplyReHead_scheduler_eq hReHead, storeDonationHeadClear_scheduler_eq hClear]

theorem storeDonationHeadPop_serviceRegistry_eq
    {scId : SeLe4n.SchedContextId} {head? : Option (SeLe4n.ReplyId × Reply)}
    {st st' : SystemState}
    (h : storeDonationHeadPop scId head? st = .ok st') :
    st'.serviceRegistry = st.serviceRegistry := by
  rcases storeDonationHeadPop_cases h with ⟨_, rfl⟩ | ⟨rid, r, s1, _, hClear, hReHead⟩
  · rfl
  · rw [storeReplyReHead_serviceRegistry_eq hReHead,
      storeDonationHeadClear_serviceRegistry_eq hClear]

theorem storeDonationHeadPop_tlbShootdown_eq
    {scId : SeLe4n.SchedContextId} {head? : Option (SeLe4n.ReplyId × Reply)}
    {st st' : SystemState}
    (h : storeDonationHeadPop scId head? st = .ok st') :
    st'.tlbShootdown = st.tlbShootdown := by
  rcases storeDonationHeadPop_cases h with ⟨_, rfl⟩ | ⟨rid, r, s1, _, hClear, hReHead⟩
  · rfl
  · rw [storeReplyReHead_tlbShootdown_eq hReHead, storeDonationHeadClear_tlbShootdown_eq hClear]

theorem storeDonationHeadPop_machine_eq
    {scId : SeLe4n.SchedContextId} {head? : Option (SeLe4n.ReplyId × Reply)}
    {st st' : SystemState}
    (h : storeDonationHeadPop scId head? st = .ok st') :
    st'.machine = st.machine := by
  rcases storeDonationHeadPop_cases h with ⟨_, rfl⟩ | ⟨rid, r, s1, _, hClear, hReHead⟩
  · rfl
  · rw [storeReplyReHead_machine_eq hReHead, storeDonationHeadClear_machine_eq hClear]

theorem storeDonationHeadPop_tcb_eq
    {scId : SeLe4n.SchedContextId} {head? : Option (SeLe4n.ReplyId × Reply)}
    {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationHeadPop scId head? st = .ok st')
    (k : SeLe4n.ObjId) (t0 : TCB) (hk : st.objects[k]? = some (.tcb t0)) :
    st'.objects[k]? = some (.tcb t0) := by
  rcases storeDonationHeadPop_cases h with ⟨_, rfl⟩ | ⟨rid, r, s1, _, hClear, hReHead⟩
  · exact hk
  · exact storeReplyReHead_tcb_eq (storeDonationHeadClear_preserves_objects_invExt hObjInv hClear)
      hReHead k t0 (storeDonationHeadClear_tcb_eq hObjInv hClear k t0 hk)

theorem storeDonationHeadPop_getTcb?_eq
    {scId : SeLe4n.SchedContextId} {head? : Option (SeLe4n.ReplyId × Reply)}
    {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationHeadPop scId head? st = .ok st') (tid : SeLe4n.ThreadId) :
    st'.getTcb? tid = st.getTcb? tid := by
  rcases storeDonationHeadPop_cases h with ⟨_, rfl⟩ | ⟨rid, r, s1, _, hClear, hReHead⟩
  · rfl
  · rw [storeReplyReHead_getTcb?_eq (storeDonationHeadClear_preserves_objects_invExt hObjInv hClear)
      hReHead tid, storeDonationHeadClear_getTcb?_eq hObjInv hClear tid]

theorem storeDonationHeadPop_getSchedContext?_eq
    {scId : SeLe4n.SchedContextId} {head? : Option (SeLe4n.ReplyId × Reply)}
    {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationHeadPop scId head? st = .ok st') (sc : SeLe4n.SchedContextId) :
    st'.getSchedContext? sc = st.getSchedContext? sc := by
  rcases storeDonationHeadPop_cases h with ⟨_, rfl⟩ | ⟨rid, r, s1, _, hClear, hReHead⟩
  · rfl
  · rw [storeReplyReHead_getSchedContext?_eq
      (storeDonationHeadClear_preserves_objects_invExt hObjInv hClear) hReHead sc,
      storeDonationHeadClear_getSchedContext?_eq hObjInv hClear sc]

theorem storeDonationHeadPop_tcb_backward
    {scId : SeLe4n.SchedContextId} {head? : Option (SeLe4n.ReplyId × Reply)}
    {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationHeadPop scId head? st = .ok st')
    (k : SeLe4n.ObjId) (t0 : TCB) (hk : st'.objects[k]? = some (.tcb t0)) :
    st.objects[k]? = some (.tcb t0) := by
  rcases storeDonationHeadPop_cases h with ⟨_, rfl⟩ | ⟨rid, r, s1, _, hClear, hReHead⟩
  · exact hk
  · exact storeDonationHeadClear_tcb_backward hObjInv hClear k t0
      (storeReplyReHead_tcb_backward (storeDonationHeadClear_preserves_objects_invExt hObjInv hClear)
        hReHead k t0 hk)

/-- Every key the pop does not name — neither the head nor the frame below it —
is untouched. -/
theorem storeDonationHeadPop_objects_ne
    {scId : SeLe4n.SchedContextId} {head? : Option (SeLe4n.ReplyId × Reply)}
    {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationHeadPop scId head? st = .ok st')
    (k : SeLe4n.ObjId)
    (hkHead : ∀ rid r, head? = some (rid, r) → k ≠ rid.toObjId)
    (hkBelow : ∀ rid r below, head? = some (rid, r) → r.prev = some below → k ≠ below.toObjId) :
    st'.objects[k]? = st.objects[k]? := by
  rcases storeDonationHeadPop_cases h with ⟨_, rfl⟩ | ⟨rid, r, s1, hEq, hClear, hReHead⟩
  · rfl
  · have hInv1 := storeDonationHeadClear_preserves_objects_invExt hObjInv hClear
    have e1 : s1.objects[k]? = st.objects[k]? := by
      rcases storeDonationHeadClear_cases hClear with rfl | ⟨rid0, r0, hRid0, _, hS0⟩
      · rfl
      · exact storeObject_objects_ne st s1 rid0.toObjId k _
          (by rw [← Option.some.inj hRid0]; exact hkHead rid r hEq) hObjInv hS0
    have e2 : st'.objects[k]? = s1.objects[k]? := by
      rcases storeReplyReHead_cases hReHead with rfl | ⟨below, b, hBelow, _, hS2⟩
      · rfl
      · exact storeObject_objects_ne s1 st' below.toObjId k _ (hkBelow rid r below hEq hBelow) hInv1 hS2
    rw [e2, e1]

/-- The pop rewrites Reply objects only, and only their stack links: every Reply
of the pre-state survives as a Reply agreeing on everything but `prev` / `next`. -/
theorem storeDonationHeadPop_reply_rewrite
    {scId : SeLe4n.SchedContextId} {head? : Option (SeLe4n.ReplyId × Reply)}
    {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationHeadPop scId head? st = .ok st')
    (oid : SeLe4n.ObjId) (r : Reply) (hReply : st.objects[oid]? = some (.reply r)) :
    ∃ r', st'.objects[oid]? = some (.reply r') ∧ replyStackRewrite r' r := by
  rcases storeDonationHeadPop_cases h with ⟨_, rfl⟩ | ⟨rid, rh, s1, _, hClear, hReHead⟩
  · exact ⟨r, hReply, replyStackRewrite.refl r⟩
  · have hInv1 := storeDonationHeadClear_preserves_objects_invExt hObjInv hClear
    obtain ⟨r1, h1, hR1⟩ : ∃ r1, s1.objects[oid]? = some (.reply r1) ∧ replyStackRewrite r1 r := by
      rcases storeDonationHeadClear_cases hClear with rfl | ⟨rid0, r0, _, hRead, hS0⟩
      · exact ⟨r, hReply, replyStackRewrite.refl r⟩
      · by_cases hk : oid = rid0.toObjId
        · have hStored : s1.objects[rid0.toObjId]? = _ := storeObject_objects_eq' st _ _ _ hObjInv hS0
          have hReadAt : st.objects[oid]? = some (.reply r0) := by rw [hk]; exact hRead
          have hr0 : r0 = r := KernelObject.reply.inj (Option.some.inj (hReadAt.symm.trans hReply))
          subst hr0
          exact ⟨_, by rw [hk]; exact hStored, ⟨none, none, rfl⟩⟩
        · exact ⟨r, (storeObject_objects_ne st s1 rid0.toObjId oid _ hk hObjInv hS0).trans hReply,
            replyStackRewrite.refl r⟩
    obtain ⟨r2, h2, hR2⟩ : ∃ r2, st'.objects[oid]? = some (.reply r2) ∧ replyStackRewrite r2 r1 := by
      rcases storeReplyReHead_cases hReHead with rfl | ⟨below, b, _, hReadB, hS2⟩
      · exact ⟨r1, h1, replyStackRewrite.refl r1⟩
      · by_cases hk : oid = below.toObjId
        · have hStored : st'.objects[below.toObjId]? = _ := storeObject_objects_eq' s1 _ _ _ hInv1 hS2
          have hReadAt : s1.objects[oid]? = some (.reply b) := by rw [hk]; exact hReadB
          have hb : b = r1 := KernelObject.reply.inj (Option.some.inj (hReadAt.symm.trans h1))
          subst hb
          exact ⟨_, by rw [hk]; exact hStored, ⟨b.prev, some (.head scId), rfl⟩⟩
        · exact ⟨r1, (storeObject_objects_ne s1 st' below.toObjId oid _ hk hInv1 hS2).trans h1,
            replyStackRewrite.refl r1⟩
    exact ⟨r2, h2, hR2.trans hR1⟩

/-- A key holding a non-Reply is untouched by the pop. -/
theorem storeDonationHeadPop_non_reply_eq
    {scId : SeLe4n.SchedContextId} {head? : Option (SeLe4n.ReplyId × Reply)}
    {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationHeadPop scId head? st = .ok st')
    (k : SeLe4n.ObjId) (hNotReply : ∀ r : Reply, st.objects[k]? ≠ some (.reply r)) :
    st'.objects[k]? = st.objects[k]? := by
  rcases storeDonationHeadPop_cases h with ⟨_, rfl⟩ | ⟨rid, rh, s1, _, hClear, hReHead⟩
  · rfl
  · have hInv1 := storeDonationHeadClear_preserves_objects_invExt hObjInv hClear
    have e1 : s1.objects[k]? = st.objects[k]? := by
      rcases storeDonationHeadClear_cases hClear with rfl | ⟨rid0, r0, _, hRead, hS0⟩
      · rfl
      · exact storeObject_objects_ne st s1 rid0.toObjId k _
          (fun hk => hNotReply r0 (by rw [hk]; exact hRead)) hObjInv hS0
    have e2 : st'.objects[k]? = s1.objects[k]? := by
      rcases storeReplyReHead_cases hReHead with rfl | ⟨below, b, _, hReadB, hS2⟩
      · rfl
      · exact storeObject_objects_ne s1 st' below.toObjId k _
          (fun hk => hNotReply b (by rw [← e1, hk]; exact hReadB)) hInv1 hS2
    rw [e2, e1]

/-- WS-RR RR8.16 (`v0.35.199`): the head clear writes no CDT table -- it is one
`storeObject`, which writes `objects`, the two indices, the lifecycle table and
the ASID table. -/
theorem storeDonationHeadClear_cdt_eq {head? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeDonationHeadClear head? st = .ok st') :
    st'.cdt = st.cdt ∧ st'.cdtNodeSlot = st.cdtNodeSlot := by
  rcases storeDonationHeadClear_cases h with rfl | ⟨rid, r, _, _, hS⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨storeObject_cdt_eq _ _ _ _ hS, storeObject_cdtNodeSlot_eq _ _ _ _ hS⟩

/-- WS-RR RR8.16 (`v0.35.199`): and neither does the re-head. -/
theorem storeReplyReHead_cdt_eq {scId : SeLe4n.SchedContextId}
    {below? : Option SeLe4n.ReplyId} {st st' : SystemState}
    (h : storeReplyReHead scId below? st = .ok st') :
    st'.cdt = st.cdt ∧ st'.cdtNodeSlot = st.cdtNodeSlot := by
  rcases storeReplyReHead_cases h with rfl | ⟨rid, r, _, _, hS⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨storeObject_cdt_eq _ _ _ _ hS, storeObject_cdtNodeSlot_eq _ _ _ _ hS⟩

/-- WS-RR RR8.16 (`v0.35.199`): so the pop writes no CDT table either. -/
theorem storeDonationHeadPop_cdt_eq {scId : SeLe4n.SchedContextId}
    {head? : Option (SeLe4n.ReplyId × Reply)} {st st' : SystemState}
    (h : storeDonationHeadPop scId head? st = .ok st') :
    st'.cdt = st.cdt ∧ st'.cdtNodeSlot = st.cdtNodeSlot := by
  cases head? with
  | none => cases h; exact ⟨rfl, rfl⟩
  | some p =>
      obtain ⟨rid, r⟩ := p
      rw [storeDonationHeadPop_some] at h
      revert h
      cases hClear : storeDonationHeadClear (some rid) st with
      | error _ => intro h; simp only at h; cases h
      | ok s1 =>
          intro h
          simp only at h
          have h1 := storeDonationHeadClear_cdt_eq hClear
          have h2 := storeReplyReHead_cdt_eq h
          exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

/-- WS-RR RR8.16 (`v0.35.199`): the pop is a `kindPreservingWrite` — every key
it touches held a Reply and still holds one, and every other key is untouched.

The shape register row 85's two bundle frames consume, so the donation return's
whole store chain composes by `.trans` rather than by a pointwise argument per
step. -/
theorem storeDonationHeadPop_kindPreservingWrite
    {scId : SeLe4n.SchedContextId} {head? : Option (SeLe4n.ReplyId × Reply)}
    {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationHeadPop scId head? st = .ok st') :
    kindPreservingWrite st st' := by
  intro k
  by_cases hRep : ∃ r : Reply, st.objects[k]? = some (.reply r)
  · obtain ⟨r, hr⟩ := hRep
    obtain ⟨r', hr', _⟩ := storeDonationHeadPop_reply_rewrite hObjInv h k r hr
    exact Or.inr ⟨.reply r, .reply r', hr, hr', rfl, by simp [KernelObject.objectType]⟩
  · exact Or.inl (storeDonationHeadPop_non_reply_eq hObjInv h k (fun r hr => hRep ⟨r, hr⟩))

/-- A non-Reply found after the pop was there before it. -/
theorem storeDonationHeadPop_non_reply_backward
    {scId : SeLe4n.SchedContextId} {head? : Option (SeLe4n.ReplyId × Reply)}
    {st st' : SystemState}
    (hObjInv : st.objects.invExt)
    (h : storeDonationHeadPop scId head? st = .ok st')
    (k : SeLe4n.ObjId) (o : KernelObject) (hNotReply : ∀ r : Reply, o ≠ .reply r)
    (hPost : st'.objects[k]? = some o) :
    st.objects[k]? = some o := by
  by_cases hRep : ∃ r : Reply, st.objects[k]? = some (.reply r)
  · obtain ⟨r, hr⟩ := hRep
    obtain ⟨r', hr', _⟩ := storeDonationHeadPop_reply_rewrite hObjInv h k r hr
    rw [hr'] at hPost
    exact absurd (Option.some.inj hPost).symm (hNotReply r')
  · rw [← storeDonationHeadPop_non_reply_eq hObjInv h k (fun r hr => hRep ⟨r, hr⟩)]
    exact hPost

-- ----------------------------------------------------------------------------
-- WS-OD (`v0.35.4`): the non-head frame removal (renamed by WS-HP HP6.1)
-- ----------------------------------------------------------------------------

/-- **WS-HP HP6.3: the frame this removal links the frame above DOWN to** — the
`prev` side of seL4's `reply_remove`, resolved and validated on the pre-state.

`some (below, b)` exactly when the cut frame names a frame below it (`r.prev`),
that frame is not the frame *above* the cut, it resolves, and it links back up to
the cut frame (`b.next = some (.frame rid)`).

**Four arms decline, and declining is not a refusal.**  That is the plan's
finding 2, and it is load-bearing rather than a convenience.
`spliceReplyFrameOutOrSelf` folds a *refusal* to the identity, and its whole
soundness argument is that a refusal means nothing links down to the cut frame,
so the `consumeCallerReply` that follows breaks no reciprocity
(`spliceReplyFrameOutOrSelf_unreferenced`).  A below-side **refusal** folded to
the identity would leave a reciprocating frame above still naming the cut frame
while the caller clears its links — the wedge WS-RM exists to prevent.  So the
below side answers an `Option`: not named, naming the frame above, not resolving,
or not reciprocating all mean *not followed*, the removal degenerates to
`severAtCut` there (`spliceReplyFrameOut_eq_sever_of_no_frame_below`), and this
operation's refusal set is therefore **exactly** the sever's — every refusal
theorem carries verbatim.

Declining is fail-closed on its own terms too: writing `above.prev := some below`
over a link `below` does not answer would stop a later walk mid-chain, since every
walk validates reciprocity (`donationChainFrom`) — trading a lost reservation for
an unreachable one.

**`below ≠ above` is a check, not a consequence.**  A frame whose `prev` and
`next` named the same neighbour would have two of the splice's stores collide at
one key, leaving `above.prev := some above` with `above.next` still naming the cut
frame — a self-referential frame no walk can leave.  Declining there severs, which
is what the pre-WS-HP kernel produced.  Under `donationChainWellFormed` the arm is
unreachable (it entails a two-frame cycle), so nothing this kernel reaches takes
it; checking it is what makes the splice branch's **pairwise** distinctness of its
three written keys a theorem (`spliceFrameBelow?_ne_above`,
`spliceFrameBelow?_ne_cut`, `spliceFrameBelow?_above_ne_cut`) rather than an
invariant obligation on every caller.

The cut frame's record is an **argument** rather than re-read from `st`: the one
caller has already resolved it and read the `next` that named `above`, so reading
it again would answer one question twice and give the two answers a way to
disagree. -/
def spliceFrameBelow? (st : SystemState) (rid : SeLe4n.ReplyId) (r : Reply)
    (above : SeLe4n.ReplyId) : Option (SeLe4n.ReplyId × Reply) :=
  match r.prev with
  | none => none
  | some below =>
    if below == above then none
    else
      match st.getReply? below with
      | none => none
      | some b => if b.next != some (.frame rid) then none else some (below, b)

/-- **WS-HP HP6.3: the resolver, characterised** — a `some` answer is the cut
frame's own `prev`, distinct from the frame above, resolving, and reciprocating.
The four facts the splice's algebra reads; nothing else may be assumed of it. -/
theorem spliceFrameBelow?_eq_some {st : SystemState} {rid above below : SeLe4n.ReplyId}
    {r b : Reply} (h : spliceFrameBelow? st rid r above = some (below, b)) :
    r.prev = some below ∧ below ≠ above ∧ st.getReply? below = some b ∧
      b.next = some (.frame rid) := by
  unfold spliceFrameBelow? at h
  revert h
  cases hP : r.prev with
  | none => intro h; cases h
  | some x =>
    simp only []
    cases hE : (x == above) with
    | true => simp only [if_true]; intro h; cases h
    | false =>
      simp only [Bool.false_eq_true, if_false]
      cases hB : st.getReply? x with
      | none => intro h; cases h
      | some bx =>
        simp only []
        cases hN : (bx.next != some (.frame rid)) with
        | true => simp only [if_true]; intro h; cases h
        | false =>
          simp only [Bool.false_eq_true, if_false]
          intro h
          rw [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hb1, hb2⟩ := h
          subst hb1; subst hb2
          exact ⟨rfl, by simpa using hE, hB, by simpa using hN⟩

/-- The frame below is not the frame above — the explicit check, read back. -/
theorem spliceFrameBelow?_ne_above {st : SystemState} {rid above below : SeLe4n.ReplyId}
    {r b : Reply} (h : spliceFrameBelow? st rid r above = some (below, b)) :
    below ≠ above := (spliceFrameBelow?_eq_some h).2.1

/-- **The frame below is not the cut frame itself**, and that is derived rather
than checked: the frame below reciprocates (`b.next = some (.frame rid)`) while
the cut frame's `next` names `above`, so `below = rid` would force `above = rid`
and hence `above = below`, which the check refuses. -/
theorem spliceFrameBelow?_ne_cut {st : SystemState} {rid above below : SeLe4n.ReplyId}
    {r b : Reply} (hR : st.getReply? rid = some r) (hN : r.next = some (.frame above))
    (h : spliceFrameBelow? st rid r above = some (below, b)) :
    below ≠ rid := by
  obtain ⟨_, hNe, hB, hBN⟩ := spliceFrameBelow?_eq_some h
  intro hEq
  subst hEq
  rw [hR] at hB
  rw [← Option.some.inj hB, hN] at hBN
  exact hNe (ReplyStackLink.frame.inj (Option.some.inj hBN)).symm

/-- **And the frame above is not the cut frame either** — derived the same way:
`above = rid` makes the validated `a.prev = some rid` read `r.prev = some rid`, so
the frame below *is* the frame above, which the check refuses.  With the two
lemmas above, the three keys the splice writes are pairwise distinct, which is
what lets its post-state be read off key by key. -/
theorem spliceFrameBelow?_above_ne_cut {st : SystemState} {rid above below : SeLe4n.ReplyId}
    {r a b : Reply} (hR : st.getReply? rid = some r) (hA : st.getReply? above = some a)
    (hP : a.prev = some rid)
    (h : spliceFrameBelow? st rid r above = some (below, b)) :
    above ≠ rid := by
  obtain ⟨hPrev, hNe, _, _⟩ := spliceFrameBelow?_eq_some h
  intro hEq
  subst hEq
  rw [hR] at hA
  rw [← Option.some.inj hA] at hP
  exact hNe (Option.some.inj (hPrev.symm.trans hP))

/-- **WS-HP HP6.3: the removal's stores, as one composed step** — one store where
there is nothing to splice to, three where there is.

Composed rather than split into named operations, and that is the plan's
finding 3: 47 sites in the tree destructure `spliceReplyFrameOut_cases`, 37 of
them in this module, so a per-store case analysis would change the pattern at all
47 where a composed step leaves the arity alone and proves the multi-store
analysis **once**, here.

**The splice writes three keys, and the third is the cut frame itself.**  The
first two are the reciprocal pair — `above.prev := some below` and
`below.next := some (.frame above)` — written *together*, so the pair the removal
repairs is never transiently inconsistent; that closes the divergence from
upstream where this tree left the frame below's upward link stale and validated
reciprocity at every read instead.  The third clears the cut frame's own `prev`,
and it is **not optional**: after the pair is written nothing links up to the cut
frame any more, so a `prev` left naming `below` would falsify
`donationChainWellFormed.prevLinkReciprocal` at the cut frame for as long as the
frame is stored.  That is seL4's `reply_unlink`, which upstream runs inside
`reply_remove` for exactly this reason, and doing it here rather than leaving it
to the `Reply.consumed` that follows is what keeps **every** state this operation
produces chain-well-formed — so the removal states the invariant outright instead
of a relaxation its callers have to discharge.  The key costs no footprint: it is
the caller's own reply object, already a declared write member of both reply
footprints (`replyId`) and of the cancellation footprint (`consumedReplyId`).

The cut frame's `next` is deliberately **not** cleared here: `Reply.consumed`
clears it, and only for a non-head, because the donation pop validates a head by
that very link.

`b` is read from the **pre**-state and stored after the first store, and `r` after
the second, which is sound because `spliceFrameBelow?` and the frame above's own
validation establish that the three keys are pairwise distinct
(`spliceReplyFrameStores_splice_values`).  Re-reading either from an intermediate
state would answer one question twice and give the two answers a way to
disagree. -/
def spliceReplyFrameStores (st : SystemState) (rid above : SeLe4n.ReplyId)
    (r a : Reply) : Except KernelError SystemState :=
  match spliceFrameBelow? st rid r above with
  | none =>
    match storeObject above.toObjId (.reply { a with prev := none }) st with
    | .error e => .error e
    | .ok ((), st') => .ok st'
  | some (below, b) =>
    match storeObject above.toObjId (.reply { a with prev := some below }) st with
    | .error e => .error e
    | .ok ((), s1) =>
      match storeObject below.toObjId (.reply { b with next := some (.frame above) }) s1 with
      | .error e => .error e
      | .ok ((), s2) =>
        match storeObject rid.toObjId (.reply { r with prev := none }) s2 with
        | .error e => .error e
        | .ok ((), st') => .ok st'

/-- **WS-HP HP6.3: the composed step, decomposed** — either nothing below to
splice to and the single sever store, or the reciprocal pair and the cut frame's
own unlink, in order.  Every `spliceReplyFrameStores_*` fact below is a two-way
split on this, which is why none of the 47 sites that destructure the removal has
to know how many stores there are. -/
theorem spliceReplyFrameStores_cases {st st' : SystemState} {rid above : SeLe4n.ReplyId}
    {r a : Reply} (h : spliceReplyFrameStores st rid above r a = .ok st') :
    (spliceFrameBelow? st rid r above = none ∧
        storeObject above.toObjId (.reply { a with prev := none }) st = .ok ((), st')) ∨
      ∃ (below : SeLe4n.ReplyId) (b : Reply) (s1 s2 : SystemState),
        spliceFrameBelow? st rid r above = some (below, b) ∧
        storeObject above.toObjId (.reply { a with prev := some below }) st = .ok ((), s1) ∧
        storeObject below.toObjId (.reply { b with next := some (.frame above) }) s1
          = .ok ((), s2) ∧
        storeObject rid.toObjId (.reply { r with prev := none }) s2 = .ok ((), st') := by
  unfold spliceReplyFrameStores at h
  revert h
  cases hBelow : spliceFrameBelow? st rid r above with
  | none =>
    simp only []
    cases hS : storeObject above.toObjId (.reply { a with prev := none }) st with
    | error _ => intro h; cases h
    | ok pr =>
      obtain ⟨u, s'⟩ := pr; cases u
      intro h; cases h
      exact Or.inl ⟨trivial, rfl⟩
  | some pair =>
    obtain ⟨below, b⟩ := pair
    simp only []
    cases hS1 : storeObject above.toObjId (.reply { a with prev := some below }) st with
    | error _ => intro h; cases h
    | ok pr1 =>
      obtain ⟨u1, s1⟩ := pr1; cases u1
      simp only []
      cases hS2 : storeObject below.toObjId
          (.reply { b with next := some (.frame above) }) s1 with
      | error _ => intro h; cases h
      | ok pr2 =>
        obtain ⟨u2, s2⟩ := pr2; cases u2
        simp only []
        cases hS3 : storeObject rid.toObjId (.reply { r with prev := none }) s2 with
        | error _ => intro h; cases h
        | ok pr3 =>
          obtain ⟨u3, s3⟩ := pr3; cases u3
          intro h; cases h
          exact Or.inr ⟨below, b, s1, s2, rfl, hS1, hS2, hS3⟩

/-- **WS-HP HP6.4: the composed step is total** — `storeObject` never fails, so
the removal's only refusals are the two the frame **above** can produce, which is
what makes this operation's refusal set exactly the sever's. -/
theorem spliceReplyFrameStores_isOk (st : SystemState) (rid above : SeLe4n.ReplyId)
    (r a : Reply) : ∃ st', spliceReplyFrameStores st rid above r a = .ok st' := by
  unfold spliceReplyFrameStores storeObject
  cases spliceFrameBelow? st rid r above with
  | none => exact ⟨_, rfl⟩
  | some pair => obtain ⟨below, b⟩ := pair; exact ⟨_, rfl⟩

-- ----------------------------------------------------------------------------
-- WS-HP HP6.4: the composed store step's read/write algebra
-- ----------------------------------------------------------------------------
--
-- Every entry below is a two-way split on `spliceFrameBelow?` and then one or
-- three `storeObject` facts, and all of them are corollaries of the first two:
-- the removal writes Replies and nothing else, so a consumer that reads a TCB, an
-- endpoint, a notification or a SchedContext sees nothing, and a consumer that
-- reads a Reply sees at most its stack links moved.  That is what keeps the
-- eighteen `spliceReplyFrameOut_*` statements below — and the projection and
-- `ipcInvariantFull` surfaces outside this module — one-symbol repairs rather
-- than fresh case analyses over three stores.

/-- **WS-HP HP6.4: the splice branch's post-state, key by key.**  Its three
written keys are pairwise distinct — the frame above, the frame below, and the cut
frame — so each holds exactly what its own store wrote and every other key is
untouched.  The master fact of this section; the general frame below reads it. -/
theorem spliceReplyFrameStores_splice_values {st st' : SystemState}
    {rid above below : SeLe4n.ReplyId} {r a b : Reply} (hObjInv : st.objects.invExt)
    (hR : st.getReply? rid = some r) (hN : r.next = some (.frame above))
    (hA : st.getReply? above = some a) (hP : a.prev = some rid)
    (hBelow : spliceFrameBelow? st rid r above = some (below, b))
    (h : spliceReplyFrameStores st rid above r a = .ok st') :
    st'.getReply? above = some { a with prev := some below } ∧
      st'.getReply? below = some { b with next := some (.frame above) } ∧
      st'.getReply? rid = some { r with prev := none } ∧
      ∀ k : SeLe4n.ObjId, k ≠ above.toObjId → k ≠ below.toObjId → k ≠ rid.toObjId →
        st'.objects[k]? = st.objects[k]? := by
  rcases spliceReplyFrameStores_cases h with ⟨hNone, _⟩ | ⟨below', b', s1, s2, hB', hS1, hS2, hS3⟩
  · rw [hNone] at hBelow; cases hBelow
  · rw [hBelow, Option.some.injEq, Prod.mk.injEq] at hB'
    obtain ⟨rfl, rfl⟩ := hB'
    have hNeBA : below ≠ above := spliceFrameBelow?_ne_above hBelow
    have hNeBR : below ≠ rid := spliceFrameBelow?_ne_cut hR hN hBelow
    have hNeAR : above ≠ rid := spliceFrameBelow?_above_ne_cut hR hA hP hBelow
    have hAB : above.toObjId ≠ below.toObjId :=
      fun hx => hNeBA (SeLe4n.ReplyId.toObjId_injective _ _ hx).symm
    have hAR : above.toObjId ≠ rid.toObjId :=
      fun hx => hNeAR (SeLe4n.ReplyId.toObjId_injective _ _ hx)
    have hBR : below.toObjId ≠ rid.toObjId :=
      fun hx => hNeBR (SeLe4n.ReplyId.toObjId_injective _ _ hx)
    have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
    have hInv2 : s2.objects.invExt := storeObject_preserves_objects_invExt s1 s2 _ _ hInv1 hS2
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [SystemState.getReply?_eq_some_iff,
        storeObject_objects_ne s2 st' rid.toObjId above.toObjId _ hAR hInv2 hS3,
        storeObject_objects_ne s1 s2 below.toObjId above.toObjId _ hAB hInv1 hS2]
      exact storeObject_objects_eq' st _ _ _ hObjInv hS1
    · rw [SystemState.getReply?_eq_some_iff,
        storeObject_objects_ne s2 st' rid.toObjId below.toObjId _ hBR hInv2 hS3]
      exact storeObject_objects_eq' s1 _ _ _ hInv1 hS2
    · rw [SystemState.getReply?_eq_some_iff]
      exact storeObject_objects_eq' s2 _ _ _ hInv2 hS3
    · intro k hkA hkB hkR
      rw [storeObject_objects_ne s2 st' rid.toObjId k _ hkR hInv2 hS3,
        storeObject_objects_ne s1 s2 below.toObjId k _ hkB hInv1 hS2,
        storeObject_objects_ne st s1 above.toObjId k _ hkA hObjInv hS1]

/-- **WS-HP HP6.4: the composed step's frame, at every key.**  Either the key is
untouched, or it held a Reply that survives with at most its stack links
rewritten.  Proved once, by the two-way split; everything else in this section
reads it. -/
theorem spliceReplyFrameStores_objects_rewrite {st st' : SystemState}
    {rid above : SeLe4n.ReplyId} {r a : Reply} (hObjInv : st.objects.invExt)
    (hR : st.getReply? rid = some r) (hN : r.next = some (.frame above))
    (hA : st.getReply? above = some a) (hP : a.prev = some rid)
    (h : spliceReplyFrameStores st rid above r a = .ok st') (k : SeLe4n.ObjId) :
    st'.objects[k]? = st.objects[k]? ∨
      ∃ o o', st.objects[k]? = some (.reply o) ∧ st'.objects[k]? = some (.reply o') ∧
        replyStackRewrite o' o := by
  rcases spliceReplyFrameStores_cases h with ⟨_, hS⟩ | ⟨below, b, _, _, hBelow, _, _, _⟩
  · by_cases hk : k = above.toObjId
    · subst hk
      exact Or.inr ⟨a, { a with prev := none },
        (SystemState.getReply?_eq_some_iff _ _ _).mp hA,
        storeObject_objects_eq' st _ _ _ hObjInv hS, ⟨none, a.next, rfl⟩⟩
    · exact Or.inl (storeObject_objects_ne st st' above.toObjId k _ hk hObjInv hS)
  · obtain ⟨hAbove, hBelowVal, hCut, hFrame⟩ :=
      spliceReplyFrameStores_splice_values hObjInv hR hN hA hP hBelow h
    obtain ⟨_, _, hB, _⟩ := spliceFrameBelow?_eq_some hBelow
    by_cases hkA : k = above.toObjId
    · subst hkA
      exact Or.inr ⟨a, { a with prev := some below },
        (SystemState.getReply?_eq_some_iff _ _ _).mp hA,
        (SystemState.getReply?_eq_some_iff _ _ _).mp hAbove, ⟨some below, a.next, rfl⟩⟩
    · by_cases hkB : k = below.toObjId
      · subst hkB
        exact Or.inr ⟨b, { b with next := some (.frame above) },
          (SystemState.getReply?_eq_some_iff _ _ _).mp hB,
          (SystemState.getReply?_eq_some_iff _ _ _).mp hBelowVal,
          ⟨b.prev, some (.frame above), rfl⟩⟩
      · by_cases hkR : k = rid.toObjId
        · subst hkR
          exact Or.inr ⟨r, { r with prev := none },
            (SystemState.getReply?_eq_some_iff _ _ _).mp hR,
            (SystemState.getReply?_eq_some_iff _ _ _).mp hCut, ⟨none, r.next, rfl⟩⟩
        · exact Or.inl (hFrame k hkA hkB hkR)

/-- The composed step preserves the object table's extension invariant — one
store or three. -/
theorem spliceReplyFrameStores_preserves_objects_invExt {st st' : SystemState}
    {rid above : SeLe4n.ReplyId} {r a : Reply} (hObjInv : st.objects.invExt)
    (h : spliceReplyFrameStores st rid above r a = .ok st') : st'.objects.invExt := by
  rcases spliceReplyFrameStores_cases h with ⟨_, hS⟩ | ⟨_, _, s1, s2, _, hS1, hS2, hS3⟩
  · exact storeObject_preserves_objects_invExt st st' _ _ hObjInv hS
  · exact storeObject_preserves_objects_invExt s2 st' _ _
      (storeObject_preserves_objects_invExt s1 s2 _ _
        (storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1) hS2) hS3

theorem spliceReplyFrameStores_scheduler_eq {st st' : SystemState}
    {rid above : SeLe4n.ReplyId} {r a : Reply}
    (h : spliceReplyFrameStores st rid above r a = .ok st') :
    st'.scheduler = st.scheduler := by
  rcases spliceReplyFrameStores_cases h with ⟨_, hS⟩ | ⟨_, _, s1, s2, _, hS1, hS2, hS3⟩
  · exact storeObject_scheduler_eq st st' _ _ hS
  · exact ((storeObject_scheduler_eq s2 st' _ _ hS3).trans
      (storeObject_scheduler_eq s1 s2 _ _ hS2)).trans (storeObject_scheduler_eq st s1 _ _ hS1)

theorem spliceReplyFrameStores_machine_eq {st st' : SystemState}
    {rid above : SeLe4n.ReplyId} {r a : Reply}
    (h : spliceReplyFrameStores st rid above r a = .ok st') :
    st'.machine = st.machine := by
  rcases spliceReplyFrameStores_cases h with ⟨_, hS⟩ | ⟨_, _, s1, s2, _, hS1, hS2, hS3⟩
  · unfold storeObject at hS; cases hS; rfl
  · unfold storeObject at hS1 hS2 hS3; cases hS1; cases hS2; cases hS3; rfl

theorem spliceReplyFrameStores_serviceRegistry_eq {st st' : SystemState}
    {rid above : SeLe4n.ReplyId} {r a : Reply}
    (h : spliceReplyFrameStores st rid above r a = .ok st') :
    st'.serviceRegistry = st.serviceRegistry := by
  rcases spliceReplyFrameStores_cases h with ⟨_, hS⟩ | ⟨_, _, s1, s2, _, hS1, hS2, hS3⟩
  · unfold storeObject at hS; cases hS; rfl
  · unfold storeObject at hS1 hS2 hS3; cases hS1; cases hS2; cases hS3; rfl

theorem spliceReplyFrameStores_cdt_eq {st st' : SystemState}
    {rid above : SeLe4n.ReplyId} {r a : Reply}
    (h : spliceReplyFrameStores st rid above r a = .ok st') : st'.cdt = st.cdt := by
  rcases spliceReplyFrameStores_cases h with ⟨_, hS⟩ | ⟨_, _, s1, s2, _, hS1, hS2, hS3⟩
  · exact storeObject_cdt_eq st st' _ _ hS
  · exact ((storeObject_cdt_eq s2 st' _ _ hS3).trans
      (storeObject_cdt_eq s1 s2 _ _ hS2)).trans (storeObject_cdt_eq st s1 _ _ hS1)

theorem spliceReplyFrameStores_cdtNodeSlot_eq {st st' : SystemState}
    {rid above : SeLe4n.ReplyId} {r a : Reply}
    (h : spliceReplyFrameStores st rid above r a = .ok st') :
    st'.cdtNodeSlot = st.cdtNodeSlot := by
  rcases spliceReplyFrameStores_cases h with ⟨_, hS⟩ | ⟨_, _, s1, s2, _, hS1, hS2, hS3⟩
  · exact storeObject_cdtNodeSlot_eq st st' _ _ hS
  · exact ((storeObject_cdtNodeSlot_eq s2 st' _ _ hS3).trans
      (storeObject_cdtNodeSlot_eq s1 s2 _ _ hS2)).trans
      (storeObject_cdtNodeSlot_eq st s1 _ _ hS1)

/-- A key holding no Reply is untouched. -/
theorem spliceReplyFrameStores_non_reply_eq {st st' : SystemState}
    {rid above : SeLe4n.ReplyId} {r a : Reply} (hObjInv : st.objects.invExt)
    (hR : st.getReply? rid = some r) (hN : r.next = some (.frame above))
    (hA : st.getReply? above = some a) (hP : a.prev = some rid)
    (h : spliceReplyFrameStores st rid above r a = .ok st')
    (k : SeLe4n.ObjId) (hNotReply : ∀ o : Reply, st.objects[k]? ≠ some (.reply o)) :
    st'.objects[k]? = st.objects[k]? := by
  rcases spliceReplyFrameStores_objects_rewrite hObjInv hR hN hA hP h k with
    hEq | ⟨o, _, hPre, _, _⟩
  · exact hEq
  · exact absurd hPre (hNotReply o)

/-- Every Reply survives the composed step with at most its stack links moved. -/
theorem spliceReplyFrameStores_reply_rewrite {st st' : SystemState}
    {rid above : SeLe4n.ReplyId} {r a : Reply} (hObjInv : st.objects.invExt)
    (hR : st.getReply? rid = some r) (hN : r.next = some (.frame above))
    (hA : st.getReply? above = some a) (hP : a.prev = some rid)
    (h : spliceReplyFrameStores st rid above r a = .ok st')
    (oid : SeLe4n.ObjId) (o : Reply) (hReply : st.objects[oid]? = some (.reply o)) :
    ∃ o', st'.objects[oid]? = some (.reply o') ∧ replyStackRewrite o' o := by
  rcases spliceReplyFrameStores_objects_rewrite hObjInv hR hN hA hP h oid with
    hEq | ⟨o0, o', hPre, hPost, hRw⟩
  · exact ⟨o, by rw [hEq]; exact hReply, replyStackRewrite.refl o⟩
  · have hEq2 : o = o0 := KernelObject.reply.inj (Option.some.inj (hReply.symm.trans hPre))
    subst hEq2
    exact ⟨o', hPost, hRw⟩

/-- A key that is none of the three the removal can write is untouched.  The
`below` exclusion is stated over the cut frame's own `prev`, which
over-approximates `spliceFrameBelow?` — so a caller need not know whether the link
validated. -/
theorem spliceReplyFrameStores_objects_ne {st st' : SystemState}
    {rid above : SeLe4n.ReplyId} {r a : Reply} (hObjInv : st.objects.invExt)
    (h : spliceReplyFrameStores st rid above r a = .ok st')
    (k : SeLe4n.ObjId) (hkAbove : k ≠ above.toObjId)
    (hkBelow : ∀ below : SeLe4n.ReplyId, r.prev = some below → k ≠ below.toObjId)
    (hkCut : k ≠ rid.toObjId) :
    st'.objects[k]? = st.objects[k]? := by
  rcases spliceReplyFrameStores_cases h with ⟨_, hS⟩ | ⟨below, b, s1, s2, hBelow, hS1, hS2, hS3⟩
  · exact storeObject_objects_ne st st' above.toObjId k _ hkAbove hObjInv hS
  · obtain ⟨hPrev, _, _, _⟩ := spliceFrameBelow?_eq_some hBelow
    have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
    have hInv2 : s2.objects.invExt := storeObject_preserves_objects_invExt s1 s2 _ _ hInv1 hS2
    rw [storeObject_objects_ne s2 st' rid.toObjId k _ hkCut hInv2 hS3,
      storeObject_objects_ne s1 s2 below.toObjId k _ (hkBelow below hPrev) hInv1 hS2,
      storeObject_objects_ne st s1 above.toObjId k _ hkAbove hObjInv hS1]

/-- **The frame above holds `a` with its `prev` pointing at whatever the removal
resolved below the cut** — `none` where nothing validated, `some below` where the
splice ran.  One statement over both branches, which is what makes the splice's
post-state readable without a case split. -/
theorem spliceReplyFrameStores_getReply?_above {st st' : SystemState}
    {rid above : SeLe4n.ReplyId} {r a : Reply} (hObjInv : st.objects.invExt)
    (hR : st.getReply? rid = some r) (hN : r.next = some (.frame above))
    (hA : st.getReply? above = some a) (hP : a.prev = some rid)
    (h : spliceReplyFrameStores st rid above r a = .ok st') :
    st'.getReply? above
      = some { a with prev := (spliceFrameBelow? st rid r above).map Prod.fst } := by
  rcases spliceReplyFrameStores_cases h with ⟨hBelow, hS⟩ | ⟨below, b, _, _, hBelow, _, _, _⟩
  · rw [SystemState.getReply?_eq_some_iff, hBelow]
    exact storeObject_objects_eq' st _ _ _ hObjInv hS
  · rw [hBelow]
    simp only [Option.map_some]
    exact (spliceReplyFrameStores_splice_values hObjInv hR hN hA hP hBelow h).1

/-- **And the frame below holds `b` linking up to the frame above** — the other
half of the reciprocal pair, written in the same step. -/
theorem spliceReplyFrameStores_getReply?_below {st st' : SystemState}
    {rid above below : SeLe4n.ReplyId} {r a b : Reply} (hObjInv : st.objects.invExt)
    (hR : st.getReply? rid = some r) (hN : r.next = some (.frame above))
    (hA : st.getReply? above = some a) (hP : a.prev = some rid)
    (hBelow : spliceFrameBelow? st rid r above = some (below, b))
    (h : spliceReplyFrameStores st rid above r a = .ok st') :
    st'.getReply? below = some { b with next := some (.frame above) } :=
  (spliceReplyFrameStores_splice_values hObjInv hR hN hA hP hBelow h).2.1

/-- **And the cut frame keeps its `next` and loses its `prev`** — seL4's
`reply_unlink` for the downward half, which is what leaves nothing on the stack
pointing at a frame nothing points down to.  On the degenerate branch the cut
frame is not written at all, because there the frame above's `prev` is cleared and
the cut frame's own `prev` is already answered (or absent). -/
theorem spliceReplyFrameStores_getReply?_cut {st st' : SystemState}
    {rid above below : SeLe4n.ReplyId} {r a b : Reply} (hObjInv : st.objects.invExt)
    (hR : st.getReply? rid = some r) (hN : r.next = some (.frame above))
    (hA : st.getReply? above = some a) (hP : a.prev = some rid)
    (hBelow : spliceFrameBelow? st rid r above = some (below, b))
    (h : spliceReplyFrameStores st rid above r a = .ok st') :
    st'.getReply? rid = some { r with prev := none } :=
  (spliceReplyFrameStores_splice_values hObjInv hR hN hA hP hBelow h).2.2.1

/-- **WS-HP HP6.4: the composed step moves no Reply's `caller`, and moves a
`next` only from one `.frame` link to another.**  Sharper than
`replyStackRewrite`, which permits `next` to become a `.head` and so cannot
answer "does this frame still head a stack?" — and that question is what a
removal path asks when it reads `hNotHead` on the pre-state.

Three arms, one per store: the frame **above** and the **cut** frame keep their
`next` outright, and the frame **below** moves from `.frame rid` to `.frame above`,
which is a `.frame` either way.  So a frame heading a context still heads that
context and a frame heading none still heads none, which is all any consumer
reads. -/
theorem spliceReplyFrameStores_reply_caller_and_headLink {st st' : SystemState}
    {rid above : SeLe4n.ReplyId} {r a : Reply} (hObjInv : st.objects.invExt)
    (hR : st.getReply? rid = some r) (hN : r.next = some (.frame above))
    (hA : st.getReply? above = some a) (hP : a.prev = some rid)
    (h : spliceReplyFrameStores st rid above r a = .ok st')
    (q : SeLe4n.ReplyId) (rq : Reply) (hq : st'.getReply? q = some rq) :
    ∃ rp, st.getReply? q = some rp ∧ rq.caller = rp.caller ∧
      (rq.next = rp.next ∨
        ∃ x y : SeLe4n.ReplyId, rp.next = some (.frame x) ∧ rq.next = some (.frame y)) := by
  by_cases hkA : q = above
  · subst hkA
    rw [spliceReplyFrameStores_getReply?_above hObjInv hR hN hA hP h] at hq
    exact ⟨a, hA, by rw [← Option.some.inj hq], Or.inl (by rw [← Option.some.inj hq])⟩
  · rcases spliceReplyFrameStores_cases h with ⟨hBelow, hS⟩ | ⟨below, b, _, _, hBelow, _, _, _⟩
    · refine ⟨rq, ?_, rfl, Or.inl rfl⟩
      rw [SystemState.getReply?_eq_some_iff] at hq ⊢
      rw [← storeObject_objects_ne st st' above.toObjId q.toObjId _
        (fun hEq => hkA (SeLe4n.ReplyId.toObjId_injective _ _ hEq)) hObjInv hS]
      exact hq
    · obtain ⟨hPrev, hNe, hB, hBN⟩ := spliceFrameBelow?_eq_some hBelow
      obtain ⟨_, hBelowVal, hCut, hFrame⟩ :=
        spliceReplyFrameStores_splice_values hObjInv hR hN hA hP hBelow h
      by_cases hkB : q = below
      · subst hkB
        rw [hBelowVal] at hq
        refine ⟨b, hB, by rw [← Option.some.inj hq], Or.inr ⟨rid, above, hBN, ?_⟩⟩
        rw [← Option.some.inj hq]
      · by_cases hkR : q = rid
        · subst hkR
          rw [hCut] at hq
          exact ⟨r, hR, by rw [← Option.some.inj hq], Or.inl (by rw [← Option.some.inj hq])⟩
        · refine ⟨rq, ?_, rfl, Or.inl rfl⟩
          rw [SystemState.getReply?_eq_some_iff] at hq ⊢
          rw [← hFrame q.toObjId
            (fun hEq => hkA (SeLe4n.ReplyId.toObjId_injective _ _ hEq))
            (fun hEq => hkB (SeLe4n.ReplyId.toObjId_injective _ _ hEq))
            (fun hEq => hkR (SeLe4n.ReplyId.toObjId_injective _ _ hEq))]
          exact hq

/-- **Take a frame that is not a head off its stack, in `O(1)`** — seL4's
`reply_remove`, non-head branch.

**What it writes.**  The frame *above* the cut stops linking down to the cut frame
and links down to the frame *below* it instead (`above.prev := some below`), and
that frame links up to the frame above (`below.next := some (.frame above)`).  The
two reciprocal links are written **together** in one composed step
(`spliceReplyFrameStores`), so the pair the removal repairs is never transiently
inconsistent.  The cut frame's own links are cleared when its caller link is
consumed (`Reply.consumed`); the removal paths run this first and the consume
second, which is what leaves nothing pointing down at the frame being consumed.

**Where there is nothing to splice to it severs**, and that is stated rather than
carried in the name: a cut frame with no `prev`, or one whose `prev` does not
resolve, does not reciprocate, or names the frame above, leaves the frame above
with `prev := none` exactly as the pre-WS-HP kernel did
(`spliceReplyFrameOut_eq_sever_of_no_frame_below`).  Every state this kernel
reaches takes the splice branch or has nothing below the cut, because
`donationChainWellFormed.prevLinkReciprocal` answers every `prev` link and the
`below = above` arm entails a two-frame cycle.

**This is an improvement on seL4-MCS, not an adoption of it** (`v0.35.40`,
re-verified against upstream source at master, 13.0.0, 12.1.0, 12.0.0 and
11.0.0).  `reply_remove`'s non-head branch writes
`REPLY_PTR(next_ptr)->replyPrev = call_stack_new(0, false)` under the comment
*"not the head, remove from middle - break the chain"* — the **sever** — so
upstream strands the reservation of a caller removed from the middle of a chain
at depth ≥ 3 too.  `v0.35.14` asserted the reverse here and cited a line that is
in no release; see the WS-RM section of `CLAUDE.md` for what that retraction cost.
What the splice buys is therefore a property neither kernel had: a callee that
delegates its caller's reply capability to a confederate can no longer capture
that caller's CBS reservation by answering out of order
(`tests/SmpIpcSuite.lean` §3.22 is the depth-three witness; §3.20's depth-two
shapes were unchanged by the policy flip, because a two-frame stack's lower frame
is its bottom and both policies write the same value there — that residue is closed
instead by the reservation's recorded origin, `donationAccountingPreserved_atCallDepthTwo`).

Three answers, and each is a decision.  `.ok st` when the frame is a head (a head
is popped, never removed this way — that is the reclaim's job — so this is not the
operation to apply, and applying it must not silently drop a stack), when it has
no frame above (a stack top or an unlinked frame: nothing to repair), or when the
frame does not resolve at all (nothing to remove it from).  `.error` when the frame
above does not resolve or does not point back (`.invalidArgument`): a frame above
that does not name this frame as its `prev` would be rewritten on the strength of a
stale upward link, which is exactly the trust `Reply.consumed` withholds from such
links.  **Resolution and validation of the frame above are unchanged from the
sever**, so this operation's refusal set is exactly the sever's and every refusal
theorem carries verbatim. -/
def spliceReplyFrameOut (st : SystemState) (rid : SeLe4n.ReplyId) :
    Except KernelError SystemState :=
  match st.getReply? rid with
  | none => .ok st
  | some r =>
    match r.next with
    | some (.frame above) =>
      match st.getReply? above with
      | none => .error .objectNotFound
      | some a =>
        if a.prev != some rid then .error .invalidArgument
        else spliceReplyFrameStores st rid above r a
    | _ => .ok st

/-- The removal, decomposed: the identity, or the composed store step at the frame
above.  **Stated at the sever's arity** (WS-HP HP6.4), which is why the 47 sites
that destructure it are one-symbol swaps: only the last component's type changed,
from a `storeObject` to a `spliceReplyFrameStores`, and
`spliceReplyFrameStores_cases` splits that once. -/
theorem spliceReplyFrameOut_cases {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (h : spliceReplyFrameOut st rid = .ok st') :
    st' = st ∨ ∃ (r : Reply) (above : SeLe4n.ReplyId) (a : Reply),
      st.getReply? rid = some r ∧ r.next = some (.frame above) ∧
      st.getReply? above = some a ∧ a.prev = some rid ∧
      spliceReplyFrameStores st rid above r a = .ok st' := by
  unfold spliceReplyFrameOut at h
  revert h
  cases hR : st.getReply? rid with
  | none => intro h; exact Or.inl (Except.ok.inj h).symm
  | some r =>
    simp only []
    cases hN : r.next with
    | none => intro h; exact Or.inl (Except.ok.inj h).symm
    | some l =>
      cases l with
      | head _ => intro h; exact Or.inl (Except.ok.inj h).symm
      | frame above =>
        simp only []
        cases hA : st.getReply? above with
        | none => intro h; cases h
        | some a =>
          simp only []
          cases hP : (a.prev != some rid) with
          | true => simp only [if_true]; intro h; cases h
          | false =>
            simp only [Bool.false_eq_true, if_false]
            intro h
            exact Or.inr ⟨r, above, a, rfl, hN, hA, by simpa using hP, h⟩

/-- **WS-HP HP6.3: where there is nothing to splice to, the splice IS the sever.**
The definitional equality that makes every repair of an existing proof a case
split on `spliceFrameBelow?` whose `none` branch is the pre-WS-HP proof verbatim,
and the statement that the frames below a *bottom* cut frame are unaffected —
which is why §3.20's depth-two shapes are byte-identical across this cut. -/
theorem spliceReplyFrameOut_eq_sever_of_no_frame_below {st st' : SystemState}
    {rid above : SeLe4n.ReplyId} {r a : Reply}
    (hR : st.getReply? rid = some r) (hN : r.next = some (.frame above))
    (hA : st.getReply? above = some a) (hP : a.prev = some rid)
    (hBelow : spliceFrameBelow? st rid r above = none) :
    spliceReplyFrameOut st rid = .ok st' ↔
      storeObject above.toObjId (.reply { a with prev := none }) st = .ok ((), st') := by
  unfold spliceReplyFrameOut spliceReplyFrameStores
  rw [hR]
  simp only [hN, hA, hP, bne_self_eq_false, Bool.false_eq_true, if_false, hBelow]
  cases hS : storeObject above.toObjId (.reply { a with prev := none }) st with
  | error e => simp
  | ok pr =>
    obtain ⟨u, s'⟩ := pr; cases u
    simp

/-- The splice is the identity on a head frame. -/
theorem spliceReplyFrameOut_of_head (st : SystemState) (rid : SeLe4n.ReplyId) (r : Reply)
    (sc : SeLe4n.SchedContextId) (hR : st.getReply? rid = some r)
    (hHead : r.next = some (.head sc)) :
    spliceReplyFrameOut st rid = .ok st := by
  unfold spliceReplyFrameOut; rw [hR]; simp only [hHead]

/-- The splice is the identity on a frame with nothing above it. -/
theorem spliceReplyFrameOut_of_no_frame_above (st : SystemState) (rid : SeLe4n.ReplyId)
    (r : Reply) (hR : st.getReply? rid = some r) (hNext : r.next = none) :
    spliceReplyFrameOut st rid = .ok st := by
  unfold spliceReplyFrameOut; rw [hR]; simp only [hNext]

/-- WS-OD (`v0.35.4`): **the frame above `rid`**, if `rid` resolves and its
`next` names one -- the object `spliceReplyFrameOut` writes.  Resolved from
the same two fields the splice reads, so the member a cancellation declares for
the splice (`cancelSplicedFrameAbove?`) and the object the splice stores cannot
disagree: `replyFrameAbove?_of_splice_store` is the relation. -/
def replyFrameAbove? (st : SystemState) (rid : SeLe4n.ReplyId) : Option SeLe4n.ReplyId :=
  match st.getReply? rid with
  | none => none
  | some r =>
    match r.next with
    | some (.frame above) => some above
    | _ => none

/-- The removal either commits nothing or runs its composed store step at exactly
the frame `replyFrameAbove?` names — which, when there is a link below the cut to
splice to, also writes the frame `replyFrameBelow?` names
(`spliceReplyFrameStores_getReply?_below`). -/
theorem replyFrameAbove?_of_splice_store {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (h : spliceReplyFrameOut st rid = .ok st') :
    st' = st ∨ ∃ (above : SeLe4n.ReplyId) (r a : Reply),
      replyFrameAbove? st rid = some above ∧ st.getReply? rid = some r ∧
      st.getReply? above = some a ∧
      spliceReplyFrameStores st rid above r a = .ok st' := by
  rcases spliceReplyFrameOut_cases h with hEq | ⟨r, above, a, hR, hN, hA, _, hS⟩
  · exact Or.inl hEq
  · refine Or.inr ⟨above, r, a, ?_, hR, hA, hS⟩
    simp [replyFrameAbove?, hR, hN]

/-- **WS-RM (`v0.35.6`)**: the resolver, characterised — a `some` answer is a
resolving frame whose `next` names the frame it returns. -/
theorem replyFrameAbove?_eq_some {st : SystemState} {rid above : SeLe4n.ReplyId}
    (h : replyFrameAbove? st rid = some above) :
    ∃ r : Reply, st.getReply? rid = some r ∧ r.next = some (.frame above) := by
  unfold replyFrameAbove? at h
  revert h
  cases hR : st.getReply? rid with
  | none => intro h; cases h
  | some r =>
    simp only []
    cases hN : r.next with
    | none => intro h; cases h
    | some link =>
      cases link with
      | head _ => intro h; cases h
      | frame ab => intro h; exact ⟨r, rfl, by rw [hN, Option.some.inj h]⟩

@[simp] theorem replyFrameAbove?_of_none (st : SystemState) (rid : SeLe4n.ReplyId)
    (h : st.getReply? rid = none) : replyFrameAbove? st rid = none := by
  unfold replyFrameAbove?; rw [h]

/-- A head has no frame above it: its `next` is the context. -/
theorem replyFrameAbove?_of_head (st : SystemState) (rid : SeLe4n.ReplyId) (r : Reply)
    (sc : SeLe4n.SchedContextId) (hR : st.getReply? rid = some r)
    (hHead : r.next = some (.head sc)) : replyFrameAbove? st rid = none := by
  simp [replyFrameAbove?, hR, hHead]

/-- An unlinked frame has none either. -/
theorem replyFrameAbove?_of_unlinked (st : SystemState) (rid : SeLe4n.ReplyId) (r : Reply)
    (hR : st.getReply? rid = some r) (hNext : r.next = none) :
    replyFrameAbove? st rid = none := by
  simp [replyFrameAbove?, hR, hNext]

theorem spliceReplyFrameOut_of_absent (st : SystemState) (rid : SeLe4n.ReplyId)
    (hR : st.getReply? rid = none) :
    spliceReplyFrameOut st rid = .ok st := by
  unfold spliceReplyFrameOut; rw [hR]

/-- **WS-HP HP6.4: the removal's frame, at every key** — the primitive's instance
of `spliceReplyFrameStores_objects_rewrite`, and what makes every read lemma
below a one-line consequence rather than a second analysis of the two stores. -/
theorem spliceReplyFrameOut_objects_rewrite {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (hObjInv : st.objects.invExt) (h : spliceReplyFrameOut st rid = .ok st')
    (k : SeLe4n.ObjId) :
    st'.objects[k]? = st.objects[k]? ∨
      ∃ o o', st.objects[k]? = some (.reply o) ∧ st'.objects[k]? = some (.reply o') ∧
        replyStackRewrite o' o := by
  rcases spliceReplyFrameOut_cases h with rfl | ⟨r, above, a, hR, hN, hA, hP, hS⟩
  · exact Or.inl rfl
  · exact spliceReplyFrameStores_objects_rewrite hObjInv hR hN hA hP hS k

theorem spliceReplyFrameOut_preserves_objects_invExt {st st' : SystemState}
    {rid : SeLe4n.ReplyId} (hObjInv : st.objects.invExt)
    (h : spliceReplyFrameOut st rid = .ok st') : st'.objects.invExt := by
  rcases spliceReplyFrameOut_cases h with rfl | ⟨_, _, _, _, _, _, _, hS⟩
  · exact hObjInv
  · exact spliceReplyFrameStores_preserves_objects_invExt hObjInv hS

theorem spliceReplyFrameOut_scheduler_eq {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (h : spliceReplyFrameOut st rid = .ok st') : st'.scheduler = st.scheduler := by
  rcases spliceReplyFrameOut_cases h with rfl | ⟨_, _, _, _, _, _, _, hS⟩
  · rfl
  · exact spliceReplyFrameStores_scheduler_eq hS

theorem spliceReplyFrameOut_machine_eq {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (h : spliceReplyFrameOut st rid = .ok st') : st'.machine = st.machine := by
  rcases spliceReplyFrameOut_cases h with rfl | ⟨_, _, _, _, _, _, _, hS⟩
  · rfl
  · exact spliceReplyFrameStores_machine_eq hS

theorem spliceReplyFrameOut_serviceRegistry_eq {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (h : spliceReplyFrameOut st rid = .ok st') : st'.serviceRegistry = st.serviceRegistry := by
  rcases spliceReplyFrameOut_cases h with rfl | ⟨_, _, _, _, _, _, _, hS⟩
  · rfl
  · exact spliceReplyFrameStores_serviceRegistry_eq hS

/-- The splice writes only Reply objects, so a notification in the post-state was
one in the pre-state. -/
theorem spliceReplyFrameOut_notification_backward {st st' : SystemState}
    {rid : SeLe4n.ReplyId} (hObjInv : st.objects.invExt)
    (h : spliceReplyFrameOut st rid = .ok st')
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : st'.objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
  rcases spliceReplyFrameOut_objects_rewrite hObjInv h oid with hEq | ⟨_, _, _, hPost, _⟩
  · rw [← hEq]; exact hNtfn
  · rw [hNtfn] at hPost; cases hPost

/-- The splice is invisible to every typed TCB read. -/
theorem spliceReplyFrameOut_getTcb?_eq {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (hObjInv : st.objects.invExt)
    (h : spliceReplyFrameOut st rid = .ok st') (tid : SeLe4n.ThreadId) :
    st'.getTcb? tid = st.getTcb? tid := by
  unfold SystemState.getTcb?
  rcases spliceReplyFrameOut_objects_rewrite hObjInv h tid.toObjId with hEq | ⟨_, _, hPre, hPost, _⟩
  · rw [hEq]
  · rw [hPre, hPost]

/-- The removal writes at most the frame above the cut, the frame below it, and
the cut frame itself; every other key is untouched.  The `below` exclusion is
stated over the cut frame's own `prev`, which over-approximates
`spliceFrameBelow?` — so a caller need not know whether the link validated — and
the cut-frame exclusion is unconditional, which the one consumer has for free
(the removal's frame theorem already excludes the consumed Reply).  WS-HP HP6.4. -/
theorem spliceReplyFrameOut_objects_ne {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (hObjInv : st.objects.invExt)
    (h : spliceReplyFrameOut st rid = .ok st') (k : SeLe4n.ObjId)
    (hk : ∀ (r : Reply) (above : SeLe4n.ReplyId), st.getReply? rid = some r →
      r.next = some (.frame above) → k ≠ above.toObjId)
    (hkBelow : ∀ (r : Reply) (above below : SeLe4n.ReplyId), st.getReply? rid = some r →
      r.next = some (.frame above) → r.prev = some below → k ≠ below.toObjId)
    (hkCut : k ≠ rid.toObjId) :
    st'.objects[k]? = st.objects[k]? := by
  rcases spliceReplyFrameOut_cases h with rfl | ⟨r, above, a, hR, hN, _, _, hS⟩
  · rfl
  · exact spliceReplyFrameStores_objects_ne hObjInv hS k (hk r above hR hN)
      (fun below hPrev => hkBelow r above below hR hN hPrev) hkCut

theorem spliceReplyFrameOut_tcb_eq {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (hObjInv : st.objects.invExt)
    (h : spliceReplyFrameOut st rid = .ok st')
    (k : SeLe4n.ObjId) (t0 : TCB) (hk : st.objects[k]? = some (.tcb t0)) :
    st'.objects[k]? = some (.tcb t0) := by
  rcases spliceReplyFrameOut_objects_rewrite hObjInv h k with hEq | ⟨_, _, hPre, _, _⟩
  · rw [hEq]; exact hk
  · rw [hk] at hPre; cases hPre

theorem spliceReplyFrameOut_tcb_backward {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (hObjInv : st.objects.invExt)
    (h : spliceReplyFrameOut st rid = .ok st')
    (k : SeLe4n.ObjId) (t0 : TCB) (hk : st'.objects[k]? = some (.tcb t0)) :
    st.objects[k]? = some (.tcb t0) := by
  rcases spliceReplyFrameOut_objects_rewrite hObjInv h k with hEq | ⟨_, _, _, hPost, _⟩
  · rw [← hEq]; exact hk
  · rw [hk] at hPost; cases hPost

theorem spliceReplyFrameOut_non_reply_eq {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (hObjInv : st.objects.invExt)
    (h : spliceReplyFrameOut st rid = .ok st')
    (k : SeLe4n.ObjId) (hNotReply : ∀ r : Reply, st.objects[k]? ≠ some (.reply r)) :
    st'.objects[k]? = st.objects[k]? := by
  rcases spliceReplyFrameOut_objects_rewrite hObjInv h k with hEq | ⟨o, _, hPre, _, _⟩
  · exact hEq
  · exact absurd hPre (hNotReply o)

theorem spliceReplyFrameOut_reply_rewrite {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (hObjInv : st.objects.invExt)
    (h : spliceReplyFrameOut st rid = .ok st')
    (oid : SeLe4n.ObjId) (r : Reply) (hReply : st.objects[oid]? = some (.reply r)) :
    ∃ r', st'.objects[oid]? = some (.reply r') ∧ replyStackRewrite r' r := by
  rcases spliceReplyFrameOut_objects_rewrite hObjInv h oid with hEq | ⟨o0, o', hPre, hPost, hRw⟩
  · exact ⟨r, by rw [hEq]; exact hReply, replyStackRewrite.refl r⟩
  · have hEq2 : r = o0 := KernelObject.reply.inj (Option.some.inj (hReply.symm.trans hPre))
    subst hEq2
    exact ⟨o', hPost, hRw⟩

/-- **WS-HP HP3.1: the frame *below* `rid`** -- the second object a `reply_remove`
**splice** writes, and the member both reply footprints declare for it.

Declared ahead of the code that writes it, which is the numbering rule: HP6
replaces `spliceReplyFrameOutOrSelf` with the splice, and a footprint that
omits a written object is *false*.  The splice itself is HP6's, not HP1's, for
the reason `ReplyStackWriteCensus` gives: a reply-stack write site owes a chain
result, and the splice's is `prevLinkReciprocal` broken at the cut frame until
the consume that follows clears its links -- a statement only the composite HP6
builds can make.

Derived from `replyFrameAbove?` composed with the cut frame's own `prev`, so the
"is this a removal from the middle at all" question is answered **once** for the
footprint and the transition: a frame with nothing above it is not spliced, so
its `prev` is not written and must not be declared.  The two refusals the splice
will add (`above = below`, and a frame below that does not link back) leave this
`some` while it writes nothing, which over-approximates in the sound direction --
a declared-but-unwritten lock costs contention, never soundness, where a written
object no lock names is a false footprint. -/
def replyFrameBelow? (st : SystemState) (rid : SeLe4n.ReplyId) : Option SeLe4n.ReplyId :=
  match replyFrameAbove? st rid with
  | none => none
  | some _ => (st.getReply? rid).bind (·.prev)

/-- A frame with nothing above it has no declared frame below. -/
@[simp] theorem replyFrameBelow?_of_no_frame_above (st : SystemState) (rid : SeLe4n.ReplyId)
    (h : replyFrameAbove? st rid = none) : replyFrameBelow? st rid = none := by
  unfold replyFrameBelow?; rw [h]

/-- `none` on a frame that does not resolve. -/
@[simp] theorem replyFrameBelow?_of_none (st : SystemState) (rid : SeLe4n.ReplyId)
    (h : st.getReply? rid = none) : replyFrameBelow? st rid = none := by
  unfold replyFrameBelow?; rw [replyFrameAbove?_of_none st rid h]

/-- A head has no declared frame below: it is popped, not spliced. -/
theorem replyFrameBelow?_of_head (st : SystemState) (rid : SeLe4n.ReplyId) (r : Reply)
    (sc : SeLe4n.SchedContextId) (hR : st.getReply? rid = some r)
    (hHead : r.next = some (.head sc)) : replyFrameBelow? st rid = none := by
  unfold replyFrameBelow?; rw [replyFrameAbove?_of_head st rid r sc hR hHead]

/-- **WS-HP HP1.4: the resolver is characterised** -- a `some` answer is a
resolving frame that has a frame above it and whose own `prev` names the answer.
The direction the splice's write-membership proof reads. -/
theorem replyFrameBelow?_eq_some {st : SystemState} {rid below : SeLe4n.ReplyId}
    (h : replyFrameBelow? st rid = some below) :
    ∃ (r : Reply) (above : SeLe4n.ReplyId), st.getReply? rid = some r ∧
      r.next = some (.frame above) ∧ r.prev = some below := by
  unfold replyFrameBelow? at h
  cases hAb : replyFrameAbove? st rid with
  | none => rw [hAb] at h; cases h
  | some above =>
    rw [hAb] at h
    obtain ⟨r, hR, hN⟩ := replyFrameAbove?_eq_some hAb
    refine ⟨r, above, hR, hN, ?_⟩
    rw [hR] at h
    simpa using h

/-- **WS-HP HP6.6: the object the splice writes below the cut is the one the
footprint declares.**

`replyFrameBelow?` is the *declared* member and `spliceFrameBelow?` is what the
operation resolves, and the two ask the same question with different strictness:
the declaration stops at "there is a frame above, and this is the cut frame's
`prev`", while the operation additionally refuses a `prev` naming the frame above
itself and one whose own `next` does not link back.  So the operation's answer is
**contained** in the declaration's, which is the direction a footprint has to
satisfy — a written object no declared lock names is a *false* footprint, where a
declared-but-unwritten lock costs contention alone.

Stated rather than left to be re-derived at each footprint: the containment is
what `lockSet_endpointReplyOnCore_covers_splicedFrameBelow` and its three siblings
rest on, and nothing said it. -/
theorem spliceFrameBelow?_mem_replyFrameBelow? {st : SystemState}
    {rid above below : SeLe4n.ReplyId} {r b : Reply}
    (hR : st.getReply? rid = some r) (hAbove : replyFrameAbove? st rid = some above)
    (h : spliceFrameBelow? st rid r above = some (below, b)) :
    replyFrameBelow? st rid = some below := by
  unfold replyFrameBelow?
  rw [hAbove, hR]
  exact (spliceFrameBelow?_eq_some h).1

/-- **...and the containment is strict.**  The declared member is the cut frame's
`prev` *whatever the operation decides*, so on either refusal — a `prev` naming
the frame above, or a frame below that does not link back — the footprint declares
a write lock the splice never uses.

This is the over-approximation `replyFrameBelow?`'s own docstring claims, stated.
It is the sound direction and it is not free: a footprint wider than its operation
carries contention that says nothing about the operation (SM8.D's CC-5), which is
why the excess is bounded to exactly one member and named here rather than left
implicit. -/
theorem replyFrameBelow?_eq_prev_of_frame_above {st : SystemState}
    {rid above : SeLe4n.ReplyId} {r : Reply}
    (hR : st.getReply? rid = some r) (hAbove : replyFrameAbove? st rid = some above) :
    replyFrameBelow? st rid = r.prev := by
  unfold replyFrameBelow?
  rw [hAbove, hR]
  rfl

/-- **WS-HP HP1.1: the scheduling context a frame HEADS, validated** -- the fact
WS-HP moves the donation pop's trigger onto, and seL4-MCS's own (`reply_pop` reads
`reply->replyNext`; it does not consult the server's binding).

`some scId` exactly when `rid` resolves, its `next` names `scId` as the context
whose stack it heads, and `scId` names `rid` back.  The context id is read **off
the frame's own link** rather than supplied, which is the whole difference from
`donationHeadOf?`: that operation is handed a `scId` and checks the frame against
it, so it can only answer "is this the head of *that* context"; this one answers
"which context, if any, does this frame head".

**`none` is the fail-closed answer for a trigger.**  Four arms decline: the frame
does not resolve, it carries no `next`, its `next` names a frame above rather
than a context, or the named context does not name it back.  The last is the
reciprocity `donationChainWellFormed.headLinkReciprocal` guarantees, so it never
fires on a well-formed state; declining rather than proceeding is right because
the alternative -- popping a context the frame does not demonstrably head --
would hand a scheduling context to a thread selected by a stale link, the
confused deputy the reciprocity tests exist to refuse.  Declining costs the
fairness the pop would have delivered, never safety.

Shared by the reply path (HP4) and the cancellation path (HP5), so "which context
does this frame head" has one answer rather than one per caller. -/
def replyFrameHeadContext? (st : SystemState) (rid : SeLe4n.ReplyId) :
    Option SeLe4n.SchedContextId :=
  match st.getReply? rid with
  | none => none
  | some r =>
    match r.next with
    | some (.head scId) =>
      match st.getSchedContext? scId with
      | none => none
      | some sc => if sc.scReply == some rid then some scId else none
    | _ => none

/-- **WS-HP HP1.2: what a `some` answer asserts** -- the frame heads the named
context and the context names the frame back.  Every fact the pop needs about the
context it is popping is a consequence of the trigger firing, not a hypothesis its
callers carry. -/
theorem replyFrameHeadContext?_eq_some {st : SystemState} {rid : SeLe4n.ReplyId}
    {scId : SeLe4n.SchedContextId} (h : replyFrameHeadContext? st rid = some scId) :
    ∃ (r : Reply) (sc : SchedContext), st.getReply? rid = some r ∧
      r.next = some (.head scId) ∧ st.getSchedContext? scId = some sc ∧
      sc.scReply = some rid := by
  unfold replyFrameHeadContext? at h
  revert h
  cases hR : st.getReply? rid with
  | none => intro h; cases h
  | some r =>
    simp only []
    cases hN : r.next with
    | none => intro h; cases h
    | some link =>
      cases link with
      | frame _ => intro h; cases h
      | head sc0 =>
        simp only []
        cases hSc : st.getSchedContext? sc0 with
        | none => intro h; cases h
        | some sc =>
          simp only []
          cases hRec : (sc.scReply == some rid) with
          | false => simp only [Bool.false_eq_true, if_false]; intro h; cases h
          | true =>
            simp only [if_true]
            intro h
            have hEq : sc0 = scId := Option.some.inj h
            subst hEq
            exact ⟨r, sc, rfl, hN, hSc, by simpa using hRec⟩

/-- ...and a thread whose frame heads a context is on one: the `.head` arm of the
test is `replyFrameHeadContext?`'s own question, so a reciprocating head answers
`true` here by that resolver's characterisation. -/
theorem replyFrameOnLiveStack_of_head (st : SystemState) (tcb : TCB)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId)
    (hRO : tcb.replyObject = some rid) (hHead : replyFrameHeadContext? st rid = some scId) :
    replyFrameOnLiveStack st tcb = true := by
  obtain ⟨r, sc, hR, hN, hSc, hRec⟩ := replyFrameHeadContext?_eq_some hHead
  simp only [replyFrameOnLiveStack, hRO, hR, hN, hSc, hRec, beq_self_eq_true]

@[simp] theorem replyFrameHeadContext?_of_none (st : SystemState) (rid : SeLe4n.ReplyId)
    (h : st.getReply? rid = none) : replyFrameHeadContext? st rid = none := by
  unfold replyFrameHeadContext?; rw [h]

/-- **WS-HP HP1.2: the resolver's constructor** -- a frame whose `next` names a
context that names it back heads that context.  The direction HP2.2's converse
reads, and the one a witness uses to exhibit a live stack. -/
theorem replyFrameHeadContext?_of_head (st : SystemState) (rid : SeLe4n.ReplyId) (r : Reply)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hR : st.getReply? rid = some r) (hN : r.next = some (.head scId))
    (hSc : st.getSchedContext? scId = some sc) (hScReply : sc.scReply = some rid) :
    replyFrameHeadContext? st rid = some scId := by
  unfold replyFrameHeadContext?
  rw [hR]
  simp only [hN, hSc, hScReply, beq_self_eq_true, if_true]

/-- **WS-HP HP1.2: a frame with a frame above it heads nothing** -- so the pop's
trigger and the splice's are mutually exclusive by construction, which is what
keeps the *reachable* footprint bound where the declared ceiling grows. -/
theorem replyFrameHeadContext?_of_frameAbove (st : SystemState) (rid above : SeLe4n.ReplyId)
    (h : replyFrameAbove? st rid = some above) : replyFrameHeadContext? st rid = none := by
  obtain ⟨r, hR, hN⟩ := replyFrameAbove?_eq_some h
  unfold replyFrameHeadContext?; rw [hR]; simp only [hN]

/-- And conversely: a frame that heads a context has no frame above it. -/
theorem replyFrameAbove?_of_headContext (st : SystemState) (rid : SeLe4n.ReplyId)
    (scId : SeLe4n.SchedContextId) (h : replyFrameHeadContext? st rid = some scId) :
    replyFrameAbove? st rid = none := by
  obtain ⟨r, _, hR, hN, _, _⟩ := replyFrameHeadContext?_eq_some h
  exact replyFrameAbove?_of_head st rid r scId hR hN

/-- **WS-HP HP1.2: the frame declared for a splice is absent on a head** -- the
same exclusion one level down, so a footprint that names both members declares at
most one of them on any state. -/
theorem replyFrameBelow?_of_headContext (st : SystemState) (rid : SeLe4n.ReplyId)
    (scId : SeLe4n.SchedContextId) (h : replyFrameHeadContext? st rid = some scId) :
    replyFrameBelow? st rid = none :=
  replyFrameBelow?_of_no_frame_above st rid (replyFrameAbove?_of_headContext st rid scId h)

/-- **WS-HP HP1.2: the trigger is a function of three store projections** -- the
frame's own record and the named context's.  The frame lemma every step that
writes no chain object crosses, stated as an agreement rather than as a list of
transitions, which is the shape `donationChainFrame` already has. -/
theorem replyFrameHeadContext?_congr {s1 s2 : SystemState} (rid : SeLe4n.ReplyId)
    (hReply : s2.getReply? rid = s1.getReply? rid)
    (hSc : ∀ scId : SeLe4n.SchedContextId,
      s2.getSchedContext? scId = s1.getSchedContext? scId) :
    replyFrameHeadContext? s2 rid = replyFrameHeadContext? s1 rid := by
  unfold replyFrameHeadContext?
  rw [hReply]
  cases s1.getReply? rid with
  | none => rfl
  | some r =>
    simp only []
    cases r.next with
    | none => rfl
    | some link =>
      cases link with
      | frame _ => rfl
      | head sc0 => simp only [hSc sc0]

-- ============================================================================
-- WS-HP HP4.1: the head-driven trigger, at the answered caller
-- ============================================================================
--
-- These two lived in `IPC/CrossCore/EndpointReply.lean` from HP1 until HP4.1,
-- which is where their HP1 consumers are -- the reply footprint and the
-- cross-core dispatch.  HP4 re-keys the *single-core* donation spine onto the
-- trigger, and `IPC/Operations/Donation/Primitives.lean` imports **this** module
-- alone, so the resolver had to come down to a module that spine can see.
--
-- A relocation, never a second spelling: the pair's second component means the
-- context's *holder* -- the thread the pop unbinds -- while the binding-driven
-- resolver it replaces carried the *owner*, the thread the pop binds.  Same type,
-- opposite roles (plan SS3.8.2), so two spellings free to drift would be the worst
-- possible shape for this question -- which is why WS-HP HP7 (`v0.35.46`) deleted
-- the binding-driven one (`endpointReplyServerDonation?`) rather than leaving it
-- beside this one once HP6.2 had repointed the last footprint off it.

/-- **WS-HP HP1.1: the Reply object a reply answers.**

The expression `answeredReplyFrameAbove?`, `answeredReplyFrameBelow?` and
`answeredFrameHeadContext?` are all resolved from, named once so the footprint
members, the removal and the pop's trigger cannot disagree about *which* frame a
reply answers.  It is the answered caller's own forward link -- the one
`linkCallerReply` wrote and `consumeCallerReply` clears -- so every one of those
sites must read it from the **pre**-state. -/
def answeredReplyObject? (st : SystemState) (target : SeLe4n.ThreadId) :
    Option SeLe4n.ReplyId :=
  (st.getTcb? target).bind (·.replyObject)

/-- **WS-HP HP1.1: the scheduling context the answered frame HEADS, with that
context's current holder** -- the pair the donation pop takes its arguments from
since HP4 (`v0.35.38`).

`replyFrameHeadContext?` answers *which* context, off the frame's own `.head`
link and validated against that context's `scReply`; this pairs it with
`SchedContext.boundThread`, which is the thread the pop unbinds.  Both halves are
reads of the context the frame names, so the pop's `scId` and its `serverTid` can
no longer disagree -- where the binding-driven trigger took `scId` from the
recorded server's `.donated` binding and `serverTid` from the recorded server,
leaving `returnDonatedSchedContext`'s own `boundThread` guard to catch a drift
between them.  Under this trigger that guard is satisfied by construction, which
is the honest direction: the operation reads the fact it used to check.

**A context with no bound thread declines**, and that arm is unreachable today:
`donateSchedContext` and `returnDonatedSchedContext` both leave `boundThread` a
`some`, and `schedContextUnbind` refuses a `.donated` holder outright, so no
reachable state has a context heading a stack while bound to nobody.  It is
written as a refusal rather than assumed away because the refusal is what keeps
this total -- and because lifting that unbind refusal, which becomes sound
exactly once this trigger is live, is the one change that makes the arm
reachable.

**WS-HP HP4.1 -- the resolver is split at the reply object, and the split is
forced by the reply leg.**  `consumeCallerReply` clears the answered caller's
`replyObject` (`answeredReplyObject?`'s own docstring says so), and the donation
pop runs *after* the reply leg -- seL4-MCS's `doReplyTransfer` order, which this
kernel keeps because the server needs the returned budget while it replies.  So
the pop cannot ask `answeredFrameHeadContext?` of its own state: the answer is
always `none` there.  What it can ask is `replyFrameHeadHolder?` of the frame,
because the frame's `.head` link and the context's `scReply` and `boundThread`
all survive the leg untouched -- `Reply.consumed` keeps a head frame's links
deliberately, for exactly this reason.

The pop therefore takes the answered **reply id**, resolved on the pre-state
through the one expression the footprint members also come from, and resolves the
context and its holder itself at the state it runs on.  That is what keeps the
`boundThread` guard vacuous and the head validation a consequence rather than a
hypothesis: both are reads of the pop's own state.  The alternative -- passing
the resolved pair -- would make them pre-state reads again and put the guard
back to work, which is the shape HP4 exists to retire. -/
def replyFrameHeadHolder? (st : SystemState) (rid : SeLe4n.ReplyId) :
    Option (SeLe4n.SchedContextId × SeLe4n.ThreadId) :=
  match replyFrameHeadContext? st rid with
  | none => none
  | some scId =>
    match (st.getSchedContext? scId).bind (·.boundThread) with
    | none => none
    | some holder => some (scId, holder)

/-- A frame that heads no context has no holder to report. -/
@[simp] theorem replyFrameHeadHolder?_of_no_head (st : SystemState)
    (rid : SeLe4n.ReplyId) (h : replyFrameHeadContext? st rid = none) :
    replyFrameHeadHolder? st rid = none := by
  unfold replyFrameHeadHolder?; rw [h]

/-- **WS-HP HP4.1: the frame-keyed resolver's constructor.** -/
theorem replyFrameHeadHolder?_of_head (st : SystemState) (rid : SeLe4n.ReplyId)
    (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (hHead : replyFrameHeadContext? st rid = some scId)
    (hBt : (st.getSchedContext? scId).bind (·.boundThread) = some holder) :
    replyFrameHeadHolder? st rid = some (scId, holder) := by
  unfold replyFrameHeadHolder?; rw [hHead]; simp only [hBt]

/-- **WS-HP HP4.1: what a `some` answer asserts** -- the frame heads the named
context (with everything `replyFrameHeadContext?_eq_some` supplies about that),
and the context is bound to the named holder. -/
theorem replyFrameHeadHolder?_eq_some {st : SystemState} {rid : SeLe4n.ReplyId}
    {scId : SeLe4n.SchedContextId} {holder : SeLe4n.ThreadId}
    (h : replyFrameHeadHolder? st rid = some (scId, holder)) :
    replyFrameHeadContext? st rid = some scId ∧
      (st.getSchedContext? scId).bind (·.boundThread) = some holder := by
  unfold replyFrameHeadHolder? at h
  revert h
  cases hHead : replyFrameHeadContext? st rid with
  | none => intro h; cases h
  | some scId0 =>
    simp only []
    cases hBt : (st.getSchedContext? scId0).bind (·.boundThread) with
    | none => intro h; cases h
    | some holder0 =>
      simp only []
      intro h
      have hPair := Option.some.inj h
      have h1 : scId0 = scId := congrArg Prod.fst hPair
      have h2 : holder0 = holder := congrArg Prod.snd hPair
      subst h1; subst h2
      exact ⟨rfl, hBt⟩

/-- **WS-HP HP4.4: a scheduling context that heads a reply stack is bound to a
thread.**

The one coherence fact the head-driven pop still needs, and the replacement for
`answeredHeadContextIsServerDonation` in the chain composite -- strictly weaker
than it, because it asks only that the head context has *a* holder rather than
that a particular recorded server holds it.  That predicate was **deleted** at
WS-HP HP7 (`v0.35.46`); this is what the composite carries instead.  It is what rules out the arm
`replyFrameHeadHolder?` declines on: a frame that heads a context bound to nobody,
where the pop would be the identity while the reply leg has already relaxed the
chain at that frame.

`answeredFrameHeadContext?`'s docstring argues the arm is unreachable
(`donateSchedContext` and `returnDonatedSchedContext` both leave `boundThread` a
`some`, and `schedContextUnbind` refuses a `.donated` holder), and that argument
is about *reachability* rather than about an invariant -- `donationChainWellFormed`
carries no binding clause at all.  So it is stated rather than assumed.

**And it is still stated** (the post-landing audit, `v0.35.61`).  This docstring
used to end "WS-HP HP7 is where it becomes a clause of the chain invariant and
retires", and HP7 (`v0.35.46`) did neither: it deleted the three *binding-driven*
coherence facts and left the two the head-driven trigger does not witness -- this
one, and `replyFrameHeadHolderDonation` -- exactly as they were, with no plan row
ever scheduling the clause.  A forward-looking sentence reads like a scheduled
obligation, which is why this one is corrected rather than left for the next
reader to re-derive.  Deriving it means a `headBound` clause of
`donationChainWellFormed` with the frame family extended over `boundThread`;
that is registered (`docs/REGISTERED_DEBT.md`, WS-HP) rather than predicted a
second time.

Vacuous wherever the frame heads no context, which is every reply in a tree with
no donation. -/
def replyFrameHeadIsBound (st : SystemState) (rid : SeLe4n.ReplyId) : Prop :=
  ∀ scId, replyFrameHeadContext? st rid = some scId →
    ∃ holder, replyFrameHeadHolder? st rid = some (scId, holder)

/-- The vacuity discharge. -/
theorem replyFrameHeadIsBound_of_no_head (st : SystemState) (rid : SeLe4n.ReplyId)
    (h : replyFrameHeadContext? st rid = none) : replyFrameHeadIsBound st rid := by
  intro scId hHead; rw [h] at hHead; cases hHead

/-- Under it, a frame that heads a context resolves a holder. -/
theorem replyFrameHeadHolder?_ne_none_of_bound {st : SystemState} {rid : SeLe4n.ReplyId}
    {scId : SeLe4n.SchedContextId} (hBound : replyFrameHeadIsBound st rid)
    (hHead : replyFrameHeadContext? st rid = some scId) :
    replyFrameHeadHolder? st rid ≠ none := by
  obtain ⟨holder, hH⟩ := hBound scId hHead
  rw [hH]; intro hx; cases hx

/-- **WS-HP HP4.1: the frame-keyed resolver is a function of the store
projections it reads** -- every Reply and every SchedContext.  The frame lemma a
step that writes no chain object crosses, and the one the answered-caller form
below is derived from. -/
theorem replyFrameHeadHolder?_congr {s1 s2 : SystemState} (rid : SeLe4n.ReplyId)
    (hReply : s2.getReply? rid = s1.getReply? rid)
    (hSc : ∀ scId : SeLe4n.SchedContextId,
      s2.getSchedContext? scId = s1.getSchedContext? scId) :
    replyFrameHeadHolder? s2 rid = replyFrameHeadHolder? s1 rid := by
  unfold replyFrameHeadHolder?
  simp only [replyFrameHeadContext?_congr rid hReply hSc]
  cases replyFrameHeadContext? s1 rid with
  | none => rfl
  | some scId => simp only [hSc scId]

/-- **WS-HP HP1.1**: the answered caller's own frame, resolved through
`replyFrameHeadHolder?`.  This is the **pre**-state form -- the footprint's and
HP2's -- and it is the composition rather than a second spelling, so the two
entry points cannot disagree about what a frame heads. -/
def answeredFrameHeadContext? (st : SystemState) (target : SeLe4n.ThreadId) :
    Option (SeLe4n.SchedContextId × SeLe4n.ThreadId) :=
  match answeredReplyObject? st target with
  | none => none
  | some rid => replyFrameHeadHolder? st rid

/-- A thread holding no reply object answers no head. -/
@[simp] theorem answeredFrameHeadContext?_of_no_reply (st : SystemState)
    (target : SeLe4n.ThreadId) (h : answeredReplyObject? st target = none) :
    answeredFrameHeadContext? st target = none := by
  unfold answeredFrameHeadContext?; rw [h]

/-- The resolver, unfolded on a thread whose reply object resolves. -/
theorem answeredFrameHeadContext?_eq (st : SystemState) (target : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (h : answeredReplyObject? st target = some rid) :
    answeredFrameHeadContext? st target = replyFrameHeadHolder? st rid := by
  unfold answeredFrameHeadContext?; rw [h]

/-- **WS-HP HP1.2: the resolver's constructor** -- the direction HP2.2's converse
reads, and the one a witness uses to exhibit a live reply stack. -/
theorem answeredFrameHeadContext?_of_head (st : SystemState) (target : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (hRid : answeredReplyObject? st target = some rid)
    (hHead : replyFrameHeadContext? st rid = some scId)
    (hBt : (st.getSchedContext? scId).bind (·.boundThread) = some holder) :
    answeredFrameHeadContext? st target = some (scId, holder) := by
  rw [answeredFrameHeadContext?_eq st target rid hRid]
  exact replyFrameHeadHolder?_of_head st rid scId holder hHead hBt

/-- **WS-HP HP1.2: what a `some` answer asserts** -- there is an answered frame,
it heads the named context (with everything `replyFrameHeadContext?_eq_some`
supplies about that), and the context is bound to the named holder. -/
theorem answeredFrameHeadContext?_eq_some {st : SystemState} {target : SeLe4n.ThreadId}
    {scId : SeLe4n.SchedContextId} {holder : SeLe4n.ThreadId}
    (h : answeredFrameHeadContext? st target = some (scId, holder)) :
    ∃ rid : SeLe4n.ReplyId, answeredReplyObject? st target = some rid ∧
      replyFrameHeadContext? st rid = some scId ∧
      (st.getSchedContext? scId).bind (·.boundThread) = some holder := by
  unfold answeredFrameHeadContext? at h
  revert h
  cases hRid : answeredReplyObject? st target with
  | none => intro h; cases h
  | some rid =>
    simp only []
    intro h
    exact ⟨rid, rfl, (replyFrameHeadHolder?_eq_some h).1, (replyFrameHeadHolder?_eq_some h).2⟩

/-- WS-RM (`v0.35.6`): **the splice folded to the identity on a refusal** — the
one spelling of "take the frame above off this frame's stack, or leave the state
alone".  Both removal paths need it and neither may fail on it, so it is defined
once here rather than answered separately at each.

The fold is sound because a refusal *is* the statement that nothing references
this frame.  `spliceReplyFrameOut` refuses exactly when the frame `next` names
either does not resolve or does not point back; under
`donationChainWellFormed.prevLinkReciprocal` the only frame whose `prev` can name
`rid` is the one `rid`'s own `next` names, so in either refusal no stored Reply
links down to `rid` and clearing its links breaks no reciprocity
(`spliceReplyFrameOutOrSelf_unreferenced`).  Committing nothing there is also
the trust the structure withholds from a stale upward link: rewriting a frame
that does not point back would be acting on one. -/
def spliceReplyFrameOutOrSelf (st : SystemState) (rid : SeLe4n.ReplyId) : SystemState :=
  match spliceReplyFrameOut st rid with
  | .ok st' => st'
  | .error _ => st

/-- The fold, decomposed: the identity, or a `spliceReplyFrameOut` that ran.
Stable across HP6.3: it says nothing about what the primitive wrote. -/
theorem spliceReplyFrameOutOrSelf_cases (st : SystemState) (rid : SeLe4n.ReplyId) :
    spliceReplyFrameOutOrSelf st rid = st ∨
      spliceReplyFrameOut st rid = .ok (spliceReplyFrameOutOrSelf st rid) := by
  unfold spliceReplyFrameOutOrSelf
  split
  · rename_i st' h; exact Or.inr h
  · exact Or.inl rfl

/-- WS-RM (`v0.35.6`): **take a thread's reply frame off its stack** — seL4's
`reply_remove_tcb`, non-head arm, keyed on the thread's own forward link.

This is the TCB-keyed wrapper over `spliceReplyFrameOutOrSelf`; the removal
paths that hold a `ReplyId` directly (the reply leg, `removeCallerReplyFrame`)
call that fold, so there is exactly one answer to "what does this removal do when
it cannot repair the frame above".  What the wrapper inherits from the fold is
whatever the primitive does: the **splice** since WS-HP HP6.3 (`v0.35.45`), and
the sever for the four cuts before it, during which the name ran ahead of the
body by HP6.1's decision (recorded in `CLAUDE.md`).

**Order.**  On the cancellation path this runs after the donation reclaim, on
whose success the frame is already unlinked and this is the identity
(`spliceReplyFrameOut_of_no_frame_above`); on a head it is the identity too,
deliberately — a head is popped by the reclaim, never removed this way, and a
reclaim that *declined* on a head is an invariant violation this step must not
paper over by dropping a stack. -/
def spliceThreadReplyFrameOut (st : SystemState) (tcb : TCB) : SystemState :=
  match tcb.replyObject with
  | none => st
  | some rid => spliceReplyFrameOutOrSelf st rid

/-- **WS-RM (`v0.35.6`), restated for the splice at WS-HP HP6.4: the fold,
decomposed as at most three `.reply` stores** — each at a key that already holds a
Reply, so every "this predicate survives a Reply store" lemma in the tree
transports across the removal's first leg by **iterating**, with no new argument
about how many stores there are.

The two intermediate states are exposed because there are genuinely three writes:
the frame above the cut, the frame below it, then the cut frame's own unlink.  A
consumer that only asks whether a key holds a Reply on both sides should reach for
`spliceReplyFrameOutOrSelf_objects_rewrite`, which answers at every key in one
statement and needs no iteration.

The three steps are spelled out rather than named as a relation, deliberately: a
`Prop`-valued relation whose body mentions `storeObject` is reported by
`ReplyStackWriteCensus`'s store frontier, and registering a relation as a
reply-stack write site is not an option — it writes nothing. -/
theorem spliceReplyFrameOutOrSelf_store_cases (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) :
    ∃ m1 m2 : SystemState,
      (m1 = st ∨ ∃ (k : SeLe4n.ReplyId) (o o' : Reply),
          st.objects[k.toObjId]? = some (.reply o) ∧
          storeObject k.toObjId (.reply o') st = .ok ((), m1)) ∧
      (m2 = m1 ∨ ∃ (k : SeLe4n.ReplyId) (o o' : Reply),
          m1.objects[k.toObjId]? = some (.reply o) ∧
          storeObject k.toObjId (.reply o') m1 = .ok ((), m2)) ∧
      (spliceReplyFrameOutOrSelf st rid = m2 ∨ ∃ (k : SeLe4n.ReplyId) (o o' : Reply),
          m2.objects[k.toObjId]? = some (.reply o) ∧
          storeObject k.toObjId (.reply o') m2
            = .ok ((), spliceReplyFrameOutOrSelf st rid)) := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · exact ⟨st, st, Or.inl rfl, Or.inl rfl, Or.inl h⟩
  · rcases spliceReplyFrameOut_cases h with hEq | ⟨r, above, a, hR, hN, hA, hP, hS⟩
    · exact ⟨st, st, Or.inl rfl, Or.inl rfl, Or.inl hEq⟩
    · rcases spliceReplyFrameStores_cases hS with
        ⟨_, hS1⟩ | ⟨below, b, s1, s2, hBelow, hS1, hS2, hS3⟩
      · exact ⟨spliceReplyFrameOutOrSelf st rid, spliceReplyFrameOutOrSelf st rid,
          Or.inr ⟨above, a, { a with prev := none },
            (SystemState.getReply?_eq_some_iff _ _ _).mp hA, hS1⟩,
          Or.inl rfl, Or.inl rfl⟩
      · obtain ⟨_, hNe, hB, _⟩ := spliceFrameBelow?_eq_some hBelow
        have hNeBR : below ≠ rid := spliceFrameBelow?_ne_cut hR hN hBelow
        have hNeAR : above ≠ rid := spliceFrameBelow?_above_ne_cut hR hA hP hBelow
        have hInv1 : s1.objects.invExt :=
          storeObject_preserves_objects_invExt st s1 _ _ hInv hS1
        have hInv2 : s2.objects.invExt :=
          storeObject_preserves_objects_invExt s1 s2 _ _ hInv1 hS2
        have hB1 : s1.objects[below.toObjId]? = some (.reply b) := by
          rw [storeObject_objects_ne st s1 above.toObjId below.toObjId _
            (fun hEq => hNe (SeLe4n.ReplyId.toObjId_injective _ _ hEq)) hInv hS1]
          exact (SystemState.getReply?_eq_some_iff _ _ _).mp hB
        have hR2 : s2.objects[rid.toObjId]? = some (.reply r) := by
          rw [storeObject_objects_ne s1 s2 below.toObjId rid.toObjId _
              (fun hEq => hNeBR (SeLe4n.ReplyId.toObjId_injective _ _ hEq).symm) hInv1 hS2,
            storeObject_objects_ne st s1 above.toObjId rid.toObjId _
              (fun hEq => hNeAR (SeLe4n.ReplyId.toObjId_injective _ _ hEq).symm) hInv hS1]
          exact (SystemState.getReply?_eq_some_iff _ _ _).mp hR
        exact ⟨s1, s2,
          Or.inr ⟨above, a, { a with prev := some below },
            (SystemState.getReply?_eq_some_iff _ _ _).mp hA, hS1⟩,
          Or.inr ⟨below, b, { b with next := some (.frame above) }, hB1, hS2⟩,
          Or.inr ⟨rid, r, { r with prev := none }, hR2, hS3⟩⟩
/-- **The fold moves no Reply's `caller`, and no frame onto or off a stack
head** — sharper than `replyStackRewrite`, which permits `next` to become a
`.head` and so cannot answer "does this frame still head a stack?".

Restated for the splice (WS-HP HP6.4): the frame **above** the cut keeps its
`next` outright and the frame **below** it moves from one `.frame` link to
another, so a `.head` link is preserved exactly and a `.frame` link stays a
`.frame`.  That is what a removal path reads when it establishes `hNotHead` on the
pre-state; it was `rq.next = rp.next` while the sever wrote only a `prev`. -/
theorem spliceReplyFrameOutOrSelf_preserves_reply_caller_and_headLink
    (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) (q : SeLe4n.ReplyId) (rq : Reply)
    (hq : (spliceReplyFrameOutOrSelf st rid).getReply? q = some rq) :
    ∃ rp, st.getReply? q = some rp ∧ rq.caller = rp.caller ∧
      (rq.next = rp.next ∨
        ∃ x y : SeLe4n.ReplyId, rp.next = some (.frame x) ∧ rq.next = some (.frame y)) := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · exact ⟨rq, by rw [← h]; exact hq, rfl, Or.inl rfl⟩
  · rcases spliceReplyFrameOut_cases h with hEq | ⟨r, above, a, hR, hN, hA, hP, hS⟩
    · exact ⟨rq, by rw [← hEq]; exact hq, rfl, Or.inl rfl⟩
    · exact spliceReplyFrameStores_reply_caller_and_headLink hInv hR hN hA hP hS q rq hq

-- ----------------------------------------------------------------------------
-- WS-RM (`v0.35.6`): the TCB-keyed splice's read/write algebra
-- ----------------------------------------------------------------------------

/-- `v0.35.4`: the splice, decomposed — the identity (no reply link, no frame
above, or a refused repair), or one `spliceReplyFrameOut` that succeeded. -/
theorem spliceThreadReplyFrameOut_cases (st : SystemState) (tcb : TCB) :
    spliceThreadReplyFrameOut st tcb = st ∨
    ∃ rid, tcb.replyObject = some rid ∧
      spliceReplyFrameOut st rid = .ok (spliceThreadReplyFrameOut st tcb) := by
  unfold spliceThreadReplyFrameOut
  split
  · exact Or.inl rfl
  · rename_i rid hRid
    rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
    · exact Or.inl h
    · exact Or.inr ⟨rid, hRid, h⟩

/-- `v0.35.4`: the splice is the identity on a frame with nothing above it — the
shape every cancellation of a head or bottom frame, and every successful reclaim,
leaves. -/
theorem spliceThreadReplyFrameOut_eq_self_of_no_frame_above (st : SystemState) (tcb : TCB)
    (hNoFrameAbove : ∀ (rid : SeLe4n.ReplyId) (r : Reply) (above : SeLe4n.ReplyId),
      tcb.replyObject = some rid → st.getReply? rid = some r →
      r.next ≠ some (.frame above)) :
    spliceThreadReplyFrameOut st tcb = st := by
  rcases spliceThreadReplyFrameOut_cases st tcb with h | ⟨rid, hRid, h⟩
  · exact h
  · rcases spliceReplyFrameOut_cases h with h' | ⟨r, above, _, hR, hN, _, _, _⟩
    · exact h'
    · exact absurd hN (hNoFrameAbove rid r above hRid hR)

theorem spliceThreadReplyFrameOut_scheduler_eq (st : SystemState) (tcb : TCB) :
    (spliceThreadReplyFrameOut st tcb).scheduler = st.scheduler := by
  rcases spliceThreadReplyFrameOut_cases st tcb with h | ⟨_, _, h⟩
  · rw [h]
  · exact spliceReplyFrameOut_scheduler_eq h

theorem spliceThreadReplyFrameOut_machine_eq (st : SystemState) (tcb : TCB) :
    (spliceThreadReplyFrameOut st tcb).machine = st.machine := by
  rcases spliceThreadReplyFrameOut_cases st tcb with h | ⟨_, _, h⟩
  · rw [h]
  · exact spliceReplyFrameOut_machine_eq h

theorem spliceThreadReplyFrameOut_serviceRegistry_eq (st : SystemState) (tcb : TCB) :
    (spliceThreadReplyFrameOut st tcb).serviceRegistry = st.serviceRegistry := by
  rcases spliceThreadReplyFrameOut_cases st tcb with h | ⟨_, _, h⟩
  · rw [h]
  · exact spliceReplyFrameOut_serviceRegistry_eq h

theorem spliceThreadReplyFrameOut_preserves_objects_invExt (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) : (spliceThreadReplyFrameOut st tcb).objects.invExt := by
  rcases spliceThreadReplyFrameOut_cases st tcb with h | ⟨_, _, h⟩
  · rw [h]; exact hInv
  · exact spliceReplyFrameOut_preserves_objects_invExt hInv h

/-- The splice writes only Reply objects, so every stored TCB is where it was. -/
theorem spliceThreadReplyFrameOut_tcb_eq (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (t0 : TCB)
    (hk : st.objects[k]? = some (.tcb t0)) :
    (spliceThreadReplyFrameOut st tcb).objects[k]? = some (.tcb t0) := by
  rcases spliceThreadReplyFrameOut_cases st tcb with h | ⟨_, _, h⟩
  · rw [h]; exact hk
  · exact spliceReplyFrameOut_tcb_eq hInv h k t0 hk

theorem spliceThreadReplyFrameOut_tcb_backward (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (t0 : TCB)
    (hk : (spliceThreadReplyFrameOut st tcb).objects[k]? = some (.tcb t0)) :
    st.objects[k]? = some (.tcb t0) := by
  rcases spliceThreadReplyFrameOut_cases st tcb with h | ⟨_, _, h⟩
  · rw [h] at hk; exact hk
  · exact spliceReplyFrameOut_tcb_backward hInv h k t0 hk

theorem spliceThreadReplyFrameOut_getTcb?_eq (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) (tid : SeLe4n.ThreadId) :
    (spliceThreadReplyFrameOut st tcb).getTcb? tid = st.getTcb? tid := by
  rcases spliceThreadReplyFrameOut_cases st tcb with h | ⟨_, _, h⟩
  · rw [h]
  · exact spliceReplyFrameOut_getTcb?_eq hInv h tid

/-- WS-RM (`v0.35.6`): **take a caller's reply frame off its stack and consume its
caller link** — seL4's `reply_remove`, with the middle case **spliced** rather
than severed (WS-HP HP6.3): upstream's non-head branch clears the frame above's
`replyPrev`; this removal links the frame above down to the frame below and that
frame back up (`spliceReplyFrameStores`), and then `reply_unlink` severs the
caller↔Reply pair.

The removal runs **first** and the consume second, and that order is the whole
point: `Reply.consumed` clears both stack links on a frame that is not a head, so
a frame still named by the `prev` of the frame above it would falsify
`donationChainWellFormed.prevLinkReciprocal` there — a wedge the later pop
refuses fail-closed.  Removing first is what leaves nothing pointing down at the
frame being consumed (`spliceReplyFrameOutOrSelf_unreferenced`).

It is deliberately **not** folded into `consumeCallerReply`: that operation's
two-key frame (`consumeCallerReply_objects_frame`) is what the whole IPC
invariant surface rests on, and a third write inside it would falsify the
statement outright.  Sequencing leaves every one of those theorems untouched, and
is also what seL4 does.

On a frame with nothing above it — every head, every bottom frame, and every
Reply the tree consumed before the stack became doubly linked — the splice is the
identity and this **is** `consumeCallerReply`, definitionally
(`removeCallerReplyFrame_eq_consume_of_no_frame_above`). -/
def removeCallerReplyFrame (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) :
    Kernel Unit :=
  fun st => SystemState.consumeCallerReply caller rid (spliceReplyFrameOutOrSelf st rid)

-- ----------------------------------------------------------------------------
-- WS-RM (`v0.35.6`): the folded splice's read/write algebra
-- ----------------------------------------------------------------------------
--
-- Each entry is the identity on the refusal arm and the corresponding
-- `spliceReplyFrameOut` fact on the other, so nothing new is argued here: the
-- fold inherits the primitive's algebra verbatim.

/-- The `cdt` is not an object-store field, so the splice leaves it alone. -/
theorem spliceReplyFrameOut_cdt_eq {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (h : spliceReplyFrameOut st rid = .ok st') : st'.cdt = st.cdt := by
  rcases spliceReplyFrameOut_cases h with rfl | ⟨_, _, _, _, _, _, _, hS⟩
  · rfl
  · exact spliceReplyFrameStores_cdt_eq hS

theorem spliceReplyFrameOut_cdtNodeSlot_eq {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (h : spliceReplyFrameOut st rid = .ok st') : st'.cdtNodeSlot = st.cdtNodeSlot := by
  rcases spliceReplyFrameOut_cases h with rfl | ⟨_, _, _, _, _, _, _, hS⟩
  · rfl
  · exact spliceReplyFrameStores_cdtNodeSlot_eq hS

/-- The splice refuses only where there is a frame above to repair, so a `rid`
with none is the identity on either arm. -/
theorem spliceReplyFrameOutOrSelf_eq_self_of_no_frame_above (st : SystemState)
    (rid : SeLe4n.ReplyId) (hNone : replyFrameAbove? st rid = none) :
    spliceReplyFrameOutOrSelf st rid = st := by
  have hDet : spliceReplyFrameOut st rid = .ok st := by
    cases hR : st.getReply? rid with
    | none => exact spliceReplyFrameOut_of_absent st rid hR
    | some r =>
      cases hN : r.next with
      | none => exact spliceReplyFrameOut_of_no_frame_above st rid r hR hN
      | some l =>
        cases l with
        | head sc => exact spliceReplyFrameOut_of_head st rid r sc hR hN
        | frame above =>
          exact absurd (show replyFrameAbove? st rid = some above by
            simp [replyFrameAbove?, hR, hN]) (by rw [hNone]; exact fun h => by cases h)
  unfold spliceReplyFrameOutOrSelf; rw [hDet]

theorem spliceReplyFrameOutOrSelf_scheduler_eq (st : SystemState) (rid : SeLe4n.ReplyId) :
    (spliceReplyFrameOutOrSelf st rid).scheduler = st.scheduler := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]
  · exact spliceReplyFrameOut_scheduler_eq h

theorem spliceReplyFrameOutOrSelf_machine_eq (st : SystemState) (rid : SeLe4n.ReplyId) :
    (spliceReplyFrameOutOrSelf st rid).machine = st.machine := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]
  · exact spliceReplyFrameOut_machine_eq h

theorem spliceReplyFrameOutOrSelf_serviceRegistry_eq (st : SystemState)
    (rid : SeLe4n.ReplyId) :
    (spliceReplyFrameOutOrSelf st rid).serviceRegistry = st.serviceRegistry := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]
  · exact spliceReplyFrameOut_serviceRegistry_eq h

theorem spliceReplyFrameOutOrSelf_cdt_eq (st : SystemState) (rid : SeLe4n.ReplyId) :
    (spliceReplyFrameOutOrSelf st rid).cdt = st.cdt := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]
  · exact spliceReplyFrameOut_cdt_eq h

theorem spliceReplyFrameOutOrSelf_cdtNodeSlot_eq (st : SystemState) (rid : SeLe4n.ReplyId) :
    (spliceReplyFrameOutOrSelf st rid).cdtNodeSlot = st.cdtNodeSlot := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]
  · exact spliceReplyFrameOut_cdtNodeSlot_eq h

theorem spliceReplyFrameOutOrSelf_preserves_objects_invExt (st : SystemState)
    (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt) :
    (spliceReplyFrameOutOrSelf st rid).objects.invExt := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]; exact hInv
  · exact spliceReplyFrameOut_preserves_objects_invExt hInv h

/-- **WS-RM (`v0.35.6`): the fold's frame at *every* key.**  A key is either
untouched, or it held a Reply that survives with only its stack links rewritten.
Stated as a disjunction rather than as `objects_ne` plus a side condition because
the consumers below cannot always *exclude* the frames the removal writes — the
answered caller's reply-stack neighbours are not keys any reply-path hypothesis
names — and a stack-link rewrite is invisible to every conjunct that reads a
Reply's `caller` rather than its `prev` / `next`, which is all of them.

It reads the primitive's own frame (WS-HP HP6.4), so a consumer never iterates the
two stores the splice performs. -/
theorem spliceReplyFrameOutOrSelf_objects_rewrite (st : SystemState)
    (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt) (x : SeLe4n.ObjId) :
    (spliceReplyFrameOutOrSelf st rid).objects[x]? = st.objects[x]? ∨
      ∃ r r', st.objects[x]? = some (.reply r) ∧
        (spliceReplyFrameOutOrSelf st rid).objects[x]? = some (.reply r') ∧
        replyStackRewrite r' r := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · exact Or.inl (by rw [h])
  · exact spliceReplyFrameOut_objects_rewrite hInv h x

/-- The fold writes at most the frame `replyFrameAbove?` names, the frame
`replyFrameBelow?` names, and the cut frame itself (WS-HP HP6.4 — the splice
writes all three). -/
theorem spliceReplyFrameOutOrSelf_objects_ne (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId)
    (hk : ∀ above, replyFrameAbove? st rid = some above → k ≠ above.toObjId)
    (hkBelow : ∀ below, replyFrameBelow? st rid = some below → k ≠ below.toObjId)
    (hkCut : k ≠ rid.toObjId) :
    (spliceReplyFrameOutOrSelf st rid).objects[k]? = st.objects[k]? := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]
  · refine spliceReplyFrameOut_objects_ne hInv h k ?_ ?_ hkCut
    · intro r above hR hN
      exact hk above (by simp [replyFrameAbove?, hR, hN])
    · intro r above below hR hN hPrev
      exact hkBelow below (by simp [replyFrameBelow?, replyFrameAbove?, hR, hN, hPrev])

theorem spliceReplyFrameOutOrSelf_tcb_eq (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (t0 : TCB)
    (hk : st.objects[k]? = some (.tcb t0)) :
    (spliceReplyFrameOutOrSelf st rid).objects[k]? = some (.tcb t0) := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]; exact hk
  · exact spliceReplyFrameOut_tcb_eq hInv h k t0 hk

theorem spliceReplyFrameOutOrSelf_tcb_backward (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (t0 : TCB)
    (hk : (spliceReplyFrameOutOrSelf st rid).objects[k]? = some (.tcb t0)) :
    st.objects[k]? = some (.tcb t0) := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h] at hk; exact hk
  · exact spliceReplyFrameOut_tcb_backward hInv h k t0 hk

theorem spliceReplyFrameOutOrSelf_getTcb?_eq (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) (tid : SeLe4n.ThreadId) :
    (spliceReplyFrameOutOrSelf st rid).getTcb? tid = st.getTcb? tid := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]
  · exact spliceReplyFrameOut_getTcb?_eq hInv h tid

theorem spliceReplyFrameOutOrSelf_non_reply_eq (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId)
    (hNotReply : ∀ r : Reply, st.objects[k]? ≠ some (.reply r)) :
    (spliceReplyFrameOutOrSelf st rid).objects[k]? = st.objects[k]? := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]
  · exact spliceReplyFrameOut_non_reply_eq hInv h k hNotReply

/-- A key the fold rewrites holds a Reply on **both** sides, so a read whose value
is not a Reply crosses the fold unchanged in either direction — the iff form
`consumeCallerReply_nonTcbNonReply_agree` composes with. -/
theorem spliceReplyFrameOutOrSelf_non_reply_agree (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) (s : SeLe4n.ObjId) (k : KernelObject)
    (hkR : ∀ rr, k ≠ .reply rr) :
    ((spliceReplyFrameOutOrSelf st rid).objects[s]? = some k ↔ st.objects[s]? = some k) := by
  rcases spliceReplyFrameOutOrSelf_objects_rewrite st rid hInv s with hEq | ⟨o, o', hPre, hPost, _⟩
  · rw [hEq]
  · refine iff_of_false ?_ ?_
    · rw [hPost]; intro hx; exact hkR o' (Option.some.inj hx).symm
    · rw [hPre]; intro hx; exact hkR o (Option.some.inj hx).symm

theorem spliceReplyFrameOutOrSelf_notification_backward (st : SystemState)
    (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : (spliceReplyFrameOutOrSelf st rid).objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h] at hNtfn; exact hNtfn
  · exact spliceReplyFrameOut_notification_backward hInv h oid ntfn hNtfn

/-- Every Reply survives the fold, with at most its stack links rewritten. -/
theorem spliceReplyFrameOutOrSelf_reply_rewrite (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) (oid : SeLe4n.ObjId) (r : Reply)
    (hReply : st.objects[oid]? = some (.reply r)) :
    ∃ r', (spliceReplyFrameOutOrSelf st rid).objects[oid]? = some (.reply r') ∧
      replyStackRewrite r' r := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · exact ⟨r, by rw [h]; exact hReply, replyStackRewrite.refl r⟩
  · exact spliceReplyFrameOut_reply_rewrite hInv h oid r hReply

/-- **WS-RM (`v0.35.6`): the fold's *decision*, read off the object store.**
Either the cut frame resolves and names a frame above that resolves and
reciprocates — and the fold is exactly that frame's composed store step — or it
does not, and the fold is the identity.  Both branches are distinguished by a
predicate over `getReply?` alone, which is what lets any relation that agrees on
objects transport the decision: without it a congruence would have to re-derive
the branch on each side and could not rule out the two sides taking different
ones.

The cut frame's own record is exposed (WS-HP HP6.4) because the composed step
reads its `prev` to decide whether to splice, so a congruence must compare that
record too — and it comes from the same `getReply?` the branch condition reads,
so nothing new has to agree. -/
theorem spliceReplyFrameOutOrSelf_decision (st : SystemState) (rid : SeLe4n.ReplyId) :
    (∃ (r : Reply) (above : SeLe4n.ReplyId) (a : Reply),
        st.getReply? rid = some r ∧ r.next = some (.frame above) ∧
        st.getReply? above = some a ∧ a.prev = some rid ∧
        spliceReplyFrameStores st rid above r a = .ok (spliceReplyFrameOutOrSelf st rid)) ∨
      (spliceReplyFrameOutOrSelf st rid = st ∧
        ∀ (r : Reply) (above : SeLe4n.ReplyId) (a : Reply),
          st.getReply? rid = some r → r.next = some (.frame above) →
          st.getReply? above = some a → a.prev ≠ some rid) := by
  by_cases hEx : ∃ (r : Reply) (above : SeLe4n.ReplyId) (a : Reply),
      st.getReply? rid = some r ∧ r.next = some (.frame above) ∧
      st.getReply? above = some a ∧ a.prev = some rid
  · obtain ⟨r, above, a, hR, hN, hA, hP⟩ := hEx
    obtain ⟨s', hS⟩ := spliceReplyFrameStores_isOk st rid above r a
    have hOut : spliceReplyFrameOut st rid = .ok s' := by
      unfold spliceReplyFrameOut
      rw [hR]
      simp only [hN, hA, hP, bne_self_eq_false, Bool.false_eq_true, if_false]
      exact hS
    have hFold : spliceReplyFrameOutOrSelf st rid = s' := by
      unfold spliceReplyFrameOutOrSelf; rw [hOut]
    exact Or.inl ⟨r, above, a, hR, hN, hA, hP, by rw [hFold]; exact hS⟩
  · refine Or.inr ⟨?_, ?_⟩
    · rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
      · exact h
      · rcases spliceReplyFrameOut_cases h with hEq | ⟨r, above, a, hR, hN, hA, hP, _⟩
        · exact hEq
        · exact absurd ⟨r, above, a, hR, hN, hA, hP⟩ hEx
    · intro r above a hR hN hA hP
      exact hEx ⟨r, above, a, hR, hN, hA, hP⟩

-- ----------------------------------------------------------------------------
-- WS-RM (`v0.35.6`): `removeCallerReplyFrame`'s read/write algebra
-- ----------------------------------------------------------------------------
--
-- Each entry composes the fold's fact above with `consumeCallerReply`'s, which
-- is why none of them needs an argument of its own.

/-- The removal is the consume, run at the state the splice left. -/
theorem removeCallerReplyFrame_eq (st : SystemState) (caller : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) :
    removeCallerReplyFrame caller rid st
      = SystemState.consumeCallerReply caller rid (spliceReplyFrameOutOrSelf st rid) := rfl

/-- **WS-RM (`v0.35.6`): on a frame with nothing above it the removal *is* the
consume**, definitionally.  Every repair of an existing reply-path proof is
therefore a case split on `answeredReplyFrameAbove?` whose `none` branch is that
proof verbatim, and every state the tree reached before the reply path detached
is in that branch. -/
theorem removeCallerReplyFrame_eq_consume_of_no_frame_above (st : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hNone : replyFrameAbove? st rid = none) :
    removeCallerReplyFrame caller rid st = SystemState.consumeCallerReply caller rid st := by
  rw [removeCallerReplyFrame_eq, spliceReplyFrameOutOrSelf_eq_self_of_no_frame_above st rid hNone]

/-- The removal is **total**: both legs are. -/
theorem removeCallerReplyFrame_isOk (st : SystemState) (caller : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) :
    ∃ st', removeCallerReplyFrame caller rid st = .ok ((), st') := by
  rw [removeCallerReplyFrame_eq]
  exact SystemState.consumeCallerReply_isOk _ caller rid

theorem removeCallerReplyFrame_scheduler_eq (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  rw [removeCallerReplyFrame_eq] at hStep
  exact (SystemState.consumeCallerReply_scheduler_eq _ st' caller rid hStep).trans
    (spliceReplyFrameOutOrSelf_scheduler_eq st rid)

theorem removeCallerReplyFrame_machine_eq (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    st'.machine = st.machine := by
  rw [removeCallerReplyFrame_eq] at hStep
  exact (SystemState.consumeCallerReply_machine_eq _ st' caller rid hStep).trans
    (spliceReplyFrameOutOrSelf_machine_eq st rid)

theorem removeCallerReplyFrame_cdt_eq (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    st'.cdt = st.cdt := by
  rw [removeCallerReplyFrame_eq] at hStep
  exact (SystemState.consumeCallerReply_cdt_eq _ st' caller rid hStep).trans
    (spliceReplyFrameOutOrSelf_cdt_eq st rid)

theorem removeCallerReplyFrame_cdtNodeSlot_eq (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    st'.cdtNodeSlot = st.cdtNodeSlot := by
  rw [removeCallerReplyFrame_eq] at hStep
  exact (SystemState.consumeCallerReply_cdtNodeSlot_eq _ st' caller rid hStep).trans
    (spliceReplyFrameOutOrSelf_cdtNodeSlot_eq st rid)

/-- **WS-RR RR8.16** (`v0.35.199`): the splice is a `kindPreservingWrite` — it
rewrites the stack links of up to three Reply objects and touches nothing else,
so every key it writes held a Reply and still holds one. -/
theorem spliceReplyFrameOutOrSelf_kindPreservingWrite (st : SystemState)
    (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt) :
    kindPreservingWrite st (spliceReplyFrameOutOrSelf st rid) := by
  intro k
  rcases spliceReplyFrameOutOrSelf_objects_rewrite st rid hObjInv k with h | ⟨r, r', hr, hr', _⟩
  · exact Or.inl h
  · exact Or.inr ⟨.reply r, .reply r', hr, hr', rfl, by simp [KernelObject.objectType]⟩

/-- **WS-RR RR8.16** (`v0.35.199`): and so is the removal — the splice above, then
the consume, which writes a Reply for a Reply and a TCB for a TCB.

This is what carries register row 85's two bundles across seL4's `reply_remove`:
the capability bundle's four transport hypotheses collapse into it
(`capabilityInvariantBundle_of_kindPreserving`) and the scheduler bundle reads the
`getTcb?` half of it. -/
theorem removeCallerReplyFrame_kindPreservingWrite (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    kindPreservingWrite st st' := by
  rw [removeCallerReplyFrame_eq] at hStep
  exact (spliceReplyFrameOutOrSelf_kindPreservingWrite st rid hObjInv).trans
    (SystemState.consumeCallerReply_kindPreservingWrite _ st' caller rid
      (spliceReplyFrameOutOrSelf_preserves_objects_invExt st rid hObjInv) hStep)

theorem removeCallerReplyFrame_preserves_objects_invExt (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    st'.objects.invExt := by
  rw [removeCallerReplyFrame_eq] at hStep
  exact SystemState.consumeCallerReply_preserves_objects_invExt _ st' caller rid
    (spliceReplyFrameOutOrSelf_preserves_objects_invExt st rid hObjInv) hStep

theorem removeCallerReplyFrame_nonTcbNonReply_agree (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    ∀ (s : SeLe4n.ObjId) (k : KernelObject),
      (∀ tt, k ≠ .tcb tt) → (∀ rr, k ≠ .reply rr) →
      (st'.objects[s]? = some k ↔ st.objects[s]? = some k) := by
  intro s k hkT hkR
  rw [removeCallerReplyFrame_eq] at hStep
  rw [SystemState.consumeCallerReply_nonTcbNonReply_agree _ st' caller rid
      (spliceReplyFrameOutOrSelf_preserves_objects_invExt st rid hObjInv) hStep s k hkT hkR]
  exact spliceReplyFrameOutOrSelf_non_reply_agree st rid hObjInv s k hkR

/-- Every stored TCB survives the removal, with only the answered caller's
`replyObject` cleared: the splice writes no TCB and the consume's TCB rewrite
preserves every field the IPC surface reads. -/
theorem removeCallerReplyFrame_tcb_forward (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    ∀ (s : SeLe4n.ObjId) (tx : TCB), st'.objects[s]? = some (.tcb tx) →
      ∃ ty, st.objects[s]? = some (.tcb ty) ∧
        tx.ipcState = ty.ipcState ∧ tx.pendingMessage = ty.pendingMessage ∧
        tx.queueNext = ty.queueNext ∧ tx.queuePrev = ty.queuePrev ∧
        tx.queuePPrev = ty.queuePPrev ∧ tx.schedContextBinding = ty.schedContextBinding ∧
        tx.timeoutBudget = ty.timeoutBudget := by
  intro s tx hx
  rw [removeCallerReplyFrame_eq] at hStep
  obtain ⟨ty, hy, hFields⟩ := SystemState.consumeCallerReply_tcb_forward _ st' caller rid
    (spliceReplyFrameOutOrSelf_preserves_objects_invExt st rid hObjInv) hStep s tx hx
  exact ⟨ty, spliceReplyFrameOutOrSelf_tcb_backward st rid hObjInv s ty hy, hFields⟩

theorem removeCallerReplyFrame_tcb_backward (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    ∀ (s : SeLe4n.ObjId) (ty : TCB), st.objects[s]? = some (.tcb ty) →
      ∃ tx, st'.objects[s]? = some (.tcb tx) ∧
        tx.ipcState = ty.ipcState ∧ tx.pendingMessage = ty.pendingMessage ∧
        tx.queueNext = ty.queueNext ∧ tx.queuePrev = ty.queuePrev ∧
        tx.queuePPrev = ty.queuePPrev ∧ tx.schedContextBinding = ty.schedContextBinding ∧
        tx.timeoutBudget = ty.timeoutBudget := by
  intro s ty hy
  rw [removeCallerReplyFrame_eq] at hStep
  exact SystemState.consumeCallerReply_tcb_backward _ st' caller rid
    (spliceReplyFrameOutOrSelf_preserves_objects_invExt st rid hObjInv) hStep s ty
    (spliceReplyFrameOutOrSelf_tcb_eq st rid hObjInv s ty hy)

/-- The answered caller's forward link is gone after the removal. -/
theorem removeCallerReplyFrame_replyObject_none (st : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt) :
    ∀ result tcb', removeCallerReplyFrame caller rid st = .ok ((), result) →
      result.getTcb? caller = some tcb' → tcb'.replyObject = none := by
  intro result tcb' hRun hGetT
  rw [removeCallerReplyFrame_eq] at hRun
  exact SystemState.consumeCallerReply_replyObject_none _ caller rid
    (spliceReplyFrameOutOrSelf_preserves_objects_invExt st rid hObjInv) result tcb' hRun hGetT

/-- The consumed Reply reads back as `Reply.consumed` of the record the *splice*
left — which is the pre-state record whenever the consumed frame is not itself
the frame above (it never is: a frame is not above itself under
`prevLinkReciprocal`, and `replyFrameAbove?` names a different key). -/
theorem removeCallerReplyFrame_getReply?_caller_none (st : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (r : Reply)
    (hObjInv : st.objects.invExt)
    (hGet : (spliceReplyFrameOutOrSelf st rid).getReply? rid = some r) :
    ∀ result, removeCallerReplyFrame caller rid st = .ok ((), result) →
      result.getReply? rid = some r.consumed := by
  intro result hRun
  rw [removeCallerReplyFrame_eq] at hRun
  exact SystemState.consumeCallerReply_getReply?_caller_none _ caller rid r
    (spliceReplyFrameOutOrSelf_preserves_objects_invExt st rid hObjInv) hGet result hRun

/-- **WS-RM (`v0.35.6`): the removal frees the consumed Reply**, stated on the
*pre-state's* Reply.  The splice rewrites `rid`'s own frame whenever a frame
below reciprocates (its third store clears the cut frame's `prev`, seL4's
`reply_unlink` downward half), so the record the consume acts on is the pre-state
record with at most its stack links moved (`spliceReplyFrameOutOrSelf_reply_rewrite`);
the existential is stated over that record, and `caller = none` — the only
projection the linkage conjuncts read here — is the same either way. -/
theorem removeCallerReplyFrame_getReply?_free (st : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (r : Reply)
    (hObjInv : st.objects.invExt)
    (hGet : st.getReply? rid = some r) :
    ∀ result, removeCallerReplyFrame caller rid st = .ok ((), result) →
      ∃ r', result.getReply? rid = some r' ∧ r'.caller = none := by
  intro result hRun
  obtain ⟨rd, hrd, _⟩ := spliceReplyFrameOutOrSelf_reply_rewrite st rid hObjInv rid.toObjId r
    ((SystemState.getReply?_eq_some_iff st rid r).mp hGet)
  exact ⟨rd.consumed,
    removeCallerReplyFrame_getReply?_caller_none st caller rid rd hObjInv
      ((SystemState.getReply?_eq_some_iff _ rid rd).mpr hrd) result hRun,
    Reply.consumed_caller rd⟩

/-- **WS-RM (`v0.35.6`): a stack *head* keeps its links across the removal.**
`Reply.consumed_of_head` is deliberate — the donation pop that follows in the same
transition validates the head by exactly this link — and the splice is the
identity on a head (a `.head` names no frame above), so the frame a reply answered
still heads the same context afterwards.  This is what lets the composite payoff
locate the relaxed frame as the one the pop is about to clear. -/
theorem removeCallerReplyFrame_head_getReply?_next (st : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (r : Reply)
    (scId : SeLe4n.SchedContextId) (hObjInv : st.objects.invExt)
    (hR : st.getReply? rid = some r) (hHead : r.next = some (.head scId))
    (st' : SystemState) (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    ∃ r', st'.getReply? rid = some r' ∧ r'.next = some (.head scId) := by
  have hFold : spliceReplyFrameOutOrSelf st rid = st :=
    spliceReplyFrameOutOrSelf_eq_self_of_no_frame_above st rid
      (replyFrameAbove?_of_head st rid r scId hR hHead)
  refine ⟨r.consumed,
    removeCallerReplyFrame_getReply?_caller_none st caller rid r hObjInv
      (by rw [hFold]; exact hR) st' hStep, ?_⟩
  rw [Reply.consumed_of_head r scId hHead]; exact hHead

/-- Every object present before the removal is present after it: both legs
rewrite records in place and neither erases a key. -/
theorem removeCallerReplyFrame_objects_isSome (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    ∀ (x : SeLe4n.ObjId), st.objects[x]? ≠ none → st'.objects[x]? ≠ none := by
  intro x hSome
  rw [removeCallerReplyFrame_eq] at hStep
  refine SystemState.consumeCallerReply_objects_isSome _ st' caller rid
    (spliceReplyFrameOutOrSelf_preserves_objects_invExt st rid hObjInv) hStep x ?_
  intro hNone
  cases hPre : st.objects[x]? with
  | none => exact hSome hPre
  | some k =>
    cases k with
    | reply r0 =>
      obtain ⟨r1, hr1, _⟩ := spliceReplyFrameOutOrSelf_reply_rewrite st rid hObjInv x r0 hPre
      rw [hr1] at hNone; cases hNone
    | tcb t0 =>
      rw [spliceReplyFrameOutOrSelf_tcb_eq st rid hObjInv x t0 hPre] at hNone; cases hNone
    | _ =>
      rw [spliceReplyFrameOutOrSelf_non_reply_eq st rid hObjInv x (by intro r hr; cases hPre.symm.trans hr), hPre] at hNone
      cases hNone

/-- Every Reply present before the removal is still a Reply after it. -/
theorem removeCallerReplyFrame_getReply?_isSome (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    ∀ (rid' : SeLe4n.ReplyId) (r' : Reply), st.getReply? rid' = some r' →
      ∃ r'', st'.getReply? rid' = some r'' := by
  intro rid' r' hGet'
  rw [removeCallerReplyFrame_eq] at hStep
  obtain ⟨r1, hr1, _⟩ := spliceReplyFrameOutOrSelf_reply_rewrite st rid hObjInv rid'.toObjId r'
    ((SystemState.getReply?_eq_some_iff _ _ _).mp hGet')
  exact SystemState.consumeCallerReply_getReply?_isSome _ st' caller rid
    (spliceReplyFrameOutOrSelf_preserves_objects_invExt st rid hObjInv) hStep rid' r1
    ((SystemState.getReply?_eq_some_iff _ _ _).mpr hr1)

/-- Z7-C2: Return a donated SchedContext from a server back to the thread that
donated it, and pop that donation off the context's reply stack.

Performs the reverse binding:
1. SchedContext `boundThread` updated to point back to the donor, and its
   reply-stack head (`scReply`) popped to the reply below;
2. the head reply's stack links cleared (`prev`, `next`) and the frame below it
   re-headed (`next := .head scId`), when there is a head — one
   `storeDonationHeadPop`, seL4's `reply_pop`;
3. the donor's TCB gets `donationReturnBinding scId newOwner?` — `.bound scId`
   at the bottom of the stack, `.donated scId outer` one level up;
4. Server TCB gets `schedContextBinding := .unbound`.

**Preconditions** (enforced by caller `endpointReply`):
- Server has `schedContextBinding = .donated(scId, originalOwner)`

**WS-OD OD3.1 — `newOwner?` is an argument, not a post-state read.**  The reply
leg consumes the target's `replyObject` (`consumeCallerReply`) *before* the
donation return runs, and `.replyRecv` has the same shape, so by the time this
operation executes the link that would name the outer caller is gone.  It is
therefore resolved from the **pre**-state by `replyStackOuterCaller?` and passed
in — the discipline `recordedReplyServer?`, `replyDonationHolderHome` and
`replyDonationRecipientHome` already follow in the same dispatch.

**This phase landed inert** (OD3, before OD4.1's push existed): with no context
heading a stack, `donationHeadOf?` answers `none`, the head pop is the identity,
the resolver answers `none`, and the operation is the pre-OD3 three-store chain
store for store (`returnDonatedSchedContext_eq_legacy_of_none`) — which is still
the depth-1 shape today.

Returns the updated state or error if lookups fail.

**Atomicity contract (AC3-A / I-02 / I-03)**:
This function performs up to 4 sequential store steps through states
`st` → `st1` → `st2` → `st3` → `st4` (the second being up to two Reply stores). The same monad-level atomicity argument as
`donateSchedContext` applies: on `.error`, no intermediate state is returned
to the caller. The `Except.bind` combinator discards partial states on
failure. On hardware, interrupts are disabled throughout kernel transitions,
providing single-core atomicity for the update sequence. -/
def returnDonatedSchedContext
    (st : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId) : Except KernelError SystemState :=
  -- Step 1: Look up and update SchedContext to point back to original owner
  match st.getSchedContext? scId with
  | some sc =>
    -- WS-RR RR2.8 (symmetry with `donateSchedContext`'s AUD-3b guard): verify the
    -- SchedContext is actually bound to the **server** before handing it back.
    -- The donation path checks its own direction (`sc.boundThread != some
    -- clientTid`); the return path did not, so a `.donated scId owner` binding
    -- that had drifted from the SchedContext's own `boundThread` would rebind the
    -- SchedContext to `originalOwner` while leaving whichever thread the
    -- SchedContext really belonged to still `.bound scId` — two threads bound to
    -- one SchedContext, i.e. a `donationBudgetTransfer` violation, silently
    -- created by a successful reply.  `donationOwnerValid` rules that drift out,
    -- so this is defence in depth on a live path and never fires in a
    -- well-formed state; it also makes the SM5.H replenishment migration's source
    -- core derivable from success rather than assumed
    -- (`returnDonatedSchedContext_ok_implies_sc_bound`).
    if sc.boundThread != some serverTid then .error .invalidArgument
    else
    -- WS-OD OD4.4: **validate the outer caller before handing it a donation.**
    -- `donateSchedContext` checks its donor side (the AUD-3b guard) before
    -- minting a `.donated` binding; this operation mints one too — at the bottom
    -- of the stack `.bound`, one level up `.donated scId outer` — and until now
    -- it checked nothing about `outer`.  That asymmetry is the defect: every
    -- consumer had to carry the donor shape as a hypothesis, and on the reply
    -- path (where the answered caller has just been woken `.ready`) no consumer
    -- could discharge it.  The check is O(1) and fail-closed, so the three
    -- structural clauses `donationOwnerValid` needs of `outer` become
    -- consequences of this operation succeeding rather than obligations of
    -- everyone who calls it.
    if !outerCallerAcceptable st serverTid originalOwner newOwner? then
      .error .invalidArgument
    else
    -- **WS-HP HP4.6**: and validate the *recipient* the same way, for the reason
    -- `donationRecipientAcceptable` records -- the head-driven trigger takes it
    -- from the answered caller rather than from a binding `donationOwnerValid`
    -- constrains, so the operation checks what it is about to overwrite.
    if !donationRecipientAcceptable st originalOwner then
      .error .invalidArgument
    else
    -- WS-OD OD3.1: resolve and validate the reply-stack head **before** any
    -- store, so a head this context does not own commits nothing.
    match donationHeadOf? st scId sc with
    | .error e => .error e
    | .ok head? =>
      -- **WS-RR RR8**: the reservation's record is `donationReturnSchedContext`,
      -- whose docstring carries what each of its three fields is for -- HP10.4's
      -- bottom-arm origin clear among them, and why the priority mirror is not a
      -- fourth.  The frozen mirror stores the *same* definition, so the two
      -- surfaces cannot disagree about what a return writes here.
      let sc' := donationReturnSchedContext sc originalOwner
        (head?.bind (fun p => p.2.prev)) newOwner?
      match storeObject scId.toObjId (.schedContext sc') st with
      | .error e => .error e
      | .ok ((), st1) =>
        -- Step 2: clear the popped head's stack fields.  The identity when the
        -- context heads no stack, which is every state this tree reaches today.
        match storeDonationHeadPop scId head? st1 with
        | .error e => .error e
        | .ok st2 =>
          -- Step 3: Look up and update the donor's TCB with its returning binding
          match lookupTcb st2 originalOwner with
          | none => .error .objectNotFound
          | some clientTcb =>
            let clientTcb' := { clientTcb with
              schedContextBinding := donationReturnBinding scId newOwner? }
            match storeObject originalOwner.toObjId (.tcb clientTcb') st2 with
            | .error e => .error e
            | .ok ((), st3) =>
              -- Step 4: Look up and update server TCB to unbound
              match lookupTcb st3 serverTid with
              | none => .error .objectNotFound
              | some serverTcb =>
                let serverTcb' := { serverTcb with
                  schedContextBinding := .unbound }
                match storeObject serverTid.toObjId (.tcb serverTcb') st3 with
                | .error e => .error e
                | .ok ((), st4) =>
                  -- S-05/PERF-O1 + F-3: the SchedContext's referencing threads change
                  -- from {server} back to {originalOwner}: remove the server and re-add the
                  -- now-bound-or-donating donor (the inverse of `donateSchedContext`'s
                  -- index update), keeping `scThreadIndexConsistent`.
                  .ok { st4 with scThreadIndex :=
                    (scThreadIndexAdd
                      (scThreadIndexRemove st4.scThreadIndex scId serverTid)
                      scId originalOwner) }
  | none => .error .objectNotFound


/-- **WS-HP HP10.6: the thread a bottom-of-stack pop hands the reservation to on
the strength of the recorded origin.**

`none` wherever stack reachability already names the right recipient, which is
every state this tree reaches today: a pop that is *not* at the bottom of its
stack, a context recording no origin, and an origin the pop may not write.  `some
o` exactly where all three fail — and that is the depth-2 gap this phase exists
for, where a delegate answered the client out of order, the removal took the
client's frame off the **bottom** of the stack, and the frame above it became the
bottom, so reachability now names the intermediate caller rather than the client
whose reservation it is.

Four things it is deliberately not.

It is **not** a second reading of the stack.  Its `.ok none` arm *is*
`returnDonatedSchedContextResolved`'s own `newOwner? = none`, so the redirect fires
on exactly the argument value the pop's bottom arm branches on
(`donationOriginRecipient?_of_outer_some` is the theorem that it is silent
everywhere else).  That is also what makes the footprint member honest: it is
declared on the states the pop writes it and on no others, which is what keeps
HP10.6's raise parametric rather than a widening of every reachable footprint
(`replyStackBelowHead?_of_originRecipient`).

It is **not** an invariant.  `SchedContext.donationOrigin` is history the kernel
validates, for the reason its own docstring records: *the origin is the bottom
frame's thread, **or** a thread whose frame was removed* has an unstateable second
disjunct, so no `donationChainWellFormed` clause can carry it.  What makes reading
it safe is that the guard is applied **here**: a stale origin falls back to the
reachability answer rather than refusing the pop, which is the difference between
a recovery and a refusal — and `donationRecipientAcceptable` is the same guard
HP4.6 put inside the operation, asked of the candidate before it is chosen rather
than after.

**The fallback is not neutral, and `v0.35.141` stopped this docstring implying it
is.**  Where the redirect declines on an origin distinct from the answered caller,
falling back *transfers* the reservation to that answered caller — see
`donationOriginRebindable` for the reachable sequence and the registered closure.
The fallback is right on the other three arms (not at the bottom; no origin
recorded; an origin that is the answered caller), where the reachability answer
and the recorded owner are the same thread.

It is **not** keyed on the answered caller.  A `some` answer is the recorded
origin whether or not it coincides with the thread the reply answers, and at
depth 1 it always does: the first push records the client, and the depth-1 pop
hands the context back to that same client, so the redirect is the identity and
`insertOrMerge` collapses the footprint member into `replyTargetTid`.  Stating it
the other way — `some` only when the two differ — would make the resolver's answer
depend on an argument the footprint does not have.

It **is** a claim that the origin resolves (`v0.35.61`, the post-landing audit).
`SchedContext.boundThread` is tied to no stored TCB by any invariant and neither
is this field, and both guards pass a thread that does not resolve (their
`_of_none` arms exist so that the *operation's* argument keeps its own error
code) -- so as first landed a recorded origin naming no thread was answered as a
candidate and the pop's own lookup refused it with `.objectNotFound`: a refusal,
on exactly the shape this resolver's own contract says falls back.  Unreachable
today, because objects are never erased and `clearDonationOriginReferences`
clears the field when the thread it names is retyped -- but a contract the code
does not decide is one a later cut can break silently.  The resolver therefore
resolves the origin through `lookupTcb` before it consults either guard
(`donationOriginRecipient?_resolves`), and `replyDonationRecipient_resolves` is
what the pop has as a consequence: whenever the answered caller resolves, so does
the recipient. -/
def donationOriginRecipient? (st : SystemState) (scId : SeLe4n.SchedContextId) :
    Option SeLe4n.ThreadId :=
  match replyStackOuterCaller? st scId with
  | .ok none =>
    match (st.getSchedContext? scId).bind (·.donationOrigin) with
    | none => none
    | some origin =>
      -- **`v0.35.61` (post-landing audit): a candidate is a thread that
      -- RESOLVES.**  Both guards below pass a thread with no TCB (their
      -- `_of_none` arms), so without this the pop's own `lookupTcb` was what
      -- met a stale origin -- as `.objectNotFound`, a refusal on the one shape
      -- this resolver exists to make a *fallback*.  Resolving first is what
      -- makes "a stale origin falls back" a fact about the resolver rather than
      -- about which stale origins the tree happens to reach.
      match lookupTcb st origin with
      | none => none
      | some _ =>
        -- **WS-HP HP10.7**: both guards, and the second is not defence in
        -- depth.  `donationRecipientAcceptable` asks that the origin hold no
        -- binding of its own; `donationOriginRebindable` asks that no *other*
        -- thread's binding names it as owner, which the first cannot see and
        -- which a redirect would otherwise falsify.  See
        -- `donationOriginRebindable` for the reachable sequence that needs it.
        if donationRecipientAcceptable st origin && donationOriginRebindable st origin then
          some origin
        else none
  | _ => none

/-- WS-HP HP10.6: **silent wherever the loan is still travelling outward.**  The
`some outer` arm of the pop hands the context to the answered caller and records
`outer` as the thread it is still owed to, so the chain's own structure names the
recipient and the recorded origin is further out still. -/
@[simp] theorem donationOriginRecipient?_of_outer_some (st : SystemState)
    (scId : SeLe4n.SchedContextId) (outer : SeLe4n.ThreadId)
    (h : replyStackOuterCaller? st scId = .ok (some outer)) :
    donationOriginRecipient? st scId = none := by
  unfold donationOriginRecipient?; rw [h]

/-- WS-HP HP10.6: **and wherever the stack walk refuses.**  A refused resolution
refuses the pop (`returnDonatedSchedContextResolved`), so there is no recipient to
redirect. -/
@[simp] theorem donationOriginRecipient?_of_outer_error (st : SystemState)
    (scId : SeLe4n.SchedContextId) (e : KernelError)
    (h : replyStackOuterCaller? st scId = .error e) :
    donationOriginRecipient? st scId = none := by
  unfold donationOriginRecipient?; rw [h]

/-- WS-HP HP10.6: **silent on a context that records no origin**, which is every
context in a tree with no donation, and every one whose loan has ended — the pop's
bottom arm, both `schedContextBind`/`Unbind` spellings and both
`cancelBoundDonation` spellings all clear the field (HP10.4). -/
@[simp] theorem donationOriginRecipient?_of_no_origin (st : SystemState)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc) (hNone : sc.donationOrigin = none) :
    donationOriginRecipient? st scId = none := by
  unfold donationOriginRecipient?
  cases hOuter : replyStackOuterCaller? st scId with
  | error e => rfl
  | ok outer? =>
    cases outer? with
    | some outer => rfl
    | none => simp only [hSc, Option.bind_some, hNone]

/-- WS-HP HP10.6: **and on a context that does not resolve at all** — reached
through the walk, which refuses such a context outright. -/
@[simp] theorem donationOriginRecipient?_of_no_sc (st : SystemState)
    (scId : SeLe4n.SchedContextId) (hSc : st.getSchedContext? scId = none) :
    donationOriginRecipient? st scId = none :=
  donationOriginRecipient?_of_outer_error st scId .objectNotFound
    (by unfold replyStackOuterCaller?; rw [hSc])

/-- **WS-HP HP10.6: what a `some` answer means, once.**

The four facts every consumer needs — the pop is at the bottom of its stack, the
context records this thread as the reservation's origin, that thread already
passes the guards the pop will apply, and it **resolves** — stated as one
characterisation rather than as four case analyses over the same match.  The
footprint reads the second (the member is the recorded origin, not a thread that
merely passes a guard), the flip reads the third (a redirected recipient never
trips HP4.6's check), the size bound reads the first through
`replyStackBelowHead?_of_originRecipient`, and the no-refusal fact
`replyDonationRecipient_resolves` reads the fourth. -/
theorem donationOriginRecipient?_eq_some_iff (st : SystemState)
    (scId : SeLe4n.SchedContextId) (o : SeLe4n.ThreadId) :
    donationOriginRecipient? st scId = some o
      ↔ (replyStackOuterCaller? st scId = .ok none
          ∧ (∃ sc, st.getSchedContext? scId = some sc ∧ sc.donationOrigin = some o)
          ∧ donationRecipientAcceptable st o = true
          ∧ donationOriginRebindable st o = true
          ∧ ∃ tcb, lookupTcb st o = some tcb) := by
  unfold donationOriginRecipient?
  constructor
  · intro h
    revert h
    cases hOuter : replyStackOuterCaller? st scId with
    | error e => intro hc; cases hc
    | ok outer? =>
      cases outer? with
      | some outer => intro hc; cases hc
      | none =>
        simp only []
        cases hSc : st.getSchedContext? scId with
        | none => simp only [Option.bind_none]; intro hc; cases hc
        | some sc =>
          simp only [Option.bind_some]
          cases hOrigin : sc.donationOrigin with
          | none => intro hc; cases hc
          | some origin =>
            dsimp only
            cases hLk : lookupTcb st origin with
            | none => intro hc; cases hc
            | some tcb =>
              dsimp only
              by_cases hOk : donationRecipientAcceptable st origin = true
                  ∧ donationOriginRebindable st origin = true
              · rw [if_pos (by simp [hOk.1, hOk.2])]
                intro hEq
                have hoe : origin = o := Option.some.inj hEq
                subst hoe
                -- `cases` generalised both scrutinees, so the characterisation's
                -- first two components are already discharged in the goal.
                exact ⟨trivial, ⟨sc, rfl, hOrigin⟩, hOk.1, hOk.2, tcb, hLk⟩
              · rw [if_neg (by
                  simp only [Bool.and_eq_true, not_and] at hOk ⊢
                  intro h1; exact hOk h1)]
                intro hc; cases hc
  · intro ⟨hOuter, ⟨sc, hSc, hOrigin⟩, hOk, hReb, ⟨tcb, hLk⟩⟩
    rw [hOuter]
    dsimp only
    simp only [hSc, Option.bind_some, hOrigin, hLk]
    exact if_pos (by simp [hOk, hReb])

/-- WS-HP HP10.6: **a `some` answer is the field's own value.**  The footprint
declares a lock on the thread the pop will write, not on one that merely passes a
guard, and this is what ties the two. -/
theorem donationOriginRecipient?_eq_donationOrigin (st : SystemState)
    {scId : SeLe4n.SchedContextId} {o : SeLe4n.ThreadId}
    (h : donationOriginRecipient? st scId = some o) :
    ∃ sc, st.getSchedContext? scId = some sc ∧ sc.donationOrigin = some o :=
  ((donationOriginRecipient?_eq_some_iff st scId o).mp h).2.1

/-- WS-HP HP10.6: **and it has already passed the pop's own recipient guard.**
HP4.6's check is applied to the *candidate* here rather than to the operation's
argument, so the redirect can fall back instead of refusing; this is the half the
flip consumes — a redirected recipient never trips the guard it is about to face. -/
theorem donationOriginRecipient?_acceptable (st : SystemState)
    {scId : SeLe4n.SchedContextId} {o : SeLe4n.ThreadId}
    (h : donationOriginRecipient? st scId = some o) :
    donationRecipientAcceptable st o = true :=
  ((donationOriginRecipient?_eq_some_iff st scId o).mp h).2.2.1

/-- WS-HP HP10.7: **and it may be rebound without invalidating a live donation.**
The second half of the redirect's guard — see `donationOriginRebindable` for the
reachable sequence in which the first half alone is not enough. -/
theorem donationOriginRecipient?_rebindable (st : SystemState)
    {scId : SeLe4n.SchedContextId} {o : SeLe4n.ThreadId}
    (h : donationOriginRecipient? st scId = some o) :
    donationOriginRebindable st o = true :=
  ((donationOriginRecipient?_eq_some_iff st scId o).mp h).2.2.2.1

/-- **`v0.35.61`: and it resolves.**  The fourth component of the
characterisation — a candidate is a thread the pop's own `lookupTcb` will find, so
the redirect can never turn a reply that succeeded into `.objectNotFound`; the
resolver declines a stale origin instead, and the pop falls back.  The no-refusal
fact `replyDonationRecipient_resolves` is stated over this. -/
theorem donationOriginRecipient?_resolves (st : SystemState)
    {scId : SeLe4n.SchedContextId} {o : SeLe4n.ThreadId}
    (h : donationOriginRecipient? st scId = some o) :
    ∃ tcb, lookupTcb st o = some tcb :=
  ((donationOriginRecipient?_eq_some_iff st scId o).mp h).2.2.2.2

/-- WS-HP HP10.6: **and the pop it redirects is at the bottom of its stack.**  The
first component of the characterisation, named because it is the one the footprint
arithmetic consumes. -/
theorem donationOriginRecipient?_outer_none (st : SystemState)
    {scId : SeLe4n.SchedContextId} {o : SeLe4n.ThreadId}
    (h : donationOriginRecipient? st scId = some o) :
    replyStackOuterCaller? st scId = .ok none :=
  ((donationOriginRecipient?_eq_some_iff st scId o).mp h).1

/-- **WS-HP HP10.6: the origin member and the two below-head members are mutually
exclusive**, so the ceiling's raise costs the *reachable* footprint nothing.

The origin member is live only at the bottom of a stack, and at the bottom there is
no frame below the head to re-head and no outer caller to validate.  This is the
same shape HP3.1 used for the splice's member — declared ceiling `+1`, reachable
bounds unmoved — and it is what
`lockSet_endpointReplyRecvOnCore_size_le_eighteen` consumes. -/
theorem replyStackBelowHead?_of_originRecipient (st : SystemState)
    {scId : SeLe4n.SchedContextId} {o : SeLe4n.ThreadId}
    (h : donationOriginRecipient? st scId = some o) :
    replyStackBelowHead? st scId = (none, none) :=
  replyStackBelowHead?_of_outer_none st scId (donationOriginRecipient?_outer_none st h)

/-! ## WS-HP HP10.7: the reply path's bottom-of-stack recipient -/

/-- **WS-HP HP10.7: which thread a reply's pop hands the reservation to.**

The recorded origin where HP10.6's resolver answers one, and the answered caller
otherwise.  This is the whole of the depth-2 remedy: at the bottom of a reply
stack the pre-HP10.7 kernel handed the reservation to the thread *stack
reachability* names, and after an out-of-order removal that is the intermediate
caller rather than the client whose reservation it is.

**One definition, three call sites.**  `applyReplyDonation`,
`applyReplyDonationOnCore` and `replyRecvPopDonation` all read this, because
"which thread receives the context" is one question and two spellings of it are
free to drift — and these two *disagree* on exactly the states the phase exists
for, which is the worst case for a duplicate.

**Its scope is the reply path, and the declaration is what fixes that.**  All six
operational pops thread `returnDonatedSchedContextResolved`, and only the two
reply footprints declare an origin member (HP10.6), so putting the redirect in
that shared resolver would make `lockSet_endpointReceive`, `lockSet_replyRecv`'s
pre-return group, `lockSet_cancelIpcBlocking`, `lockSet_cancelDonation` and
`lockSet_tcbSuspendOnCore` **false** of their own transitions — a footprint that
omits a written object is false, and this project rates that worse than a wide
one.  It is also the right scope on the merits: the registered defect is the
reply path's, and the cancellation reclaim resolves its recipient off the
victim's own frame head (`cancelledCallerDonation?`), which is a different
question.  Widening the redirect is a cut that declares first.

**It is the identity wherever the resolver is silent**
(`replyDonationRecipient_eq_of_no_origin`), which is every state reachable before
HP10.4 recorded an origin and every `some`-arm pop after it — the loan is still
travelling outward there, so the surviving stack names the recipient and the
origin is further out still.  That definitional equality is what carries every
pre-HP10.7 result across as a case split whose `none` branch is the old proof
verbatim. -/
def replyDonationRecipient (st : SystemState) (scId : SeLe4n.SchedContextId)
    (answeredCaller : SeLe4n.ThreadId) : SeLe4n.ThreadId :=
  (donationOriginRecipient? st scId).getD answeredCaller

/-- WS-HP HP10.7: **the identity wherever no origin is recorded or usable.**  The
definitional equality every pre-HP10.7 result crosses. -/
@[simp] theorem replyDonationRecipient_eq_of_no_origin (st : SystemState)
    (scId : SeLe4n.SchedContextId) (answeredCaller : SeLe4n.ThreadId)
    (h : donationOriginRecipient? st scId = none) :
    replyDonationRecipient st scId answeredCaller = answeredCaller := by
  unfold replyDonationRecipient; rw [h]; rfl

/-- WS-HP HP10.7: **and the recorded origin where there is one.** -/
@[simp] theorem replyDonationRecipient_eq_origin (st : SystemState)
    {scId : SeLe4n.SchedContextId} {answeredCaller o : SeLe4n.ThreadId}
    (h : donationOriginRecipient? st scId = some o) :
    replyDonationRecipient st scId answeredCaller = o := by
  unfold replyDonationRecipient; rw [h]; rfl

/-- WS-HP HP10.7: **the redirect is the identity on every `some`-arm pop.**

`donationOriginRecipient?` answers only at `replyStackOuterCaller? = .ok none`, so
a pop whose surviving stack still names an outer caller is untouched — which is
what confines this phase's behavioural change to the bottom of a stack. -/
theorem replyDonationRecipient_eq_of_outer_some (st : SystemState)
    (scId : SeLe4n.SchedContextId) (answeredCaller outer : SeLe4n.ThreadId)
    (h : replyStackOuterCaller? st scId = .ok (some outer)) :
    replyDonationRecipient st scId answeredCaller = answeredCaller :=
  replyDonationRecipient_eq_of_no_origin st scId answeredCaller
    (donationOriginRecipient?_of_outer_some st scId outer h)

/-- **WS-HP HP10.7: the redirect never introduces a refusal.**

The no-regression fact this phase owes: every reply that succeeded before the flip
still succeeds.  `returnDonatedSchedContext` refuses a recipient that fails
HP4.6's `donationRecipientAcceptable`, so a redirect that could hand it a thread
failing the guard would turn a working reply into `.invalidArgument` — and that is
precisely why HP10.6 applied the guard to the **candidate** rather than to the
operation's argument.  Either the redirect is the identity, and the hypothesis is
the conclusion, or it is the recorded origin, which
`donationOriginRecipient?_acceptable` has already checked. -/
theorem replyDonationRecipient_acceptable (st : SystemState)
    (scId : SeLe4n.SchedContextId) (answeredCaller : SeLe4n.ThreadId)
    (h : donationRecipientAcceptable st answeredCaller = true) :
    donationRecipientAcceptable st (replyDonationRecipient st scId answeredCaller) = true := by
  unfold replyDonationRecipient
  cases hOrigin : donationOriginRecipient? st scId with
  | none => simpa using h
  | some o =>
    simp only [Option.getD_some]
    exact donationOriginRecipient?_acceptable st hOrigin

/-- **`v0.35.61`: and never a lookup failure either.**  `replyDonationRecipient_acceptable`
says the redirect never trips HP4.6's guard; this is the other refusal
`returnDonatedSchedContext` has for its recipient — its Step 3 `lookupTcb`,
`.objectNotFound` — and the resolver's own resolution check is what closes it:
whenever the answered caller resolves, the thread the pop actually rebinds does.
Either the redirect is the identity, and the witness is the caller's own, or it is
the recorded origin, which `donationOriginRecipient?_resolves` has already found. -/
theorem replyDonationRecipient_resolves (st : SystemState)
    (scId : SeLe4n.SchedContextId) {answeredCaller : SeLe4n.ThreadId} {tcb : TCB}
    (h : lookupTcb st answeredCaller = some tcb) :
    ∃ tcb', lookupTcb st (replyDonationRecipient st scId answeredCaller) = some tcb' := by
  unfold replyDonationRecipient
  cases hOrigin : donationOriginRecipient? st scId with
  | none => exact ⟨tcb, by simpa using h⟩
  | some o =>
    simp only [Option.getD_some]
    exact donationOriginRecipient?_resolves st hOrigin

/-- WS-HP HP10.7: **the redirected recipient is declared.**  HP10.6's footprint
member is `donationOriginRecipient? st scId`, and this says the thread the pop
actually writes is that one whenever the resolver answers — so the declaration and
the transition name the same TCB rather than merely both being present. -/
theorem replyDonationRecipient_mem_originRecipient (st : SystemState)
    {scId : SeLe4n.SchedContextId} {answeredCaller o : SeLe4n.ThreadId}
    (h : donationOriginRecipient? st scId = some o) :
    replyDonationRecipient st scId answeredCaller = o
      ∧ donationOriginRecipient? st scId = some (replyDonationRecipient st scId answeredCaller) := by
  have hEq := replyDonationRecipient_eq_origin st (answeredCaller := answeredCaller) h
  exact ⟨hEq, by rw [hEq]; exact h⟩

/-- WS-OD OD4.4: **the donation return with its new owner resolved from the state
it runs on.**

Every operational pop in this tree answers the same question before it runs —
*which thread does this scheduling context settle on?* — and the answer is
`replyStackOuterCaller?` of the very state the pop is applied to.  Six call sites
ask it (the reply return single-core and per-core, `.replyRecv`'s return leg, the
two pre-receive cleanups, the cancellation reclaim and thread destruction), so it
is answered **once**, here, rather than spelled out six times: a second spelling
is a second thing that can be given the wrong state, and the state is exactly
what is delicate — the reply leg consumes the target's reply link before the
return runs, which is why §3.3 makes the argument a pre-state resolution in the
first place.

**A refused resolution refuses the pop.**  `replyStackOuterCaller?`'s `.error`
means a stack link exists and does not validate — a Reply that has been re-linked
to a new caller, the confused deputy of plan §3.4.  Reading that as "bottom of
the stack" would settle a scheduling context that is still owed outward, on a
thread chosen by object reuse; so it propagates, and the pop commits nothing.

**Inert wherever the context heads no stack** (`_eq_legacy_of_no_stack`), which
is every state reachable before OD4.1's push and every depth-1 state after it. -/
def returnDonatedSchedContextResolved (st : SystemState)
    (serverTid : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId) : Except KernelError SystemState :=
  match replyStackOuterCaller? st scId with
  | .error e => .error e
  | .ok newOwner? => returnDonatedSchedContext st serverTid scId originalOwner newOwner?

/-- WS-OD OD4.4: **what a successful resolved return decomposes into** — the
resolver's answer, and the pop at that answer.  Every frame, field reading and
preservation theorem about the six call sites crosses this one hop. -/
theorem returnDonatedSchedContextResolved_ok_decompose
    {st st' : SystemState} {serverTid : SeLe4n.ThreadId}
    {scId : SeLe4n.SchedContextId} {originalOwner : SeLe4n.ThreadId}
    (h : returnDonatedSchedContextResolved st serverTid scId originalOwner = .ok st') :
    ∃ newOwner?, replyStackOuterCaller? st scId = .ok newOwner? ∧
      returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st' := by
  unfold returnDonatedSchedContextResolved at h
  revert h
  cases hRes : replyStackOuterCaller? st scId with
  | error e => intro hc; cases hc
  | ok newOwner? => intro hOk; exact ⟨newOwner?, rfl, hOk⟩

/-- WS-OD OD4.4: **any property the pop has at every `newOwner?` is a property of
the resolved return.**

The one-line bridge the frame lemmas of the six call sites cross.  Without it
each of them restates its frame at a fixed argument, which is the shape that made
them all break the day the argument stopped being fixed. -/
theorem returnDonatedSchedContextResolved_lift {P : SystemState → Prop}
    {st st' : SystemState} {serverTid : SeLe4n.ThreadId}
    {scId : SeLe4n.SchedContextId} {originalOwner : SeLe4n.ThreadId}
    (h : returnDonatedSchedContextResolved st serverTid scId originalOwner = .ok st')
    (hAll : ∀ (newOwner? : Option SeLe4n.ThreadId) (s : SystemState),
      returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok s → P s) :
    P st' := by
  obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose h
  exact hAll n st' hPop

/-- WS-OD OD4.4: and conversely — a resolver answer plus the pop at it *is* the
resolved return.  The direction a caller uses when it already knows what the
stack says. -/
theorem returnDonatedSchedContextResolved_of_resolved
    {st : SystemState} {serverTid : SeLe4n.ThreadId}
    {scId : SeLe4n.SchedContextId} {originalOwner : SeLe4n.ThreadId}
    {newOwner? : Option SeLe4n.ThreadId}
    (hRes : replyStackOuterCaller? st scId = .ok newOwner?) :
    returnDonatedSchedContextResolved st serverTid scId originalOwner =
      returnDonatedSchedContext st serverTid scId originalOwner newOwner? := by
  unfold returnDonatedSchedContextResolved; rw [hRes]

/-- WS-OD OD4.4: **inert on a context that heads no reply stack.**

The resolver answers `none` there (`replyStackOuterCaller?_of_no_stack`), so the
resolved return is the argument-`none` pop — which
`returnDonatedSchedContext_eq_legacy_of_none` in turn shows is the pre-OD3
operation store for store.  This is what makes threading the resolver a refactor
on every state the tree reached before OD4.1's push. -/
theorem returnDonatedSchedContextResolved_eq_legacy_of_no_stack
    (st : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc)
    (hNoHead : sc.scReply = none) :
    returnDonatedSchedContextResolved st serverTid scId originalOwner =
      returnDonatedSchedContext st serverTid scId originalOwner none :=
  returnDonatedSchedContextResolved_of_resolved
    (replyStackOuterCaller?_of_no_stack st scId sc hSc hNoHead)

-- **WS-RR RR8.12 follow-on (`v0.35.192`): `cleanupActiveDonation` is DELETED.**
--
-- Z7-E's alias for `returnDonatedSchedContext` — definitionally that function,
-- with the same five arguments in the same order — whose docstring described
-- "a server with a `.donated` binding blocking on receive without replying
-- first".  That scenario has a live implementation, and has had one since
-- AK1-A: `cleanupPreReceiveDonation` resolves the binding out of the receiver's
-- own TCB rather than taking it as three arguments a caller must already know,
-- `cleanupPreReceiveDonationChecked` propagates the failure a kernel path needs
-- surfaced, and `cleanupPreReceiveDonationMigrated` (WS-RR, `v0.35.161`) carries
-- the replenishment across cores.  The alias was superseded by all three and
-- consumed by nothing: no live path, no theorem, no suite, no gate.
--
-- The register row that scheduled the wire-or-retire judgement recorded the risk
-- of deleting part of a symmetric family; this one is not part of one — it is a
-- lone alias whose replacement family is three definitions wide.  The two X2-I
-- wrappers named in the same row were judged the other way and kept, with
-- witnesses: see `SeLe4n/Kernel/API.lean`.

-- ============================================================================
-- AN10 residual closure (H5–H6): typed entry-points for donation handlers
-- ============================================================================
-- Same wrapper pattern as the H1–H4 lifecycle handlers — provides a typed
-- entry-point that documents the dispatch-boundary discipline.  Wired
-- into production at:
--   * `applyCallDonation` (`Donation/Primitives.lean`) routes through
--     `donateSchedContextValid` via `ThreadId.toValid?` after the inner
--     `lookupTcb` lookups have already validated the ids.
--   * `applyReplyDonation` (`Donation/Primitives.lean`) routes through
--     `returnDonatedSchedContextValid` similarly.
--
-- Both production callers retain a raw-form fallback for observational
-- equivalence in proof contexts that cannot establish the
-- `lookupTcb = some _` witness; under the production invariants
-- (which the prior `lookupTcb` guards already establish), the fallback
-- branch is structurally unreachable.
--
-- The `cleanupPreReceiveDonation` / `cleanupPreReceiveDonationChecked`
-- helpers retain the raw `returnDonatedSchedContext` call to preserve
-- compatibility with the extensive frame-lemma infrastructure in
-- `IPC/Invariant/Defs.lean` / `EndpointPreservation.lean` /
-- `Structural/*.lean`.  Migrating those would cascade ~20 proof-surface
-- destructures; tracked under AN10-A.handler-internal-hygiene.

/-- AN10-H5: typed entry-point for `donateSchedContext`. -/
@[inline] def donateSchedContextValid (st : SystemState)
    (clientVtid serverVtid : SeLe4n.ValidThreadId)
    (clientScId : SeLe4n.SchedContextId) : Except KernelError SystemState :=
  donateSchedContext st clientVtid.val serverVtid.val clientScId

@[simp] theorem donateSchedContextValid_eq (st : SystemState)
    (clientVtid serverVtid : SeLe4n.ValidThreadId)
    (clientScId : SeLe4n.SchedContextId) :
    donateSchedContextValid st clientVtid serverVtid clientScId =
      donateSchedContext st clientVtid.val serverVtid.val clientScId := rfl

/-- AN10-H6: typed entry-point for `returnDonatedSchedContext`. -/
@[inline] def returnDonatedSchedContextValid (st : SystemState)
    (serverVtid : SeLe4n.ValidThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwnerVtid : SeLe4n.ValidThreadId)
    (newOwner? : Option SeLe4n.ThreadId) : Except KernelError SystemState :=
  returnDonatedSchedContext st serverVtid.val scId originalOwnerVtid.val newOwner?

@[simp] theorem returnDonatedSchedContextValid_eq (st : SystemState)
    (serverVtid : SeLe4n.ValidThreadId) (scId : SeLe4n.SchedContextId)
    (originalOwnerVtid : SeLe4n.ValidThreadId)
    (newOwner? : Option SeLe4n.ThreadId) :
    returnDonatedSchedContextValid st serverVtid scId originalOwnerVtid newOwner? =
      returnDonatedSchedContext st serverVtid.val scId originalOwnerVtid.val newOwner? := rfl

/-- **`v0.35.161` (register row 57): the context a pre-receive return POPS, with the
owner it settles back on — `cleanupPreReceiveDonationChecked`'s own guard, named.**

The two cleanups below decide whether to run `returnDonatedSchedContextResolved` by
reading the receiver through `lookupTcb` and matching its binding for
`.donated scId originalOwner`; this is that reading, so the pre-receive replenishment
migration (`preReceiveReturnMigration`, at the cross-core layer) fires on exactly the
states the pop fires on rather than on a proxy for them — *a proxy is not the fact*.
`endpointReplyDonation?` asks the same question of the store raw (`getTcb?`), which
is what a footprint resolver must do; the two agree on every receiver `lookupTcb`
resolves (`preReceiveDonation?_eq_endpointReplyDonation?_of_lookup`) and differ only
on a reserved id, where this one answers `none` — the pop's own answer, since
`lookupTcb` refuses a reserved id — and the footprint over-declares two members for a
migration that never runs.

The cleanups are **not** restated over it: their bodies are pinned by some forty
proofs that case on `lookupTcb` and the binding directly, and by a Tier 3 anchor on
the `Checked` variant's own match.  `cleanupPreReceiveDonationChecked_of_no_donation`
and `_of_donation` are the two characterisations that hold this reading and the
cleanups' to one answer. -/
def preReceiveDonation? (st : SystemState) (receiver : SeLe4n.ThreadId) :
    Option (SeLe4n.SchedContextId × SeLe4n.ThreadId) :=
  match lookupTcb st receiver with
  | some recvTcb =>
      match recvTcb.schedContextBinding with
      | .donated scId originalOwner => some (scId, originalOwner)
      | _ => none
  | none => none

/-- `v0.35.161`: the resolver at a receiver the store resolves as holding a loan. -/
theorem preReceiveDonation?_of_donated (st : SystemState) (receiver : SeLe4n.ThreadId)
    (recvTcb : TCB) (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hLk : lookupTcb st receiver = some recvTcb)
    (hB : recvTcb.schedContextBinding = .donated scId originalOwner) :
    preReceiveDonation? st receiver = some (scId, originalOwner) := by
  unfold preReceiveDonation?
  rw [hLk]
  simp only [hB]

/-- `v0.35.161`: and a `some` answer names a stored, `lookupTcb`-resolved TCB whose
binding is that loan — the direction the migration's own proofs consume. -/
theorem preReceiveDonation?_some_lookup (st : SystemState) (receiver : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (h : preReceiveDonation? st receiver = some (scId, originalOwner)) :
    ∃ recvTcb, lookupTcb st receiver = some recvTcb ∧
      recvTcb.schedContextBinding = .donated scId originalOwner := by
  unfold preReceiveDonation? at h
  cases hLk : lookupTcb st receiver with
  | none => rw [hLk] at h; cases h
  | some recvTcb =>
    simp only [hLk] at h
    cases hB : recvTcb.schedContextBinding with
    | donated scId' owner' =>
        rw [hB] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨recvTcb, rfl, hB⟩
    | unbound => rw [hB] at h; cases h
    | bound _ => rw [hB] at h; cases h

/-- AI4-A (M-01): Clean up stale donation before a server blocks on receive.

If the receiver has a `.donated` binding from a previous call that was never
replied to (abnormal path), return the SchedContext to the original owner
before blocking. Otherwise, return the state unchanged.

Moved from Donation.lean to Endpoint.lean to break the import cycle
(Donation.lean → Transport.lean → Core.lean → Operations.lean → Endpoint.lean).
This placement allows Transport.lean to call the function via its transitive
import chain.

AK1-A (I-H01): This is the defensive-fallback variant that absorbs any
`returnDonatedSchedContext` error by returning `st` unchanged. It is retained
for backward compatibility with the existing frame-lemma infrastructure in
`IPC/Invariant/Defs.lean`. Production code (`endpointReceiveDual`) must use
`cleanupPreReceiveDonationChecked` below to propagate errors per the
codebase's error-propagation policy (AJ1-A / AI4-A). Under `ipcInvariantFull`
the `.error` branch is unreachable — see
`cleanupPreReceiveDonationChecked_never_errors_under_ipcInvariantFull`. -/
def cleanupPreReceiveDonation (st : SystemState) (receiver : SeLe4n.ThreadId) : SystemState :=
  match lookupTcb st receiver with
  | none => st
  | some recvTcb =>
    match recvTcb.schedContextBinding with
    | .donated scId originalOwner =>
      -- **WS-OD OD4.4**: the resolver decides where the context settles here
      -- too.  Abandoning a call is not replying to it, but the *stack* question
      -- is the same one: the frame this pop clears is the abandoning server's
      -- own, and the thread the context is owed to is the caller of the frame
      -- below it.  At depth 1 that is `none` and this is the pre-OD4 behaviour.
      match returnDonatedSchedContextResolved st receiver scId originalOwner with
      | .error _ => st    -- Defensive fallback (used by frame lemmas only)
      | .ok st' => st'
    | _ => st             -- No donation to clean up

/-- AK1-A (I-H01 / HIGH): Error-propagating variant of `cleanupPreReceiveDonation`.

Production code (the `endpointReceiveDual` no-sender blocking path) uses this
variant so that a `returnDonatedSchedContext` failure surfaces as a kernel
error rather than being silently absorbed. The defensive-fallback
`cleanupPreReceiveDonation` is retained as a SystemState-returning helper so
that the existing frame-lemma/preservation-theorem infrastructure in
`IPC/Invariant/Defs.lean` / `EndpointPreservation.lean` / `Structural.lean`
continues to compose unchanged; a `.ok` result here coincides pointwise with
the defensive variant (see `cleanupPreReceiveDonationChecked_ok_eq_cleanup`
below).

Under `ipcInvariantFull`, the `.error` branch is formally unreachable because
the only internal failure paths inside `returnDonatedSchedContext` require
either a missing SchedContext/TCB or a mistyped object, all of which are
excluded by `donationOwnerValid` + `boundThreadConsistent` + `objects.invExt`.
This is discharged in
`cleanupPreReceiveDonationChecked_never_errors_under_ipcInvariantFull`. -/
def cleanupPreReceiveDonationChecked
    (st : SystemState) (receiver : SeLe4n.ThreadId) : Except KernelError SystemState :=
  match lookupTcb st receiver with
  | none => .ok st
  | some recvTcb =>
    match recvTcb.schedContextBinding with
    | .donated scId originalOwner =>
      -- **WS-OD OD4.4**: the resolved return, matching the defensive twin — the
      -- two must stay pointwise equal on `.ok`, so they resolve the same way.
      returnDonatedSchedContextResolved st receiver scId originalOwner
    | _ => .ok st             -- No donation to clean up

/-- AK1-A (I-H01): Bridge between the `Checked` variant and the defensive
fallback. On `.ok`, both variants return the same state. -/
theorem cleanupPreReceiveDonationChecked_ok_eq_cleanup
    (st st' : SystemState) (receiver : SeLe4n.ThreadId)
    (h : cleanupPreReceiveDonationChecked st receiver = .ok st') :
    cleanupPreReceiveDonation st receiver = st' := by
  unfold cleanupPreReceiveDonationChecked at h
  unfold cleanupPreReceiveDonation
  cases hLk : lookupTcb st receiver with
  | none =>
    simp only [hLk] at h ⊢
    exact Except.ok.inj h
  | some recvTcb =>
    simp only [hLk] at h ⊢
    cases hBind : recvTcb.schedContextBinding with
    | unbound =>
      simp only [hBind] at h ⊢
      exact Except.ok.inj h
    | bound _ =>
      simp only [hBind] at h ⊢
      exact Except.ok.inj h
    | donated scId owner =>
      simp only [hBind] at h ⊢
      -- WS-OD OD4.4: both variants now resolve the new owner, and they resolve
      -- it identically because they resolve it from the same state — which is
      -- why the case split is on the *resolved* composite rather than on the
      -- pop at a fixed argument.  Splitting on the pop at `none` would state
      -- the bridge only at the bottom of the stack.
      cases hRet : returnDonatedSchedContextResolved st receiver scId owner with
      | error e => rw [hRet] at h; cases h
      | ok st'' =>
        simp only [hRet] at h ⊢
        exact Except.ok.inj h

/-- AK1-A (I-H01): Symmetric bridge — on `.ok`, `cleanupPreReceiveDonation`
and the `Checked` variant agree. -/
theorem cleanupPreReceiveDonation_eq_cleanupChecked_ok
    (st st' : SystemState) (receiver : SeLe4n.ThreadId)
    (h : cleanupPreReceiveDonationChecked st receiver = .ok st') :
    st' = cleanupPreReceiveDonation st receiver :=
  (cleanupPreReceiveDonationChecked_ok_eq_cleanup st st' receiver h).symm

/-- **`v0.35.161`**: with no loan to return (`preReceiveDonation?` answers `none`),
the checked cleanup is the identity — one of the two characterisations that hold
the cleanup's own guard and its named reading to one answer. -/
theorem cleanupPreReceiveDonationChecked_of_no_donation
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (h : preReceiveDonation? st receiver = none) :
    cleanupPreReceiveDonationChecked st receiver = .ok st := by
  unfold preReceiveDonation? at h
  unfold cleanupPreReceiveDonationChecked
  cases hLk : lookupTcb st receiver with
  | none => rfl
  | some recvTcb =>
    simp only [hLk] at h
    simp only []
    cases hB : recvTcb.schedContextBinding with
    | donated scId owner => rw [hB] at h; cases h
    | unbound => rfl
    | bound _ => rfl

/-- **`v0.35.161`**: and with one, the checked cleanup **is** the resolved return of
that context to that owner — the other characterisation, and the one the
pre-receive replenishment migration's affinity proof crosses to reach the pop's
own frame lemmas. -/
theorem cleanupPreReceiveDonationChecked_of_donation
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (h : preReceiveDonation? st receiver = some (scId, originalOwner)) :
    cleanupPreReceiveDonationChecked st receiver
      = returnDonatedSchedContextResolved st receiver scId originalOwner := by
  obtain ⟨recvTcb, hLk, hB⟩ := preReceiveDonation?_some_lookup st receiver scId originalOwner h
  unfold cleanupPreReceiveDonationChecked
  rw [hLk]
  simp only [hB]

/-- AN3-E.5 (IPC-M09): compile-time guard — if `cleanupPreReceiveDonation`
or `cleanupPreReceiveDonationChecked` is relocated out of this file, this
example fails to elaborate and the build breaks.  The banner at the top of
this file explains why the functions must stay here.  DO NOT remove this
guard without also updating the banner. -/
private example : @cleanupPreReceiveDonation = @cleanupPreReceiveDonation := rfl
private example : @cleanupPreReceiveDonationChecked = @cleanupPreReceiveDonationChecked := rfl

/-- Z7: storeObject preserves the scheduler field.

**AN3-E.2 (IPC-M06) — INTENTIONALLY PRIVATE.** The donation path consumes
the general `storeObject_scheduler_eq_*` forms exported from
`Donation/Primitives.lean` and from the general-purpose preservation
layers. This `_z7` variant is an optimization used exclusively by
`returnDonatedSchedContext_scheduler_eq` below — a three-step sequence
of `storeObject` calls whose schedulerstability must be proved
compositionally without leaking `_z7` out as a user-facing API.
Promoting this helper to public would invite spurious callers; keeping
it file-private reflects its one-proof scope. See WH:Z7 for the
donation-atomicity context. -/
private theorem storeObject_scheduler_eq_z7 (st : SystemState) (oid : SeLe4n.ObjId)
    (obj : KernelObject) (pair : Unit × SystemState)
    (h : storeObject oid obj st = .ok pair) :
    pair.2.scheduler = st.scheduler := by
  unfold storeObject at h; cases h; rfl

/-- **WS-RR RR7.22 (residual, remediation)**: the donation return **is** three
`storeObject`s followed by a `scThreadIndex` update.

The one derivation every field frame for this operation is a corollary of.  Three
copies of its case analysis had accumulated — the scheduler frame here, the
machine frame in `Donation/Primitives.lean`, the serviceRegistry frame in
`Lifecycle/Invariant/SuspendPreservation.lean` — which is one question answered
in three places; they are now three-line consequences of this, and a fourth field
frame is three more lines rather than a fourth copy.

It is stated as a **complete** decomposition — the SchedContext read, the three
objects actually stored, and `st' = { s3 with scThreadIndex := st'.scThreadIndex }`
for the final step — rather than as a list of properties that happen to hold, so
every consequence (which fields of a TCB move, which objects survive, which state
fields agree) is a corollary rather than a fresh case analysis, and a field added
to `TCB` or `SystemState` is covered by construction. -/
theorem returnDonatedSchedContext_ok_storeChain
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    ∃ (sc : SchedContext) (head? : Option (SeLe4n.ReplyId × Reply))
      (clientTcb serverTcb : TCB) (s1 s2 s3 s4 : SystemState),
      st.objects[scId.toObjId]? = some (.schedContext sc) ∧
      -- WS-OD OD4.4: the outer-caller guard belongs here, not beside here.  This
      -- theorem is "what a successful pop tells you" — it already carries the
      -- context lookup and the head validation, neither of which is a store — so
      -- a decomposition that omitted the third precondition would be an
      -- incomplete description of the operation, and an incomplete description
      -- licenses conclusions the operation does not earn.
      outerCallerAcceptable st serverTid originalOwner newOwner? = true ∧
      -- **WS-HP HP4.6**: and the recipient guard, for the same reason — a
      -- successful pop witnesses that the thread it rewrote held no reservation
      -- of its own, which is what makes `donationBudgetTransfer` survive a
      -- recipient the operation did not read out of a binding.
      donationRecipientAcceptable st originalOwner = true ∧
      donationHeadOf? st scId sc = .ok head? ∧
      storeObject scId.toObjId
        (.schedContext (donationReturnSchedContext sc originalOwner
   (head?.bind (fun p => p.2.prev)) newOwner?)) st = .ok ((), s1) ∧
      storeDonationHeadPop scId head? s1 = .ok s2 ∧
      lookupTcb s2 originalOwner = some clientTcb ∧
      storeObject originalOwner.toObjId
        (.tcb { clientTcb with
                  schedContextBinding := donationReturnBinding scId newOwner? }) s2
          = .ok ((), s3) ∧
      lookupTcb s3 serverTid = some serverTcb ∧
      storeObject serverTid.toObjId
        (.tcb { serverTcb with schedContextBinding := .unbound }) s3 = .ok ((), s4) ∧
      st' = { s4 with scThreadIndex := st'.scThreadIndex } := by
  unfold returnDonatedSchedContext SystemState.getSchedContext? at h
  revert h
  cases hObj : st.objects[scId.toObjId]? with
  | none => intro h; cases h
  | some obj => cases obj with
    | schedContext sc =>
      simp only []
      split
      · intro h; cases h
      -- WS-OD OD4.4: peel the outer-caller guard; a refused outer caller commits
      -- nothing, so the `.ok` branch carries its verdict.
      cases hOuterOk : outerCallerAcceptable st serverTid originalOwner newOwner? with
      | false => simp only [Bool.not_false, if_true]; intro h; cases h
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      -- **WS-HP HP4.6**: peel the recipient guard the same way.
      cases hRecipOk : donationRecipientAcceptable st originalOwner with
      | false => simp only [Bool.not_false, if_true]; intro h; cases h
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      · cases hHead : donationHeadOf? st scId sc with
        | error _ => intro h; cases h
        | ok head? =>
          simp only []
          cases hS1 : storeObject scId.toObjId
              (.schedContext (donationReturnSchedContext sc originalOwner
   (head?.bind (fun p => p.2.prev)) newOwner?)) st with
          | error _ => intro h; cases h
          | ok p1 =>
            simp only []
            cases hS2 : storeDonationHeadPop scId head? p1.2 with
            | error _ => intro h; cases h
            | ok s2 =>
              simp only []
              cases hL1 : lookupTcb s2 originalOwner with
              | none => intro h; cases h
              | some clientTcb =>
                simp only []
                cases hS3 : storeObject originalOwner.toObjId
                    (.tcb { clientTcb with
                              schedContextBinding := donationReturnBinding scId newOwner? }) s2 with
                | error _ => intro h; cases h
                | ok p3 =>
                  simp only []
                  cases hL2 : lookupTcb p3.2 serverTid with
                  | none => intro h; cases h
                  | some serverTcb =>
                    simp only []
                    cases hS4 : storeObject serverTid.toObjId
                        (.tcb { serverTcb with schedContextBinding := .unbound }) p3.2 with
                    | error _ => intro h; cases h
                    | ok p4 =>
                      simp only []
                      intro h
                      cases h
                      exact ⟨sc, head?, clientTcb, serverTcb, p1.2, s2, p3.2, p4.2, rfl,
                        trivial, trivial, hHead, by rw [← hS1], hS2, hL1, by rw [← hS3],
                        hL2, by rw [← hS4], rfl⟩
    | _ => intro h; cases h

/-- WS-OD OD4.4: **a successful pop validated its outer caller.**

The guard's payoff, and the reason it is worth an O(1) read: the three structural
facts `donationOwnerValid` needs of a `.donated scId outer` binding — that `outer`
is a stored TCB which has given up its binding and waits on a reply, and that it
is neither of the two threads the pop rewrites — are now *consequences of the
operation succeeding*.  Before the guard they were hypotheses every consumer had
to carry, and on the reply path (where the answered caller has just been woken)
no consumer could discharge them.

Stated as its own corollary rather than folded into
`returnDonatedSchedContext_ok_storeChain`: the guard is an independent fact about
the operation, not a link of its store chain, and twenty-two consumers destructure
that chain by position. -/
theorem returnDonatedSchedContext_ok_outerAcceptable
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    outerCallerAcceptable st serverTid originalOwner newOwner? = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hOuterOk, _⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  exact hOuterOk

/-- **WS-HP HP4.6: a successful pop validated its recipient**, so every consumer
reads back that the thread the pop rebound held no reservation of its own. -/
theorem returnDonatedSchedContext_ok_recipientAcceptable
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    donationRecipientAcceptable st originalOwner = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hRecipOk, _⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  exact hRecipOk

/-- **WS-HP HP4.6 (the useful form): a successful pop's recipient was
`.unbound`.**  The fact `donationBudgetTransfer` needs of a recipient the
operation did not read out of a binding -- and the reason the head-driven trigger
cannot orphan a reservation the answered caller had acquired for itself. -/
theorem returnDonatedSchedContext_ok_recipient_unbound
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (tcb : TCB) (hLk : lookupTcb st originalOwner = some tcb) :
    tcb.schedContextBinding = .unbound := by
  have hOk := returnDonatedSchedContext_ok_recipientAcceptable st st' serverTid scId
    originalOwner newOwner? h
  rw [donationRecipientAcceptable_eq_of_some st originalOwner tcb hLk] at hOk
  -- `BEq SchedContextBinding` is hand-written (`SchedContext/Types.lean`), so the
  -- `==` is discharged by evaluation on the three constructors rather than
  -- through a `LawfulBEq` instance the type does not carry.
  revert hOk; cases tcb.schedContextBinding <;> simp [BEq.beq]

/-- **WS-HP HP5.2: a successful pop's server id is not reserved.**

`returnDonatedSchedContext` resolves the thread it unbinds through `lookupTcb`,
which refuses a reserved id -- so the refusal is a *consequence* of the pop
succeeding rather than a hypothesis its callers carry.

It is the head-driven trigger that makes this worth stating.  The binding-driven
resolvers read a thread out of a stored `schedContextBinding`, so the thread they
name is a thread the store holds by construction; `replyFrameHeadHolder?` reads a
scheduling context's `boundThread`, which no invariant in this tree ties to a
stored TCB at all.  So the cancellation reclaim can now name a holder that
resolves to nothing, or to a reserved id, and what rules those out is the pop
declining -- which is exactly what a consumer reads back here. -/
theorem returnDonatedSchedContext_ok_server_not_reserved
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    ¬ serverTid.isReserved := by
  obtain ⟨_, _, _, serverTcb, _, _, s3, _, _, _, _, _, _, _, _, _, hL2, _⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  exact lookupTcb_some_not_reserved s3 serverTid serverTcb hL2

/-- **`v0.35.183`**: and neither is its recipient.

The sibling of the fact above, at the other thread the pop resolves through
`lookupTcb`: the recipient's binding write reads it (`_ok_storeChain`'s `hL1`),
and `lookupTcb` refuses a reserved id, so a successful pop's recipient is
promotable.  Added beside the server's for register row 63, whose Z4-O proof
needs the recipient's *pre*-state binding and can only reach it through
`lookupTcb`. -/
theorem returnDonatedSchedContext_ok_recipient_not_reserved
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    ¬ originalOwner.isReserved := by
  obtain ⟨_, _, clientTcb, _, _, s2, _, _, _, _, _, _, _, _, hL1, _, _, _⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  exact lookupTcb_some_not_reserved s2 originalOwner clientTcb hL1

/-- **`v0.35.185`**: a successful pop's recipient is not its holder.

One thread has one binding, and the pop's own guard refuses a recipient that
holds any (`_ok_recipient_unbound`) — so a holder whose binding is *not*
`.unbound` cannot also be the recipient.  `hNotUnbound` is what every caller has:
the pop is reached through the `.donated` arm of a binding match.

Extracted at `v0.35.185` from the Z4-O preservation proof that first needed it,
because the destroy path's own `.donated` arm needs the same distinctness to read
the pop's per-thread characterisation, and a second copy of a four-line argument
is the duplication this project treats as debt. -/
theorem returnDonatedSchedContext_ok_recipient_ne_server
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId) (serverTcb : TCB)
    (hServer : st.getTcb? serverTid = some serverTcb)
    (hNotUnbound : serverTcb.schedContextBinding ≠ SchedContextBinding.unbound)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    originalOwner ≠ serverTid := by
  intro hEq
  have hNotResOwn : ¬ originalOwner.isReserved :=
    returnDonatedSchedContext_ok_recipient_not_reserved st st' serverTid scId originalOwner
      newOwner? h
  have hLk : lookupTcb st originalOwner = some serverTcb := by
    unfold lookupTcb
    rw [if_neg hNotResOwn, hEq]
    exact hServer
  exact hNotUnbound (returnDonatedSchedContext_ok_recipient_unbound st st' serverTid scId
    originalOwner newOwner? h serverTcb hLk)

/-- **WS-HP HP4.6 (the refusal): the pop declines a recipient that already holds a
binding**, committing nothing.  The direction that says the guard fires, stated
so a mutation which deletes it is visible: without the guard this state reaches
the store chain and overwrites a live binding. -/
theorem returnDonatedSchedContext_rejects_bound_recipient
    (st : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (sc : SchedContext) (tcb : TCB)
    (hSc : st.objects[scId.toObjId]? = some (.schedContext sc))
    (hBoundThread : sc.boundThread = some serverTid)
    (hOuter : outerCallerAcceptable st serverTid originalOwner newOwner? = true)
    (hLk : lookupTcb st originalOwner = some tcb)
    (hBound : tcb.schedContextBinding ≠ .unbound) :
    returnDonatedSchedContext st serverTid scId originalOwner newOwner?
      = .error .invalidArgument := by
  have hRecip : donationRecipientAcceptable st originalOwner = false := by
    rw [donationRecipientAcceptable_eq_of_some st originalOwner tcb hLk]
    -- Same hand-written `BEq`: evaluate on the constructor the hypothesis rules in.
    revert hBound; cases tcb.schedContextBinding <;> simp [BEq.beq]
  unfold returnDonatedSchedContext SystemState.getSchedContext?
  rw [hSc]
  simp only [hBoundThread, bne_self_eq_false, Bool.false_eq_true, if_false, hOuter,
    Bool.not_true, hRecip, Bool.not_false, if_true]

/-- WS-OD OD3.3: **at an empty reply stack the pop is the pre-OD3 operation,
store for store.**

The right-hand side is the pre-OD3 body verbatim — three `storeObject`s and the
`scThreadIndex` update, with the donor rebound `.bound` — written out *here*,
where the elaborator checks it against the live definition, rather than retained
as a second live definition the two could drift apart in.

This is the row that makes OD3 inert.  No transition in this tree writes
`SchedContext.scReply`, so `donationHeadOf?` answers `none` on every reachable
state, the head clear is the identity, the head write is idempotent, and
`replyStackOuterCaller?` answers `none` at every call site — so the operation's
behaviour is bit-identical to pre-OD3 until the push lands, and the push is the
only phase in this workstream that changes what the kernel does.

**WS-HP HP4.6**: the equation now carries the recipient guard as a hypothesis
rather than folding it into the right-hand side.  Either spelling is true; this
one keeps the right-hand side *exactly* the pre-OD3 body, which is what the
theorem is for — an equation whose right-hand side grows a guard every time the
operation does stops being a statement about the legacy shape.  The hypothesis is
discharged wherever the recipient is `.unbound`, which `donationOwnerValid` gives
at every call site that resolves it from a binding. -/
theorem returnDonatedSchedContext_eq_legacy_of_none
    (st : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (sc : SchedContext)
    (hSc : st.objects[scId.toObjId]? = some (.schedContext sc))
    (hNoHead : sc.scReply = none)
    -- **WS-HP HP10.4**: and no recorded reservation origin.  The bottom arm clears
    -- the origin — that is where the loan ends — so on a state carrying one the
    -- operation genuinely differs from the pre-OD3 body by that clear.  Stated as a
    -- hypothesis for the reason HP4.6 states the recipient guard as one: an
    -- equation whose right-hand side grows a field every time the operation does
    -- stops being a statement about the legacy shape.  Discharged on every state
    -- before a first donation records one, and by `bootSafeSchedContextCheck` at
    -- boot.
    (hNoOrigin : sc.donationOrigin = none)
    (hRecip : donationRecipientAcceptable st originalOwner = true) :
    returnDonatedSchedContext st serverTid scId originalOwner none =
      (if sc.boundThread != some serverTid then .error .invalidArgument
       else
         match storeObject scId.toObjId
             (.schedContext { sc with boundThread := some originalOwner }) st with
         | .error e => .error e
         | .ok ((), st1) =>
           match lookupTcb st1 originalOwner with
           | none => .error .objectNotFound
           | some clientTcb =>
             match storeObject originalOwner.toObjId
                 (.tcb { clientTcb with schedContextBinding := .bound scId }) st1 with
             | .error e => .error e
             | .ok ((), st2) =>
               match lookupTcb st2 serverTid with
               | none => .error .objectNotFound
               | some serverTcb =>
                 match storeObject serverTid.toObjId
                     (.tcb { serverTcb with schedContextBinding := .unbound }) st2 with
                 | .error e => .error e
                 | .ok ((), st3) =>
                   .ok { st3 with scThreadIndex :=
                     (scThreadIndexAdd
                       (scThreadIndexRemove st3.scThreadIndex scId serverTid)
                       scId originalOwner) }) := by
  have hSame : donationReturnSchedContext sc originalOwner
      ((none : Option (SeLe4n.ReplyId × Reply)).bind (fun p => p.2.prev)) none
      = { sc with boundThread := some originalOwner } := by
    show ({ sc with boundThread := some originalOwner,
                    scReply := (none : Option SeLe4n.ReplyId),
                    donationOrigin := (none : Option SeLe4n.ThreadId) } : SchedContext) = _
    rw [← hNoHead, ← hNoOrigin]
  unfold returnDonatedSchedContext SystemState.getSchedContext?
  rw [hSc]
  -- WS-OD OD4.4: at the bottom of the reply stack the outer-caller guard demands
  -- nothing, so it reduces away and the body is the pre-OD3 one exactly.
  -- **WS-HP HP4.6**: the recipient guard reduces away under its hypothesis.
  simp only [outerCallerAcceptable_none, hRecip, Bool.not_true, Bool.false_eq_true, if_false,
    donationHeadOf?_of_no_stack st scId sc hNoHead,
    storeDonationHeadPop_none, donationReturnBinding_none, hSame]

/-- WS-OD OD3.2: **the donation return's Reply frame.**

A Reply present before the pop is present after it, with at most its stack links
cleared — the head the context pointed at loses them, every other Reply is
untouched.  This replaces the pre-OD3 claim that the return writes no Reply,
which the head clear makes false. -/
theorem returnDonatedSchedContext_reply_rewrite
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (oid : SeLe4n.ObjId) (r : Reply)
    (hReply : st.objects[oid]? = some (.reply r)) :
    ∃ r', st'.objects[oid]? = some (.reply r') ∧ replyStackRewrite r' r := by
  obtain ⟨sc, head?, clientTcb, serverTcb, s1, s2, s3, s4,
    hSc, _, _, _hHead, hS1, hClear, hL1, hS3, hL2, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeDonationHeadPop_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  -- First write: a SchedContext, which lands on a key holding no Reply.
  have h1 : s1.objects[oid]? = some (.reply r) := by
    by_cases hk : oid = scId.toObjId
    · rw [hk, hSc] at hReply; cases hReply
    · rw [storeObject_objects_ne st s1 scId.toObjId oid _ hk hObjInv hS1]; exact hReply
  -- Second write: the head clear.  At the head key the stack links go; elsewhere nothing does.
  obtain ⟨r2, h2, hR2⟩ : ∃ r2, s2.objects[oid]? = some (.reply r2) ∧ replyStackRewrite r2 r :=
    storeDonationHeadPop_reply_rewrite hInv1 hClear oid r h1
  -- Third and fourth writes: TCB keys, which hold no Reply.
  have h3 : s3.objects[oid]? = some (.reply r2) := by
    by_cases hk : oid = originalOwner.toObjId
    · rw [hk, lookupTcb_some_objects s2 originalOwner clientTcb hL1] at h2; cases h2
    · rw [storeObject_objects_ne s2 s3 originalOwner.toObjId oid _ hk hInv2 hS3]; exact h2
  have h4 : s4.objects[oid]? = some (.reply r2) := by
    by_cases hk : oid = serverTid.toObjId
    · rw [hk, lookupTcb_some_objects s3 serverTid serverTcb hL2] at h3; cases h3
    · rw [storeObject_objects_ne s3 s4 serverTid.toObjId oid _ hk hInv3 hS4]; exact h3
  exact ⟨r2, by rw [hEq]; exact h4, hR2⟩

theorem storeObject_tcb_bindingRewrite (st s : SystemState) (id : SeLe4n.ObjId)
    (obj : KernelObject) (hInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok ((), s))
    (hDisj : ∀ t0, st.objects[id]? = some (.tcb t0) →
      ∃ t, obj = .tcb t ∧ tcbBindingRewrite t t0)
    (k : SeLe4n.ObjId) (t0 : TCB) (hk : st.objects[k]? = some (.tcb t0)) :
    ∃ t', s.objects[k]? = some (.tcb t') ∧ tcbBindingRewrite t' t0 := by
  by_cases hEq : k = id
  · subst hEq
    obtain ⟨t, hObjEq, hRw⟩ := hDisj t0 hk
    refine ⟨t, ?_, hRw⟩
    rw [← hObjEq]
    exact storeObject_objects_eq' st k obj ((), s) hInv hStore
  · exact ⟨t0, by
      rw [storeObject_objects_ne st s id k obj hEq hInv hStore]
      exact hk, tcbBindingRewrite.refl t0⟩

/-- **WS-RR RR7.22 (residual, remediation)**: the complete description of what the
donation return does to a TCB — exactly one field is rewritten, at every key.

Read off the operation's own decomposition, so every field a conjunct might
consume (`ipcState`, the queue links, `cpuAffinity`, `replyObject`,
`pendingReceiveReply`, `timeoutBudget`) follows by `rfl`, and a field added to
`TCB` is covered by construction.  The narrower per-field forms in this file are
corollaries. -/
theorem returnDonatedSchedContext_tcb_rewrite
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (k : SeLe4n.ObjId) (t0 : TCB) (hk : st.objects[k]? = some (.tcb t0)) :
    ∃ t', st'.objects[k]? = some (.tcb t') ∧ tcbBindingRewrite t' t0 := by
  obtain ⟨sc, head?, clientTcb, serverTcb, s1, s2, s3, s4,
    hSc, _, _, _hHead, hS1, hClear, hL1, hS3, hL2, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeDonationHeadPop_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  obtain ⟨t1, hk1, hR1⟩ := storeObject_tcb_bindingRewrite st s1 scId.toObjId _ hObjInv hS1
    (by intro u hu; rw [hSc] at hu; cases hu) k t0 hk
  -- WS-OD OD3.1: the head clear writes a Reply, so it is invisible to every TCB.
  have hk2 : s2.objects[k]? = some (.tcb t1) :=
    storeDonationHeadPop_tcb_eq hInv1 hClear k t1 hk1
  obtain ⟨t3, hk3, hR3⟩ := storeObject_tcb_bindingRewrite s2 s3 originalOwner.toObjId _ hInv2 hS3
    (by
      intro u hu
      have hEqU : clientTcb = u := by
        rw [lookupTcb_some_objects s2 originalOwner clientTcb hL1] at hu
        exact (KernelObject.tcb.inj (Option.some.inj hu))
      exact ⟨_, rfl, by rw [hEqU]; exact ⟨_, rfl⟩⟩) k t1 hk2
  obtain ⟨t4, hk4, hR4⟩ := storeObject_tcb_bindingRewrite s3 s4 serverTid.toObjId _ hInv3 hS4
    (by
      intro u hu
      have hEqU : serverTcb = u := by
        rw [lookupTcb_some_objects s3 serverTid serverTcb hL2] at hu
        exact (KernelObject.tcb.inj (Option.some.inj hu))
      exact ⟨_, rfl, by rw [hEqU]; exact ⟨_, rfl⟩⟩) k t3 hk3
  exact ⟨t4, by rw [hEq]; exact hk4, (hR4.trans hR3).trans hR1⟩

/-- WS-OD OD3.2: **the backward half of `returnDonatedSchedContext_tcb_rewrite`.**

A TCB in the post-state was a TCB in the pre-state with exactly its SchedContext
binding rewritten.  Every `_tcb_<field>_backward` frame in the IPC invariant
surface — the queue links, `ipcState`, `replyObject`, `timeoutBudget`,
`pendingReceiveReply`, `pendingMessage` — is this theorem plus one `rfl`, so a
field added to `TCB` is framed by construction rather than by a new copy of the
operation's case analysis. -/
theorem returnDonatedSchedContext_tcb_rewrite_backward
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (k : SeLe4n.ObjId) (t' : TCB) (hk : st'.objects[k]? = some (.tcb t')) :
    ∃ t0, st.objects[k]? = some (.tcb t0) ∧ tcbBindingRewrite t' t0 := by
  obtain ⟨sc, head?, clientTcb, serverTcb, s1, s2, s3, s4,
    hSc, _, _, _hHead, hS1, hClear, hL1, hS3, hL2, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeDonationHeadPop_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  have h4 : s4.objects[k]? = some (.tcb t') := by rw [hEq] at hk; exact hk
  -- Fourth write: the server's binding.
  obtain ⟨t3, hk3, hR3⟩ : ∃ t3, s3.objects[k]? = some (.tcb t3) ∧ tcbBindingRewrite t' t3 := by
    by_cases hEqK : k = serverTid.toObjId
    · subst hEqK
      have hStored : s4.objects[serverTid.toObjId]? = _ :=
        storeObject_objects_eq' s3 _ _ _ hInv3 hS4
      have hVal := KernelObject.tcb.inj (Option.some.inj (hStored.symm.trans h4))
      exact ⟨serverTcb, lookupTcb_some_objects s3 serverTid serverTcb hL2,
        ⟨_, hVal.symm⟩⟩
    · exact ⟨t', (storeObject_objects_ne s3 s4 serverTid.toObjId k _ hEqK hInv3 hS4).symm.trans h4,
        tcbBindingRewrite.refl t'⟩
  -- Third write: the client's binding.
  obtain ⟨t2, hk2, hR2⟩ : ∃ t2, s2.objects[k]? = some (.tcb t2) ∧ tcbBindingRewrite t3 t2 := by
    by_cases hEqK : k = originalOwner.toObjId
    · subst hEqK
      have hStored : s3.objects[originalOwner.toObjId]? = _ :=
        storeObject_objects_eq' s2 _ _ _ hInv2 hS3
      have hVal := KernelObject.tcb.inj (Option.some.inj (hStored.symm.trans hk3))
      exact ⟨clientTcb, lookupTcb_some_objects s2 originalOwner clientTcb hL1,
        ⟨_, hVal.symm⟩⟩
    · exact ⟨t3,
        (storeObject_objects_ne s2 s3 originalOwner.toObjId k _ hEqK hInv2 hS3).symm.trans hk3,
        tcbBindingRewrite.refl t3⟩
  -- Second write: the head clear, invisible to every TCB.
  have hk1 : s1.objects[k]? = some (.tcb t2) := storeDonationHeadPop_tcb_backward hInv1 hClear k t2 hk2
  -- First write: the SchedContext, which lands on a key holding no TCB.
  have hk0 : st.objects[k]? = some (.tcb t2) := by
    by_cases hEqK : k = scId.toObjId
    · subst hEqK
      have hStored : s1.objects[scId.toObjId]? = _ :=
        storeObject_objects_eq' st _ _ _ hObjInv hS1
      cases hStored.symm.trans hk1
    · exact (storeObject_objects_ne st s1 scId.toObjId k _ hEqK hObjInv hS1).symm.trans hk1
  exact ⟨t2, hk0, hR3.trans hR2⟩

/-- **WS-OD OD3.5: the pop leaves every TCB but its two rewrite targets
verbatim.**

`returnDonatedSchedContext_tcb_rewrite` beside this says that *every* TCB
survives with at most its `schedContextBinding` changed, which is what the
invariant surface needs.  A **footprint** argument needs the other reading: away
from the two threads the pop names, the stored TCB is not merely of the same
shape, it is the same object — so no undeclared TCB is written at all.

The two are different statements and neither implies the other: `tcbBindingRewrite`
permits a binding change at any key, and this permits no change at these keys.
Derived from the one decomposition (`_ok_storeChain`) rather than from a second
reading of the operation, so a fifth store cannot satisfy both.

The non-TCB stores drop out by kind: the SchedContext key holds a
`.schedContext` in the pre-state and the stack head a `.reply`, so neither can
alias a key the hypothesis says holds a `.tcb`. -/
theorem returnDonatedSchedContext_other_tcb_eq
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (k : SeLe4n.ObjId) (t0 : TCB)
    (hkOwner : k ≠ originalOwner.toObjId) (hkServer : k ≠ serverTid.toObjId)
    (hPre : st.objects[k]? = some (.tcb t0)) :
    st'.objects[k]? = some (.tcb t0) := by
  obtain ⟨sc, head?, clientTcb, serverTcb, s1, s2, s3, s4,
    hSc, _, _, _hHead, hS1, hClear, _hL1, hS3, _hL2, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  -- The SchedContext key holds a `.schedContext`, so it is not `k`.
  have hkSc : k ≠ scId.toObjId := by
    intro hEqK
    rw [hEqK, hSc] at hPre
    exact absurd hPre (by simp)
  have h1 : s1.objects[k]? = st.objects[k]? :=
    storeObject_objects_ne st s1 _ k _ hkSc hObjInv hS1
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have h2 : s2.objects[k]? = s1.objects[k]? := by
    have hT1 : s1.objects[k]? = some (.tcb t0) := by rw [h1]; exact hPre
    rw [storeDonationHeadPop_tcb_eq hInv1 hClear k t0 hT1, hT1]
  have hInv2 : s2.objects.invExt := storeDonationHeadPop_preserves_objects_invExt hInv1 hClear
  have h3 : s3.objects[k]? = s2.objects[k]? :=
    storeObject_objects_ne s2 s3 _ k _ hkOwner hInv2 hS3
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  have h4 : s4.objects[k]? = s3.objects[k]? :=
    storeObject_objects_ne s3 s4 _ k _ hkServer hInv3 hS4
  have hObjEq : st'.objects = s4.objects := by rw [hEq]
  rw [hObjEq, h4, h3, h2, h1, hPre]

/-- WS-OD OD3.2: **what the donation return leaves in each TCB's binding.**

The trichotomy the invariant surface reads: the server is unbound, the thread the
context goes back to carries `donationReturnBinding scId newOwner?` — `.bound
scId` at the bottom of the stack, `.donated scId outer` one level up, which is
the widening the chain needs — and every other thread keeps the binding it had.

Stated at the *general* `newOwner?` rather than at `none`, so the depth-≥ 2
arm's frame existed before OD4 made it reachable -- the order the plan's
numbering rule requires, and what let OD4.1 land without re-deriving it. -/
theorem returnDonatedSchedContext_tcb_binding_cases
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (k : SeLe4n.ObjId) (t' : TCB) (hk : st'.objects[k]? = some (.tcb t')) :
    (k = serverTid.toObjId → t'.schedContextBinding = .unbound) ∧
    (k ≠ serverTid.toObjId → k = originalOwner.toObjId →
      t'.schedContextBinding = donationReturnBinding scId newOwner?) ∧
    (k ≠ serverTid.toObjId → k ≠ originalOwner.toObjId →
      ∃ t0, st.objects[k]? = some (.tcb t0) ∧
        t0.schedContextBinding = t'.schedContextBinding) := by
  obtain ⟨sc, head?, clientTcb, serverTcb, s1, s2, s3, s4,
    hSc, _, _, _hHead, hS1, hClear, hL1, hS3, hL2, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeDonationHeadPop_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  have h4 : s4.objects[k]? = some (.tcb t') := by rw [hEq] at hk; exact hk
  refine ⟨?_, ?_, ?_⟩
  · intro hKs
    subst hKs
    have hStored : s4.objects[serverTid.toObjId]? = _ :=
      storeObject_objects_eq' s3 _ _ _ hInv3 hS4
    rw [← KernelObject.tcb.inj (Option.some.inj (hStored.symm.trans h4))]
  · intro hKs hKo
    have h3 : s3.objects[k]? = some (.tcb t') :=
      (storeObject_objects_ne s3 s4 serverTid.toObjId k _ hKs hInv3 hS4).symm.trans h4
    subst hKo
    have hStored : s3.objects[originalOwner.toObjId]? = _ :=
      storeObject_objects_eq' s2 _ _ _ hInv2 hS3
    rw [← KernelObject.tcb.inj (Option.some.inj (hStored.symm.trans h3))]
  · intro hKs hKo
    have h3 : s3.objects[k]? = some (.tcb t') :=
      (storeObject_objects_ne s3 s4 serverTid.toObjId k _ hKs hInv3 hS4).symm.trans h4
    have h2 : s2.objects[k]? = some (.tcb t') :=
      (storeObject_objects_ne s2 s3 originalOwner.toObjId k _ hKo hInv2 hS3).symm.trans h3
    have h1 : s1.objects[k]? = some (.tcb t') :=
      storeDonationHeadPop_tcb_backward hInv1 hClear k t' h2
    by_cases hEqK : k = scId.toObjId
    · subst hEqK
      have hStored : s1.objects[scId.toObjId]? = _ :=
        storeObject_objects_eq' st _ _ _ hObjInv hS1
      cases hStored.symm.trans h1
    · exact ⟨t', (storeObject_objects_ne st s1 scId.toObjId k _ hEqK hObjInv hS1).symm.trans h1,
        rfl⟩

/-- WS-OD OD3.2: **the object kinds the donation return can write.**

The pop stores a SchedContext (the rebind and the stack pop), a Reply (the head
clear) and two TCBs (the two bindings) — and nothing else.  Named here rather
than spelled as three inequalities at each of the frames below, so that a store
of a *fifth* kind is one edit at this definition and a failing proof at every
frame, instead of a silent hole in each copy of the same three inequalities. -/
def donationReturnWritesKind : KernelObject → Prop
  | .schedContext _ => True
  | .reply _ => True
  | .tcb _ => True
  | _ => False

instance (o : KernelObject) : Decidable (donationReturnWritesKind o) := by
  cases o <;> unfold donationReturnWritesKind <;> infer_instance

@[simp] theorem donationReturnWritesKind_notification (n : Notification) :
    ¬ donationReturnWritesKind (.notification n) := id

@[simp] theorem donationReturnWritesKind_endpoint (e : Endpoint) :
    ¬ donationReturnWritesKind (.endpoint e) := id

@[simp] theorem donationReturnWritesKind_cnode (c : CNode) :
    ¬ donationReturnWritesKind (.cnode c) := id

/-- WS-OD OD3.2: **the donation return moves only objects of the kinds it
writes.**

At every key whose post-state content is not a SchedContext, a Reply or a TCB,
the store is unchanged — so the notification, endpoint and CNode backward
transports in the IPC invariant surface are instances of one derivation rather
than one copy of the operation's case analysis each.

Read off `returnDonatedSchedContext_ok_storeChain`: each of the four writes lands
on a key that already held the kind it stores (the SchedContext read, the head
clear's own Reply read, and the two `lookupTcb`s), so a key holding anything else
afterwards was never a target. -/
theorem returnDonatedSchedContext_objects_backward_of_kind
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (oid : SeLe4n.ObjId) (o : KernelObject)
    (hKind : ¬ donationReturnWritesKind o)
    (hPost : st'.objects[oid]? = some o) :
    st.objects[oid]? = some o := by
  obtain ⟨sc, head?, clientTcb, serverTcb, s1, s2, s3, s4,
    hSc, _, _, _hHead, hS1, hClear, hL1, hS3, hL2, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeDonationHeadPop_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  have h4 : s4.objects[oid]? = some o := by
    rw [hEq] at hPost; exact hPost
  -- Fourth write: a TCB.  A key holding `o` afterwards is not the stored key.
  have h3 : s3.objects[oid]? = some o := by
    by_cases hk : oid = serverTid.toObjId
    · rw [hk, storeObject_objects_eq' s3 _ _ _ hInv3 hS4] at h4
      exact absurd (by rw [← Option.some.inj h4]; exact trivial) hKind
    · rw [← storeObject_objects_ne s3 s4 serverTid.toObjId oid _ hk hInv3 hS4]; exact h4
  -- Third write: a TCB.
  have h2 : s2.objects[oid]? = some o := by
    by_cases hk : oid = originalOwner.toObjId
    · rw [hk, storeObject_objects_eq' s2 _ _ _ hInv2 hS3] at h3
      exact absurd (by rw [← Option.some.inj h3]; exact trivial) hKind
    · rw [← storeObject_objects_ne s2 s3 originalOwner.toObjId oid _ hk hInv2 hS3]; exact h3
  -- Second write: the head clear, a Reply.
  have h1 : s1.objects[oid]? = some o :=
    storeDonationHeadPop_non_reply_backward hInv1 hClear oid o
      (fun r hr => by subst hr; exact hKind trivial) h2
  -- First write: a SchedContext.
  by_cases hk : oid = scId.toObjId
  · rw [hk, storeObject_objects_eq' st _ _ _ hObjInv hS1] at h1
    exact absurd (by rw [← Option.some.inj h1]; exact trivial) hKind
  · rw [← storeObject_objects_ne st s1 scId.toObjId oid _ hk hObjInv hS1]; exact h1

/-- WS-OD OD3.2: the forward direction of
`returnDonatedSchedContext_objects_backward_of_kind` — a notification, endpoint
or CNode in the pre-state is still there afterwards. -/
theorem returnDonatedSchedContext_objects_forward_of_kind
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (oid : SeLe4n.ObjId) (o : KernelObject)
    (hKind : ¬ donationReturnWritesKind o)
    (hPre : st.objects[oid]? = some o) :
    st'.objects[oid]? = some o := by
  obtain ⟨sc, head?, clientTcb, serverTcb, s1, s2, s3, s4,
    hSc, _, _, _hHead, hS1, hClear, hL1, hS3, hL2, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeDonationHeadPop_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  have h1 : s1.objects[oid]? = some o := by
    by_cases hk : oid = scId.toObjId
    · rw [hk, hSc] at hPre
      exact absurd (by rw [← Option.some.inj hPre]; exact trivial) hKind
    · rw [storeObject_objects_ne st s1 scId.toObjId oid _ hk hObjInv hS1]; exact hPre
  have h2 : s2.objects[oid]? = some o := by
    rw [storeDonationHeadPop_non_reply_eq hInv1 hClear oid
      (fun r hr => by rw [h1] at hr; cases hr; exact hKind trivial)]
    exact h1
  have h3 : s3.objects[oid]? = some o := by
    by_cases hk : oid = originalOwner.toObjId
    · rw [hk, lookupTcb_some_objects s2 originalOwner clientTcb hL1] at h2
      exact absurd (by rw [← Option.some.inj h2]; exact trivial) hKind
    · rw [storeObject_objects_ne s2 s3 originalOwner.toObjId oid _ hk hInv2 hS3]; exact h2
  have h4 : s4.objects[oid]? = some o := by
    by_cases hk : oid = serverTid.toObjId
    · rw [hk, lookupTcb_some_objects s3 serverTid serverTcb hL2] at h3
      exact absurd (by rw [← Option.some.inj h3]; exact trivial) hKind
    · rw [storeObject_objects_ne s3 s4 serverTid.toObjId oid _ hk hInv3 hS4]; exact h3
  rw [hEq]; exact h4

/-- WS-RR RR8.16 (`v0.35.199`): **the donation return is a `kindPreservingWrite`.**

Its whole store chain, composed: a SchedContext for a SchedContext, the head
pop's Reply-for-Reply, and two TCBs for two TCBs.  Register row 85's two bundle
frames consume exactly this, so the reply chain's lift is a `.trans` rather than
a fresh pointwise argument -- and the `.trans` is the content, since a key the
first store rewrote and a later one left alone is still a same-kind
replacement. -/
theorem returnDonatedSchedContext_kindPreservingWrite
    {st st' : SystemState} {serverTid : SeLe4n.ThreadId}
    {scId : SeLe4n.SchedContextId} {originalOwner : SeLe4n.ThreadId}
    {newOwner? : Option SeLe4n.ThreadId}
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    kindPreservingWrite st st' := by
  obtain ⟨sc, head?, clientTcb, serverTcb, s1, s2, s3, s4,
    hSc, _, _, _hHead, hS1, hClear, hL1, hS3, hL2, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  -- Step 1: the SchedContext rewrite.
  have hW1 : kindPreservingWrite st s1 :=
    storeObject_kindPreservingWrite hObjInv hS1 hSc rfl (by simp [KernelObject.objectType])
  have hInv1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  -- Step 2: the head pop, a Reply for a Reply.
  have hW2 : kindPreservingWrite s1 s2 := storeDonationHeadPop_kindPreservingWrite hInv1 hClear
  have hInv2 := storeDonationHeadPop_preserves_objects_invExt hInv1 hClear
  -- Step 3: the recipient's TCB.
  have hPre3 : s2.objects[originalOwner.toObjId]? = some (.tcb clientTcb) :=
    lookupTcb_some_objects s2 originalOwner clientTcb hL1
  have hW3 : kindPreservingWrite s2 s3 :=
    storeObject_kindPreservingWrite hInv2 hS3 hPre3 rfl (by simp [KernelObject.objectType])
  have hInv3 := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  -- Step 4: the holder's TCB.
  have hPre4 : s3.objects[serverTid.toObjId]? = some (.tcb serverTcb) :=
    lookupTcb_some_objects s3 serverTid serverTcb hL2
  have hW4 : kindPreservingWrite s3 s4 :=
    storeObject_kindPreservingWrite hInv3 hS4 hPre4 rfl (by simp [KernelObject.objectType])
  -- The `scThreadIndex` rewrite that closes the chain touches no object.
  have hLast : kindPreservingWrite s4 st' :=
    kindPreservingWrite.of_objects_eq (by rw [hEq])
  exact ((((hW1.trans hW2).trans hW3).trans hW4).trans hLast)

/-- WS-RR RR8.16 (`v0.35.199`): the donation return writes no CDT table.

Read off its own store chain, beside the transition, rather than from
`CrossSubsystem.lean`'s `returnDonatedSchedContext_preservesFieldsOutside`: that
module is downstream of every capability-side asker, so the bundle frame could
not reach it.  The two are the same fact at different strengths, and this is the
one the capability lift consumes. -/
theorem returnDonatedSchedContext_cdt_eq
    {st st' : SystemState} {serverTid : SeLe4n.ThreadId}
    {scId : SeLe4n.SchedContextId} {originalOwner : SeLe4n.ThreadId}
    {newOwner? : Option SeLe4n.ThreadId}
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    st'.cdt = st.cdt ∧ st'.cdtNodeSlot = st.cdtNodeSlot := by
  obtain ⟨sc, head?, clientTcb, serverTcb, s1, s2, s3, s4,
    _hSc, _, _, _hHead, hS1, hClear, _hL1, hS3, _hL2, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  have e1 := storeObject_cdt_eq st s1 _ _ hS1
  have e1' := storeObject_cdtNodeSlot_eq st s1 _ _ hS1
  have e2 := storeDonationHeadPop_cdt_eq hClear
  have e3 := storeObject_cdt_eq s2 s3 _ _ hS3
  have e3' := storeObject_cdtNodeSlot_eq s2 s3 _ _ hS3
  have e4 := storeObject_cdt_eq s3 s4 _ _ hS4
  have e4' := storeObject_cdtNodeSlot_eq s3 s4 _ _ hS4
  refine ⟨?_, ?_⟩
  · rw [hEq]; simp only
    rw [e4, e3, e2.1, e1]
  · rw [hEq]; simp only
    rw [e4', e3', e2.2, e1']

/-- WS-OD OD3.2: the donation return preserves the object store's extended
invariant.  Relocated off the store chain, where it was a fifth copy of the
operation's case analysis. -/
theorem returnDonatedSchedContext_preserves_objects_invExt'
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    st'.objects.invExt := by
  obtain ⟨_, _, _, _, s1, s2, s3, s4, _, _, _, _, hS1, hClear, _, hS3, _, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeDonationHeadPop_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  have hInv4 : s4.objects.invExt := storeObject_preserves_objects_invExt s3 s4 _ _ hInv3 hS4
  rw [hEq]; exact hInv4

/-- `v0.35.4`: the pop preserves the identity registry's well-formedness — five
`storeObject`s (the pop's own two included), each of which does. -/
theorem returnDonatedSchedContext_preserves_objectIndexSet_invExt
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (hSetInv : st.objectIndexSet.table.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    st'.objectIndexSet.table.invExt := by
  obtain ⟨_, _, _, _, s1, s2, s3, s4, _, _, _, _, hS1, hClear, _, hS3, _, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  have h1 := storeObject_preserves_objectIndexSet_invExt st s1 _ _ hSetInv hS1
  have h2 := storeDonationHeadPop_preserves_objectIndexSet_invExt h1 hClear
  have h3 := storeObject_preserves_objectIndexSet_invExt s2 s3 _ _ h2 hS3
  have h4 := storeObject_preserves_objectIndexSet_invExt s3 s4 _ _ h3 hS4
  rw [hEq]; exact h4

/-- `v0.35.4`: ...and its completeness. -/
theorem returnDonatedSchedContext_preserves_objectIndexSetComplete
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hSetInv : st.objectIndexSet.table.invExt)
    (hComplete : objectIndexSetComplete st)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    objectIndexSetComplete st' := by
  obtain ⟨_, _, _, _, s1, s2, s3, s4, _, _, _, _, hS1, hClear, _, hS3, _, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  have hInv1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 := storeDonationHeadPop_preserves_objects_invExt hInv1 hClear
  have hInv3 := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  have hSet1 := storeObject_preserves_objectIndexSet_invExt st s1 _ _ hSetInv hS1
  have hSet2 := storeDonationHeadPop_preserves_objectIndexSet_invExt hSet1 hClear
  have hSet3 := storeObject_preserves_objectIndexSet_invExt s2 s3 _ _ hSet2 hS3
  have c1 := storeObject_preserves_objectIndexSetComplete st s1 _ _ hObjInv hSetInv hComplete hS1
  have c2 := storeDonationHeadPop_preserves_objectIndexSetComplete hInv1 hSet1 c1 hClear
  have c3 := storeObject_preserves_objectIndexSetComplete s2 s3 _ _ hInv2 hSet2 c2 hS3
  have c4 := storeObject_preserves_objectIndexSetComplete s3 s4 _ _ hInv3 hSet3 c3 hS4
  intro oid hOid
  rw [hEq] at hOid ⊢
  exact c4 oid hOid

/-- WS-OD OD3.2: **the donation return frames every key it does not store at.**

The head key is existentially quantified in the chain, so it is named here as a
hypothesis over *whatever* the context's stack head was: a key that is neither
the context, nor either thread, nor the Reply the context headed, is untouched. -/
theorem returnDonatedSchedContext_objects_ne_stored
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (sc : SchedContext)
    (hSc : st.objects[scId.toObjId]? = some (.schedContext sc))
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (oid : SeLe4n.ObjId)
    (hNeSc : oid ≠ scId.toObjId)
    (hNeOwner : oid ≠ originalOwner.toObjId)
    (hNeServer : oid ≠ serverTid.toObjId)
    (hNeHead : ∀ rid : SeLe4n.ReplyId, sc.scReply = some rid → oid ≠ rid.toObjId)
    (hNeBelow : ∀ (rid : SeLe4n.ReplyId) (r : Reply) (below : SeLe4n.ReplyId),
      sc.scReply = some rid → st.getReply? rid = some r → r.prev = some below →
      oid ≠ below.toObjId) :
    st'.objects[oid]? = st.objects[oid]? := by
  obtain ⟨sc0, head?, _, _, s1, s2, s3, s4, hSc0, _, _, hHead, hS1, hClear, _, hS3, _, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  have hScEq : sc0 = sc := by
    rw [hSc0] at hSc; exact KernelObject.schedContext.inj (Option.some.inj hSc)
  subst hScEq
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeDonationHeadPop_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  have e1 := storeObject_objects_ne st s1 scId.toObjId oid _ hNeSc hObjInv hS1
  have e2 : s2.objects[oid]? = s1.objects[oid]? := by
    refine storeDonationHeadPop_objects_ne hInv1 hClear oid ?_ ?_
    · intro rid r hHeadEq
      exact hNeHead rid ((donationHeadOf?_ok_key st scId sc0 head? hHead).symm.trans
        (by rw [hHeadEq]; rfl))
    · intro rid r below hHeadEq hPrev
      have hKey : sc0.scReply = some rid :=
        (donationHeadOf?_ok_key st scId sc0 head? hHead).symm.trans (by rw [hHeadEq]; rfl)
      have hObjR := (donationHeadOf?_ok_resolves st scId sc0 rid r (by rw [hHead, hHeadEq])).1
      exact hNeBelow rid r below hKey ((SystemState.getReply?_eq_some_iff _ _ _).mpr hObjR) hPrev
  have e3 := storeObject_objects_ne s2 s3 originalOwner.toObjId oid _ hNeOwner hInv2 hS3
  have e4 := storeObject_objects_ne s3 s4 serverTid.toObjId oid _ hNeServer hInv3 hS4
  rw [hEq]
  show s4.objects[oid]? = st.objects[oid]?
  rw [e4, e3, e2, e1]

/-- WS-OD OD3.2: **the donation return frames every non-Reply key it does not
store at.**

The consumer-facing form of `returnDonatedSchedContext_objects_ne_stored`: the
head the pop clears is a Reply, so a key that holds anything else in the
pre-state cannot be it, and the caller supplies what it already knows about the
key's contents instead of resolving the context's stack head. -/
theorem returnDonatedSchedContext_objects_ne_of_not_reply
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (oid : SeLe4n.ObjId)
    (hNeSc : oid ≠ scId.toObjId)
    (hNeOwner : oid ≠ originalOwner.toObjId)
    (hNeServer : oid ≠ serverTid.toObjId)
    (hNotReply : ∀ r : Reply, st.objects[oid]? ≠ some (.reply r)) :
    st'.objects[oid]? = st.objects[oid]? := by
  obtain ⟨sc, head?, _, _, _, _, _, _, hSc, _, _, hHead, _, _, _, _, _, _, _⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  refine returnDonatedSchedContext_objects_ne_stored st st' serverTid scId originalOwner
    newOwner? sc hSc hObjInv h oid hNeSc hNeOwner hNeServer ?_ ?_
  · intro rid hRid hEqK
    have hKey := donationHeadOf?_ok_key st scId sc head? hHead
    rw [hRid] at hKey
    obtain ⟨p, hp, hpFst⟩ : ∃ p, head? = some p ∧ p.1 = rid := by
      cases head? with
      | none => cases hKey
      | some p => exact ⟨p, rfl, Option.some.inj hKey⟩
    subst hp
    obtain ⟨hObj, _⟩ := donationHeadOf?_ok_resolves st scId sc p.1 p.2 (by rw [hHead])
    exact hNotReply p.2 (by rw [hEqK, ← hpFst]; exact hObj)
  · intro rid r below hRid hRep hPrev hEqK
    obtain ⟨sc', head?', _, _, s1, _, _, _, hSc', _, _, hHead', hS1, hClear, _, _, _, _, _⟩ :=
      returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
    have hScEq : sc' = sc := by
      rw [hSc] at hSc'; exact (KernelObject.schedContext.inj (Option.some.inj hSc')).symm
    rw [hScEq] at hHead'
    have hHeadEq : head?' = head? := by rw [hHead'] at hHead; exact Except.ok.inj hHead
    subst hHeadEq
    have hKey := donationHeadOf?_ok_key st scId sc head?' hHead'
    rw [hRid] at hKey
    obtain ⟨p, hp, hpFst⟩ : ∃ p, head?' = some p ∧ p.1 = rid := by
      cases head?' with
      | none => cases hKey
      | some p => exact ⟨p, rfl, Option.some.inj hKey⟩
    subst hp
    obtain ⟨hObj, _⟩ := donationHeadOf?_ok_resolves st scId sc p.1 p.2 (by rw [hHead'])
    have hpSnd : p.2 = r := by
      rw [← hpFst] at hRep
      exact KernelObject.reply.inj (Option.some.inj
        (((SystemState.getReply?_eq_some_iff _ _ _).mp hRep).symm.trans hObj)).symm
    have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
    obtain ⟨b, hB⟩ := storeDonationHeadPop_ok_below_resolves hInv1 hClear p.1 p.2 below rfl
      (by rw [hpSnd]; exact hPrev)
    have hNeScBelow : below.toObjId ≠ scId.toObjId := by
      intro hEq
      have hAt : s1.objects[scId.toObjId]? = some (.reply b) := by rw [← hEq]; exact hB
      rw [storeObject_objects_eq' st scId.toObjId _ _ hObjInv hS1] at hAt
      cases hAt
    have hBPre : st.objects[below.toObjId]? = some (.reply b) := by
      rw [← storeObject_objects_ne st s1 scId.toObjId below.toObjId _ hNeScBelow hObjInv hS1]
      exact hB
    exact hNotReply b (by rw [hEqK]; exact hBPre)

/-- WS-OD OD3.1: **the complete description of the rebound SchedContext.**

The donation return writes the context exactly once, with `boundThread` set to
the original owner and `scReply` popped to the reply below the head it consumed.
Stating the whole record rather than one field keeps the two halves one
derivation: `returnDonatedSchedContext_post_boundThread` and
`returnDonatedSchedContext_post_scReply` are both corollaries, so a field added
to `SchedContext` is covered by construction rather than needing a third
theorem. -/
theorem returnDonatedSchedContext_post_schedContext
    (st st' : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    ∃ (sc : SchedContext) (head? : Option (SeLe4n.ReplyId × Reply)),
      st.objects[scId.toObjId]? = some (.schedContext sc) ∧
      st'.objects[scId.toObjId]? =
        some (.schedContext (donationReturnSchedContext sc originalOwner
   (head?.bind (fun p => p.2.prev)) newOwner?)) := by
  obtain ⟨sc, head?, clientTcb, serverTcb, s1, s2, s3, s4,
    hSc, _, _, hHead, hS1, hClear, hL1, hS3, hL2, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeDonationHeadPop_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  refine ⟨sc, head?, hSc, ?_⟩
  -- First write: the rebind and the pop.
  have e1 : s1.objects[scId.toObjId]? =
      some (.schedContext (donationReturnSchedContext sc originalOwner
   (head?.bind (fun p => p.2.prev)) newOwner?)) :=
    storeObject_objects_eq' st scId.toObjId _ _ hObjInv hS1
  -- Second write: the head clear, which lands on a Reply key, never a SchedContext one.
  have e2 : s2.objects[scId.toObjId]? = s1.objects[scId.toObjId]? :=
    storeDonationHeadPop_non_reply_eq hInv1 hClear scId.toObjId
      (fun r hr => by rw [e1] at hr; cases hr)
  -- Third and fourth writes: TCB keys, and a key holding a SchedContext is not one.
  have e3 : s3.objects[scId.toObjId]? = s2.objects[scId.toObjId]? := by
    refine storeObject_objects_ne s2 s3 originalOwner.toObjId scId.toObjId _ ?_ hInv2 hS3
    intro hEqK
    have hTcbAt : s2.objects[scId.toObjId]? = some (.tcb clientTcb) := by
      rw [hEqK]; exact lookupTcb_some_objects s2 originalOwner clientTcb hL1
    cases (e2.trans e1).symm.trans hTcbAt
  have e4 : s4.objects[scId.toObjId]? = s3.objects[scId.toObjId]? := by
    refine storeObject_objects_ne s3 s4 serverTid.toObjId scId.toObjId _ ?_ hInv3 hS4
    intro hEqK
    have hTcbAt : s3.objects[scId.toObjId]? = some (.tcb serverTcb) := by
      rw [hEqK]; exact lookupTcb_some_objects s3 serverTid serverTcb hL2
    cases (e3.trans (e2.trans e1)).symm.trans hTcbAt
  have hGet : st'.objects[scId.toObjId]? = s4.objects[scId.toObjId]? := by rw [hEq]
  rw [hGet, e4, e3, e2, e1]

/-- WS-OD OD3.1: the typed reading of `returnDonatedSchedContext_post_schedContext`
— the same fact through `SystemState.getSchedContext?`, which is the accessor the
invariant surface reads. -/
theorem returnDonatedSchedContext_post_getSchedContext?
    (st st' : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    ∃ (sc : SchedContext) (head? : Option (SeLe4n.ReplyId × Reply)),
      st.getSchedContext? scId = some sc ∧
      st'.getSchedContext? scId =
        some (donationReturnSchedContext sc originalOwner
   (head?.bind (fun p => p.2.prev)) newOwner?) := by
  obtain ⟨sc, head?, hPre, hPost⟩ :=
    returnDonatedSchedContext_post_schedContext st st' serverTid scId originalOwner hObjInv
      newOwner? h
  refine ⟨sc, head?, ?_, ?_⟩
  · unfold SystemState.getSchedContext?; rw [hPre]
  · unfold SystemState.getSchedContext?; rw [hPost]

/-- WS-RR RR2.9: after `returnDonatedSchedContext`, the rebound SchedContext's
`boundThread` is the **original owner** — the mirror of
`donateSchedContext_post_boundThread`, and the fact that makes the
replenishment migration's destination the owner's home core.

WS-OD OD3.1: the stored context now also carries the popped stack head, and the
statement is deliberately still about `boundThread` alone — the reply-stack half
is `returnDonatedSchedContext_post_scReply` below, so a consumer that cares about
one is not made to reason about the other. -/
theorem returnDonatedSchedContext_post_boundThread
    (st st' : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    ∃ sc', st'.getSchedContext? scId = some sc' ∧ sc'.boundThread = some originalOwner := by
  obtain ⟨sc, _head?, _hPre, hPost⟩ :=
    returnDonatedSchedContext_post_getSchedContext? st st' serverTid scId originalOwner hObjInv
      newOwner? h
  exact ⟨_, hPost, rfl⟩

/-- WS-OD OD3.1: **the pop is a pop** — after the donation return, the context's
reply-stack head is the reply *below* the one it consumed.

The half of `returnDonatedSchedContext_post_schedContext` OD4's push consumes: a
return at depth `n` leaves the context heading the stack of depth `n − 1`, so the
chain shortens by exactly one frame.  At depth 1 the head was the only entry and
`prev` is `none`, which is the pre-OD3 behaviour verbatim. -/
theorem returnDonatedSchedContext_post_scReply
    (st st' : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    ∃ (sc' : SchedContext) (head? : Option (SeLe4n.ReplyId × Reply)),
      st'.getSchedContext? scId = some sc' ∧
      sc'.scReply = head?.bind (fun p => p.2.prev) := by
  obtain ⟨sc, head?, _hPre, hPost⟩ :=
    returnDonatedSchedContext_post_getSchedContext? st st' serverTid scId originalOwner hObjInv
      newOwner? h
  exact ⟨_, head?, hPost, rfl⟩

/-- Helper: `storeObject` preserves the service registry. -/
theorem storeObject_serviceRegistry_eq
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.serviceRegistry = st.serviceRegistry := by
  unfold storeObject at hStore; cases hStore; rfl

/-- Z7-C: returnDonatedSchedContext only modifies objects — scheduler preserved. -/
theorem returnDonatedSchedContext_scheduler_eq
    (st st' : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    st'.scheduler = st.scheduler := by
  obtain ⟨_, _, _, _, s1, s2, s3, s4, _, _, _, _, h1, hClear, _, h3, _, h4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  rw [hEq]
  show s4.scheduler = st.scheduler
  rw [SeLe4n.Model.storeObject_scheduler_eq s3 s4 _ _ h4,
    SeLe4n.Model.storeObject_scheduler_eq s2 s3 _ _ h3,
    storeDonationHeadPop_scheduler_eq hClear,
    SeLe4n.Model.storeObject_scheduler_eq st s1 _ _ h1]

/-- **WS-RR RR7.22 (residual, remediation)**: the donation return preserves the
service registry.  Relocated here from `SuspendPreservation`, where it was a
private third copy of the case analysis above. -/
theorem returnDonatedSchedContext_serviceRegistry_eq
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    st'.serviceRegistry = st.serviceRegistry := by
  obtain ⟨_, _, _, _, s1, s2, s3, s4, _, _, _, _, h1, hClear, _, h3, _, h4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  rw [hEq]
  show s4.serviceRegistry = st.serviceRegistry
  rw [storeObject_serviceRegistry_eq s3 s4 _ _ h4, storeObject_serviceRegistry_eq s2 s3 _ _ h3,
    storeDonationHeadPop_serviceRegistry_eq hClear,
    storeObject_serviceRegistry_eq st s1 _ _ h1]

/-- WS-SM SM7.B: `returnDonatedSchedContext` only modifies `objects` and
`scThreadIndex` — the TLB-shootdown state is framed.  Mirrors the proof
structure of `returnDonatedSchedContext_scheduler_eq` (Z7-C); a link of
the `pendingBounded` bundle-carriage chain through the retype cleanup
pipeline. -/
theorem returnDonatedSchedContext_tlbShootdown_eq
    (st st' : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    st'.tlbShootdown = st.tlbShootdown := by
  -- WS-OD OD3.1: read off the operation's own decomposition rather than by a
  -- fourth copy of its case analysis, which is what the store chain exists for
  -- and what kept this frame from needing a fifth arm when the pop landed.
  obtain ⟨_, _, _, _, s1, s2, s3, s4, _, _, _, _, h1, hClear, _, h3, _, h4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  rw [hEq]
  show s4.tlbShootdown = st.tlbShootdown
  have hStore : ∀ (a b : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject),
      storeObject id obj a = .ok ((), b) → b.tlbShootdown = a.tlbShootdown := by
    intro a b id obj hS; unfold storeObject at hS; cases hS; rfl
  rw [hStore s3 s4 _ _ h4, hStore s2 s3 _ _ h3,
    storeDonationHeadPop_tlbShootdown_eq hClear, hStore st s1 _ _ h1]

/-- Signal a notification: wake one waiter or mark one pending badge.

**U5-J/U-M29: Wake-path pendingMessage overwrite**: When a waiter is present,
the wake path creates a badge-only `IpcMessage` and stores it in the waiter's
`pendingMessage` field via `storeTcbIpcStateAndMessage`. This unconditionally
overwrites any previous `pendingMessage` value. This is safe because:
1. `notificationWaiterConsistent` guarantees threads in the wait queue have
   `ipcState = .blockedOnNotification oid` — they entered via `notificationWait`
   which transitions from `.ready` without modifying `pendingMessage`.
2. The `storeTcbIpcStateAndMessage` call atomically sets both `ipcState := .ready`
   AND `pendingMessage := some badgeMsg`, so the overwrite is the intended
   delivery mechanism, not a loss of prior state.
AF5-A (AF-12): `pendingMessage = none` for waiting threads IS formally proven:
defined as `blockedThreadsPendingMessageConsistent` in IPC/Invariant/Defs.lean
with preservation theorems in IPC/Invariant/WaitingThreadHelpers.lean
(helper extraction in WS-AC Phase AC1-A). The safety argument is now both
structural (entry path analysis above) AND formally verified. -/
def notificationSignal (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) : Kernel Unit :=
  fun st =>
    match st.getObject? notificationId with
    | some (.notification ntfn) =>
        -- WS-RC R4.C: pop via the structural `NoDupList.tail?` smart accessor;
        -- it returns the head and a `NoDupList`-typed tail with the Nodup
        -- proof discharged inline. Proof-side preservation theorems use the
        -- `tail?_eq_{none,some}_iff` bridge lemmas to align with the
        -- underlying `.val` cons/nil case-split.
        match ntfn.waitingThreads.tail? with
        | some (waiter, rest) =>
            let nextState : NotificationState := if rest.val.isEmpty then .idle else .waiting
            -- WS-SM SM6.B (review #2, single-core): preserve `boundTCB` so an ordinary
            -- signal does not destroy a bound notification's binding.
            let ntfn' : Notification := {
              state := nextState
              waitingThreads := rest
              pendingBadge := none
              boundTCB := ntfn.boundTCB
            }
            match storeObject notificationId (.notification ntfn') st with
            | .error e => .error e
            | .ok ((), st') =>
                -- R3-A/M-16: Deliver signaled badge to woken waiter via pendingMessage.
                -- In seL4, the badge from Signal is returned as the Wait syscall's result.
                let badgeMsg : IpcMessage := { IpcMessage.empty with badge := some badge }
                match storeTcbIpcStateAndMessage st' waiter .ready (some badgeMsg) with
                | .error e => .error e
                | .ok st'' => .ok ((), ensureRunnable st'' waiter)
        | none =>
            -- WS-F5/D1c: Use word-bounded Badge.bor for accumulation.
            -- U8-C/U-L24: Notification word overflow note: Badge.bor uses
            -- unbounded Lean Nat internally (bitwise OR). In the formal model
            -- this is correct — no overflow is possible. However, on real
            -- hardware (ARM64), notification words are 64-bit. AN9 (hardware
            -- binding) must enforce 64-bit word width by masking Badge values
            -- to 2^64 - 1 at the platform boundary.
            -- Badge.ofNatMasked already applies a 64-bit mask, and Badge.bor
            -- preserves the mask (see Badge.bor definition in Prelude.lean).
            -- AF5-D (AF-15): Nat round-trip via `Badge.ofNatMasked badge.toNat`
            -- is safe: `ofNatMasked` applies `% machineWordMax` (64-bit masking).
            -- `bor_valid` theorem (AC3/I-04) proves result validity.
            -- H3 hardware binding: verify masking consistency at ABI boundary.
            let mergedBadge : SeLe4n.Badge :=
              match ntfn.pendingBadge with
              | some existing => SeLe4n.Badge.bor existing badge
              | none => SeLe4n.Badge.ofNatMasked badge.toNat
            let ntfn' : Notification := {
              state := .active
              waitingThreads := SeLe4n.NoDupList.empty
              pendingBadge := some mergedBadge
              boundTCB := ntfn.boundTCB
            }
            storeObject notificationId (.notification ntfn') st
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

-- AK1-E (I-M03): `notificationSignal_respects_pipBoost` correctness lemma
-- is defined in `IPC/Operations/SchedulerLemmas.lean` (downstream of this
-- file), where it can use `ensureRunnable_mem_self`.

/-- Wait on a notification: consume pending badge or block the caller.

WS-G7/F-P11: Duplicate-wait check uses O(1) TCB ipcState lookup instead of
O(n) list membership scan. If the waiter's ipcState is already
`.blockedOnNotification notificationId`, the thread is already waiting and
`alreadyWaiting` is returned.

WS-G7/F-P11: Waiter is prepended (`waiter :: waitingThreads`) instead of
appended (`waitingThreads ++ [waiter]`), reducing enqueue from O(n) to O(1).
FIFO ordering is not required by the seL4 notification spec — any waiter may
be woken on signal. -/
def notificationWait
    (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) : Kernel (Option SeLe4n.Badge) :=
  fun st =>
    match st.getObject? notificationId with
    | some (.notification ntfn) =>
        match ntfn.pendingBadge with
        | some badge =>
            let ntfn' : Notification :=
              { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none,
                boundTCB := ntfn.boundTCB }
            match storeObject notificationId (.notification ntfn') st with
            | .error e => .error e
            | .ok ((), st') =>
                match storeTcbIpcState st' waiter .ready with
                | .error e => .error e
                | .ok st'' => .ok (some badge, st'')
        | none =>
            -- WS-G7/F-P11/WS-RC R4.C: O(1) duplicate check via TCB ipcState
            -- (fast-path) PLUS structural duplicate guarantee via
            -- `NoDupList.consWithGuard?`. The TCB-state check fires first
            -- (cheaper, fail-fast on the common case); the consWithGuard?
            -- discharge is the type-level invariant carrier that makes the
            -- Nodup property structural rather than upstream-convention.
            match lookupTcb st waiter with
            | none => .error .objectNotFound
            | some tcb =>
                if tcb.ipcState = .blockedOnNotification notificationId then
                  .error .alreadyWaiting
                else
                  match ntfn.waitingThreads.consWithGuard? waiter with
                  | none =>
                      -- WS-RC R4.C: structurally unreachable under
                      -- `notificationWaiterConsistent` because the TCB
                      -- ipcState check above implies non-membership, but
                      -- preserved as defence-in-depth — if a future
                      -- refactor weakens the invariant chain, this branch
                      -- still fails closed with the explicit error code.
                      .error .alreadyWaiting
                  | some wt' =>
                      let ntfn' : Notification := {
                        state := .waiting
                        waitingThreads := wt'
                        pendingBadge := none
                        boundTCB := ntfn.boundTCB
                      }
                      match storeObject notificationId (.notification ntfn') st with
                      | .error e => .error e
                      | .ok ((), st') =>
                          -- WS-L1/L1-C: Use _fromTcb — storeObject at notificationId
                          -- does not modify waiter's TCB, so tcb is still valid in st'
                          --
                          -- WS-RR RR3.5: clear `pendingMessage` **atomically** with the
                          -- block, exactly as `endpointReceiveDual`'s block path does
                          -- (PR #873 round 11).  A waiter that already collected a
                          -- message stays `.ready` holding it -- `stageDeliveredMessage`
                          -- reads it at the delivering syscall's boundary and does not
                          -- clear it -- so parking it without the clear carried that
                          -- consumed message into `.blockedOnNotification`, leaving its
                          -- body readable on a parked thread and making
                          -- `blockedThreadsPendingMessageConsistent` (a conjunct of
                          -- `ipcInvariantFull`) FALSE in a reachable state: receive a
                          -- message, then Wait on an idle notification.  The invariant
                          -- was previously threaded as a post-state hypothesis on every
                          -- `notificationWait` bundle, which is what hid it.
                          --
                          -- Nothing owes the parked waiter that payload: the wake
                          -- (`notificationSignal`) overwrites `pendingMessage` with the
                          -- badge message it delivers, so the cleared field is dead
                          -- from the block to the wake.
                          match storeTcbIpcStateAndMessage_fromTcb st' waiter tcb
                              (.blockedOnNotification notificationId) none with
                          | .error e => .error e
                          | .ok st'' => .ok (none, removeRunnable st'' waiter)
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

-- ============================================================================
-- F-12: Supporting lemmas for notification waiting-list proofs (WS-D4)
-- ============================================================================

/-- `storeTcbIpcState` preserves objects at IDs other than `tid.toObjId`. -/
theorem storeTcbIpcState_preserves_objects_ne
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId)
    (hNe : oid ≠ tid.toObjId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects[oid]? = st.objects[oid]? := by
  unfold storeTcbIpcState at hStep
  cases hTcb : lookupTcb st tid with
  | none =>
    simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq : pair.snd = st' := Except.ok.inj hStep
      subst hEq
      exact storeObject_objects_ne st pair.2 tid.toObjId oid
        (.tcb { tcb with ipcState := ipc }) hNe hObjInv hStore

/-- `storeTcbIpcState` preserves notification objects (it only writes TCBs). -/
theorem storeTcbIpcState_preserves_notification
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (notifId : SeLe4n.ObjId)
    (ntfn : Notification)
    (hNtfn : st.objects[notifId]? = some (.notification ntfn))
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects[notifId]? = some (.notification ntfn) := by
  by_cases hEq : notifId = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    have hLookup : lookupTcb st tid = none := by
      unfold lookupTcb SystemState.getTcb?; simp [hNtfn]
    simp [hLookup] at hStep
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc notifId hEq hObjInv hStep]
    exact hNtfn

-- WS-RR RR3.5: the `storeTcbIpcStateAndMessage` twins of the two frames above.
-- They used to live in `IPC/Operations/SchedulerLemmas.lean`, which imports this
-- module; `notificationWait`'s block path now clears `pendingMessage` atomically
-- with the block (see the transition), so the frames are needed *here* and were
-- moved rather than duplicated.

open SeLe4n.Model.SystemState in
/-- SM6.D transport helper: a post-`storeTcbIpcStateAndMessage` TCB lookup
pulls back to a pre-state TCB agreeing on `pendingReceiveReply` and
`timeoutBudget`, and either identical or rewritten to the stored `ipcState`. -/
theorem storeTcbIpcStateAndMessage_tcb_backward_fields
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    ∀ (s : SeLe4n.ObjId) (tx : TCB), st'.objects[s]? = some (.tcb tx) →
      ∃ ty, st.objects[s]? = some (.tcb ty) ∧
        tx.pendingReceiveReply = ty.pendingReceiveReply ∧
        tx.timeoutBudget = ty.timeoutBudget ∧
        (tx = ty ∨ tx.ipcState = ipc) := by
  intro s tx hObj
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId
        (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      obtain ⟨⟨⟩, st''⟩ := pair
      simp only [hStore, Except.ok.injEq] at hStep
      subst hStep
      by_cases hs : s = tid.toObjId
      · subst hs
        rw [storeObject_objects_eq st st'' tid.toObjId _ hObjInv hStore] at hObj
        obtain rfl := KernelObject.tcb.inj (Option.some.inj hObj)
        exact ⟨tcb, lookupTcb_some_objects st tid tcb hLookup, rfl, rfl, Or.inr rfl⟩
      · rw [storeObject_objects_ne st st'' tid.toObjId s _ hs hObjInv hStore] at hObj
        exact ⟨tx, hObj, rfl, rfl, Or.inl rfl⟩

/-- WS-F1: `storeTcbIpcStateAndMessage` preserves objects at IDs other than `tid.toObjId`. -/
theorem storeTcbIpcStateAndMessage_preserves_objects_ne
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (oid : SeLe4n.ObjId) (hNe : oid ≠ tid.toObjId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    st'.objects[oid]? = st.objects[oid]? := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      obtain ⟨⟨⟩, stMid⟩ := pair
      simp only [hStore] at hStep
      have hEq : stMid = st' := Except.ok.inj hStep; subst hEq
      exact storeObject_objects_ne st stMid tid.toObjId oid _ hNe hObjInv hStore

/-- WS-F1: `storeTcbIpcStateAndMessage` preserves notification objects. -/
theorem storeTcbIpcStateAndMessage_preserves_notification
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (notifId : SeLe4n.ObjId) (ntfn : Notification)
    (hObjInv : st.objects.invExt)
    (hNtfn : st.objects[notifId]? = some (.notification ntfn))
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    st'.objects[notifId]? = some (.notification ntfn) := by
  by_cases hEq : notifId = tid.toObjId
  · subst hEq
    unfold storeTcbIpcStateAndMessage at hStep
    have hLookup : lookupTcb st tid = none := by unfold lookupTcb SystemState.getTcb?; simp [hNtfn]
    simp [hLookup] at hStep
  · rw [storeTcbIpcStateAndMessage_preserves_objects_ne st st' tid ipc msg notifId hEq hObjInv hStep]
    exact hNtfn

/-- `removeRunnable` only modifies the scheduler; all objects are preserved. -/
theorem removeRunnable_preserves_objects
    (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (removeRunnable st tid).objects = st.objects := by
  rfl

/-- WS-E3/H-09: `ensureRunnable` only modifies the scheduler; all objects are preserved. -/
theorem ensureRunnable_preserves_objects
    (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (ensureRunnable st tid).objects = st.objects := by
  unfold ensureRunnable
  split
  · rfl
  · split <;> rfl

/-- TPI-D1: ensureRunnable preserves objectIndexSet (only modifies scheduler). -/
theorem ensureRunnable_preserves_objectIndexSet
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (ensureRunnable st tid).objectIndexSet = st.objectIndexSet := by
  unfold ensureRunnable
  split
  · rfl
  · split <;> rfl

/-- TPI-D1: ensureRunnable preserves objectIndexSetComplete. -/
theorem ensureRunnable_preserves_objectIndexSetComplete
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hComplete : objectIndexSetComplete st) :
    objectIndexSetComplete (ensureRunnable st tid) := by
  intro oid hNe
  rw [ensureRunnable_preserves_objectIndexSet st tid]
  apply hComplete
  rwa [ensureRunnable_preserves_objects st tid] at hNe

/-- TPI-D1: ensureRunnable preserves objectIndexSet.table.invExt. -/
theorem ensureRunnable_preserves_objectIndexSet_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objectIndexSet.table.invExt) :
    (ensureRunnable st tid).objectIndexSet.table.invExt := by
  rw [ensureRunnable_preserves_objectIndexSet st tid]; exact hInv

/-- WS-E3/H-09: `storeTcbIpcState` does not modify the scheduler. -/
theorem storeTcbIpcState_scheduler_eq
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold storeTcbIpcState at hStep
  cases hTcb : lookupTcb st tid with
  | none =>
    simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep
      subst hEq
      exact storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore

/-- WS-E3/H-09: `storeTcbIpcState` preserves endpoint objects. -/
theorem storeTcbIpcState_preserves_endpoint
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (epId : SeLe4n.ObjId)
    (ep : Endpoint)
    (hEp : st.objects[epId]? = some (.endpoint ep))
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects[epId]? = some (.endpoint ep) := by
  by_cases hEq : epId = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    have hLookup : lookupTcb st tid = none := by
      unfold lookupTcb SystemState.getTcb?; simp [hEp]
    simp [hLookup] at hStep
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc epId hEq hObjInv hStep]
    exact hEp

/-- WS-E3/H-09: `storeTcbIpcState` preserves CNode objects. -/
theorem storeTcbIpcState_preserves_cnode
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (cnodeId : SeLe4n.ObjId)
    (cn : CNode)
    (hCn : st.objects[cnodeId]? = some (.cnode cn))
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects[cnodeId]? = some (.cnode cn) := by
  by_cases hEq : cnodeId = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    have hLookup : lookupTcb st tid = none := by
      unfold lookupTcb SystemState.getTcb?; simp [hCn]
    simp [hLookup] at hStep
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc cnodeId hEq hObjInv hStep]
    exact hCn

/-- WS-E3/H-09: `storeTcbIpcState` preserves VSpaceRoot objects. -/
theorem storeTcbIpcState_preserves_vspaceRoot
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId)
    (vs : VSpaceRoot)
    (hVs : st.objects[oid]? = some (.vspaceRoot vs))
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects[oid]? = some (.vspaceRoot vs) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    have hLookup : lookupTcb st tid = none := by
      unfold lookupTcb SystemState.getTcb?; simp [hVs]
    simp [hLookup] at hStep
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc oid hEq hObjInv hStep]
    exact hVs

/-- WS-E3/H-09: Backward CNode preservation: if post-state has a CNode, pre-state had it.
`storeTcbIpcState` only writes TCBs, so it cannot create or modify CNode objects. -/
theorem storeTcbIpcState_cnode_backward
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId)
    (cn : CNode)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (hCn : st'.objects[oid]? = some (.cnode cn)) :
    st.objects[oid]? = some (.cnode cn) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    cases hLookup : lookupTcb st tid with
    | none =>
      simp [hLookup] at hStep;
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore] at hCn; cases hCn
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc oid hEq hObjInv hStep] at hCn; exact hCn

/-- WS-E3/H-09: Backward endpoint preservation for `storeTcbIpcState`. -/
theorem storeTcbIpcState_endpoint_backward
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId)
    (ep : Endpoint)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (hEp : st'.objects[oid]? = some (.endpoint ep)) :
    st.objects[oid]? = some (.endpoint ep) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    cases hLookup : lookupTcb st tid with
    | none =>
      simp [hLookup] at hStep;
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore] at hEp; cases hEp
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc oid hEq hObjInv hStep] at hEp; exact hEp

/-- WS-E3/H-09: Backward notification preservation for `storeTcbIpcState`. -/
theorem storeTcbIpcState_notification_backward
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId)
    (ntfn : Notification)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (hNtfn : st'.objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    cases hLookup : lookupTcb st tid with
    | none =>
      simp [hLookup] at hStep
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore] at hNtfn; cases hNtfn
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc oid hEq hObjInv hStep] at hNtfn; exact hNtfn

/-- WS-G7/F-P11: Double-wait is rejected: if the waiter's TCB ipcState is
already `.blockedOnNotification notifId`, `notificationWait` returns
`alreadyWaiting`. Uses O(1) TCB lookup instead of O(n) list membership. -/
theorem notificationWait_error_alreadyWaiting
    (waiter : SeLe4n.ThreadId)
    (notifId : SeLe4n.ObjId)
    (st : SystemState)
    (ntfn : Notification)
    (tcb : TCB)
    (hObj : st.objects[notifId]? = some (.notification ntfn))
    (hNoBadge : ntfn.pendingBadge = none)
    (hTcb : lookupTcb st waiter = some tcb)
    (hBlocked : tcb.ipcState = .blockedOnNotification notifId) :
    notificationWait notifId waiter st = .error .alreadyWaiting := by
  unfold notificationWait SystemState.getObject?
  simp [hObj, hNoBadge, hTcb, hBlocked]

/-- Decomposition: on the badge-consumed path, the post-state notification
has an empty waiting list.

WS-RC R4.C: the conclusion references `.val` (the underlying `List
ThreadId`) because the field type is `NoDupList ThreadId`.  Equivalently,
`ntfn'.waitingThreads = SeLe4n.NoDupList.empty`. -/
theorem notificationWait_badge_path_notification
    (st st' : SystemState)
    (notifId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notifId waiter st = .ok (some badge, st')) :
    ∃ ntfn', st'.objects[notifId]? = some (.notification ntfn') ∧
      ntfn'.waitingThreads.val = [] := by
  -- The proof reasons about the object store directly, so the kind-agnostic
  -- accessor the transition now reads through is unfolded once, here.
  unfold notificationWait SystemState.getObject? at hStep
  cases hObj : st.objects[notifId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _
    | schedContext _ | reply _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | none =>
        simp only [hBadge] at hStep
        -- WS-G7: lookupTcb match
        cases hLookup : lookupTcb st waiter with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          split at hStep
          · simp at hStep
          · -- WS-RC R4.C: also case-split on consWithGuard?
            cases hCons : ntfn.waitingThreads.consWithGuard? waiter with
            | none => simp [hCons] at hStep
            | some wt' =>
              simp only [hCons] at hStep
              revert hStep
              cases hStore : storeObject notifId _ st with
              | error e => simp
              | ok pair =>
                simp only []
                intro hStep
                -- WS-L1: rewrite _fromTcb back to original for proof compatibility
                -- (WS-RR RR3.5: the block store now clears `pendingMessage`, so the
                -- bridge is `storeTcbIpcStateAndMessage_fromTcb_eq`).
                have hLookup' := lookupTcb_preserved_by_storeObject_notification hLookup hObj hObjInv hStore
                rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup'] at hStep
                revert hStep
                cases hTcb : storeTcbIpcStateAndMessage pair.2 waiter _ none with
                | error e => simp
                | ok st2 =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨h, _⟩
                  exact absurd h (by simp)
      | some b =>
        simp only [hBadge] at hStep
        let newNtfn : Notification :=
          { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none,
            boundTCB := ntfn.boundTCB }
        revert hStep
        cases hStore : storeObject notifId (.notification newNtfn) st with
        | error e => simp
        | ok pair =>
          simp only []
          intro hStep
          revert hStep
          cases hTcb : storeTcbIpcState pair.2 waiter .ready with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hStEq⟩
            subst hStEq
            have hNtfnStored : pair.2.objects[notifId]? = some (.notification newNtfn) :=
              storeObject_objects_eq st pair.2 notifId (.notification newNtfn) hObjInv hStore
            have hPairObjInv : pair.2.objects.invExt := by
              unfold storeObject at hStore; cases hStore
              exact RHTable_insert_preserves_invExt _ _ _ hObjInv
            have hNtfnPreserved : st2.objects[notifId]? = some (.notification newNtfn) :=
              storeTcbIpcState_preserves_notification pair.2 st2 waiter .ready notifId newNtfn hNtfnStored hPairObjInv hTcb
            exact ⟨newNtfn, hNtfnPreserved, rfl⟩

/-- WS-G7/F-P11/WS-RC R4.C: Decomposition: on the wait path, the post-state
notification has the waiter prepended.  The waiter's TCB existed and was
not already blocked on this notification.

WS-RC R4.C: the conclusion references `.val` (the underlying `List
ThreadId`) because the field type is now `NoDupList ThreadId`.  The
prepend witness is derived from `NoDupList.consWithGuard?_eq_some_iff`. -/
theorem notificationWait_wait_path_notification
    (st st' : SystemState)
    (notifId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notifId waiter st = .ok (none, st')) :
    ∃ ntfn ntfn',
      st.objects[notifId]? = some (.notification ntfn) ∧
      ntfn.pendingBadge = none ∧
      st'.objects[notifId]? = some (.notification ntfn') ∧
      ntfn'.waitingThreads.val = waiter :: ntfn.waitingThreads.val := by
  unfold notificationWait SystemState.getObject? at hStep
  cases hObj : st.objects[notifId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _
    | schedContext _ | reply _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | some b =>
        simp only [hBadge] at hStep
        revert hStep
        cases hStore : storeObject notifId (.notification
            { state := .idle, waitingThreads := SeLe4n.NoDupList.empty,
              pendingBadge := none, boundTCB := ntfn.boundTCB }) st with
        | error e => simp
        | ok pair =>
          simp only []
          intro hStep
          revert hStep
          cases hTcb : storeTcbIpcState pair.2 waiter .ready with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨h, _⟩
            exact absurd h (by simp)
      | none =>
        simp only [hBadge] at hStep
        -- WS-G7: match on lookupTcb
        cases hLookup : lookupTcb st waiter with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          -- ipcState check
          by_cases hBlocked : tcb.ipcState = .blockedOnNotification notifId
          · simp [hBlocked] at hStep
          · simp only [hBlocked, ite_false] at hStep
            -- WS-RC R4.C: structural consWithGuard? case-split
            cases hCons : ntfn.waitingThreads.consWithGuard? waiter with
            | none => simp [hCons] at hStep
            | some wt' =>
              simp only [hCons] at hStep
              -- Recover wt'.val = waiter :: ntfn.waitingThreads.val from the
              -- structural smart-constructor equation.
              have hConsEq : wt'.val = waiter :: ntfn.waitingThreads.val :=
                ((SeLe4n.NoDupList.consWithGuard?_eq_some_iff waiter
                  ntfn.waitingThreads wt').mp hCons).2
              let ntfn' : Notification :=
                { state := .waiting, waitingThreads := wt', pendingBadge := none,
                  boundTCB := ntfn.boundTCB }
              revert hStep
              cases hStore : storeObject notifId (.notification ntfn') st with
              | error e => simp
              | ok pair =>
                simp only []
                intro hStep
                -- WS-L1: rewrite _fromTcb back to original for proof compatibility
                have hLookup' := lookupTcb_preserved_by_storeObject_notification hLookup hObj hObjInv hStore
                rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup'] at hStep
                revert hStep
                cases hTcb : storeTcbIpcStateAndMessage pair.2 waiter (.blockedOnNotification notifId) none with
                | error e => simp
                | ok st2 =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨_, hStEq⟩
                  have hRemObj : (removeRunnable st2 waiter).objects = st2.objects := rfl
                  have hNtfnStored : pair.2.objects[notifId]? = some (.notification ntfn') :=
                    storeObject_objects_eq st pair.2 notifId (.notification ntfn') hObjInv hStore
                  have hPairObjInv : pair.2.objects.invExt := by
                    unfold storeObject at hStore; cases hStore
                    exact RHTable_insert_preserves_invExt _ _ _ hObjInv
                  have hNtfnPreserved : st2.objects[notifId]? = some (.notification ntfn') :=
                    storeTcbIpcStateAndMessage_preserves_notification pair.2 st2 waiter
                      (.blockedOnNotification notifId) none notifId ntfn' hPairObjInv hNtfnStored hTcb
                  refine ⟨ntfn, ntfn', rfl, hBadge, ?_, hConsEq⟩
                  rw [← hStEq, hRemObj]
                  exact hNtfnPreserved

