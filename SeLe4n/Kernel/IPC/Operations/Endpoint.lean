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

- **I-L3 — `endpointCallWithDonation` `popHead_returns_head` external
  composition.** `endpointQueuePopHead_returns_head` (defined in
  `IPC/Invariant/Defs.lean`) is referenced across both
  `endpointCallWithDonation` (Operations/Donation.lean) and
  `endpointSendDualWithCaps` (DualQueue/WithCaps.lean) without a local
  composition wrapper. The theorem is non-fragile (invariant-independent)
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

/-- AK1-E (I-M03): Inlined PIP-effective priority. Duplicated from
`Scheduler/Invariant.lean:146` (`effectiveRunQueuePriority`) to avoid a
circular import (Scheduler.Invariant → ... → Endpoint). When a TCB has a
PIP boost (from priority inheritance), the RunQueue must insert at the
boosted priority to preserve priority-inversion bounds; otherwise the
boosted thread lands in the wrong priority bucket until the next
scheduler tick.

The agreement with the scheduler's copy is **checked**, not assumed:
`ipcEffectiveRunQueuePriority_eq_effectiveRunQueuePriority`
(`IPC/CrossCore/EndpointSend.lean`, the first module that sees both names)
makes a change to either body that the other does not mirror a build failure. -/
@[inline] def ipcEffectiveRunQueuePriority (tcb : TCB) : SeLe4n.Priority :=
  match tcb.pipBoost with
  | none => tcb.priority
  | some boost => ⟨Nat.max tcb.priority.val boost.val⟩

/-- WS-G4/F-P02: O(1) amortized insert via RunQueue.
    AK1-E (I-M03): Priority is computed via `ipcEffectiveRunQueuePriority`
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
              ((st.scheduler.runQueueOnCore bootCoreId).insert tid (ipcEffectiveRunQueuePriority tcb))
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
detach: with it, taking a frame out of the middle repairs its two neighbours and
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
        let sc' := { sc with boundThread := some serverTid,
                             scReply := some pushRid }
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
                                 scReply := some pushRid }) st = .ok ((), s1) ∧
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
                                         scReply := some pushRid }) st with
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
    ∃ (sc : SchedContext) (pushRid : SeLe4n.ReplyId) (pushReply : Reply),
      st.getSchedContext? clientScId = some sc ∧
      st.getReply? pushRid = some pushReply ∧
      pushReply.prev = none ∧ pushReply.next = none ∧
      st'.getSchedContext? clientScId =
        some { sc with boundThread := some serverTid, scReply := some pushRid } ∧
      st'.getReply? pushRid =
        some { pushReply with prev := sc.scReply, next := some (.head clientScId) } := by
  obtain ⟨sc, donorTcb, clientTcb, serverTcb, pushRid, pushReply, s1, s2, s3, s4,
      hObj, _, _, hFrame, hS1, hS2, hLC, hS3, hLS, hS4, hEq⟩ :=
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
      = some { sc with boundThread := some serverTid, scReply := some pushRid } := by
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
  refine ⟨sc, pushRid, pushReply, hObj, hRepPre, hPrevNone, hNextNone, ?_, ?_⟩
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
retype.  The `severAtCut` policy is unchanged and is now carried out by the
*detach* at the cancellation (`detachReplyFrameAbove`), so a linked frame always
has a blocked caller (`Reply.wellFormed`); a frame that validates and has none
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
(neither could be retyped, the Reply could never be linked again).  The policy is
unchanged and is now implemented by the detach (`detachReplyFrameAbove`), which
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
-- WS-OD (`v0.35.4`): the frame detach — the non-head removal arm
-- ----------------------------------------------------------------------------

/-- **Take a frame that is not a head off its stack, in `O(1)`.**  The frame
*above* the cut one (`next = .frame above`) stops linking down to it
(`above.prev := none`), which makes it the bottom of the stack it heads — so the
next pop that reaches it binds that thread outright — and cuts everything below
off the context's stack.

**This writes `none`, not the cut frame's own `prev`**, and that is the
`cancelledMiddleCallerPolicy` decision rather than an omission: the alternative
(`spliceOutTheCut`) keeps the frames below on the stack — it is what seL4-MCS's
`reply_remove` does — and taking it would require moving the reply path's pop
trigger from the recorded server's binding to the answered frame's head-ness.  The two write the same value whenever the cut
frame is the bottom of its stack, which is every stack of depth two;
`tests/SmpIpcSuite.lean` §3.22 is the depth-three witness where they differ.  The cancelled frame's own links are cleared when
its caller link is consumed (`Reply.consumed`), and the frame below it keeps an
upward link the structure never trusts (see `Reply.consumed`).

Three answers, and each is a decision.  `.ok st` when the frame is a head (a
head is popped, never detached — that is the reclaim's job — so this is not the
operation to apply, and applying it must not silently drop a stack), when it has
no frame above (a detached top or an unlinked frame: nothing to repair), or when
the frame does not resolve at all (nothing to detach from).  `.error` when the
frame above does not resolve or does not point back (`.invalidArgument`): a
frame above that does not name this frame as its `prev` would be rewritten on the
strength of a stale upward link, which is exactly the trust `Reply.consumed`
withholds from such links. -/
def detachReplyFrameAbove (st : SystemState) (rid : SeLe4n.ReplyId) :
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
        else
          match storeObject above.toObjId (.reply { a with prev := none }) st with
          | .error e => .error e
          | .ok ((), st') => .ok st'
    | _ => .ok st

/-- The detach, decomposed: the identity, or one Reply store at the frame above. -/
theorem detachReplyFrameAbove_cases {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (h : detachReplyFrameAbove st rid = .ok st') :
    st' = st ∨ ∃ (r : Reply) (above : SeLe4n.ReplyId) (a : Reply),
      st.getReply? rid = some r ∧ r.next = some (.frame above) ∧
      st.getReply? above = some a ∧ a.prev = some rid ∧
      storeObject above.toObjId (.reply { a with prev := none }) st = .ok ((), st') := by
  unfold detachReplyFrameAbove at h
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
            cases hS : storeObject above.toObjId (.reply { a with prev := none }) st with
            | error _ => intro h; cases h
            | ok pr =>
              obtain ⟨u, s'⟩ := pr; cases u
              intro h; cases h
              exact Or.inr ⟨r, above, a, rfl, hN, hA, by simpa using hP, hS⟩

/-- The detach is the identity on a head frame. -/
theorem detachReplyFrameAbove_of_head (st : SystemState) (rid : SeLe4n.ReplyId) (r : Reply)
    (sc : SeLe4n.SchedContextId) (hR : st.getReply? rid = some r)
    (hHead : r.next = some (.head sc)) :
    detachReplyFrameAbove st rid = .ok st := by
  unfold detachReplyFrameAbove; rw [hR]; simp only [hHead]

/-- The detach is the identity on a frame with nothing above it. -/
theorem detachReplyFrameAbove_of_no_frame_above (st : SystemState) (rid : SeLe4n.ReplyId)
    (r : Reply) (hR : st.getReply? rid = some r) (hNext : r.next = none) :
    detachReplyFrameAbove st rid = .ok st := by
  unfold detachReplyFrameAbove; rw [hR]; simp only [hNext]

/-- WS-OD (`v0.35.4`): **the frame above `rid`**, if `rid` resolves and its
`next` names one -- the object `detachReplyFrameAbove` writes.  Resolved from
the same two fields the detach reads, so the member a cancellation declares for
the detach (`cancelDetachedFrameAbove?`) and the object the detach stores cannot
disagree: `replyFrameAbove?_of_detach_store` is the relation. -/
def replyFrameAbove? (st : SystemState) (rid : SeLe4n.ReplyId) : Option SeLe4n.ReplyId :=
  match st.getReply? rid with
  | none => none
  | some r =>
    match r.next with
    | some (.frame above) => some above
    | _ => none

/-- The detach either commits nothing or stores exactly the frame
`replyFrameAbove?` names. -/
theorem replyFrameAbove?_of_detach_store {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (h : detachReplyFrameAbove st rid = .ok st') :
    st' = st ∨ ∃ (above : SeLe4n.ReplyId) (a : Reply),
      replyFrameAbove? st rid = some above ∧ st.getReply? above = some a ∧
      storeObject above.toObjId (.reply { a with prev := none }) st = .ok ((), st') := by
  rcases detachReplyFrameAbove_cases h with hEq | ⟨r, above, a, hR, hN, hA, _, hS⟩
  · exact Or.inl hEq
  · refine Or.inr ⟨above, a, ?_, hA, hS⟩
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

theorem detachReplyFrameAbove_of_absent (st : SystemState) (rid : SeLe4n.ReplyId)
    (hR : st.getReply? rid = none) :
    detachReplyFrameAbove st rid = .ok st := by
  unfold detachReplyFrameAbove; rw [hR]

theorem detachReplyFrameAbove_preserves_objects_invExt {st st' : SystemState}
    {rid : SeLe4n.ReplyId} (hObjInv : st.objects.invExt)
    (h : detachReplyFrameAbove st rid = .ok st') : st'.objects.invExt := by
  rcases detachReplyFrameAbove_cases h with rfl | ⟨_, _, _, _, _, _, _, hS⟩
  · exact hObjInv
  · exact storeObject_preserves_objects_invExt st st' _ _ hObjInv hS

theorem detachReplyFrameAbove_scheduler_eq {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (h : detachReplyFrameAbove st rid = .ok st') : st'.scheduler = st.scheduler := by
  rcases detachReplyFrameAbove_cases h with rfl | ⟨_, _, _, _, _, _, _, hS⟩
  · rfl
  · unfold storeObject at hS; cases hS; rfl

theorem detachReplyFrameAbove_machine_eq {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (h : detachReplyFrameAbove st rid = .ok st') : st'.machine = st.machine := by
  rcases detachReplyFrameAbove_cases h with rfl | ⟨_, _, _, _, _, _, _, hS⟩
  · rfl
  · unfold storeObject at hS; cases hS; rfl

theorem detachReplyFrameAbove_serviceRegistry_eq {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (h : detachReplyFrameAbove st rid = .ok st') : st'.serviceRegistry = st.serviceRegistry := by
  rcases detachReplyFrameAbove_cases h with rfl | ⟨_, _, _, _, _, _, _, hS⟩
  · rfl
  · unfold storeObject at hS; cases hS; rfl

/-- The detach writes a Reply, so a notification in the post-state was one in the
pre-state. -/
theorem detachReplyFrameAbove_notification_backward {st st' : SystemState}
    {rid : SeLe4n.ReplyId} (hObjInv : st.objects.invExt)
    (h : detachReplyFrameAbove st rid = .ok st')
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : st'.objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
  rcases detachReplyFrameAbove_cases h with rfl | ⟨_, above, _, _, _, _, _, hS⟩
  · exact hNtfn
  · by_cases hk : oid = above.toObjId
    · rw [hk, storeObject_objects_eq' st _ _ _ hObjInv hS] at hNtfn; cases hNtfn
    · rw [storeObject_objects_ne st st' above.toObjId oid _ hk hObjInv hS] at hNtfn; exact hNtfn

/-- The detach is invisible to every typed TCB read. -/
theorem detachReplyFrameAbove_getTcb?_eq {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (hObjInv : st.objects.invExt)
    (h : detachReplyFrameAbove st rid = .ok st') (tid : SeLe4n.ThreadId) :
    st'.getTcb? tid = st.getTcb? tid := by
  rcases detachReplyFrameAbove_cases h with rfl | ⟨_, above, a, _, _, hA, _, hS⟩
  · rfl
  · unfold SystemState.getTcb?
    by_cases hk : tid.toObjId = above.toObjId
    · rw [hk, storeObject_objects_eq' st _ _ _ hObjInv hS,
        (SystemState.getReply?_eq_some_iff _ _ _).mp hA]
    · rw [storeObject_objects_ne st st' above.toObjId tid.toObjId _ hk hObjInv hS]

/-- The detach writes at most the frame above; every other key is untouched. -/
theorem detachReplyFrameAbove_objects_ne {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (hObjInv : st.objects.invExt)
    (h : detachReplyFrameAbove st rid = .ok st') (k : SeLe4n.ObjId)
    (hk : ∀ (r : Reply) (above : SeLe4n.ReplyId), st.getReply? rid = some r →
      r.next = some (.frame above) → k ≠ above.toObjId) :
    st'.objects[k]? = st.objects[k]? := by
  rcases detachReplyFrameAbove_cases h with rfl | ⟨r, above, a, hR, hN, _, _, hS⟩
  · rfl
  · exact storeObject_objects_ne st st' above.toObjId k _ (hk r above hR hN) hObjInv hS

theorem detachReplyFrameAbove_tcb_eq {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (hObjInv : st.objects.invExt)
    (h : detachReplyFrameAbove st rid = .ok st')
    (k : SeLe4n.ObjId) (t0 : TCB) (hk : st.objects[k]? = some (.tcb t0)) :
    st'.objects[k]? = some (.tcb t0) := by
  rcases detachReplyFrameAbove_cases h with rfl | ⟨r, above, a, hR, hN, hA, _, hS⟩
  · exact hk
  · have hNe : k ≠ above.toObjId := by
      intro hEq; rw [hEq, ((SystemState.getReply?_eq_some_iff _ _ _).mp hA)] at hk; cases hk
    rw [storeObject_objects_ne st st' above.toObjId k _ hNe hObjInv hS]; exact hk

theorem detachReplyFrameAbove_tcb_backward {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (hObjInv : st.objects.invExt)
    (h : detachReplyFrameAbove st rid = .ok st')
    (k : SeLe4n.ObjId) (t0 : TCB) (hk : st'.objects[k]? = some (.tcb t0)) :
    st.objects[k]? = some (.tcb t0) := by
  rcases detachReplyFrameAbove_cases h with rfl | ⟨_, above, _, _, _, _, _, hS⟩
  · exact hk
  · by_cases hEq : k = above.toObjId
    · rw [hEq, storeObject_objects_eq' st _ _ _ hObjInv hS] at hk; cases hk
    · rw [storeObject_objects_ne st st' above.toObjId k _ hEq hObjInv hS] at hk; exact hk

theorem detachReplyFrameAbove_non_reply_eq {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (hObjInv : st.objects.invExt)
    (h : detachReplyFrameAbove st rid = .ok st')
    (k : SeLe4n.ObjId) (hNotReply : ∀ r : Reply, st.objects[k]? ≠ some (.reply r)) :
    st'.objects[k]? = st.objects[k]? := by
  rcases detachReplyFrameAbove_cases h with rfl | ⟨r, above, a, hR, hN, hA, _, hS⟩
  · rfl
  · exact storeObject_objects_ne st st' above.toObjId k _
      (fun hEq => hNotReply a (by rw [hEq]; exact (SystemState.getReply?_eq_some_iff _ _ _).mp hA))
      hObjInv hS

theorem detachReplyFrameAbove_reply_rewrite {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (hObjInv : st.objects.invExt)
    (h : detachReplyFrameAbove st rid = .ok st')
    (oid : SeLe4n.ObjId) (r : Reply) (hReply : st.objects[oid]? = some (.reply r)) :
    ∃ r', st'.objects[oid]? = some (.reply r') ∧ replyStackRewrite r' r := by
  rcases detachReplyFrameAbove_cases h with rfl | ⟨r0, above, a, _, _, hA, _, hS⟩
  · exact ⟨r, hReply, replyStackRewrite.refl r⟩
  · by_cases hk : oid = above.toObjId
    · subst hk
      have hStored : st'.objects[above.toObjId]? = _ := storeObject_objects_eq' st _ _ _ hObjInv hS
      have ha : a = r := KernelObject.reply.inj (Option.some.inj
        (((SystemState.getReply?_eq_some_iff _ _ _).mp hA).symm.trans hReply))
      subst ha
      exact ⟨_, hStored, ⟨none, a.next, rfl⟩⟩
    · exact ⟨r, (storeObject_objects_ne st st' above.toObjId oid _ hk hObjInv hS).trans hReply,
        replyStackRewrite.refl r⟩

/-- WS-RM (`v0.35.6`): **the detach folded to the identity on a refusal** — the
one spelling of "take the frame above off this frame's stack, or leave the state
alone".  Both removal paths need it and neither may fail on it, so it is defined
once here rather than answered separately at each.

The fold is sound because a refusal *is* the statement that nothing references
this frame.  `detachReplyFrameAbove` refuses exactly when the frame `next` names
either does not resolve or does not point back; under
`donationChainWellFormed.prevLinkReciprocal` the only frame whose `prev` can name
`rid` is the one `rid`'s own `next` names, so in either refusal no stored Reply
links down to `rid` and clearing its links breaks no reciprocity
(`detachReplyFrameAboveOrSelf_unreferenced`).  Committing nothing there is also
the trust the structure withholds from a stale upward link: rewriting a frame
that does not point back would be acting on one. -/
def detachReplyFrameAboveOrSelf (st : SystemState) (rid : SeLe4n.ReplyId) : SystemState :=
  match detachReplyFrameAbove st rid with
  | .ok st' => st'
  | .error _ => st

/-- The fold, decomposed: the identity, or a `detachReplyFrameAbove` that ran. -/
theorem detachReplyFrameAboveOrSelf_cases (st : SystemState) (rid : SeLe4n.ReplyId) :
    detachReplyFrameAboveOrSelf st rid = st ∨
      detachReplyFrameAbove st rid = .ok (detachReplyFrameAboveOrSelf st rid) := by
  unfold detachReplyFrameAboveOrSelf
  split
  · rename_i st' h; exact Or.inr h
  · exact Or.inl rfl

/-- WS-RM (`v0.35.6`): **sever a thread's reply frame from the frame above it** —
seL4's `reply_remove_tcb`, non-head arm, keyed on the thread's own forward link.

This is the TCB-keyed wrapper over `detachReplyFrameAboveOrSelf`; the removal
paths that hold a `ReplyId` directly (the reply leg, `removeCallerReplyFrame`)
call that fold, so there is exactly one answer to "what does a detach do when it
cannot repair the frame above".

**Order.**  On the cancellation path this runs after the donation reclaim, on
whose success the frame is already unlinked and this is the identity
(`detachReplyFrameAbove_of_no_frame_above`); on a head it is the identity too,
deliberately — a head is popped by the reclaim, never detached, and a reclaim
that *declined* on a head is an invariant violation this step must not paper over
by dropping a stack. -/
def detachFrameAboveThreadReply (st : SystemState) (tcb : TCB) : SystemState :=
  match tcb.replyObject with
  | none => st
  | some rid => detachReplyFrameAboveOrSelf st rid

/-- **WS-RM (`v0.35.6`): the fold, decomposed as a store.**  Either the identity,
or exactly one `.reply` store at a key that already holds a Reply — so every
"this predicate survives a Reply store" lemma in the tree transports across the
removal's first leg without a new argument. -/
theorem detachReplyFrameAboveOrSelf_store_cases (st : SystemState) (rid : SeLe4n.ReplyId) :
    detachReplyFrameAboveOrSelf st rid = st ∨
      ∃ (above : SeLe4n.ReplyId) (a : Reply),
        st.objects[above.toObjId]? = some (.reply a) ∧
        storeObject above.toObjId (.reply { a with prev := none }) st
          = .ok ((), detachReplyFrameAboveOrSelf st rid) := by
  rcases detachReplyFrameAboveOrSelf_cases st rid with h | h
  · exact Or.inl h
  · rcases detachReplyFrameAbove_cases h with hEq | ⟨_, above, a, _, _, hA, _, hS⟩
    · exact Or.inl hEq
    · exact Or.inr ⟨above, a, (SystemState.getReply?_eq_some_iff _ _ _).mp hA, hS⟩

/-- The fold's one write sets a `prev`, so **every Reply's `next` and `caller`
are exactly where they were** — sharper than `replyStackRewrite`, which permits
`next` to move too and so cannot answer "does this frame still head a stack?". -/
theorem detachReplyFrameAboveOrSelf_reply_next (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) (q : SeLe4n.ReplyId) (rq : Reply)
    (hq : (detachReplyFrameAboveOrSelf st rid).getReply? q = some rq) :
    ∃ rp, st.getReply? q = some rp ∧ rq.next = rp.next ∧ rq.caller = rp.caller := by
  rcases detachReplyFrameAboveOrSelf_cases st rid with h | h
  · exact ⟨rq, by rw [← h]; exact hq, rfl, rfl⟩
  · rcases detachReplyFrameAbove_cases h with hEq | ⟨_, above, a, _, _, hA, _, hS⟩
    · exact ⟨rq, by rw [← hEq]; exact hq, rfl, rfl⟩
    · rw [SystemState.getReply?_eq_some_iff] at hq
      by_cases hk : q.toObjId = above.toObjId
      · rw [hk, storeObject_objects_eq' st _ _ _ hInv hS] at hq
        refine ⟨a, ?_, ?_, ?_⟩
        · rw [SeLe4n.ReplyId.toObjId_injective _ _ hk]; exact hA
        · rw [← KernelObject.reply.inj (Option.some.inj hq)]
        · rw [← KernelObject.reply.inj (Option.some.inj hq)]
      · rw [storeObject_objects_ne st _ above.toObjId q.toObjId _ hk hInv hS] at hq
        exact ⟨rq, (SystemState.getReply?_eq_some_iff _ _ _).mpr hq, rfl, rfl⟩

-- ----------------------------------------------------------------------------
-- WS-RM (`v0.35.6`): the TCB-keyed detach's read/write algebra
-- ----------------------------------------------------------------------------

/-- `v0.35.4`: the detach, decomposed — the identity (no reply link, no frame
above, or a refused repair), or one `detachReplyFrameAbove` that succeeded. -/
theorem detachFrameAboveThreadReply_cases (st : SystemState) (tcb : TCB) :
    detachFrameAboveThreadReply st tcb = st ∨
    ∃ rid, tcb.replyObject = some rid ∧
      detachReplyFrameAbove st rid = .ok (detachFrameAboveThreadReply st tcb) := by
  unfold detachFrameAboveThreadReply
  split
  · exact Or.inl rfl
  · rename_i rid hRid
    rcases detachReplyFrameAboveOrSelf_cases st rid with h | h
    · exact Or.inl h
    · exact Or.inr ⟨rid, hRid, h⟩

/-- `v0.35.4`: the detach is the identity on a frame with nothing above it — the
shape every cancellation of a head or bottom frame, and every successful reclaim,
leaves. -/
theorem detachFrameAboveThreadReply_eq_self_of_no_frame_above (st : SystemState) (tcb : TCB)
    (hNoFrameAbove : ∀ (rid : SeLe4n.ReplyId) (r : Reply) (above : SeLe4n.ReplyId),
      tcb.replyObject = some rid → st.getReply? rid = some r →
      r.next ≠ some (.frame above)) :
    detachFrameAboveThreadReply st tcb = st := by
  rcases detachFrameAboveThreadReply_cases st tcb with h | ⟨rid, hRid, h⟩
  · exact h
  · rcases detachReplyFrameAbove_cases h with h' | ⟨r, above, _, hR, hN, _, _, _⟩
    · exact h'
    · exact absurd hN (hNoFrameAbove rid r above hRid hR)

theorem detachFrameAboveThreadReply_scheduler_eq (st : SystemState) (tcb : TCB) :
    (detachFrameAboveThreadReply st tcb).scheduler = st.scheduler := by
  rcases detachFrameAboveThreadReply_cases st tcb with h | ⟨_, _, h⟩
  · rw [h]
  · exact detachReplyFrameAbove_scheduler_eq h

theorem detachFrameAboveThreadReply_machine_eq (st : SystemState) (tcb : TCB) :
    (detachFrameAboveThreadReply st tcb).machine = st.machine := by
  rcases detachFrameAboveThreadReply_cases st tcb with h | ⟨_, _, h⟩
  · rw [h]
  · exact detachReplyFrameAbove_machine_eq h

theorem detachFrameAboveThreadReply_serviceRegistry_eq (st : SystemState) (tcb : TCB) :
    (detachFrameAboveThreadReply st tcb).serviceRegistry = st.serviceRegistry := by
  rcases detachFrameAboveThreadReply_cases st tcb with h | ⟨_, _, h⟩
  · rw [h]
  · exact detachReplyFrameAbove_serviceRegistry_eq h

theorem detachFrameAboveThreadReply_preserves_objects_invExt (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) : (detachFrameAboveThreadReply st tcb).objects.invExt := by
  rcases detachFrameAboveThreadReply_cases st tcb with h | ⟨_, _, h⟩
  · rw [h]; exact hInv
  · exact detachReplyFrameAbove_preserves_objects_invExt hInv h

/-- The detach writes at most one Reply, so every stored TCB is where it was. -/
theorem detachFrameAboveThreadReply_tcb_eq (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (t0 : TCB)
    (hk : st.objects[k]? = some (.tcb t0)) :
    (detachFrameAboveThreadReply st tcb).objects[k]? = some (.tcb t0) := by
  rcases detachFrameAboveThreadReply_cases st tcb with h | ⟨_, _, h⟩
  · rw [h]; exact hk
  · exact detachReplyFrameAbove_tcb_eq hInv h k t0 hk

theorem detachFrameAboveThreadReply_tcb_backward (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (t0 : TCB)
    (hk : (detachFrameAboveThreadReply st tcb).objects[k]? = some (.tcb t0)) :
    st.objects[k]? = some (.tcb t0) := by
  rcases detachFrameAboveThreadReply_cases st tcb with h | ⟨_, _, h⟩
  · rw [h] at hk; exact hk
  · exact detachReplyFrameAbove_tcb_backward hInv h k t0 hk

theorem detachFrameAboveThreadReply_getTcb?_eq (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) (tid : SeLe4n.ThreadId) :
    (detachFrameAboveThreadReply st tcb).getTcb? tid = st.getTcb? tid := by
  rcases detachFrameAboveThreadReply_cases st tcb with h | ⟨_, _, h⟩
  · rw [h]
  · exact detachReplyFrameAbove_getTcb?_eq hInv h tid

/-- WS-RM (`v0.35.6`): **take a caller's reply frame off its stack and consume its
caller link** — seL4's `reply_remove`: the non-head branch clears the frame
above's `replyPrev`, then `reply_unlink` severs the caller↔Reply pair.

The detach runs **first** and the consume second, and that order is the whole
point: `Reply.consumed` clears both stack links on a frame that is not a head, so
a frame still named by the `prev` of the frame above it would falsify
`donationChainWellFormed.prevLinkReciprocal` there — a wedge the later pop
refuses fail-closed.  Detaching first is what leaves nothing pointing down at the
frame being consumed (`detachReplyFrameAboveOrSelf_unreferenced`).

It is deliberately **not** folded into `consumeCallerReply`: that operation's
two-key frame (`consumeCallerReply_objects_frame`) is what the whole IPC
invariant surface rests on, and a third write inside it would falsify the
statement outright.  Sequencing leaves every one of those theorems untouched, and
is also what seL4 does.

On a frame with nothing above it — every head, every bottom frame, and every
Reply the tree consumed before the stack became doubly linked — the detach is the
identity and this **is** `consumeCallerReply`, definitionally
(`removeCallerReplyFrame_eq_consume_of_no_frame_above`). -/
def removeCallerReplyFrame (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) :
    Kernel Unit :=
  fun st => SystemState.consumeCallerReply caller rid (detachReplyFrameAboveOrSelf st rid)

-- ----------------------------------------------------------------------------
-- WS-RM (`v0.35.6`): the folded detach's read/write algebra
-- ----------------------------------------------------------------------------
--
-- Each entry is the identity on the refusal arm and the corresponding
-- `detachReplyFrameAbove` fact on the other, so nothing new is argued here: the
-- fold inherits the primitive's algebra verbatim.

/-- The `cdt` is not an object-store field, so the detach leaves it alone. -/
theorem detachReplyFrameAbove_cdt_eq {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (h : detachReplyFrameAbove st rid = .ok st') : st'.cdt = st.cdt := by
  rcases detachReplyFrameAbove_cases h with rfl | ⟨_, _, _, _, _, _, _, hS⟩
  · rfl
  · exact storeObject_cdt_eq st st' _ _ hS

theorem detachReplyFrameAbove_cdtNodeSlot_eq {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (h : detachReplyFrameAbove st rid = .ok st') : st'.cdtNodeSlot = st.cdtNodeSlot := by
  rcases detachReplyFrameAbove_cases h with rfl | ⟨_, _, _, _, _, _, _, hS⟩
  · rfl
  · exact storeObject_cdtNodeSlot_eq st st' _ _ hS

/-- The detach refuses only where there is a frame above to repair, so a `rid`
with none is the identity on either arm. -/
theorem detachReplyFrameAboveOrSelf_eq_self_of_no_frame_above (st : SystemState)
    (rid : SeLe4n.ReplyId) (hNone : replyFrameAbove? st rid = none) :
    detachReplyFrameAboveOrSelf st rid = st := by
  have hDet : detachReplyFrameAbove st rid = .ok st := by
    cases hR : st.getReply? rid with
    | none => exact detachReplyFrameAbove_of_absent st rid hR
    | some r =>
      cases hN : r.next with
      | none => exact detachReplyFrameAbove_of_no_frame_above st rid r hR hN
      | some l =>
        cases l with
        | head sc => exact detachReplyFrameAbove_of_head st rid r sc hR hN
        | frame above =>
          exact absurd (show replyFrameAbove? st rid = some above by
            simp [replyFrameAbove?, hR, hN]) (by rw [hNone]; exact fun h => by cases h)
  unfold detachReplyFrameAboveOrSelf; rw [hDet]

theorem detachReplyFrameAboveOrSelf_scheduler_eq (st : SystemState) (rid : SeLe4n.ReplyId) :
    (detachReplyFrameAboveOrSelf st rid).scheduler = st.scheduler := by
  rcases detachReplyFrameAboveOrSelf_cases st rid with h | h
  · rw [h]
  · exact detachReplyFrameAbove_scheduler_eq h

theorem detachReplyFrameAboveOrSelf_machine_eq (st : SystemState) (rid : SeLe4n.ReplyId) :
    (detachReplyFrameAboveOrSelf st rid).machine = st.machine := by
  rcases detachReplyFrameAboveOrSelf_cases st rid with h | h
  · rw [h]
  · exact detachReplyFrameAbove_machine_eq h

theorem detachReplyFrameAboveOrSelf_serviceRegistry_eq (st : SystemState)
    (rid : SeLe4n.ReplyId) :
    (detachReplyFrameAboveOrSelf st rid).serviceRegistry = st.serviceRegistry := by
  rcases detachReplyFrameAboveOrSelf_cases st rid with h | h
  · rw [h]
  · exact detachReplyFrameAbove_serviceRegistry_eq h

theorem detachReplyFrameAboveOrSelf_cdt_eq (st : SystemState) (rid : SeLe4n.ReplyId) :
    (detachReplyFrameAboveOrSelf st rid).cdt = st.cdt := by
  rcases detachReplyFrameAboveOrSelf_cases st rid with h | h
  · rw [h]
  · exact detachReplyFrameAbove_cdt_eq h

theorem detachReplyFrameAboveOrSelf_cdtNodeSlot_eq (st : SystemState) (rid : SeLe4n.ReplyId) :
    (detachReplyFrameAboveOrSelf st rid).cdtNodeSlot = st.cdtNodeSlot := by
  rcases detachReplyFrameAboveOrSelf_cases st rid with h | h
  · rw [h]
  · exact detachReplyFrameAbove_cdtNodeSlot_eq h

theorem detachReplyFrameAboveOrSelf_preserves_objects_invExt (st : SystemState)
    (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt) :
    (detachReplyFrameAboveOrSelf st rid).objects.invExt := by
  rcases detachReplyFrameAboveOrSelf_cases st rid with h | h
  · rw [h]; exact hInv
  · exact detachReplyFrameAbove_preserves_objects_invExt hInv h

/-- The fold writes at most the frame `replyFrameAbove?` names. -/
theorem detachReplyFrameAboveOrSelf_objects_ne (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId)
    (hk : ∀ above, replyFrameAbove? st rid = some above → k ≠ above.toObjId) :
    (detachReplyFrameAboveOrSelf st rid).objects[k]? = st.objects[k]? := by
  rcases detachReplyFrameAboveOrSelf_cases st rid with h | h
  · rw [h]
  · refine detachReplyFrameAbove_objects_ne hInv h k ?_
    intro r above hR hN
    exact hk above (by simp [replyFrameAbove?, hR, hN])

theorem detachReplyFrameAboveOrSelf_tcb_eq (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (t0 : TCB)
    (hk : st.objects[k]? = some (.tcb t0)) :
    (detachReplyFrameAboveOrSelf st rid).objects[k]? = some (.tcb t0) := by
  rcases detachReplyFrameAboveOrSelf_cases st rid with h | h
  · rw [h]; exact hk
  · exact detachReplyFrameAbove_tcb_eq hInv h k t0 hk

theorem detachReplyFrameAboveOrSelf_tcb_backward (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (t0 : TCB)
    (hk : (detachReplyFrameAboveOrSelf st rid).objects[k]? = some (.tcb t0)) :
    st.objects[k]? = some (.tcb t0) := by
  rcases detachReplyFrameAboveOrSelf_cases st rid with h | h
  · rw [h] at hk; exact hk
  · exact detachReplyFrameAbove_tcb_backward hInv h k t0 hk

theorem detachReplyFrameAboveOrSelf_getTcb?_eq (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) (tid : SeLe4n.ThreadId) :
    (detachReplyFrameAboveOrSelf st rid).getTcb? tid = st.getTcb? tid := by
  rcases detachReplyFrameAboveOrSelf_cases st rid with h | h
  · rw [h]
  · exact detachReplyFrameAbove_getTcb?_eq hInv h tid

theorem detachReplyFrameAboveOrSelf_non_reply_eq (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId)
    (hNotReply : ∀ r : Reply, st.objects[k]? ≠ some (.reply r)) :
    (detachReplyFrameAboveOrSelf st rid).objects[k]? = st.objects[k]? := by
  rcases detachReplyFrameAboveOrSelf_cases st rid with h | h
  · rw [h]
  · exact detachReplyFrameAbove_non_reply_eq hInv h k hNotReply

/-- A key the fold rewrites holds a Reply on **both** sides, so a read whose value
is not a Reply crosses the fold unchanged in either direction — the iff form
`consumeCallerReply_nonTcbNonReply_agree` composes with. -/
theorem detachReplyFrameAboveOrSelf_non_reply_agree (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) (s : SeLe4n.ObjId) (k : KernelObject)
    (hkR : ∀ rr, k ≠ .reply rr) :
    ((detachReplyFrameAboveOrSelf st rid).objects[s]? = some k ↔ st.objects[s]? = some k) := by
  rcases detachReplyFrameAboveOrSelf_cases st rid with h | h
  · rw [h]
  · rcases detachReplyFrameAbove_cases h with hEq | ⟨_, above, a, _, _, hA, _, hS⟩
    · rw [hEq]
    · by_cases hk : s = above.toObjId
      · subst hk
        refine iff_of_false ?_ ?_
        · rw [storeObject_objects_eq' st _ _ _ hInv hS]
          intro hx
          exact hkR { a with prev := none } (Option.some.inj hx).symm
        · rw [(SystemState.getReply?_eq_some_iff _ _ _).mp hA]
          intro hx
          exact hkR a (Option.some.inj hx).symm
      · rw [storeObject_objects_ne st _ above.toObjId s _ hk hInv hS]

theorem detachReplyFrameAboveOrSelf_notification_backward (st : SystemState)
    (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : (detachReplyFrameAboveOrSelf st rid).objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
  rcases detachReplyFrameAboveOrSelf_cases st rid with h | h
  · rw [h] at hNtfn; exact hNtfn
  · exact detachReplyFrameAbove_notification_backward hInv h oid ntfn hNtfn

/-- Every Reply survives the fold, with at most its stack links rewritten. -/
theorem detachReplyFrameAboveOrSelf_reply_rewrite (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) (oid : SeLe4n.ObjId) (r : Reply)
    (hReply : st.objects[oid]? = some (.reply r)) :
    ∃ r', (detachReplyFrameAboveOrSelf st rid).objects[oid]? = some (.reply r') ∧
      replyStackRewrite r' r := by
  rcases detachReplyFrameAboveOrSelf_cases st rid with h | h
  · exact ⟨r, by rw [h]; exact hReply, replyStackRewrite.refl r⟩
  · exact detachReplyFrameAbove_reply_rewrite hInv h oid r hReply

/-- **WS-RM (`v0.35.6`): the fold's *decision*, read off the object store.**
Either `replyFrameAbove?` names a frame that resolves and reciprocates — and the
fold is exactly that one store — or it does not, and the fold is the identity.
Both branches are distinguished by a predicate over `getReply?` alone, which is
what lets any relation that agrees on objects transport the decision: without it
a congruence would have to re-derive the branch on each side and could not rule
out the two sides taking different ones. -/
theorem detachReplyFrameAboveOrSelf_decision (st : SystemState) (rid : SeLe4n.ReplyId) :
    (∃ (above : SeLe4n.ReplyId) (a : Reply),
        replyFrameAbove? st rid = some above ∧ st.getReply? above = some a ∧
        a.prev = some rid ∧
        storeObject above.toObjId (.reply { a with prev := none }) st
          = .ok ((), detachReplyFrameAboveOrSelf st rid)) ∨
      (detachReplyFrameAboveOrSelf st rid = st ∧
        ∀ (above : SeLe4n.ReplyId) (a : Reply),
          replyFrameAbove? st rid = some above → st.getReply? above = some a →
          a.prev ≠ some rid) := by
  unfold detachReplyFrameAboveOrSelf detachReplyFrameAbove replyFrameAbove?
  cases hR : st.getReply? rid with
  | none => exact Or.inr ⟨by simp, by intro above a h _; simp at h⟩
  | some r =>
    cases hN : r.next with
    | none => exact Or.inr ⟨by simp [hN], by intro above a h _; simp [hN] at h⟩
    | some link =>
      cases link with
      | head sc => exact Or.inr ⟨by simp [hN], by intro above a h _; simp [hN] at h⟩
      | frame above =>
        cases hA : st.getReply? above with
        | none =>
          refine Or.inr ⟨by simp [hN, hA], ?_⟩
          intro ab a h hA2
          simp only [hN] at h
          cases h
          rw [hA] at hA2; cases hA2
        | some a =>
          by_cases hP : a.prev = some rid
          · exact Or.inl ⟨above, a, by simp [hN], hA, hP, by simp [hN, hA, hP, storeObject]⟩
          · refine Or.inr ⟨by simp [hN, hA, hP], ?_⟩
            intro ab a2 h hA2
            simp only [hN] at h
            cases h
            rw [hA] at hA2; cases hA2
            exact hP

/-- **WS-RM (`v0.35.6`): the fold's frame at *every* key.**  A key is either
untouched, or it held a Reply that survives with only its stack links rewritten.
Stated as a disjunction rather than as `objects_ne` plus a side condition because
the consumers below cannot always *exclude* the frame above — the answered
caller's reply-stack neighbour is not a key any reply-path hypothesis names — and
a rewrite is invisible to every conjunct that reads a Reply's `caller` rather
than its `prev` / `next`, which is all of them. -/
theorem detachReplyFrameAboveOrSelf_objects_rewrite (st : SystemState)
    (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt) (x : SeLe4n.ObjId) :
    (detachReplyFrameAboveOrSelf st rid).objects[x]? = st.objects[x]? ∨
      ∃ r r', st.objects[x]? = some (.reply r) ∧
        (detachReplyFrameAboveOrSelf st rid).objects[x]? = some (.reply r') ∧
        replyStackRewrite r' r := by
  rcases detachReplyFrameAboveOrSelf_store_cases st rid with h | ⟨above, a, hA, hS⟩
  · exact Or.inl (by rw [h])
  · by_cases hk : x = above.toObjId
    · subst hk
      exact Or.inr ⟨a, { a with prev := none }, hA,
        storeObject_objects_eq' st _ _ _ hInv hS, ⟨none, a.next, rfl⟩⟩
    · exact Or.inl (storeObject_objects_ne st _ above.toObjId x _ hk hInv hS)

-- ----------------------------------------------------------------------------
-- WS-RM (`v0.35.6`): `removeCallerReplyFrame`'s read/write algebra
-- ----------------------------------------------------------------------------
--
-- Each entry composes the fold's fact above with `consumeCallerReply`'s, which
-- is why none of them needs an argument of its own.

/-- The removal is the consume, run at the state the detach left. -/
theorem removeCallerReplyFrame_eq (st : SystemState) (caller : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) :
    removeCallerReplyFrame caller rid st
      = SystemState.consumeCallerReply caller rid (detachReplyFrameAboveOrSelf st rid) := rfl

/-- **WS-RM (`v0.35.6`): on a frame with nothing above it the removal *is* the
consume**, definitionally.  Every repair of an existing reply-path proof is
therefore a case split on `answeredReplyFrameAbove?` whose `none` branch is that
proof verbatim, and every state the tree reached before the reply path detached
is in that branch. -/
theorem removeCallerReplyFrame_eq_consume_of_no_frame_above (st : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hNone : replyFrameAbove? st rid = none) :
    removeCallerReplyFrame caller rid st = SystemState.consumeCallerReply caller rid st := by
  rw [removeCallerReplyFrame_eq, detachReplyFrameAboveOrSelf_eq_self_of_no_frame_above st rid hNone]

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
    (detachReplyFrameAboveOrSelf_scheduler_eq st rid)

theorem removeCallerReplyFrame_machine_eq (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    st'.machine = st.machine := by
  rw [removeCallerReplyFrame_eq] at hStep
  exact (SystemState.consumeCallerReply_machine_eq _ st' caller rid hStep).trans
    (detachReplyFrameAboveOrSelf_machine_eq st rid)

theorem removeCallerReplyFrame_cdt_eq (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    st'.cdt = st.cdt := by
  rw [removeCallerReplyFrame_eq] at hStep
  exact (SystemState.consumeCallerReply_cdt_eq _ st' caller rid hStep).trans
    (detachReplyFrameAboveOrSelf_cdt_eq st rid)

theorem removeCallerReplyFrame_cdtNodeSlot_eq (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    st'.cdtNodeSlot = st.cdtNodeSlot := by
  rw [removeCallerReplyFrame_eq] at hStep
  exact (SystemState.consumeCallerReply_cdtNodeSlot_eq _ st' caller rid hStep).trans
    (detachReplyFrameAboveOrSelf_cdtNodeSlot_eq st rid)

theorem removeCallerReplyFrame_preserves_objects_invExt (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    st'.objects.invExt := by
  rw [removeCallerReplyFrame_eq] at hStep
  exact SystemState.consumeCallerReply_preserves_objects_invExt _ st' caller rid
    (detachReplyFrameAboveOrSelf_preserves_objects_invExt st rid hObjInv) hStep

theorem removeCallerReplyFrame_nonTcbNonReply_agree (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    ∀ (s : SeLe4n.ObjId) (k : KernelObject),
      (∀ tt, k ≠ .tcb tt) → (∀ rr, k ≠ .reply rr) →
      (st'.objects[s]? = some k ↔ st.objects[s]? = some k) := by
  intro s k hkT hkR
  rw [removeCallerReplyFrame_eq] at hStep
  rw [SystemState.consumeCallerReply_nonTcbNonReply_agree _ st' caller rid
      (detachReplyFrameAboveOrSelf_preserves_objects_invExt st rid hObjInv) hStep s k hkT hkR]
  exact detachReplyFrameAboveOrSelf_non_reply_agree st rid hObjInv s k hkR

/-- Every stored TCB survives the removal, with only the answered caller's
`replyObject` cleared: the detach writes no TCB and the consume's TCB rewrite
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
    (detachReplyFrameAboveOrSelf_preserves_objects_invExt st rid hObjInv) hStep s tx hx
  exact ⟨ty, detachReplyFrameAboveOrSelf_tcb_backward st rid hObjInv s ty hy, hFields⟩

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
    (detachReplyFrameAboveOrSelf_preserves_objects_invExt st rid hObjInv) hStep s ty
    (detachReplyFrameAboveOrSelf_tcb_eq st rid hObjInv s ty hy)

/-- The answered caller's forward link is gone after the removal. -/
theorem removeCallerReplyFrame_replyObject_none (st : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt) :
    ∀ result tcb', removeCallerReplyFrame caller rid st = .ok ((), result) →
      result.getTcb? caller = some tcb' → tcb'.replyObject = none := by
  intro result tcb' hRun hGetT
  rw [removeCallerReplyFrame_eq] at hRun
  exact SystemState.consumeCallerReply_replyObject_none _ caller rid
    (detachReplyFrameAboveOrSelf_preserves_objects_invExt st rid hObjInv) result tcb' hRun hGetT

/-- The consumed Reply reads back as `Reply.consumed` of the record the *detach*
left — which is the pre-state record whenever the consumed frame is not itself
the frame above (it never is: a frame is not above itself under
`prevLinkReciprocal`, and `replyFrameAbove?` names a different key). -/
theorem removeCallerReplyFrame_getReply?_caller_none (st : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (r : Reply)
    (hObjInv : st.objects.invExt)
    (hGet : (detachReplyFrameAboveOrSelf st rid).getReply? rid = some r) :
    ∀ result, removeCallerReplyFrame caller rid st = .ok ((), result) →
      result.getReply? rid = some r.consumed := by
  intro result hRun
  rw [removeCallerReplyFrame_eq] at hRun
  exact SystemState.consumeCallerReply_getReply?_caller_none _ caller rid r
    (detachReplyFrameAboveOrSelf_preserves_objects_invExt st rid hObjInv) hGet result hRun

/-- **WS-RM (`v0.35.6`): the removal frees the consumed Reply**, stated on the
*pre-state's* Reply.  The detach rewrites `rid`'s own frame only in the
degenerate case where it links to itself, which no state satisfying
`donationChainWellFormed` has; the existential tolerates that rather than
assuming it away, and `caller = none` — the only projection the linkage
conjuncts read here — is the same either way. -/
theorem removeCallerReplyFrame_getReply?_free (st : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (r : Reply)
    (hObjInv : st.objects.invExt)
    (hGet : st.getReply? rid = some r) :
    ∀ result, removeCallerReplyFrame caller rid st = .ok ((), result) →
      ∃ r', result.getReply? rid = some r' ∧ r'.caller = none := by
  intro result hRun
  obtain ⟨rd, hrd, _⟩ := detachReplyFrameAboveOrSelf_reply_rewrite st rid hObjInv rid.toObjId r
    ((SystemState.getReply?_eq_some_iff st rid r).mp hGet)
  exact ⟨rd.consumed,
    removeCallerReplyFrame_getReply?_caller_none st caller rid rd hObjInv
      ((SystemState.getReply?_eq_some_iff _ rid rd).mpr hrd) result hRun,
    Reply.consumed_caller rd⟩

/-- **WS-RM (`v0.35.6`): a stack *head* keeps its links across the removal.**
`Reply.consumed_of_head` is deliberate — the donation pop that follows in the same
transition validates the head by exactly this link — and the detach is the
identity on a head (a `.head` names no frame above), so the frame a reply answered
still heads the same context afterwards.  This is what lets the composite payoff
locate the relaxed frame as the one the pop is about to clear. -/
theorem removeCallerReplyFrame_head_getReply?_next (st : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (r : Reply)
    (scId : SeLe4n.SchedContextId) (hObjInv : st.objects.invExt)
    (hR : st.getReply? rid = some r) (hHead : r.next = some (.head scId))
    (st' : SystemState) (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    ∃ r', st'.getReply? rid = some r' ∧ r'.next = some (.head scId) := by
  have hFold : detachReplyFrameAboveOrSelf st rid = st :=
    detachReplyFrameAboveOrSelf_eq_self_of_no_frame_above st rid
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
    (detachReplyFrameAboveOrSelf_preserves_objects_invExt st rid hObjInv) hStep x ?_
  intro hNone
  cases hPre : st.objects[x]? with
  | none => exact hSome hPre
  | some k =>
    cases k with
    | reply r0 =>
      obtain ⟨r1, hr1, _⟩ := detachReplyFrameAboveOrSelf_reply_rewrite st rid hObjInv x r0 hPre
      rw [hr1] at hNone; cases hNone
    | tcb t0 =>
      rw [detachReplyFrameAboveOrSelf_tcb_eq st rid hObjInv x t0 hPre] at hNone; cases hNone
    | _ =>
      rw [detachReplyFrameAboveOrSelf_non_reply_eq st rid hObjInv x (by intro r hr; cases hPre.symm.trans hr), hPre] at hNone
      cases hNone

/-- Every Reply present before the removal is still a Reply after it. -/
theorem removeCallerReplyFrame_getReply?_isSome (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    ∀ (rid' : SeLe4n.ReplyId) (r' : Reply), st.getReply? rid' = some r' →
      ∃ r'', st'.getReply? rid' = some r'' := by
  intro rid' r' hGet'
  rw [removeCallerReplyFrame_eq] at hStep
  obtain ⟨r1, hr1, _⟩ := detachReplyFrameAboveOrSelf_reply_rewrite st rid hObjInv rid'.toObjId r'
    ((SystemState.getReply?_eq_some_iff _ _ _).mp hGet')
  exact SystemState.consumeCallerReply_getReply?_isSome _ st' caller rid
    (detachReplyFrameAboveOrSelf_preserves_objects_invExt st rid hObjInv) hStep rid' r1
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
in — the discipline `recordedReplyServer?` and `replyDonationOwnerHome` already
follow in the same dispatch.

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
    -- WS-OD OD3.1: resolve and validate the reply-stack head **before** any
    -- store, so a head this context does not own commits nothing.
    match donationHeadOf? st scId sc with
    | .error e => .error e
    | .ok head? =>
      let sc' := { sc with boundThread := some originalOwner,
                           scReply := head?.bind (fun p => p.2.prev) }
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

/-- Z7-E: Clean up an active donation when a server with `.donated` binding
blocks on receive without replying first (abnormal path).

Returns the SchedContext to the original owner and sets the server to unbound.
This prevents resource leaks when a server drops a call without replying. -/
def cleanupActiveDonation
    (st : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId) : Except KernelError SystemState :=
  returnDonatedSchedContext st serverTid scId originalOwner newOwner?

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
      donationHeadOf? st scId sc = .ok head? ∧
      storeObject scId.toObjId
        (.schedContext { sc with boundThread := some originalOwner,
                                 scReply := head?.bind (fun p => p.2.prev) }) st = .ok ((), s1) ∧
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
      · cases hHead : donationHeadOf? st scId sc with
        | error _ => intro h; cases h
        | ok head? =>
          simp only []
          cases hS1 : storeObject scId.toObjId
              (.schedContext { sc with boundThread := some originalOwner,
                                       scReply := head?.bind (fun p => p.2.prev) }) st with
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
                        trivial, hHead, by rw [← hS1], hS2, hL1, by rw [← hS3], hL2,
                        by rw [← hS4], rfl⟩
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
only phase in this workstream that changes what the kernel does. -/
theorem returnDonatedSchedContext_eq_legacy_of_none
    (st : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (sc : SchedContext)
    (hSc : st.objects[scId.toObjId]? = some (.schedContext sc))
    (hNoHead : sc.scReply = none) :
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
  have hSame : ({ sc with boundThread := some originalOwner,
                          scReply := (none : Option (SeLe4n.ReplyId × Reply)).bind
                            (fun p => p.2.prev) } : SchedContext)
      = { sc with boundThread := some originalOwner } := by
    show ({ sc with boundThread := some originalOwner,
                    scReply := (none : Option SeLe4n.ReplyId) } : SchedContext) = _
    rw [← hNoHead]
  unfold returnDonatedSchedContext SystemState.getSchedContext?
  rw [hSc]
  -- WS-OD OD4.4: at the bottom of the reply stack the outer-caller guard demands
  -- nothing, so it reduces away and the body is the pre-OD3 one exactly.
  simp only [outerCallerAcceptable_none, Bool.not_true, Bool.false_eq_true, if_false,
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
    hSc, _, _hHead, hS1, hClear, hL1, hS3, hL2, hS4, hEq⟩ :=
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
    hSc, _, _hHead, hS1, hClear, hL1, hS3, hL2, hS4, hEq⟩ :=
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
    hSc, _, _hHead, hS1, hClear, hL1, hS3, hL2, hS4, hEq⟩ :=
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
    hSc, _, _hHead, hS1, hClear, _hL1, hS3, _hL2, hS4, hEq⟩ :=
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
    hSc, _, _hHead, hS1, hClear, hL1, hS3, hL2, hS4, hEq⟩ :=
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
    hSc, _, _hHead, hS1, hClear, hL1, hS3, hL2, hS4, hEq⟩ :=
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
    hSc, _, _hHead, hS1, hClear, hL1, hS3, hL2, hS4, hEq⟩ :=
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
  obtain ⟨_, _, _, _, s1, s2, s3, s4, _, _, _, hS1, hClear, _, hS3, _, hS4, hEq⟩ :=
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
  obtain ⟨_, _, _, _, s1, s2, s3, s4, _, _, _, hS1, hClear, _, hS3, _, hS4, hEq⟩ :=
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
  obtain ⟨_, _, _, _, s1, s2, s3, s4, _, _, _, hS1, hClear, _, hS3, _, hS4, hEq⟩ :=
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
  obtain ⟨sc0, head?, _, _, s1, s2, s3, s4, hSc0, _, hHead, hS1, hClear, _, hS3, _, hS4, hEq⟩ :=
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
  obtain ⟨sc, head?, _, _, _, _, _, _, hSc, _, hHead, _, _, _, _, _, _, _⟩ :=
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
    obtain ⟨sc', head?', _, _, s1, _, _, _, hSc', _, hHead', hS1, hClear, _, _, _, _, _⟩ :=
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
        some (.schedContext { sc with boundThread := some originalOwner,
                                      scReply := head?.bind (fun p => p.2.prev) }) := by
  obtain ⟨sc, head?, clientTcb, serverTcb, s1, s2, s3, s4,
    hSc, _, hHead, hS1, hClear, hL1, hS3, hL2, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeDonationHeadPop_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  refine ⟨sc, head?, hSc, ?_⟩
  -- First write: the rebind and the pop.
  have e1 : s1.objects[scId.toObjId]? =
      some (.schedContext { sc with boundThread := some originalOwner,
                                    scReply := head?.bind (fun p => p.2.prev) }) :=
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
        some { sc with boundThread := some originalOwner,
                       scReply := head?.bind (fun p => p.2.prev) } := by
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
  obtain ⟨_, _, _, _, s1, s2, s3, s4, _, _, _, h1, hClear, _, h3, _, h4, hEq⟩ :=
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
  obtain ⟨_, _, _, _, s1, s2, s3, s4, _, _, _, h1, hClear, _, h3, _, h4, hEq⟩ :=
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
  obtain ⟨_, _, _, _, s1, s2, s3, s4, _, _, _, h1, hClear, _, h3, _, h4, hEq⟩ :=
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

