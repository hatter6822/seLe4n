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
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) => some tcb
    | _ => none

/-- WS-RR RR3.12: a successful `lookupTcb` witnesses that the tid is not reserved —
the half of `lookupTcb`'s guard that lets a lookup be *re-established* in another
state at the same tid. -/
theorem lookupTcb_some_not_reserved
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : lookupTcb st tid = some tcb) : ¬ tid.isReserved := by
  unfold lookupTcb at h
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
  unfold lookupTcb
  rw [if_neg hNotReserved, hObj]

/-- If lookupTcb succeeds, the underlying objects map has a TCB at tid.toObjId. -/
theorem lookupTcb_some_objects
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : lookupTcb st tid = some tcb) :
    st.objects[tid.toObjId]? = some (.tcb tcb) := by
  unfold lookupTcb at h
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
  unfold lookupTcb at hLookup ⊢
  rw [hPreserved]
  exact hLookup

-- ============================================================================
-- Z7: SchedContext Donation Helpers
-- ============================================================================

/-- Z7-B2: Transfer a client's SchedContext to a passive server during IPC Call.

Performs the full ownership transfer of the SchedContext from donor to server:
1. SchedContext `boundThread` updated to point to the server.
2. Donor (client) TCB's `schedContextBinding` cleared to `.unbound` — the donor
   gives up its SchedContext for the duration of the Call.
3. Server TCB gets `schedContextBinding := .donated(clientScId, clientTid)`.

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
This function performs 3 sequential `storeObject` mutations (through states
`st` → `st1` → `st2` → `st3`) with intermediate lookups:
  1. `storeObject` SchedContext with `boundThread := some serverTid` → `st1`.
  2. `storeObject` donor TCB with `schedContextBinding := .unbound` → `st2`.
  3. `storeObject` server TCB with `schedContextBinding := .donated` → `st3`.
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
  -- Step 1: Look up the SchedContext
  match st.objects[clientScId.toObjId]? with
  | some (.schedContext sc) =>
    -- AUD-3b: Defense-in-depth — verify SchedContext is bound to the caller
    if sc.boundThread != some clientTid then .error .invalidArgument
    else
    -- Step 2: Update SchedContext to point to server
    let sc' := { sc with boundThread := some serverTid }
    match storeObject clientScId.toObjId (.schedContext sc') st with
    | .error e => .error e
    | .ok ((), st1) =>
      -- Step 3 (F-3 fix): Clear the donor's binding — the client gives up its
      -- SchedContext for the duration of the Call.  Ordered before the server
      -- store so the server's `.donated` write is the final object mutation.
      match lookupTcb st1 clientTid with
      | none => .error .objectNotFound
      | some clientTcb =>
        let clientTcb' := { clientTcb with schedContextBinding := .unbound }
        match storeObject clientTid.toObjId (.tcb clientTcb') st1 with
        | .error e => .error e
        | .ok ((), st2) =>
          -- Step 4: Look up and update server TCB with donated binding
          match lookupTcb st2 serverTid with
          | none => .error .objectNotFound
          | some serverTcb =>
            let serverTcb' := { serverTcb with
              schedContextBinding := .donated clientScId clientTid }
            match storeObject serverTid.toObjId (.tcb serverTcb') st2 with
            | .error e => .error e
            | .ok ((), st3) =>
              -- S-05/PERF-O1 + F-3: the SchedContext's referencing threads change
              -- from {donor} to {server}: add the server and remove the now-`.unbound`
              -- donor.  This keeps `scThreadIndexConsistent` (a thread is indexed under
              -- `scId` iff its binding references `scId`) and `timeoutBlockedThreads`
              -- accurate — only the server (which actually runs on the SchedContext) is
              -- iterated on budget exhaustion, never the descheduled donor.
              .ok { st3 with scThreadIndex :=
                (scThreadIndexRemove
                  (scThreadIndexAdd st3.scThreadIndex clientScId serverTid)
                  clientScId clientTid) }
  | _ => .error .objectNotFound

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
      if r.donatedSc != some scId then .error .invalidArgument
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
      cases hD : (r.donatedSc != some scId) with
      | true => simp only [if_true]; intro h; cases h
      | false => simp only [Bool.false_eq_true, if_false]; intro h; cases h; rfl

/-- WS-OD OD3.1: a validated head resolves to a Reply that donates **this**
context — the fact the head clear's write is sound on, and the one OD4's push
consumes to know the popped frame was its own. -/
theorem donationHeadOf?_ok_resolves (st : SystemState) (scId : SeLe4n.SchedContextId)
    (sc : SchedContext) (rid : SeLe4n.ReplyId) (r : Reply)
    (h : donationHeadOf? st scId sc = .ok (some (rid, r))) :
    st.objects[rid.toObjId]? = some (.reply r) ∧ r.donatedSc = some scId := by
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
      cases hD : (r0.donatedSc != some scId) with
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

**Three answers, not two.**  `.ok none` means the head *is* the bottom of the
stack, so the pop's target becomes `.bound` — the depth-1 case, and the answer on
every state this tree reaches today.  `.ok (some outer)` names the outer caller,
so the target becomes `.donated scId outer`.  `.error` means a link exists but
does not validate, which is a different fact from there being no link and must
not be conflated with it: a caller that read a corrupt link as "bottom of stack"
would silently settle a scheduling context that is still owed outward.  This is
the same three-way shape `donationHeadOf?` has, for the same reason.

**It validates the frame it follows** (plan §3.4, the confused deputy).  `Reply`
has `prev` and no `next`, and Reply objects are re-linked to new callers by
`replyIdEstablishFresh`, so a stale `prev` over a reused Reply would name a
caller that has nothing to do with this context — handing a thread's scheduling
context to an unrelated thread, in another domain, driven by object reuse.  The
frame below the head is therefore accepted only when it donates **this** context,
exactly as `donationHeadOf?` accepts the head only when it does.  The plan puts
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
    | .ok (some (_, head)) =>
      match head.prev with
      | none => .ok none
      | some below =>
        match st.getReply? below with
        | none => .error .objectNotFound
        | some b =>
          if b.donatedSc != some scId then .error .invalidArgument
          else .ok b.caller

/-- WS-OD OD3.4: **the resolver is inert on every state this tree reaches.**

A context that heads no reply stack has no outer caller, so the argument OD4.4
threads through the six call sites is the literal `none` they pass today.  This
is the theorem that makes OD4.4 a refactor rather than a behaviour change; the
answer stops being `none` exactly when OD4's push writes a `scReply`. -/
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
      b.donatedSc = some scId ∧
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
            cases hDon : (b.donatedSc != some scId) with
            | true => simp only [if_true]; intro h; cases h
            | false =>
              simp only [Bool.false_eq_true, if_false]
              intro h
              exact ⟨sc, rid, head, below, b, rfl, hHead, hPrev, hBelow,
                by simpa using hDon, Except.ok.inj h⟩

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

Both components are `none` on every state this tree reaches today, since nothing
writes a `scReply` until OD4's push (`replyStackBelowHeadReads?_of_no_stack`), so
this widens no live footprint — it declares ahead of the code, which is the
order the plan's own numbering rule requires. -/
def replyStackBelowHeadReads? (st : SystemState) (scId : SeLe4n.SchedContextId) :
    Option SeLe4n.ReplyId × Option SeLe4n.ThreadId :=
  match st.getSchedContext? scId with
  | none => (none, none)
  | some sc =>
    match donationHeadOf? st scId sc with
    | .error _ => (none, none)
    | .ok none => (none, none)
    | .ok (some (_, head)) =>
      match head.prev with
      | none => (none, none)
      | some below =>
        -- The Reply below the head is read whether or not the validation that
        -- follows accepts it, so it is declared on the link alone.  The caller's
        -- TCB is read only when the resolver yields one, which is exactly when
        -- the call site passes a `some` for `outerCallerAcceptable` to check.
        (some below,
         match st.getReply? below with
         | none => none
         | some b => if b.donatedSc != some scId then none else b.caller)

/-- WS-OD OD3.7: **inert on every state this tree reaches.**

A context heading no reply stack has nothing below its head, so both members are
`none` and every footprint that gained them is definitionally the one it was
before (`lockSetExtendOpt S none = S`).  This is what makes the row a
declaration rather than a widening: the members become live exactly when OD4's
push first writes a `scReply`. -/
@[simp] theorem replyStackBelowHeadReads?_of_no_stack (st : SystemState)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc) (hNoHead : sc.scReply = none) :
    replyStackBelowHeadReads? st scId = (none, none) := by
  unfold replyStackBelowHeadReads?
  rw [hSc]
  simp only [donationHeadOf?_of_no_stack st scId sc hNoHead]

/-- WS-OD OD3.7: **the bottom of the stack reads nothing below it.**

The depth-1 shape OD4's first push produces: a head with no `prev` is the last
frame, so the pop reads no further and returns the context `.bound`.  Stated
separately from `_of_no_stack` because the two are different states — no stack at
all, versus a stack exactly one frame deep — and a reader checking that this
footprint is inert at depth 1 needs the second. -/
theorem replyStackBelowHeadReads?_of_bottom_head (st : SystemState)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (rid : SeLe4n.ReplyId) (r : Reply)
    (hSc : st.getSchedContext? scId = some sc)
    (hHead : donationHeadOf? st scId sc = .ok (some (rid, r)))
    (hBottom : r.prev = none) :
    replyStackBelowHeadReads? st scId = (none, none) := by
  unfold replyStackBelowHeadReads?
  rw [hSc]
  simp only [hHead, hBottom]

/-- WS-OD OD3.7: **the declared caller is the resolver's answer.**

The footprint's TCB member and `replyStackOuterCaller?`'s `some` answer are the
same thread whenever the resolver succeeds — so the lock the footprint declares
is a lock on the thread `outerCallerAcceptable` will actually read, not on one
that merely happens to sit below the head.  Without this the two could drift,
which is the shape OD3.5 spent a whole row closing on the delegated reply. -/
theorem replyStackBelowHeadReads?_snd_eq_outerCaller (st : SystemState)
    (scId : SeLe4n.SchedContextId) (outer? : Option SeLe4n.ThreadId)
    (h : replyStackOuterCaller? st scId = .ok outer?) :
    (replyStackBelowHeadReads? st scId).2 = outer? := by
  unfold replyStackBelowHeadReads?
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
            cases hDon : (b.donatedSc != some scId) with
            | true => simp only [if_true]; intro h; cases h
            | false =>
              simp only [Bool.false_eq_true, if_false]
              intro h
              exact Except.ok.inj h

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
      match storeObject rid.toObjId (.reply { r with donatedSc := none, prev := none }) st with
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
             (.reply { r with donatedSc := none, prev := none }) st with
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
      storeObject rid.toObjId (.reply { r with donatedSc := none, prev := none }) st
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
          (.reply { r with donatedSc := none, prev := none }) st with
      | error e => intro h; cases h
      | ok pr =>
        simp only []
        intro h
        cases h
        exact Or.inr ⟨rid, r, rfl,
          (SystemState.getReply?_eq_some_iff st rid r).mp hRep, by rw [← hS]⟩

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
        (.reply { r with donatedSc := none, prev := none }) st = .ok p := ⟨_, rfl⟩
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

/-- Z7-C2: Return a donated SchedContext from a server back to the thread that
donated it, and pop that donation off the context's reply stack.

Performs the reverse binding:
1. SchedContext `boundThread` updated to point back to the donor, and its
   reply-stack head (`scReply`) popped to the reply below;
2. the head reply's stack fields cleared (`donatedSc`, `prev`), when there is a
   head;
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

**This phase is inert.**  No transition writes `Reply.donatedSc`, `Reply.prev`
or `SchedContext.scReply` yet, so `donationHeadOf?` answers `none` on every
reachable state, the head clear is the identity, the resolver answers `none`,
and the operation is the pre-OD3 three-store chain store for store
(`returnDonatedSchedContext_eq_legacy_of_none`).  The push is a later phase, and
lands against a pop that is already correct at depth `n`.

Returns the updated state or error if lookups fail.

**Atomicity contract (AC3-A / I-02 / I-03)**:
This function performs up to 4 sequential `storeObject` mutations through states
`st` → `st1` → `st2` → `st3` → `st4`. The same monad-level atomicity argument as
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
  match st.objects[scId.toObjId]? with
  | some (.schedContext sc) =>
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
        match storeDonationHeadClear (head?.map Prod.fst) st1 with
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
  | _ => .error .objectNotFound

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
      -- WS-OD OD4.4: this path is a call *abandonment*, not a reply, and its
      -- chain behaviour is OD5.4's (teardown) rather than OD4.4's.  See the
      -- note on `cleanupPreReceiveDonationChecked` below for why the resolver
      -- cannot simply be threaded here.
      match returnDonatedSchedContext st receiver scId originalOwner none with
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
      -- WS-OD OD4.4: `none`, matching the defensive twin — see the note above.
      returnDonatedSchedContext st receiver scId originalOwner none
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
      cases hRet : returnDonatedSchedContext st receiver scId owner none with
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
      storeDonationHeadClear (head?.map Prod.fst) s1 = .ok s2 ∧
      lookupTcb s2 originalOwner = some clientTcb ∧
      storeObject originalOwner.toObjId
        (.tcb { clientTcb with
                  schedContextBinding := donationReturnBinding scId newOwner? }) s2
          = .ok ((), s3) ∧
      lookupTcb s3 serverTid = some serverTcb ∧
      storeObject serverTid.toObjId
        (.tcb { serverTcb with schedContextBinding := .unbound }) s3 = .ok ((), s4) ∧
      st' = { s4 with scThreadIndex := st'.scThreadIndex } := by
  unfold returnDonatedSchedContext at h
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
            cases hS2 : storeDonationHeadClear (head?.map Prod.fst) p1.2 with
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
  unfold returnDonatedSchedContext
  rw [hSc]
  -- WS-OD OD4.4: at the bottom of the reply stack the outer-caller guard demands
  -- nothing, so it reduces away and the body is the pre-OD3 one exactly.
  simp only [outerCallerAcceptable_none, Bool.not_true, Bool.false_eq_true, if_false,
    donationHeadOf?_of_no_stack st scId sc hNoHead, Option.map_none,
    storeDonationHeadClear_none, donationReturnBinding_none, hSame]

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
honest replacement — every field a conjunct reads other than `donatedSc` and
`prev` still agrees by `rfl`. -/
def replyStackRewrite (a b : Reply) : Prop :=
  ∃ d p, a = { b with donatedSc := d, prev := p }

theorem replyStackRewrite.refl (r : Reply) : replyStackRewrite r r := ⟨r.donatedSc, r.prev, rfl⟩

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
  have hInv2 : s2.objects.invExt := storeDonationHeadClear_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  -- First write: a SchedContext, which lands on a key holding no Reply.
  have h1 : s1.objects[oid]? = some (.reply r) := by
    by_cases hk : oid = scId.toObjId
    · rw [hk, hSc] at hReply; cases hReply
    · rw [storeObject_objects_ne st s1 scId.toObjId oid _ hk hObjInv hS1]; exact hReply
  -- Second write: the head clear.  At the head key the stack links go; elsewhere nothing does.
  obtain ⟨r2, h2, hR2⟩ : ∃ r2, s2.objects[oid]? = some (.reply r2) ∧ replyStackRewrite r2 r := by
    rcases storeDonationHeadClear_cases hClear with rfl | ⟨rid, r0, _, hRead, hS2⟩
    · exact ⟨r, h1, replyStackRewrite.refl r⟩
    · by_cases hk : oid = rid.toObjId
      · have hStored : s2.objects[rid.toObjId]? = _ := storeObject_objects_eq' s1 _ _ _ hInv1 hS2
        have hReadAt : s1.objects[oid]? = some (.reply r0) := by rw [hk]; exact hRead
        have hr0 : r0 = r := KernelObject.reply.inj (Option.some.inj (hReadAt.symm.trans h1))
        subst hr0
        exact ⟨_, by rw [hk]; exact hStored, ⟨none, none, rfl⟩⟩
      · exact ⟨r, (storeObject_objects_ne s1 s2 rid.toObjId oid _ hk hInv1 hS2).trans h1,
          replyStackRewrite.refl r⟩
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
  have hInv2 : s2.objects.invExt := storeDonationHeadClear_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  obtain ⟨t1, hk1, hR1⟩ := storeObject_tcb_bindingRewrite st s1 scId.toObjId _ hObjInv hS1
    (by intro u hu; rw [hSc] at hu; cases hu) k t0 hk
  -- WS-OD OD3.1: the head clear writes a Reply, so it is invisible to every TCB.
  have hk2 : s2.objects[k]? = some (.tcb t1) :=
    storeDonationHeadClear_tcb_eq hInv1 hClear k t1 hk1
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
  have hInv2 : s2.objects.invExt := storeDonationHeadClear_preserves_objects_invExt hInv1 hClear
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
  have hk1 : s1.objects[k]? = some (.tcb t2) := storeDonationHeadClear_tcb_backward hInv1 hClear k t2 hk2
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
    rcases storeDonationHeadClear_cases hClear with hId | ⟨rid, r, _, hR, hStore⟩
    · rw [hId]
    · have hkR : k ≠ rid.toObjId := by
        intro hEqK
        subst hEqK
        rw [hPre] at h1
        rw [hR] at h1
        exact absurd h1 (by simp)
      exact storeObject_objects_ne s1 s2 _ k _ hkR hInv1 hStore
  have hInv2 : s2.objects.invExt := storeDonationHeadClear_preserves_objects_invExt hInv1 hClear
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

Stated at the *general* `newOwner?` rather than at `none`, so the depth-≥ 2 arm's
frame exists before OD4 makes it reachable. -/
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
  have hInv2 : s2.objects.invExt := storeDonationHeadClear_preserves_objects_invExt hInv1 hClear
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
      storeDonationHeadClear_tcb_backward hInv1 hClear k t' h2
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
  have hInv2 : s2.objects.invExt := storeDonationHeadClear_preserves_objects_invExt hInv1 hClear
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
  have h1 : s1.objects[oid]? = some o := by
    rcases storeDonationHeadClear_cases hClear with rfl | ⟨rid, r, _, _, hS2⟩
    · exact h2
    · by_cases hk : oid = rid.toObjId
      · rw [hk, storeObject_objects_eq' s1 _ _ _ hInv1 hS2] at h2
        exact absurd (by rw [← Option.some.inj h2]; exact trivial) hKind
      · rw [← storeObject_objects_ne s1 s2 rid.toObjId oid _ hk hInv1 hS2]; exact h2
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
  have hInv2 : s2.objects.invExt := storeDonationHeadClear_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  have h1 : s1.objects[oid]? = some o := by
    by_cases hk : oid = scId.toObjId
    · rw [hk, hSc] at hPre
      exact absurd (by rw [← Option.some.inj hPre]; exact trivial) hKind
    · rw [storeObject_objects_ne st s1 scId.toObjId oid _ hk hObjInv hS1]; exact hPre
  have h2 : s2.objects[oid]? = some o := by
    rcases storeDonationHeadClear_cases hClear with rfl | ⟨rid, r, _, hRead, hS2⟩
    · exact h1
    · by_cases hk : oid = rid.toObjId
      · rw [hk, hRead] at h1
        exact absurd (by rw [← Option.some.inj h1]; exact trivial) hKind
      · rw [storeObject_objects_ne s1 s2 rid.toObjId oid _ hk hInv1 hS2]; exact h1
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
  have hInv2 : s2.objects.invExt := storeDonationHeadClear_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  have hInv4 : s4.objects.invExt := storeObject_preserves_objects_invExt s3 s4 _ _ hInv3 hS4
  rw [hEq]; exact hInv4

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
    (hNeHead : ∀ rid : SeLe4n.ReplyId, sc.scReply = some rid → oid ≠ rid.toObjId) :
    st'.objects[oid]? = st.objects[oid]? := by
  obtain ⟨sc0, head?, _, _, s1, s2, s3, s4, hSc0, _, hHead, hS1, hClear, _, hS3, _, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  have hScEq : sc0 = sc := by
    rw [hSc0] at hSc; exact KernelObject.schedContext.inj (Option.some.inj hSc)
  subst hScEq
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeDonationHeadClear_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  have e1 := storeObject_objects_ne st s1 scId.toObjId oid _ hNeSc hObjInv hS1
  have e2 : s2.objects[oid]? = s1.objects[oid]? := by
    rcases storeDonationHeadClear_cases hClear with rfl | ⟨rid, r, hHeadEq, _, hS2⟩
    · rfl
    · refine storeObject_objects_ne s1 s2 rid.toObjId oid _ ?_ hInv1 hS2
      exact hNeHead rid ((donationHeadOf?_ok_key st scId sc0 head? hHead).symm.trans hHeadEq)
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
    newOwner? sc hSc hObjInv h oid hNeSc hNeOwner hNeServer ?_
  intro rid hRid hEqK
  have hKey := donationHeadOf?_ok_key st scId sc head? hHead
  rw [hRid] at hKey
  obtain ⟨p, hp, hpFst⟩ : ∃ p, head? = some p ∧ p.1 = rid := by
    cases head? with
    | none => cases hKey
    | some p => exact ⟨p, rfl, Option.some.inj hKey⟩
  subst hp
  obtain ⟨hObj, _⟩ := donationHeadOf?_ok_resolves st scId sc p.1 p.2 (by rw [hHead])
  exact hNotReply p.2 (by rw [hEqK, ← hpFst]; exact hObj)

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
  have hInv2 : s2.objects.invExt := storeDonationHeadClear_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  refine ⟨sc, head?, hSc, ?_⟩
  -- First write: the rebind and the pop.
  have e1 : s1.objects[scId.toObjId]? =
      some (.schedContext { sc with boundThread := some originalOwner,
                                    scReply := head?.bind (fun p => p.2.prev) }) :=
    storeObject_objects_eq' st scId.toObjId _ _ hObjInv hS1
  -- Second write: the head clear, which lands on a Reply key, never a SchedContext one.
  have e2 : s2.objects[scId.toObjId]? = s1.objects[scId.toObjId]? := by
    rcases storeDonationHeadClear_cases hClear with rfl | ⟨rid, r, _, hRead, hS2⟩
    · rfl
    · refine storeObject_objects_ne s1 s2 rid.toObjId scId.toObjId _ ?_ hInv1 hS2
      intro hEqK
      have hReplyAt : s1.objects[scId.toObjId]? = some (.reply r) := by rw [hEqK]; exact hRead
      cases e1.symm.trans hReplyAt
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
    storeDonationHeadClear_scheduler_eq hClear,
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
    storeDonationHeadClear_serviceRegistry_eq hClear,
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
    storeDonationHeadClear_tlbShootdown_eq hClear, hStore st s1 _ _ h1]

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
    match st.objects[notificationId]? with
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
    match st.objects[notificationId]? with
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
      unfold lookupTcb; simp [hNtfn]
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
    have hLookup : lookupTcb st tid = none := by unfold lookupTcb; simp [hNtfn]
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
      unfold lookupTcb; simp [hEp]
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
      unfold lookupTcb; simp [hCn]
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
      unfold lookupTcb; simp [hVs]
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
  unfold notificationWait
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
  unfold notificationWait at hStep
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
  unfold notificationWait at hStep
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

