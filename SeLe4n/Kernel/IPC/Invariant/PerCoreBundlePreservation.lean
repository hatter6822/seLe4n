-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.IPC.Invariant.PerCoreBundle
import SeLe4n.Kernel.Scheduler.Operations.Selection

/-!
# WS-SM SM6.D.2 — Per-operation preservation of the per-core IPC bundle

This module is the preservation layer of SM6.D (plan
`docs/planning/SMP_CROSS_CORE_IPC_PLAN.md` §3.3, Theorem 3.3.1): each of
the six IPC operations — send, receive, call, reply (+ the combined
reply-receive), signal, wait — preserves every core's view of the IPC
invariant bundle (`ipcInvariantFull_perCore`, SM6.D.1).

## Proof architecture

Nineteen of the bundle's twenty conjuncts read only the object store, so
their per-core preservation is *derived* from the existing single-core
whole-bundle theorems (`…_preserves_ipcInvariantFull`,
`Structural/DualQueueMembership.lean`) through the SM6.D.1 exact-
decomposition bridges — precisely the plan's "the existing single-core
proof carries through" (§3.3), with zero proof duplication and zero
weakening.

The one scheduler-reading conjunct, `passiveServerIdle_perCore`, is the
genuinely new SMP obligation: its slice at a non-boot core is *not*
implied by the boot-pinned conjunct the global bundle carries.  §1–§3
build its preservation the same way the single-core D6 layer did — a
reusable pullback frame (`passiveServerIdleFrameOnCore`, the
core-parameterised counterpart of `passiveServerIdleFrame`), per-store
micro-frames, and one composition per operation following the
operation's branch structure.  Two facts make every micro-frame uniform
in the core: the store-ops never touch the scheduler (their
`…_scheduler_eq` lemmas rewrite *any* core's slot projection), and the
scheduler-ops (`ensureRunnable` / `removeRunnable`) write only
`bootCoreId`'s slots (the SM4.B independence algebra frames every other
core).  **No idle-core assumption is used anywhere** — unlike the
SM4.D-era `…_smp_of_singleCore_and_idle` lifters, these theorems hold
on a state where all four cores are actively scheduling.

Axiom-clean: every theorem depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §0  Home-core / wake-target coherence
-- ============================================================================

/-- WS-SM SM6.D: the per-core bundle's thread-domain restriction
(`threadHomeCore`, SM6.D.1) coincides with the operational cross-core
wake target (`determineTargetCore`, SM5.C) on every live thread — the
invariant slices partition threads by exactly the core the wake path
delivers them to. -/
theorem determineTargetCore_eq_threadHomeCore {st : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB}
    (hTcb : st.getTcb? tid = some tcb) :
    determineTargetCore st tid = threadHomeCore tcb := by
  unfold determineTargetCore threadHomeCore
  rw [hTcb]
  cases h : tcb.cpuAffinity <;> simp [h, Option.getD]

-- ============================================================================
-- §1  The per-core passive-server pullback frame
-- ============================================================================

/-- WS-SM SM6.D.2: the core-parameterised counterpart of the D6
`passiveServerIdleFrame` — a transition frames core `c`'s
`passiveServerIdle_perCore` slice whenever every thread that is unbound,
descheduled *on core `c`*, and in a non-allowed state in the post-state
pulls back to an unbound, core-`c`-descheduled thread with the same
`ipcState` in the pre-state.  TCB lookups route through the typed
`getTcb?` (AK7 discipline). -/
structure passiveServerIdleFrameOnCore (st st' : SystemState) (c : CoreId) : Prop where
  pullback : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
    st'.getTcb? tid = some tcb' →
    tcb'.schedContextBinding = .unbound →
    tid ∉ (st'.scheduler.runQueueOnCore c) →
    (st'.scheduler.currentOnCore c) ≠ some tid →
    ¬ passiveServerIdleAllowed tcb'.ipcState →
    ∃ tcb, st.getTcb? tid = some tcb ∧
      tcb.schedContextBinding = .unbound ∧
      tid ∉ (st.scheduler.runQueueOnCore c) ∧
      (st.scheduler.currentOnCore c) ≠ some tid ∧
      tcb.ipcState = tcb'.ipcState

namespace passiveServerIdleFrameOnCore

/-- Reflexivity: a state frames onto itself on every core. -/
theorem refl (st : SystemState) {c : CoreId} : passiveServerIdleFrameOnCore st st c :=
  ⟨fun _ tcb' h hU hQ hC _ => ⟨tcb', h, hU, hQ, hC, rfl⟩⟩

/-- Transitivity: chain two per-core passive-server frames on the same core. -/
theorem trans {st st' st'' : SystemState} {c : CoreId}
    (h1 : passiveServerIdleFrameOnCore st st' c)
    (h2 : passiveServerIdleFrameOnCore st' st'' c) :
    passiveServerIdleFrameOnCore st st'' c :=
  ⟨fun tid tcb'' h hU hQ hC hNA => by
    obtain ⟨tcb', h', hU', hQ', hC', hIpc'⟩ := h2.pullback tid tcb'' h hU hQ hC hNA
    obtain ⟨tcb, hh, hUU, hQQ, hCC, hIpc⟩ := h1.pullback tid tcb' h' hU' hQ' hC' (hIpc' ▸ hNA)
    exact ⟨tcb, hh, hUU, hQQ, hCC, hIpc.trans hIpc'⟩⟩

end passiveServerIdleFrameOnCore

/-- WS-SM SM6.D.2: a transition that preserves every TCB's `ipcState` and
`schedContextBinding` **backward** and leaves the whole scheduler
untouched frames every core's slice (queue-link rewrites, reply-link
stores). -/
theorem passiveServerIdleFrameOnCore_of_backward {st st' : SystemState} {c : CoreId}
    (hBack : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB), st'.getTcb? tid = some tcb' →
      ∃ tcb, st.getTcb? tid = some tcb ∧
        tcb.ipcState = tcb'.ipcState ∧ tcb.schedContextBinding = tcb'.schedContextBinding)
    (hSched : st'.scheduler = st.scheduler) :
    passiveServerIdleFrameOnCore st st' c :=
  ⟨fun tid tcb' hTcb' hUnbound' hNotInQ' hNotCurrent' _ => by
    obtain ⟨tcb, hTcb, hIpcEq, hBindEq⟩ := hBack tid tcb' hTcb'
    exact ⟨tcb, hTcb, hBindEq.trans hUnbound', by rw [hSched] at hNotInQ'; exact hNotInQ',
      by rw [hSched] at hNotCurrent'; exact hNotCurrent', hIpcEq⟩⟩

/-- WS-SM SM6.D.2: consume a per-core frame — core `c`'s
`passiveServerIdle_perCore` slice carries across a framing transition. -/
theorem passiveServerIdle_perCore_of_frameOnCore {st st' : SystemState} {c : CoreId}
    (hFrame : passiveServerIdleFrameOnCore st st' c)
    (hInv : passiveServerIdle_perCore st c) :
    passiveServerIdle_perCore st' c := by
  intro tid tcb' hTcb' hUnbound' hNotInQ' hNotCurrent'
  by_cases hAllowed : passiveServerIdleAllowed tcb'.ipcState
  · exact hAllowed
  · obtain ⟨tcb, hTcb, hUnbound, hNotInQ, hNotCurrent, hIpc⟩ :=
      hFrame.pullback tid tcb' hTcb' hUnbound' hNotInQ' hNotCurrent' hAllowed
    rw [← hIpc]
    exact hInv tid tcb hTcb hUnbound hNotInQ hNotCurrent

-- ============================================================================
-- §2  Per-store / per-scheduler-op micro-frames (all cores, no idle crutch)
-- ============================================================================

/-- Object-store agreement lifts to `getTcb?` agreement (public so the
staged cross-core mirrors can reuse it). -/
theorem getTcb?_congr_objects
    {st st' : SystemState} (h : st'.objects = st.objects)
    (tid : SeLe4n.ThreadId) : st'.getTcb? tid = st.getTcb? tid := by
  unfold SystemState.getTcb?; rw [h]

open SeLe4n.Model.SystemState in
/-- SM6.D.2 micro-frame: a `storeObject` of a **non-TCB** object frames
every core's slice (the scheduler is untouched; every TCB slot is
preserved). -/
theorem storeObject_oldNonTcb_passiveServerIdleFrameOnCore
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject) {c : CoreId}
    (hNewNonTcb : ∀ t, obj ≠ .tcb t)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok ((), st')) :
    passiveServerIdleFrameOnCore st st' c := by
  have hSched := storeObject_scheduler_eq st st' id obj hStore
  refine ⟨fun tid tcb' hTcb' hUnbound' hNotInQ' hNotCurrent' _ => ?_⟩
  have hRaw' := (getTcb?_eq_some_iff st' tid tcb').mp hTcb'
  by_cases hEq : tid.toObjId = id
  · rw [hEq, storeObject_objects_eq st st' id obj hObjInv hStore] at hRaw'
    exact absurd (Option.some.inj hRaw') (hNewNonTcb tcb')
  · rw [storeObject_objects_ne st st' id tid.toObjId obj hEq hObjInv hStore] at hRaw'
    exact ⟨tcb', (getTcb?_eq_some_iff st tid tcb').mpr hRaw', hUnbound',
      by rw [hSched] at hNotInQ'; exact hNotInQ',
      by rw [hSched] at hNotCurrent'; exact hNotCurrent', rfl⟩

open SeLe4n.Model.SystemState in
/-- SM6.D.2 micro-frame: a `storeObject` rewriting a TCB whose new
`ipcState` is passive-allowed, or whose pre-state binding is not
`.unbound`, frames every core's slice. -/
theorem storeObject_modifiedTcb_passiveServerIdleFrameOnCore
    (st st' : SystemState) (id : SeLe4n.ObjId) (origTcb newTcb : TCB) {c : CoreId}
    (_hOrig : st.objects[id]? = some (.tcb origTcb))
    (hBindEq : newTcb.schedContextBinding = origTcb.schedContextBinding)
    (hAllowedOrBound : passiveServerIdleAllowed newTcb.ipcState ∨ origTcb.schedContextBinding ≠ .unbound)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id (.tcb newTcb) st = .ok ((), st')) :
    passiveServerIdleFrameOnCore st st' c := by
  have hSched := storeObject_scheduler_eq st st' id (.tcb newTcb) hStore
  refine ⟨fun tid tcb' hTcb' hUnbound' hNotInQ' hNotCurrent' hNA => ?_⟩
  have hRaw' := (getTcb?_eq_some_iff st' tid tcb').mp hTcb'
  by_cases hEq : tid.toObjId = id
  · rw [hEq, storeObject_objects_eq st st' id (.tcb newTcb) hObjInv hStore] at hRaw'
    obtain rfl := KernelObject.tcb.inj (Option.some.inj hRaw')
    rcases hAllowedOrBound with hA | hB
    · exact absurd hA hNA
    · exact absurd (hBindEq ▸ hUnbound') hB
  · rw [storeObject_objects_ne st st' id tid.toObjId (.tcb newTcb) hEq hObjInv hStore] at hRaw'
    exact ⟨tcb', (getTcb?_eq_some_iff st tid tcb').mpr hRaw', hUnbound',
      by rw [hSched] at hNotInQ'; exact hNotInQ',
      by rw [hSched] at hNotCurrent'; exact hNotCurrent', rfl⟩

open SeLe4n.Model.SystemState in
/-- SM6.D.2 micro-frame: `storeTcbIpcState` frames every core's slice (the
new `ipcState` is allowed, or the rewritten thread is bound). -/
theorem storeTcbIpcState_passiveServerIdleFrameOnCore
    (st st' : SystemState) (tid0 : SeLe4n.ThreadId) (ipc : ThreadIpcState) {c : CoreId}
    (hAllowedOrBound : passiveServerIdleAllowed ipc ∨
      ∀ tcb, st.getTcb? tid0 = some tcb → tcb.schedContextBinding ≠ .unbound)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid0 ipc = .ok st') :
    passiveServerIdleFrameOnCore st st' c := by
  unfold storeTcbIpcState at hStep
  cases hL : lookupTcb st tid0 with
  | none => simp [hL] at hStep
  | some tcb =>
    simp only [hL] at hStep
    cases hSO : storeObject tid0.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hSO] at hStep
    | ok p =>
      obtain ⟨_, st''⟩ := p
      simp only [hSO, Except.ok.injEq] at hStep
      subst hStep
      have hOrig := lookupTcb_some_objects st tid0 tcb hL
      refine storeObject_modifiedTcb_passiveServerIdleFrameOnCore st st'' tid0.toObjId tcb
        { tcb with ipcState := ipc } hOrig rfl ?_ hObjInv hSO
      rcases hAllowedOrBound with hA | hB
      · exact Or.inl hA
      · exact Or.inr (hB tcb ((getTcb?_eq_some_iff st tid0 tcb).mpr hOrig))

open SeLe4n.Model.SystemState in
/-- SM6.D.2 micro-frame: `storeTcbIpcStateAndMessage` frames every core's
slice. -/
theorem storeTcbIpcStateAndMessage_passiveServerIdleFrameOnCore
    (st st' : SystemState) (tid0 : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (msg : Option IpcMessage) {c : CoreId}
    (hAllowedOrBound : passiveServerIdleAllowed ipc ∨
      ∀ tcb, st.getTcb? tid0 = some tcb → tcb.schedContextBinding ≠ .unbound)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid0 ipc msg = .ok st') :
    passiveServerIdleFrameOnCore st st' c := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hL : lookupTcb st tid0 with
  | none => simp [hL] at hStep
  | some tcb =>
    simp only [hL] at hStep
    cases hSO : storeObject tid0.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hSO] at hStep
    | ok p =>
      obtain ⟨_, st''⟩ := p
      simp only [hSO, Except.ok.injEq] at hStep
      subst hStep
      have hOrig := lookupTcb_some_objects st tid0 tcb hL
      refine storeObject_modifiedTcb_passiveServerIdleFrameOnCore st st'' tid0.toObjId tcb
        { tcb with ipcState := ipc, pendingMessage := msg } hOrig rfl ?_ hObjInv hSO
      rcases hAllowedOrBound with hA | hB
      · exact Or.inl hA
      · exact Or.inr (hB tcb ((getTcb?_eq_some_iff st tid0 tcb).mpr hOrig))

open SeLe4n.Model.SystemState in
/-- SM6.D.2 micro-frame: `storeTcbReceiveComplete` frames every core's
slice (sets the rewritten thread `.ready`, an allowed passive state). -/
theorem storeTcbReceiveComplete_passiveServerIdleFrameOnCore
    (st st' : SystemState) (tid0 : SeLe4n.ThreadId) (msg : Option IpcMessage) {c : CoreId}
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbReceiveComplete st tid0 msg = .ok st') :
    passiveServerIdleFrameOnCore st st' c := by
  unfold storeTcbReceiveComplete at hStep
  cases hL : lookupTcb st tid0 with
  | none => simp [hL] at hStep
  | some tcb =>
    simp only [hL] at hStep
    cases hSO : storeObject tid0.toObjId (.tcb { tcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none }) st with
    | error e => simp [hSO] at hStep
    | ok p =>
      obtain ⟨_, st''⟩ := p
      simp only [hSO, Except.ok.injEq] at hStep
      subst hStep
      have hOrig := lookupTcb_some_objects st tid0 tcb hL
      exact storeObject_modifiedTcb_passiveServerIdleFrameOnCore st st'' tid0.toObjId tcb
        { tcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none }
        hOrig rfl (Or.inl (Or.inl rfl)) hObjInv hSO

/-- SM6.D.2: `ensureRunnable` leaves every core's `current` slot untouched
(it writes only `bootCoreId`'s run queue). -/
theorem ensureRunnable_currentOnCore (st : SystemState) (tid0 : SeLe4n.ThreadId) (c : CoreId) :
    (ensureRunnable st tid0).scheduler.currentOnCore c = st.scheduler.currentOnCore c := by
  unfold ensureRunnable
  split
  · rfl
  · split <;> simp

/-- SM6.D.2: `ensureRunnable` only *adds* to `bootCoreId`'s run queue —
every pre-state member of any core's queue remains a member. -/
theorem ensureRunnable_mem_old_onCore (st : SystemState) (tid0 x : SeLe4n.ThreadId)
    (c : CoreId) (hMem : x ∈ (st.scheduler.runQueueOnCore c)) :
    x ∈ ((ensureRunnable st tid0).scheduler.runQueueOnCore c) := by
  unfold ensureRunnable
  split
  · exact hMem
  · split
    · by_cases hc : bootCoreId = c
      · subst hc
        simp only [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
        rw [RunQueue.mem_insert]
        exact Or.inl hMem
      · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hc]
        exact hMem
    · exact hMem

/-- SM6.D.2 micro-frame: `ensureRunnable` frames every core's slice — it
only adds a thread to the boot run queue (so every descheduled thread in
the post-state was descheduled in the pre-state), leaves every core's
`current` untouched, and preserves the object map. -/
theorem ensureRunnable_passiveServerIdleFrameOnCore
    (st : SystemState) (tid0 : SeLe4n.ThreadId) {c : CoreId} :
    passiveServerIdleFrameOnCore st (ensureRunnable st tid0) c := by
  refine ⟨fun tid tcb' hTcb' hUnbound' hNotInQ' hNotCurrent' _ => ?_⟩
  rw [getTcb?_congr_objects (ensureRunnable_preserves_objects st tid0) tid] at hTcb'
  refine ⟨tcb', hTcb', hUnbound', ?_, ?_, rfl⟩
  · exact fun hIn => hNotInQ' (ensureRunnable_mem_old_onCore st tid0 tid c hIn)
  · rwa [ensureRunnable_currentOnCore st tid0 c] at hNotCurrent'

/-- SM6.D.2: on a core other than `bootCoreId`, `removeRunnable` leaves the
run-queue slot untouched. -/
theorem removeRunnable_runQueueOnCore_other (st : SystemState) (tid0 : SeLe4n.ThreadId)
    (c : CoreId) (hc : bootCoreId ≠ c) :
    (removeRunnable st tid0).scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c := by
  simp [removeRunnable, hc]

/-- SM6.D.2: on a core other than `bootCoreId`, `removeRunnable` leaves the
`current` slot untouched. -/
theorem removeRunnable_currentOnCore_other (st : SystemState) (tid0 : SeLe4n.ThreadId)
    (c : CoreId) (hc : bootCoreId ≠ c) :
    (removeRunnable st tid0).scheduler.currentOnCore c = st.scheduler.currentOnCore c := by
  simp [removeRunnable, hc]

open SeLe4n.Model.SystemState in
/-- SM6.D.2 micro-frame: `removeRunnable` frames every core's slice given
the removed thread is bound or already in an allowed state — the only
thread whose descheduled status changes (on `bootCoreId`; other cores'
slots are untouched by the SM4.B independence algebra) is the removed
one, which the pullback filter excludes. -/
theorem removeRunnable_passiveServerIdleFrameOnCore
    (st : SystemState) (removed : SeLe4n.ThreadId) {c : CoreId}
    (hRemoved : ∀ tcb, st.getTcb? removed = some tcb →
      tcb.schedContextBinding ≠ .unbound ∨ passiveServerIdleAllowed tcb.ipcState) :
    passiveServerIdleFrameOnCore st (removeRunnable st removed) c := by
  refine ⟨fun tid tcb' hTcb' hUnbound' hNotInQ' hNotCurrent' hNA => ?_⟩
  rw [getTcb?_congr_objects (removeRunnable_preserves_objects st removed) tid] at hTcb'
  by_cases hEq : tid = removed
  · subst hEq
    rcases hRemoved tcb' hTcb' with hB | hA
    · exact absurd hUnbound' hB
    · exact absurd hA hNA
  · refine ⟨tcb', hTcb', hUnbound', ?_, ?_, rfl⟩
    · by_cases hc : bootCoreId = c
      · subst hc
        exact fun hIn => hNotInQ' ((removeRunnable_mem st removed tid).mpr ⟨hIn, hEq⟩)
      · intro hIn
        apply hNotInQ'
        rw [removeRunnable_runQueueOnCore_other st removed c hc]
        exact hIn
    · by_cases hc : bootCoreId = c
      · subst hc
        intro hCur
        apply hNotCurrent'
        rw [removeRunnable_scheduler_current, hCur, if_neg (fun h => hEq (Option.some.inj h))]
      · intro hCur
        apply hNotCurrent'
        rw [removeRunnable_currentOnCore_other st removed c hc]
        exact hCur

open SeLe4n.Model.SystemState in
/-- SM6.D.2 micro-frame: `endpointQueuePopHead` frames every core's slice
(queue-link rewrites + endpoint store preserve every `ipcState`/binding
and the scheduler). -/
theorem endpointQueuePopHead_passiveServerIdleFrameOnCore
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (rTid : SeLe4n.ThreadId) (rTcb : TCB) {c : CoreId}
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (rTid, rTcb, st')) :
    passiveServerIdleFrameOnCore st st' c :=
  passiveServerIdleFrameOnCore_of_backward
    (fun tid tcb' hTcb' => by
      have hRaw' := (getTcb?_eq_some_iff st' tid tcb').mp hTcb'
      obtain ⟨tcb, hTcb, hIpcEq⟩ := endpointQueuePopHead_tcb_ipcState_backward endpointId isReceiveQ
        st st' rTid tid tcb' hObjInv hStep hRaw'
      obtain ⟨tcb2, hTcb2, hBindEq⟩ := endpointQueuePopHead_sameSchedContextBindings endpointId
        isReceiveQ st st' rTid rTcb hObjInv hStep tid tcb' hRaw'
      rw [hTcb] at hTcb2; obtain rfl := KernelObject.tcb.inj (Option.some.inj hTcb2)
      exact ⟨tcb, (getTcb?_eq_some_iff st tid tcb).mpr hTcb, hIpcEq, hBindEq⟩)
    (endpointQueuePopHead_scheduler_eq endpointId isReceiveQ st st' rTid hStep)

open SeLe4n.Model.SystemState in
/-- SM6.D.2 micro-frame: `endpointQueueEnqueue` frames every core's slice. -/
theorem endpointQueueEnqueue_passiveServerIdleFrameOnCore
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid0 : SeLe4n.ThreadId)
    (st st' : SystemState) {c : CoreId}
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid0 st = .ok st') :
    passiveServerIdleFrameOnCore st st' c :=
  passiveServerIdleFrameOnCore_of_backward
    (fun tid tcb' hTcb' => by
      have hRaw' := (getTcb?_eq_some_iff st' tid tcb').mp hTcb'
      obtain ⟨tcb, hTcb, hIpcEq⟩ := endpointQueueEnqueue_tcb_ipcState_backward endpointId isReceiveQ
        tid0 st st' tid tcb' hObjInv hStep hRaw'
      obtain ⟨tcb2, hTcb2, hBindEq⟩ := endpointQueueEnqueue_sameSchedContextBindings endpointId
        isReceiveQ tid0 st st' hObjInv hStep tid tcb' hRaw'
      rw [hTcb] at hTcb2; obtain rfl := KernelObject.tcb.inj (Option.some.inj hTcb2)
      exact ⟨tcb, (getTcb?_eq_some_iff st tid tcb).mpr hTcb, hIpcEq, hBindEq⟩)
    (endpointQueueEnqueue_scheduler_eq endpointId isReceiveQ tid0 st st' hStep)

open SeLe4n.Model.SystemState in
/-- SM6.D.2 micro-frame: `linkCallerReply` frames every core's slice
(reply-object store + caller `replyObject` write — both preserve every
`ipcState`/binding and the scheduler). -/
theorem linkCallerReply_passiveServerIdleFrameOnCore
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) {c : CoreId}
    (hObjInv : st.objects.invExt)
    (hStep : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    passiveServerIdleFrameOnCore st st' c :=
  passiveServerIdleFrameOnCore_of_backward
    (fun tid tcb' hTcb' => by
      have hRaw' := (getTcb?_eq_some_iff st' tid tcb').mp hTcb'
      obtain ⟨tcb, hTcb, hIpcEq⟩ := linkCallerReply_tcb_ipcState_backward st st' caller rid tid tcb' hObjInv hStep hRaw'
      obtain ⟨tcb2, hTcb2, hBindEq⟩ := linkCallerReply_sameSchedContextBindings st st' caller rid hObjInv hStep tid tcb' hRaw'
      rw [hTcb] at hTcb2; obtain rfl := KernelObject.tcb.inj (Option.some.inj hTcb2)
      exact ⟨tcb, (getTcb?_eq_some_iff st tid tcb).mpr hTcb, hIpcEq, hBindEq⟩)
    (linkCallerReply_scheduler_eq st st' caller rid hStep)

open SeLe4n.Model.SystemState in
/-- SM6.D.2 micro-frame: `linkServerStashedReply` frames every core's
slice. -/
theorem linkServerStashedReply_passiveServerIdleFrameOnCore
    (st st' : SystemState) (caller server : SeLe4n.ThreadId) {c : CoreId}
    (hObjInv : st.objects.invExt)
    (hStep : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    passiveServerIdleFrameOnCore st st' c :=
  passiveServerIdleFrameOnCore_of_backward
    (fun tid tcb' hTcb' => by
      have hRaw' := (getTcb?_eq_some_iff st' tid tcb').mp hTcb'
      obtain ⟨tcb, hTcb, hIpcEq⟩ := linkServerStashedReply_tcb_ipcState_backward st st' caller server tid tcb' hObjInv hStep hRaw'
      obtain ⟨tcb2, hTcb2, hBindEq⟩ := linkServerStashedReply_sameSchedContextBindings st st' caller server hObjInv hStep tid tcb' hRaw'
      rw [hTcb] at hTcb2; obtain rfl := KernelObject.tcb.inj (Option.some.inj hTcb2)
      exact ⟨tcb, (getTcb?_eq_some_iff st tid tcb).mpr hTcb, hIpcEq, hBindEq⟩)
    (linkServerStashedReply_scheduler_eq st st' caller server hStep)

open SeLe4n.Model.SystemState in
/-- SM6.D.2 micro-frame: `consumeCallerReply` frames every core's slice
(the scheduler is untouched and `schedContextBinding`/`ipcState` are
preserved TCB fields). -/
theorem consumeCallerReply_passiveServerIdleFrameOnCore
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) {c : CoreId}
    (hObjInv : st.objects.invExt)
    (hStep : consumeCallerReply caller rid st = .ok ((), st')) :
    passiveServerIdleFrameOnCore st st' c := by
  have hFwd := consumeCallerReply_tcb_forward st st' caller rid hObjInv hStep
  have hSched := consumeCallerReply_scheduler_eq st st' caller rid hStep
  refine ⟨fun tid tcb' h hU hQ hC _ => ?_⟩
  obtain ⟨tcb, hSt, hIS, _, _, _, _, hSCB, _⟩ :=
    hFwd tid.toObjId tcb' ((getTcb?_eq_some_iff st' tid tcb').mp h)
  rw [hSched] at hQ hC
  exact ⟨tcb, (getTcb?_eq_some_iff st tid tcb).mpr hSt, hSCB.symm.trans hU, hQ, hC, hIS.symm⟩

open SeLe4n.Model.SystemState in
/-- SM6.D.2 micro-frame: `cleanupPreReceiveDonation` frames every core's
slice.  The donation return rebinds the owner `.unbound → .bound`
(excluded from the pullback: it becomes bound) and the receiver
`.donated → .unbound` (excluded: it is allowed via `hReceiverReady`);
every other thread's binding is framed. -/
theorem cleanupPreReceiveDonation_passiveServerIdleFrameOnCore
    (st : SystemState) (receiver : SeLe4n.ThreadId) {c : CoreId}
    (hObjInv : st.objects.invExt)
    (hReceiverReady : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
      passiveServerIdleAllowed tcb.ipcState) :
    passiveServerIdleFrameOnCore st (cleanupPreReceiveDonation st receiver) c := by
  unfold cleanupPreReceiveDonation
  cases hL : lookupTcb st receiver with
  | none => exact passiveServerIdleFrameOnCore.refl st
  | some recvTcb =>
    simp only []
    cases hBind : recvTcb.schedContextBinding with
    | unbound => exact passiveServerIdleFrameOnCore.refl st
    | bound scId => exact passiveServerIdleFrameOnCore.refl st
    | donated scId originalOwner =>
      simp only []
      cases hRet : returnDonatedSchedContext st receiver scId originalOwner with
      | error _ => exact passiveServerIdleFrameOnCore.refl st
      | ok st' =>
        simp only []
        refine ⟨fun tid tcb' hTcb' hUnbound' hNotInQ' hNotCurrent' hNA => ?_⟩
        have hRaw' := (getTcb?_eq_some_iff st' tid tcb').mp hTcb'
        obtain ⟨tcbI, hTcbI, _, _, hIpcEq, _⟩ := returnDonatedSchedContext_tcb_queue_backward
          st st' receiver scId originalOwner hObjInv hRet tid.toObjId tcb' hRaw'
        have hSched := returnDonatedSchedContext_scheduler_eq st st' receiver scId originalOwner hRet
        have h3 := returnDonatedSchedContext_tcb_schedContextBinding_backward st st' receiver scId
          originalOwner hObjInv hRet tid.toObjId tcb' hRaw'
        by_cases hRecv : tid.toObjId = receiver.toObjId
        · exfalso
          apply hNA
          rw [← hIpcEq]
          exact hReceiverReady tcbI ((getTcb?_eq_some_iff st receiver tcbI).mpr (by
            have := hRecv ▸ hTcbI
            exact this))
        · by_cases hOwner : tid.toObjId = originalOwner.toObjId
          · rw [h3.2.1 hRecv hOwner] at hUnbound'; cases hUnbound'
          · obtain ⟨tcbB, hTcbB, hBindEq⟩ := h3.2.2 hRecv hOwner
            have hIdEq : tcbI = tcbB := KernelObject.tcb.inj (Option.some.inj (hTcbI.symm.trans hTcbB))
            exact ⟨tcbI, (getTcb?_eq_some_iff st tid tcbI).mpr hTcbI,
              by rw [hIdEq]; exact hBindEq.trans hUnbound',
              by rw [hSched] at hNotInQ'; exact hNotInQ',
              by rw [hSched] at hNotCurrent'; exact hNotCurrent', hIpcEq⟩

-- ============================================================================
-- §3  Per-operation per-core passive-server frames
-- ============================================================================
--
-- Each composition mirrors the D6 boot-core proof one-for-one (same branch
-- structure, same side conditions), with every micro-frame replaced by its
-- core-parameterised counterpart — so the frame holds on EVERY core `c`,
-- with no idle-core assumption.

open SeLe4n.Model.SystemState in
/-- SM6.D.2: `notificationSignal` frames every core's slice.  It wakes the
head waiter `.ready` and reschedules it (allowed state); the no-waiter
branch only rewrites the notification object. -/
theorem notificationSignal_passiveServerIdleFrameOnCore
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    passiveServerIdleFrameOnCore st st' c := by
  simp only [notificationSignal] at hStep
  split at hStep
  · rename_i ntfn hObj
    cases hWaiters : ntfn.waitingThreads.tail? with
    | some headTail =>
      obtain ⟨waiter, rest⟩ := headTail
      simp only [hWaiters] at hStep
      split at hStep
      next => contradiction
      next st1 hSO =>
        have hF1 := storeObject_oldNonTcb_passiveServerIdleFrameOnCore (c := c)
          st st1 notificationId (.notification _) (fun _ => by simp) hObjInv hSO
        have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
        split at hStep
        next => contradiction
        next st2 hSM =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          exact (hF1.trans (storeTcbIpcStateAndMessage_passiveServerIdleFrameOnCore st1 st2 waiter .ready _
            (Or.inl (Or.inl rfl)) hObjInv1 hSM)).trans
            (ensureRunnable_passiveServerIdleFrameOnCore st2 waiter)
    | none =>
      simp only [hWaiters] at hStep
      split at hStep
      all_goals
        exact storeObject_oldNonTcb_passiveServerIdleFrameOnCore
          st st' notificationId (.notification _) (fun _ => by simp) hObjInv hStep
  · contradiction
  · contradiction

open SeLe4n.Model.SystemState in
/-- SM6.D.2: `notificationWait` frames every core's slice.  The deliver
branch wakes the waiter `.ready`; the block branch sets it
`.blockedOnNotification` and deschedules it — both allowed passive
states. -/
theorem notificationWait_passiveServerIdleFrameOnCore
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (badge : Option SeLe4n.Badge) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notificationId waiter st = .ok (badge, st')) :
    passiveServerIdleFrameOnCore st st' c := by
  simp only [notificationWait] at hStep
  split at hStep
  · rename_i ntfn hObj
    split at hStep
    · split at hStep
      next => contradiction
      next st1 hSO =>
        have hF1 := storeObject_oldNonTcb_passiveServerIdleFrameOnCore (c := c)
          st st1 notificationId (.notification _) (fun _ => by simp) hObjInv hSO
        have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
        split at hStep
        next => contradiction
        next st2 hSI =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          exact hF1.trans (storeTcbIpcState_passiveServerIdleFrameOnCore st1 st2 waiter .ready
            (Or.inl (Or.inl rfl)) hObjInv1 hSI)
    · split at hStep
      · contradiction
      · rename_i waiterTcb hLookup
        split at hStep
        · contradiction
        · split at hStep
          · contradiction
          · split at hStep
            next => contradiction
            next st1 hSO =>
              have hF1 := storeObject_oldNonTcb_passiveServerIdleFrameOnCore (c := c)
                st st1 notificationId (.notification _) (fun _ => by simp) hObjInv hSO
              have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
              have hWaiterObj := lookupTcb_some_objects st waiter waiterTcb hLookup
              have hNeWN : waiter.toObjId ≠ notificationId := by
                intro h; rw [h, hObj] at hWaiterObj; simp at hWaiterObj
              have hOrig1 := (storeObject_objects_ne st st1 notificationId waiter.toObjId _
                hNeWN hObjInv hSO).trans hWaiterObj
              have hLk1 : lookupTcb st1 waiter = some waiterTcb := by
                rw [lookupTcb]; rw [lookupTcb] at hLookup
                by_cases hRes : waiter.isReserved
                · rw [if_pos hRes] at hLookup; simp at hLookup
                · rw [if_neg hRes, hOrig1]
              split at hStep
              next => contradiction
              next st2 hSI =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, rfl⟩ := hStep
                rw [storeTcbIpcState_fromTcb_eq hLk1] at hSI
                refine (hF1.trans (storeTcbIpcState_passiveServerIdleFrameOnCore st1 st2 waiter
                    (.blockedOnNotification notificationId)
                    (Or.inl (Or.inr (Or.inl ⟨notificationId, Or.inr rfl⟩))) hObjInv1 hSI)).trans
                  (removeRunnable_passiveServerIdleFrameOnCore st2 waiter (fun tcb hTcb => Or.inr ?_))
                rw [storeTcbIpcState_ipcState_eq st1 st2 waiter _ hObjInv1 hSI tcb
                  ((getTcb?_eq_some_iff st2 waiter tcb).mp hTcb)]
                exact Or.inr (Or.inl ⟨notificationId, Or.inr rfl⟩)
  · contradiction
  · contradiction

open SeLe4n.Model.SystemState in
/-- SM6.D.2: `endpointSendDual` frames every core's slice.  Rendezvous:
pop the receiver + complete it `.ready` + reschedule.  Block: enqueue the
sender + set it `.blockedOnSend` (non-allowed, so the sender must hold a
SchedContext — `hSenderNotUnbound`) + deschedule. -/
theorem endpointSendDual_passiveServerIdleFrameOnCore
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hSenderNotUnbound : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        tcb.schedContextBinding ≠ .unbound)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    passiveServerIdleFrameOnCore st st' c := by
  unfold endpointSendDual at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
          have hF1 := endpointQueuePopHead_passiveServerIdleFrameOnCore (c := c) endpointId true st pair.2.2 pair.1 _ hObjInv hPop
          cases hMsg : storeTcbReceiveComplete pair.2.2 pair.1 (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact (hF1.trans (storeTcbReceiveComplete_passiveServerIdleFrameOnCore pair.2.2 st2 pair.1 (some msg) hObjInv1 hMsg)).trans
              (ensureRunnable_passiveServerIdleFrameOnCore st2 pair.1)
      | none =>
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false sender st st1 hObjInv hEnq
          have hF1 := endpointQueueEnqueue_passiveServerIdleFrameOnCore (c := c) endpointId false sender st st1 hObjInv hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            refine (hF1.trans (storeTcbIpcStateAndMessage_passiveServerIdleFrameOnCore st1 st2 sender (.blockedOnSend endpointId) (some msg)
              (Or.inr (fun tcb hTcb => ?_)) hObjInv1 hMsg)).trans
              (removeRunnable_passiveServerIdleFrameOnCore st2 sender (fun tcb hTcb => Or.inl ?_))
            · obtain ⟨tcb0, hTcb0, hBindEq⟩ := endpointQueueEnqueue_sameSchedContextBindings endpointId false sender st st1 hObjInv hEnq sender tcb
                ((getTcb?_eq_some_iff st1 sender tcb).mp hTcb)
              exact hBindEq ▸ hSenderNotUnbound tcb0 ((getTcb?_eq_some_iff st sender tcb0).mpr hTcb0)
            · obtain ⟨tcb1, hTcb1, hBindEq1⟩ := storeTcbIpcStateAndMessage_sameSchedContextBindings st1 st2 sender (.blockedOnSend endpointId) (some msg) hObjInv1 hMsg sender tcb
                ((getTcb?_eq_some_iff st2 sender tcb).mp hTcb)
              obtain ⟨tcb0, hTcb0, hBindEq0⟩ := endpointQueueEnqueue_sameSchedContextBindings endpointId false sender st st1 hObjInv hEnq sender tcb1 hTcb1
              exact hBindEq1 ▸ hBindEq0 ▸ hSenderNotUnbound tcb0 ((getTcb?_eq_some_iff st sender tcb0).mpr hTcb0)

open SeLe4n.Model.SystemState in
/-- SM6.D.2: `endpointReceiveDual` frames every core's slice.  Rendezvous:
pop the sender + set it `.blockedOnReply` (Call) or `.ready` (Send) +
complete the receiver `.ready`.  Blocking: return the receiver's own
donation (needs the running receiver `.ready` via `hReceiverReady`) +
enqueue + block `.blockedOnReceive` (allowed) + optional stash +
deschedule. -/
theorem endpointReceiveDual_passiveServerIdleFrameOnCore
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (senderId : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (c : CoreId)
    (hReceiverReady : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        tcb.ipcState = .ready)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReceiveDual endpointId receiver replyId st = .ok (senderId, st')) :
    passiveServerIdleFrameOnCore st st' c := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInvPop : pair.2.2.objects.invExt :=
            endpointQueuePopHead_preserves_objects_invExt endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hF1 := endpointQueuePopHead_passiveServerIdleFrameOnCore (c := c) endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          cases hSenderIpc : pair.2.1.ipcState with
          | blockedOnCall _ =>
            simp only [hSenderIpc, ite_true] at hStep
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInvMsg : st2.objects.invExt :=
                storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInvPop hMsg
              have hF2 := hF1.trans (storeTcbIpcStateAndMessage_passiveServerIdleFrameOnCore pair.2.2 st2 pair.1
                (.blockedOnReply endpointId (some receiver)) none
                (Or.inl (Or.inr (Or.inr ⟨endpointId, some receiver, rfl⟩))) hObjInvPop hMsg)
              cases hReplyId : replyId with
              | none => simp [hReplyId] at hStep
              | some rid =>
                simp only [hReplyId] at hStep
                cases hLink : SystemState.linkCallerReply pair.1 rid st2 with
                | error e => simp [hLink] at hStep
                | ok pLink =>
                  obtain ⟨_, stLinked⟩ := pLink
                  simp only [hLink] at hStep
                  have hObjInvLink : stLinked.objects.invExt :=
                    linkCallerReply_preserves_objects_invExt st2 stLinked pair.1 rid hObjInvMsg hLink
                  have hF3 := hF2.trans (linkCallerReply_passiveServerIdleFrameOnCore st2 stLinked pair.1 rid hObjInvMsg hLink)
                  revert hStep
                  cases hPend : storeTcbIpcStateAndMessage stLinked receiver .ready _ with
                  | ok st4 =>
                    intro h
                    obtain ⟨_, hEq⟩ := Prod.mk.inj (Except.ok.inj h); subst hEq
                    exact hF3.trans (storeTcbIpcStateAndMessage_passiveServerIdleFrameOnCore stLinked st4 receiver
                      .ready _ (Or.inl (Or.inl rfl)) hObjInvLink hPend)
                  | error _ => simp
          | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnReply _ _ =>
            simp only [hSenderIpc] at hStep
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInvMsg : st2.objects.invExt :=
                storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInvPop hMsg
              have hF2 := hF1.trans (storeTcbIpcStateAndMessage_passiveServerIdleFrameOnCore pair.2.2 st2 pair.1
                .ready none (Or.inl (Or.inl rfl)) hObjInvPop hMsg)
              have hObjInvEns : (ensureRunnable st2 pair.1).objects.invExt := by rwa [ensureRunnable_preserves_objects]
              have hF3 := hF2.trans (ensureRunnable_passiveServerIdleFrameOnCore st2 pair.1)
              revert hStep
              cases hPend : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) receiver .ready _ with
              | ok st4 =>
                intro h
                obtain ⟨_, hEq⟩ := Prod.mk.inj (Except.ok.inj h); subst hEq
                exact hF3.trans (storeTcbIpcStateAndMessage_passiveServerIdleFrameOnCore (ensureRunnable st2 pair.1) st4
                  receiver .ready _ (Or.inl (Or.inl rfl)) hObjInvEns hPend)
              | error _ => simp
      | none =>
        cases hChecked : cleanupPreReceiveDonationChecked st receiver with
        | error _ => simp [hHead, hChecked] at hStep
        | ok stClean =>
          have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
            (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked).symm
          simp only [hHead, hChecked] at hStep
          rw [hBridge] at hStep
          have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
          have hFClean := cleanupPreReceiveDonation_passiveServerIdleFrameOnCore (c := c) st receiver hObjInv
            (fun tcb h => Or.inl (hReceiverReady tcb h))
          cases hEnq : endpointQueueEnqueue endpointId true receiver (cleanupPreReceiveDonation st receiver) with
          | error e => simp [hEnq] at hStep
          | ok st1 =>
            simp only [hEnq] at hStep
            have hObjInvEnq : st1.objects.invExt :=
              endpointQueueEnqueue_preserves_objects_invExt endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
            have hF1 := hFClean.trans (endpointQueueEnqueue_passiveServerIdleFrameOnCore endpointId true receiver
              (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq)
            cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
            | error e => simp [hIpc] at hStep
            | ok st2 =>
              simp only [hIpc] at hStep
              have hObjInv2 : st2.objects.invExt :=
                storeTcbIpcState_preserves_objects_invExt st1 st2 receiver _ hObjInvEnq hIpc
              have hF2 := hF1.trans (storeTcbIpcState_passiveServerIdleFrameOnCore st1 st2 receiver
                (.blockedOnReceive endpointId) (Or.inl (Or.inr (Or.inl ⟨endpointId, Or.inl rfl⟩))) hObjInvEnq hIpc)
              cases hGetR : st2.getTcb? receiver with
              | none =>
                simp only [hGetR, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact hF2.trans (removeRunnable_passiveServerIdleFrameOnCore st2 receiver (fun tcb hTcb => Or.inr (by
                  rw [storeTcbIpcState_ipcState_eq st1 st2 receiver _ hObjInvEnq hIpc tcb
                    ((getTcb?_eq_some_iff st2 receiver tcb).mp hTcb)]
                  exact Or.inr (Or.inl ⟨endpointId, Or.inl rfl⟩))))
              | some rTcb =>
                simp only [hGetR] at hStep
                have hValid : st.replyStashValid replyId = true := by
                  cases hb : st.replyStashValid replyId with
                  | false => simp [hb] at hStep
                  | true => rfl
                rw [if_pos hValid] at hStep
                cases hStash : storeObject receiver.toObjId (.tcb { rTcb with pendingReceiveReply := replyId }) st2 with
                | error e => simp [hStash] at hStep
                | ok pStash =>
                  obtain ⟨_, stStashed⟩ := pStash
                  simp only [hStash, Except.ok.injEq, Prod.mk.injEq] at hStep
                  obtain ⟨_, hEq⟩ := hStep; subst hEq
                  have hRecvObj := (getTcb?_eq_some_iff st2 receiver rTcb).mp hGetR
                  have hRTcbIpc : rTcb.ipcState = .blockedOnReceive endpointId :=
                    storeTcbIpcState_ipcState_eq st1 st2 receiver _ hObjInvEnq hIpc rTcb hRecvObj
                  have hF3 := hF2.trans (storeObject_modifiedTcb_passiveServerIdleFrameOnCore st2 stStashed receiver.toObjId rTcb
                    { rTcb with pendingReceiveReply := replyId } hRecvObj rfl
                    (Or.inl (by rw [show ({ rTcb with pendingReceiveReply := replyId } : TCB).ipcState
                      = .blockedOnReceive endpointId from hRTcbIpc]; exact Or.inr (Or.inl ⟨endpointId, Or.inl rfl⟩)))
                    hObjInv2 hStash)
                  have hStashObj := storeObject_objects_eq st2 stStashed receiver.toObjId
                    (.tcb { rTcb with pendingReceiveReply := replyId }) hObjInv2 hStash
                  exact hF3.trans (removeRunnable_passiveServerIdleFrameOnCore stStashed receiver (fun tcb hTcb => Or.inr (by
                    have hTcbRaw := (getTcb?_eq_some_iff stStashed receiver tcb).mp hTcb
                    rw [hStashObj] at hTcbRaw; obtain rfl := KernelObject.tcb.inj (Option.some.inj hTcbRaw)
                    rw [show ({ rTcb with pendingReceiveReply := replyId } : TCB).ipcState
                      = .blockedOnReceive endpointId from hRTcbIpc]
                    exact Or.inr (Or.inl ⟨endpointId, Or.inl rfl⟩))))

open SeLe4n.Model.SystemState in
/-- SM6.D.2: `endpointCall` frames every core's slice.  Rendezvous: pop +
complete the receiver `.ready` + reschedule + set the caller
`.blockedOnReply` (allowed) + stash the reply + deschedule the caller.
Block: enqueue the caller + set it `.blockedOnCall` (non-allowed, so the
caller must hold a SchedContext — `hCallerNotUnbound`) + deschedule. -/
theorem endpointCall_passiveServerIdleFrameOnCore
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hCallerNotUnbound : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        tcb.schedContextBinding ≠ .unbound)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    passiveServerIdleFrameOnCore st st' c := by
  unfold endpointCall at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
          have hF1 := endpointQueuePopHead_passiveServerIdleFrameOnCore (c := c) endpointId true st pair.2.2 pair.1 _ hObjInv hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ _ hObjInv1 hMsg
            have hF2 := storeTcbIpcStateAndMessage_passiveServerIdleFrameOnCore (c := c) pair.2.2 st2 pair.1 .ready (some msg)
              (Or.inl (Or.inl rfl)) hObjInv1 hMsg
            have hObjInvEns : (ensureRunnable st2 pair.1).objects.invExt := by rwa [ensureRunnable_preserves_objects]
            have hF3 := ensureRunnable_passiveServerIdleFrameOnCore (c := c) st2 pair.1
            cases hIpc : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId (some pair.1)) none with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc] at hStep
              have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt (ensureRunnable st2 pair.1) st4 caller _ _ hObjInvEns hIpc
              have hF4 := storeTcbIpcStateAndMessage_passiveServerIdleFrameOnCore (c := c) (ensureRunnable st2 pair.1) st4 caller
                (.blockedOnReply endpointId (some pair.1)) none
                (Or.inl (Or.inr (Or.inr ⟨endpointId, some pair.1, rfl⟩))) hObjInvEns hIpc
              cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
              | error e => simp [hLink] at hStep
              | ok pL =>
                obtain ⟨_, st5⟩ := pL
                simp only [hLink, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                have hF5 := linkServerStashedReply_passiveServerIdleFrameOnCore (c := c) st4 st5 caller pair.1 hObjInv4 hLink
                refine ((((hF1.trans hF2).trans hF3).trans hF4).trans hF5).trans
                  (removeRunnable_passiveServerIdleFrameOnCore st5 caller (fun tcb hTcb => Or.inr ?_))
                obtain ⟨tcb4, hTcb4, hIpc4⟩ := linkServerStashedReply_tcb_ipcState_backward st4 st5 caller pair.1 caller tcb hObjInv4 hLink
                  ((getTcb?_eq_some_iff st5 caller tcb).mp hTcb)
                have hRep := storeTcbIpcStateAndMessage_ipcState_eq (ensureRunnable st2 pair.1) st4 caller _ none hObjInvEns hIpc tcb4 hTcb4
                rw [← hIpc4, hRep]; exact Or.inr (Or.inr ⟨endpointId, some pair.1, rfl⟩)
      | none =>
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st1 hObjInv hEnq
          have hF1 := endpointQueueEnqueue_passiveServerIdleFrameOnCore (c := c) endpointId false caller st st1 hObjInv hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            refine (hF1.trans (storeTcbIpcStateAndMessage_passiveServerIdleFrameOnCore st1 st2 caller (.blockedOnCall endpointId) (some msg)
              (Or.inr (fun tcb hTcb => ?_)) hObjInv1 hMsg)).trans
              (removeRunnable_passiveServerIdleFrameOnCore st2 caller (fun tcb hTcb => Or.inl ?_))
            · obtain ⟨tcb0, hTcb0, hBindEq⟩ := endpointQueueEnqueue_sameSchedContextBindings endpointId false caller st st1 hObjInv hEnq caller tcb
                ((getTcb?_eq_some_iff st1 caller tcb).mp hTcb)
              exact hBindEq ▸ hCallerNotUnbound tcb0 ((getTcb?_eq_some_iff st caller tcb0).mpr hTcb0)
            · obtain ⟨tcb1, hTcb1, hBindEq1⟩ := storeTcbIpcStateAndMessage_sameSchedContextBindings st1 st2 caller (.blockedOnCall endpointId) (some msg) hObjInv1 hMsg caller tcb
                ((getTcb?_eq_some_iff st2 caller tcb).mp hTcb)
              obtain ⟨tcb0, hTcb0, hBindEq0⟩ := endpointQueueEnqueue_sameSchedContextBindings endpointId false caller st st1 hObjInv hEnq caller tcb1 hTcb1
              exact hBindEq1 ▸ hBindEq0 ▸ hCallerNotUnbound tcb0 ((getTcb?_eq_some_iff st caller tcb0).mpr hTcb0)

open SeLe4n.Model.SystemState in
/-- SM6.D.2: `endpointReplyRecv` frames every core's slice.  The reply leg
unblocks the reply target `.ready` + reschedules it (allowed); the
receive leg is `endpointReceiveDual`. -/
theorem endpointReplyRecv_passiveServerIdleFrameOnCore
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (replyId : Option SeLe4n.ReplyId) (c : CoreId)
    (hReceiverReady : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        tcb.ipcState = .ready)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg replyId st = .ok ((), st')) :
    passiveServerIdleFrameOnCore st st' c := by
  unfold endpointReplyRecv at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready => simp [hIpc] at hStep
    | blockedOnSend _ => simp [hIpc] at hStep
    | blockedOnReceive _ => simp [hIpc] at hStep
    | blockedOnNotification _ => simp [hIpc] at hStep
    | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply epId expectedReplier =>
      simp only [hIpc] at hStep
      cases expectedReplier with
      | none => simp at hStep
      | some expected =>
        simp only at hStep
        split at hStep
        · revert hStep
          cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
          | error e => simp
          | ok stReplied =>
            simp only []
            have hObjInvR := storeTcbIpcStateAndMessage_preserves_objects_invExt st stReplied replyTarget _ _ hObjInv hMsg
            have hF1 := (storeTcbIpcStateAndMessage_passiveServerIdleFrameOnCore (c := c) st stReplied replyTarget .ready (some msg)
              (Or.inl (Or.inl rfl)) hObjInv hMsg).trans (ensureRunnable_passiveServerIdleFrameOnCore stReplied replyTarget)
            have hObjInvE : (ensureRunnable stReplied replyTarget).objects.invExt := by rwa [ensureRunnable_preserves_objects]
            have hReceiverReadyE : ∀ (t : TCB),
                (ensureRunnable stReplied replyTarget).getTcb? receiver = some t →
                t.ipcState = .ready := by
              intro t hT
              have hTRaw := (getTcb?_eq_some_iff _ receiver t).mp hT
              rw [ensureRunnable_preserves_objects] at hTRaw
              by_cases hRT : receiver = replyTarget
              · exact storeTcbIpcStateAndMessage_ipcState_eq st stReplied replyTarget .ready (some msg)
                  hObjInv hMsg t (hRT ▸ hTRaw)
              · have hNe : receiver.toObjId ≠ replyTarget.toObjId :=
                  fun h => hRT (ThreadId.toObjId_injective receiver replyTarget h)
                rw [storeTcbIpcStateAndMessage_preserves_objects_ne st stReplied replyTarget _ (some msg)
                  receiver.toObjId hNe hObjInv hMsg] at hTRaw
                exact hReceiverReady t ((getTcb?_eq_some_iff st receiver t).mpr hTRaw)
            cases hRO : tcb.replyObject with
            | none =>
              simp only []
              cases hRecv : endpointReceiveDual endpointId receiver replyId (ensureRunnable stReplied replyTarget) with
              | error e => simp
              | ok pair =>
                intro hStep
                simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, rfl⟩ := hStep
                exact hF1.trans (endpointReceiveDual_passiveServerIdleFrameOnCore
                  (ensureRunnable stReplied replyTarget) pair.2 endpointId receiver pair.1 replyId c
                  hReceiverReadyE hObjInvE hRecv)
            | some rid =>
              cases hCons : SystemState.consumeCallerReply replyTarget rid (ensureRunnable stReplied replyTarget) with
              | error e => simp [hCons]
              | ok p3 =>
                obtain ⟨⟨⟩, st3⟩ := p3
                simp only [hCons]
                have hObjInv3 := SystemState.consumeCallerReply_preserves_objects_invExt _ _ replyTarget rid hObjInvE hCons
                have hF13 := hF1.trans (consumeCallerReply_passiveServerIdleFrameOnCore _ _ replyTarget rid hObjInvE hCons)
                have hReceiverReady3 : ∀ (t : TCB),
                    st3.getTcb? receiver = some t →
                    t.ipcState = .ready := by
                  intro t hT
                  obtain ⟨ty, hSt, hIS, _⟩ :=
                    SystemState.consumeCallerReply_tcb_forward _ _ replyTarget rid hObjInvE hCons receiver.toObjId t
                      ((getTcb?_eq_some_iff st3 receiver t).mp hT)
                  rw [hIS]
                  exact hReceiverReadyE ty ((getTcb?_eq_some_iff _ receiver ty).mpr hSt)
                cases hRecv : endpointReceiveDual endpointId receiver replyId st3 with
                | error e => simp
                | ok pair =>
                  intro hStep
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                  obtain ⟨_, rfl⟩ := hStep
                  exact hF13.trans (endpointReceiveDual_passiveServerIdleFrameOnCore
                    st3 pair.2 endpointId receiver pair.1 replyId c
                    hReceiverReady3 hObjInv3 hRecv)
        · simp at hStep

open SeLe4n.Model.SystemState in
/-- SM6.D.2: `endpointReply` frames every core's slice — it unblocks the
target `.ready` (allowed) and reschedules it; no thread is descheduled
into a non-allowed state. -/
theorem endpointReply_passiveServerIdleFrameOnCore
    (st st' : SystemState) (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    passiveServerIdleFrameOnCore st st' c := by
  unfold endpointReply at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready => simp [hIpc] at hStep
    | blockedOnSend _ => simp [hIpc] at hStep
    | blockedOnReceive _ => simp [hIpc] at hStep
    | blockedOnNotification _ => simp [hIpc] at hStep
    | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply epId replyTarget =>
      simp only [hIpc] at hStep
      cases replyTarget with
      | none => simp at hStep
      | some expected =>
        simp only at hStep
        split at hStep
        · cases hMsg : storeTcbIpcStateAndMessage st target .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st'' =>
            simp only [hMsg] at hStep
            have hMid : passiveServerIdleFrameOnCore st (ensureRunnable st'' target) c :=
              (storeTcbIpcStateAndMessage_passiveServerIdleFrameOnCore st st'' target .ready (some msg)
                (Or.inl (Or.inl rfl)) hObjInv hMsg).trans
                (ensureRunnable_passiveServerIdleFrameOnCore st'' target)
            have hObjInvMid : (ensureRunnable st'' target).objects.invExt := by
              rw [ensureRunnable_preserves_objects]
              exact storeTcbIpcStateAndMessage_preserves_objects_invExt st st'' target .ready (some msg) hObjInv hMsg
            cases hRO : tcb.replyObject with
            | none =>
              simp only [hRO, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
              rw [← hStep]; exact hMid
            | some rid =>
              simp only [hRO] at hStep
              exact hMid.trans (consumeCallerReply_passiveServerIdleFrameOnCore _ _ target rid hObjInvMid hStep)
        · simp at hStep

-- ============================================================================
-- §4  SM6.D.2: per-operation preservation of the per-core IPC bundle
-- ============================================================================
--
-- Theorem 3.3.1 of the plan, one theorem per IPC operation: from the
-- ∀-core pre-state bundle (`ipcInvariantFull_smp`), the operation's
-- post-state satisfies EVERY core's bundle view.  Nineteen conjuncts ride
-- the existing single-core whole-bundle theorem through the SM6.D.1
-- exact-decomposition bridges; the per-core `passiveServerIdle` slice
-- rides the §3 per-core frame.  Hypotheses mirror the single-core
-- theorems' (freshness, readiness, binding side conditions, and the
-- threaded post-state facts `hWtpmn'`/`hRCLRecip'`/`hDOV'`), with TCB
-- lookups routed through the typed `getTcb?`.

open SeLe4n.Model.SystemState in
/-- SM6.D.2 (signal): `notificationSignal` preserves every core's view of
the IPC invariant bundle. -/
theorem notificationSignal_preserves_ipcInvariantFull_perCore
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hNWC : notificationWaiterConsistent st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hStep : notificationSignal notificationId badge st = .ok ((), st'))
    (c : CoreId) :
    ipcInvariantFull_perCore st' c :=
  ipcInvariantFull_perCore_of_full
    (notificationSignal_preserves_ipcInvariantFull st st' notificationId badge
      (ipcInvariantFull_of_smp hInv) hObjInv hWtpmn' hRCLRecip' hNWC hAllBudgetsNone hStep)
    (passiveServerIdle_perCore_of_frameOnCore
      (notificationSignal_passiveServerIdleFrameOnCore st st' notificationId badge c hObjInv hStep)
      (hInv c).passiveServerIdle)

open SeLe4n.Model.SystemState in
/-- SM6.D.2 (wait): `notificationWait` preserves every core's view of the
IPC invariant bundle. -/
theorem notificationWait_preserves_ipcInvariantFull_perCore
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hWaiterNotRecv : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hWaiterNotReply : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hWaiterReady : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        tcb.ipcState = .ready)
    (hStep : notificationWait notificationId waiter st = .ok (result, st'))
    (c : CoreId) :
    ipcInvariantFull_perCore st' c :=
  ipcInvariantFull_perCore_of_full
    (notificationWait_preserves_ipcInvariantFull st st' notificationId waiter result
      (ipcInvariantFull_of_smp hInv) hObjInv hWtpmn' hRCLRecip' hWaiterNotRecv
      (fun tcb hRaw => hWaiterNotReply tcb ((getTcb?_eq_some_iff st waiter tcb).mpr hRaw))
      hAllBudgetsNone
      (fun tcb hRaw => hWaiterReady tcb ((getTcb?_eq_some_iff st waiter tcb).mpr hRaw))
      hStep)
    (passiveServerIdle_perCore_of_frameOnCore
      (notificationWait_passiveServerIdleFrameOnCore st st' notificationId waiter result c hObjInv hStep)
      (hInv c).passiveServerIdle)

open SeLe4n.Model.SystemState in
/-- SM6.D.2 (send): `endpointSendDual` preserves every core's view of the
IPC invariant bundle. -/
theorem endpointSendDual_preserves_ipcInvariantFull_perCore
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hFreshSender : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some sender ∧ ep.sendQ.tail ≠ some sender ∧
      ep.receiveQ.head ≠ some sender ∧ ep.receiveQ.tail ≠ some sender)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hSenderNotRecv : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hSenderNotReply : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hSenderNotUnbound : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        tcb.schedContextBinding ≠ .unbound)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st'))
    (c : CoreId) :
    ipcInvariantFull_perCore st' c :=
  ipcInvariantFull_perCore_of_full
    (endpointSendDual_preserves_ipcInvariantFull st st' endpointId sender msg
      (ipcInvariantFull_of_smp hInv) hObjInv hWtpmn' hAllBudgetsNone hRCLRecip'
      hFreshSender hSendTailFresh hSenderNotRecv
      (fun tcb hRaw => hSenderNotReply tcb ((getTcb?_eq_some_iff st sender tcb).mpr hRaw))
      (fun tcb hRaw => hSenderNotUnbound tcb ((getTcb?_eq_some_iff st sender tcb).mpr hRaw))
      hStep)
    (passiveServerIdle_perCore_of_frameOnCore
      (endpointSendDual_passiveServerIdleFrameOnCore st st' endpointId sender msg c hObjInv
        hSenderNotUnbound hStep)
      (hInv c).passiveServerIdle)

open SeLe4n.Model.SystemState in
/-- SM6.D.2 (receive): `endpointReceiveDual` preserves every core's view
of the IPC invariant bundle. -/
theorem endpointReceiveDual_preserves_ipcInvariantFull_perCore
    (endpointId : SeLe4n.ObjId) (receiver senderId : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (st st' : SystemState)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid))
    (hReplyIdValid : ∀ rid, replyId = some rid → replyIdEstablishFresh st rid)
    (hReceiverNotRecv : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hReceiverReady : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        tcb.ipcState = .ready)
    (hStep : endpointReceiveDual endpointId receiver replyId st = .ok (senderId, st'))
    (c : CoreId) :
    ipcInvariantFull_perCore st' c :=
  ipcInvariantFull_perCore_of_full
    (endpointReceiveDual_preserves_ipcInvariantFull endpointId receiver senderId replyId st st'
      (ipcInvariantFull_of_smp hInv) hObjInv hWtpmn' hAllBudgetsNone hRCLRecip'
      hFreshReceiver hRecvTailFresh hReplyIdValid hReceiverNotRecv
      (fun tcb hRaw => hReceiverReady tcb ((getTcb?_eq_some_iff st receiver tcb).mpr hRaw))
      hStep)
    (passiveServerIdle_perCore_of_frameOnCore
      (endpointReceiveDual_passiveServerIdleFrameOnCore st st' endpointId receiver senderId replyId c
        hReceiverReady hObjInv hStep)
      (hInv c).passiveServerIdle)

open SeLe4n.Model.SystemState in
/-- SM6.D.2 (call): `endpointCall` preserves every core's view of the IPC
invariant bundle. -/
theorem endpointCall_preserves_ipcInvariantFull_perCore
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hFreshCaller : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some caller ∧ ep.sendQ.tail ≠ some caller ∧
      ep.receiveQ.head ≠ some caller ∧ ep.receiveQ.tail ≠ some caller)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hCallerNotRecv : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hCallerNotReply : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hCallerNotUnbound : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        tcb.schedContextBinding ≠ .unbound)
    (hCallerReady : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        tcb.ipcState = .ready)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st'))
    (c : CoreId) :
    ipcInvariantFull_perCore st' c :=
  ipcInvariantFull_perCore_of_full
    (endpointCall_preserves_ipcInvariantFull st st' endpointId caller msg
      (ipcInvariantFull_of_smp hInv) hObjInv hWtpmn' hAllBudgetsNone hRCLRecip'
      hFreshCaller hSendTailFresh hCallerNotRecv
      (fun tcb hRaw => hCallerNotReply tcb ((getTcb?_eq_some_iff st caller tcb).mpr hRaw))
      (fun tcb hRaw => hCallerNotUnbound tcb ((getTcb?_eq_some_iff st caller tcb).mpr hRaw))
      (fun tcb hRaw => hCallerReady tcb ((getTcb?_eq_some_iff st caller tcb).mpr hRaw))
      hStep)
    (passiveServerIdle_perCore_of_frameOnCore
      (endpointCall_passiveServerIdleFrameOnCore st st' endpointId caller msg c hObjInv
        hCallerNotUnbound hStep)
      (hInv c).passiveServerIdle)

open SeLe4n.Model.SystemState in
/-- SM6.D.2 (reply): `endpointReply` preserves every core's view of the
IPC invariant bundle. -/
theorem endpointReply_preserves_ipcInvariantFull_perCore
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hDOV' : donationOwnerValid st')
    (hStep : endpointReply replier target msg st = .ok ((), st'))
    (c : CoreId) :
    ipcInvariantFull_perCore st' c :=
  ipcInvariantFull_perCore_of_full
    (endpointReply_preserves_ipcInvariantFull st st' replier target msg
      (ipcInvariantFull_of_smp hInv) hObjInv hWtpmn' hAllBudgetsNone hDOV' hStep)
    (passiveServerIdle_perCore_of_frameOnCore
      (endpointReply_passiveServerIdleFrameOnCore st st' replier target msg c hObjInv hStep)
      (hInv c).passiveServerIdle)

open SeLe4n.Model.SystemState in
/-- SM6.D.2 (reply-receive): `endpointReplyRecv` preserves every core's
view of the IPC invariant bundle. -/
theorem endpointReplyRecv_preserves_ipcInvariantFull_perCore
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (replyId : Option SeLe4n.ReplyId)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hDOV' : donationOwnerValid st')
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid))
    (hReplyIdValid : ∀ rid, replyId = some rid → replyIdEstablishFresh st rid)
    (hReceiverNotRecv : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hReceiverReady : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        tcb.ipcState = .ready)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg replyId st = .ok ((), st'))
    (c : CoreId) :
    ipcInvariantFull_perCore st' c :=
  ipcInvariantFull_perCore_of_full
    (endpointReplyRecv_preserves_ipcInvariantFull st st' endpointId receiver replyTarget msg replyId
      (ipcInvariantFull_of_smp hInv) hObjInv hWtpmn' hAllBudgetsNone hDOV' hRCLRecip'
      hFreshReceiver hRecvTailFresh hReplyIdValid hReceiverNotRecv
      (fun tcb hRaw => hReceiverReady tcb ((getTcb?_eq_some_iff st receiver tcb).mpr hRaw))
      hStep)
    (passiveServerIdle_perCore_of_frameOnCore
      (endpointReplyRecv_passiveServerIdleFrameOnCore st st' endpointId receiver replyTarget msg replyId c
        hReceiverReady hObjInv hStep)
      (hInv c).passiveServerIdle)

end SeLe4n.Kernel
