/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.SavedRegisters

/-!
# A thread blocked in IPC is resident on no core

WS-ZA ZA6.16.  A core's resident thread (`MachineState.residentOnCore`) is one
whose live registers a remote deschedule left in that core's bank; the core's
next entry saves them over the thread's saved context.  The IPC writes that
name a blocked thread (a cancellation's restore, a delivery, a reply) are sound
only if that save cannot overwrite them, so a blocked thread must be resident on
no core.  A core records as resident only the thread it resumes at EL0, a ready
current thread, so `SystemState.blockedNotResident` holds whenever residency is
recorded; this file states it, proves it where no core holds a resident (boot,
the default state), carries it across a step that keeps the residency records
and the residents' IPC states, and gives the census's free-ness for a blocked
thread (`offCoreFree_of_blocked`).  ZA6.17 decomposes its preservation across
an entry (`BlockedNotResident.of_entry`); the two halves an entry supplies are
ZA6.18's.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- WS-ZA ZA6.16: **every core's resident thread is ready in IPC**: a thread
blocked in IPC is resident on no core. -/
def _root_.SeLe4n.Model.SystemState.blockedNotResident (st : SystemState) : Prop :=
  ∀ (d : CoreId) (tid : SeLe4n.ThreadId) (t : TCB),
    st.machine.residentOnCore d = some tid → st.getTcb? tid = some t → t.ipcState = .ready

namespace BlockedNotResident

/-- A state no core holds a resident in satisfies it. -/
theorem of_noResidents {st : SystemState} (h : ∀ d, st.machine.residentOnCore d = none) :
    st.blockedNotResident :=
  fun d _ _ hR _ => absurd (hR.symm.trans (h d)) (by simp)

/-- A machine whose residency codes are the default's holds no resident. -/
theorem of_defaultCodes {st : SystemState}
    (h : st.machine.residentCode = (default : SystemState).machine.residentCode) :
    st.blockedNotResident :=
  of_noResidents fun d => by
    simp [MachineState.residentOnCore, h, CurrentNotResidentElsewhere.default_residentCode,
      SeLe4n.PerCoreVector.get_eq_getElem]

/-- **It carries across a step that records no new resident and keeps each
resident's IPC state.** -/
theorem of_frame {X Y : SystemState} (h : X.blockedNotResident)
    (hR : ∀ d tid, Y.machine.residentOnCore d = some tid → X.machine.residentOnCore d = some tid)
    (hT : ∀ tid t', Y.getTcb? tid = some t' → ∃ t, X.getTcb? tid = some t ∧ t.ipcState = t'.ipcState) :
    Y.blockedNotResident := fun d tid t' hY hT' => by
  obtain ⟨t, hX, hS⟩ := hT tid t' hT'
  rw [← hS]; exact h d tid t (hR d tid hY) hX

/-- WS-ZA ZA6.17: **the entry's decomposition.**  After a step on core `e`, the
residents are of two kinds.  A resident of another core was resident there
before (`residentKeptOffCore`, the coverage relation's `residentKept`), so it was
ready if it had a TCB; it stays ready if the step left a ready thread on another
core ready (`hKeep`, the frame that the step blocks no thread another core
holds).  The resident of `e` is the one `e`'s own settle recorded, its current
thread resumed at EL0, which is ready (`hOwn`). -/
theorem of_entry {e : CoreId} {pre post : SystemState} (h : pre.blockedNotResident)
    (hRK : residentKeptOffCore e pre post)
    (hKeep : ∀ d, d ≠ e → ∀ tid t', post.machine.residentOnCore d = some tid →
      post.getTcb? tid = some t' →
      ∃ t, pre.getTcb? tid = some t ∧ (t.ipcState = .ready → t'.ipcState = .ready))
    (hOwn : ∀ tid t', post.machine.residentOnCore e = some tid → post.getTcb? tid = some t' →
      t'.ipcState = .ready) :
    post.blockedNotResident := fun d tid t' hR hT' => by
  by_cases hd : d = e
  · subst hd; exact hOwn tid t' hR hT'
  · obtain ⟨t, hT, hS⟩ := hKeep d hd tid t' hR hT'
    exact hS (h d tid t (hRK d hd tid hR) hT)

end BlockedNotResident

/-- The default state holds no resident. -/
theorem _root_.SeLe4n.Model.SystemState.default_blockedNotResident :
    (default : SystemState).blockedNotResident :=
  BlockedNotResident.of_defaultCodes rfl

/-- **A thread blocked in IPC is held by no core**: it is current nowhere
(`blockedCurrentNowhere`) and resident nowhere (`blockedNotResident`) — the
free-ness the census's writes to a blocked thread need (ZA6.15's cancellation
restore, ZA6.20's deliveries and reply). -/
theorem offCoreFree_of_blocked {e : CoreId} {st : SystemState} {tid : SeLe4n.ThreadId}
    {t : TCB} (hB : blockedCurrentNowhere st) (hN : st.blockedNotResident)
    (hT : st.getTcb? tid = some t) (hS : t.ipcState ≠ .ready) : offCoreFree e st tid :=
  fun d _ => ⟨hB tid t hT hS d, fun h => hS (hN d tid t h hT)⟩

end SeLe4n.Kernel

namespace SeLe4n.Platform.Boot
open SeLe4n.Model
open SeLe4n.Kernel

/-- WS-ZA ZA6.16: **the state the started boot installs holds no blocked
resident** — it holds no resident at all
(`bootFromPlatformCheckedWithIdleThreadsFor_ok_residentCode`). -/
theorem bootFromPlatformCheckedStartedFor_blockedNotResident
    (cores : List SeLe4n.Kernel.Concurrency.CoreId) (config : PlatformConfig)
    (ist : IntermediateState) (h : bootFromPlatformCheckedStartedFor cores config = .ok ist) :
    ist.state.blockedNotResident := by
  obtain ⟨base, started, hBase, hStart, rfl⟩ := bootFromPlatformCheckedStartedFor_ok cores config ist h
  refine BlockedNotResident.of_defaultCodes ?_
  rw [linkBootCapabilities_machine, startInitialThreads_machine _ _ _ hStart]
  exact bootFromPlatformCheckedWithIdleThreadsFor_ok_residentCode cores config base hBase

end SeLe4n.Platform.Boot
