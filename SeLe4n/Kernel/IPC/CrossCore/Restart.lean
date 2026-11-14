/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.Cancellation
import SeLe4n.Kernel.IPC.Operations.Fault

/-!
# The restart of a thread (`.tcbResume`)

WS-SX SX4: seL4's `restart` (`thread.c`), which `seL4_TCB_Resume` runs, acts on
a **stopped** thread only (`isStopped`, `include/kernel/thread.h`): one that is
`Inactive`, or blocked in an IPC — on a send, a receive, a notification or a
reply.  It cancels the thread's IPC (`cancelIPC`), sets it `Restart`, resumes
its scheduling context and makes it runnable.  A thread that is not stopped —
running, or already set to restart — is left as it is, and the call succeeds.

`restartThreadOnCore` is that, over the model's two existing transitions:

* **`Inactive`** — the resume (`resumeThreadOnCore`), after the fault retire the
  resume of a fault-suspended thread runs (`retirePendingFaultForResume`).
* **Blocked in an IPC** — the IPC cancelled as the suspend cancels it
  (`suspendThreadOnCore`: seL4-MCS's `cancelIPC`, which leaves the thread
  `Inactive` with its saved program counter at its restart PC), then the resume.
  seL4's `suspend` is `cancelIPC`, the `Inactive` write, `tcbSchedDequeue` and
  `tcbReleaseRemove`, and a thread blocked in an IPC is queued on no core and
  its context is on no release queue, so on it the two agree.
* **Otherwise** — no write and no error.
-/

namespace SeLe4n.Kernel.Lifecycle.Suspend

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

/-- seL4's `isStopped`: the thread is `Inactive`, or blocked in an IPC. -/
@[inline] def threadStopped (tcb : TCB) : Bool :=
  tcb.threadState == .Inactive || tcb.ipcState != .ready

/-- **seL4's `restart`** — the `.tcbResume` transition.  See the module
docstring for its three arms. -/
def restartThreadOnCore (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) :
    Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  match st.getTcb? vtid.val with
  | none => .error (.invalidArgument 0)
  | some tcb =>
    if tcb.threadState == .Inactive then
      resumeThreadOnCore (retirePendingFaultForResume st vtid.val) vtid executingCore
    else if tcb.ipcState != .ready then
      match suspendThreadOnCore st vtid executingCore with
      | .error e => .error e
      | .ok (st1, _) =>
        resumeThreadOnCore (retirePendingFaultForResume st1 vtid.val) vtid executingCore
    else .ok (st, none)

/-- The three arms of the restart, as one disjunction a proof cases on. -/
theorem restartThreadOnCore_cases {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {executingCore : CoreId} {sgi : Option (CoreId × SgiKind)}
    (h : restartThreadOnCore st vtid executingCore = .ok (st', sgi)) :
    resumeThreadOnCore (retirePendingFaultForResume st vtid.val) vtid executingCore
        = .ok (st', sgi) ∨
    (∃ st1 sgi1, suspendThreadOnCore st vtid executingCore = .ok (st1, sgi1) ∧
      resumeThreadOnCore (retirePendingFaultForResume st1 vtid.val) vtid executingCore
        = .ok (st', sgi)) ∨
    (st' = st ∧ sgi = none) := by
  unfold restartThreadOnCore at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact Or.inl h
    · split at h
      · split at h
        · exact absurd h (by simp)
        · rename_i st1 sgi1 hS
          exact Or.inr (Or.inl ⟨st1, sgi1, hS, h⟩)
      · rw [Except.ok.injEq, Prod.mk.injEq] at h
        exact Or.inr (Or.inr ⟨h.1.symm, h.2.symm⟩)

/-- A predicate the suspend and the retire-then-resume both carry is carried by
the restart. -/
theorem restartThreadOnCore_preserves {P : SystemState → Prop}
    {st st' : SystemState} {vtid : SeLe4n.ValidThreadId} {executingCore : CoreId}
    {sgi : Option (CoreId × SgiKind)}
    (hSus : ∀ s s' g, P s → suspendThreadOnCore s vtid executingCore = .ok (s', g) → P s')
    (hRes : ∀ s s' g, P s →
      resumeThreadOnCore (retirePendingFaultForResume s vtid.val) vtid executingCore
        = .ok (s', g) → P s')
    (hP : P st) (h : restartThreadOnCore st vtid executingCore = .ok (st', sgi)) : P st' := by
  rcases restartThreadOnCore_cases h with h | ⟨st1, sgi1, h1, h2⟩ | ⟨rfl, _⟩
  · exact hRes _ _ _ hP h
  · exact hRes _ _ _ (hSus _ _ _ hP h1) h2
  · exact hP

/-- On an `Inactive` thread the restart is the resume of the retired state. -/
theorem restartThreadOnCore_of_inactive {st : SystemState} {vtid : SeLe4n.ValidThreadId}
    {executingCore : CoreId} {tcb : TCB} (hT : st.getTcb? vtid.val = some tcb)
    (hI : tcb.threadState = .Inactive) :
    restartThreadOnCore st vtid executingCore =
      resumeThreadOnCore (retirePendingFaultForResume st vtid.val) vtid executingCore := by
  unfold restartThreadOnCore
  simp [hT, hI]

/-- A thread that is not stopped is left as it is. -/
theorem restartThreadOnCore_of_not_stopped {st : SystemState} {vtid : SeLe4n.ValidThreadId}
    {executingCore : CoreId} {tcb : TCB} (hT : st.getTcb? vtid.val = some tcb)
    (hS : threadStopped tcb = false) :
    restartThreadOnCore st vtid executingCore = .ok (st, none) := by
  unfold threadStopped at hS
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, bne_eq_false_iff_eq] at hS
  unfold restartThreadOnCore
  simp [hT, hS.1, hS.2]

/-- A target that is not a TCB is refused, as seL4's decode refuses a capability
that names no thread. -/
theorem restartThreadOnCore_of_getTcb?_none {st : SystemState}
    {vtid : SeLe4n.ValidThreadId} {executingCore : CoreId}
    (hT : st.getTcb? vtid.val = none) :
    restartThreadOnCore st vtid executingCore = .error (.invalidArgument 0) := by
  unfold restartThreadOnCore
  simp [hT]

/-- On a target that is ready in IPC (the dispatch premises' quiescent shape),
the restart is the resume of an `Inactive` thread or nothing at all: the
cancelling arm needs a blocked thread. -/
theorem restartThreadOnCore_cases_of_ready {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {executingCore : CoreId} {sgi : Option (CoreId × SgiKind)}
    (hReady : ∀ tcb : TCB, st.getTcb? vtid.val = some tcb → tcb.ipcState = .ready)
    (h : restartThreadOnCore st vtid executingCore = .ok (st', sgi)) :
    resumeThreadOnCore (retirePendingFaultForResume st vtid.val) vtid executingCore
        = .ok (st', sgi) ∨
    (st' = st ∧ sgi = none) := by
  unfold restartThreadOnCore at h
  split at h
  · exact absurd h (by simp)
  · rename_i tcb hT
    split at h
    · exact Or.inl h
    · split at h
      · rename_i hB
        exact absurd (hReady tcb hT) (by simpa using hB)
      · rw [Except.ok.injEq, Prod.mk.injEq] at h
        exact Or.inr ⟨h.1.symm, h.2.symm⟩

/-- An admitted resume (`resumeAdmitted`: an `Inactive` thread) is the restart's
`Inactive` arm. -/
theorem restartThreadOnCore_of_resumeAdmitted {st : SystemState}
    {vtid : SeLe4n.ValidThreadId} {executingCore : CoreId}
    (h : resumeAdmitted st vtid.val = true) :
    restartThreadOnCore st vtid executingCore =
      resumeThreadOnCore (retirePendingFaultForResume st vtid.val) vtid executingCore := by
  unfold resumeAdmitted at h
  cases hT : st.getTcb? vtid.val with
  | none => rw [hT] at h; cases h
  | some tcb =>
    rw [hT] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_eq_false_iff_eq] at h
    exact restartThreadOnCore_of_inactive hT h.1

end SeLe4n.Kernel.Lifecycle.Suspend
