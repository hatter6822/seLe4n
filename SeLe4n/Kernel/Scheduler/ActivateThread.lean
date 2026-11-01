-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.SchedContext.YieldLinkFrame
import SeLe4n.Kernel.SchedContext.YieldLinkInvariant
import SeLe4n.Kernel.Concurrency.Runtime
import SeLe4n.Kernel.SlotConfinement.Predicate
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore

/-! # The current thread's activation at entry exit

WS-ZA ZA6.7.  seL4-MCS completes a pending yield when the yielder next runs:
`activateThread` begins

```c
if (unlikely(NODE_STATE(ksCurThread)->tcbYieldTo)) {
    schedContext_completeYieldTo(NODE_STATE(ksCurThread));
}
```

after the scheduler's choice and before the return to user.  This kernel picks a
core's current thread at many sites and restores it read-only
(`Architecture.restoreTargetOnCore`), so the completion is one write step run at
the tail of every kernel entry, after the residency settle and before the
restore target is read: `activateThreadOnCore`.

* **No link pending**: the step reads core `c`'s current-thread code and that
  thread's yield-to code, and answers the state it was given.
* **A link pending**: `completeYieldTo` (ZA6.6) hands the yielder the consumed
  time of the context it yielded to and clears both ends; the core's register
  bank takes the same two registers (`x1` the message info, `x2` the consumed
  time), because the yielder is the core's current thread and the bank holds its
  live context (`contextMatchesCurrentOnCore`), as `stageCallerReturnFor` writes a
  still-current caller's result into both.

seL4's `setConsumed` writes `ksCurThread`, which at activation is the yielder,
so here the thread the consumed time is for and the thread whose registers are
written are one thread, with no correction needed (ZA6.6's `setConsumed` writes
the yielder by construction).

Until the yieldTo invocation (ZA6.22) sets a link, no thread has one, and the
step is the identity (`activateThreadOnCore_of_unlinked`). -/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **The linked case of the activation**: core `c`'s current thread `tid`,
linked to context `s`, has its yield completed (`completeYieldTo`), and the
core's bank takes the two registers the completion wrote into its saved
context (`RegisterFile.withConsumed`).  A context that does not exist is read
as no consumed time and writes no register, as `setConsumed` writes none for
it.  Out of line, so the entries' common path, which never links, stays the
two reads of `activateThreadOnCoreImpl`. -/
@[noinline] def completeCurrentYield (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (s : SeLe4n.SchedContextId) : SystemState :=
  match st.getSchedContext? s with
  | some sc =>
    let w := sc.consumedReading.toUInt64
    let s1 := completeYieldTo st tid
    { s1 with machine := s1.machine.modifyRegsOnCore c (·.withConsumed w) }
  | none => completeYieldTo st tid

/-- **seL4-MCS's `activateThread` yield completion on core `c`**: the core's
current thread, when its yield link names a context, completes that yield
(`completeCurrentYield`); a core with no current thread, a current thread with
no TCB and one with no link leave the state as it is. -/
def activateThreadOnCore (st : SystemState) (c : CoreId) : SystemState :=
  match st.scheduler.currentOnCore c with
  | some tid =>
    match st.getTcb? tid with
    | some t =>
      match t.yieldToCode with
      | 0 => st
      | k + 1 => completeCurrentYield st c tid ⟨k⟩
    | none => st
  | none => st

/-- `activateThreadOnCore` as compiled: the current thread read as its code, so
no `some` is built, and the linked case out of line.  On the path every entry
takes until a link is set, the step reads two codes and answers its input.
Out of line itself: inlined, its branches meet in the entry's own body, and a
join point there builds what the entry carries across it (the timer entry's
step result pair, one cell per tick); called, it takes the state and hands it
back, building nothing. -/
@[noinline] def activateThreadOnCoreImpl (st : SystemState) (c : CoreId) : SystemState :=
  match st.scheduler.currentCode.get c with
  | 0 => st
  | k + 1 =>
    match st.getTcb? ⟨k⟩ with
    | some t =>
      match t.yieldToCode with
      | 0 => st
      | j + 1 => completeCurrentYield st c ⟨k⟩ ⟨j⟩
    | none => st

@[csimp] theorem activateThreadOnCore_eq_impl :
    @activateThreadOnCore = @activateThreadOnCoreImpl := by
  funext st c
  unfold activateThreadOnCore activateThreadOnCoreImpl SchedulerState.currentOnCore
  cases st.scheduler.currentCode.get c <;> rfl

/-- `activateThreadOnCore` for a per-core entry's raw core id: nothing when the
id names no core, as the verified steps commit nothing for such an id
(`PriorityInheritance.settleResidencyAt`'s guard).  Out of line, as
`activateThreadOnCoreImpl` is, so its branch makes no join point in an entry. -/
@[noinline] def activateThreadAt (st : SystemState) (coreId : UInt64) : SystemState :=
  match Concurrency.coreIdOfUInt64? coreId with
  | some c => activateThreadOnCore st c
  | none => st

/-! ### The step's shape -/

/-- The activation on a core whose current thread has no yield link is the
identity. -/
theorem activateThreadOnCore_of_unlinked (st : SystemState) (c : CoreId)
    (h : ∀ tid t, st.scheduler.currentOnCore c = some tid → st.getTcb? tid = some t →
      t.yieldToCode = 0) :
    activateThreadOnCore st c = st := by
  unfold activateThreadOnCore
  split
  · rename_i tid hC
    split
    · rename_i t hT
      rw [h tid t hC hT]
    · rfl
  · rfl

/-- **Until a link is set the step is the identity**: on a state in which no
thread holds a yield link — every state before the yieldTo invocation exists,
since boot sets none (`bootTcbShape`) and nothing else writes one — the
activation leaves the state as it is. -/
theorem activateThreadOnCore_of_noLinks (st : SystemState) (c : CoreId)
    (h : ∀ tid t, st.getTcb? tid = some t → t.yieldToCode = 0) :
    activateThreadOnCore st c = st :=
  activateThreadOnCore_of_unlinked st c fun tid t _ hT => h tid t hT

theorem activateThreadAt_of_noLinks (st : SystemState) (coreId : UInt64)
    (h : ∀ tid t, st.getTcb? tid = some t → t.yieldToCode = 0) :
    activateThreadAt st coreId = st := by
  unfold activateThreadAt
  split
  · exact activateThreadOnCore_of_noLinks st _ h
  · rfl

/-- **The linked case is the completion**: on a current thread linked to a
context, the activation is `completeYieldTo` of it with the bank mirroring the
two registers. -/
theorem activateThreadOnCore_of_linked (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (t : TCB) (k : Nat) (hC : st.scheduler.currentOnCore c = some tid)
    (hT : st.getTcb? tid = some t) (hY : t.yieldToCode = k + 1) :
    activateThreadOnCore st c = completeCurrentYield st c tid ⟨k⟩ := by
  unfold activateThreadOnCore
  rw [hC]; dsimp only; rw [hT]; dsimp only; rw [hY]

/-- What the activation is, by cases: its input, or the completion of the
current thread's link. -/
theorem activateThreadOnCore_cases (st : SystemState) (c : CoreId) :
    activateThreadOnCore st c = st ∨
      ∃ tid t k, st.scheduler.currentOnCore c = some tid ∧ st.getTcb? tid = some t ∧
        t.yieldToCode = k + 1 ∧ activateThreadOnCore st c = completeCurrentYield st c tid ⟨k⟩ := by
  unfold activateThreadOnCore
  split
  · rename_i tid hC
    split
    · rename_i t hT
      split
      · exact Or.inl rfl
      · rename_i k hY
        exact Or.inr ⟨tid, t, k, hC, hT, hY, rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

/-! ### What the step writes

The object store, as `completeYieldTo` writes it, and core `c`'s register bank;
every other field of the state is its input's. -/

theorem completeCurrentYield_objects (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (s : SeLe4n.SchedContextId) :
    (completeCurrentYield st c tid s).objects = (completeYieldTo st tid).objects := by
  unfold completeCurrentYield; split <;> rfl

/-- The linked case writes the objects and the machine alone. -/
theorem completeCurrentYield_eq_objects_machine (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (s : SeLe4n.SchedContextId) :
    completeCurrentYield st c tid s =
      { st with objects := (completeCurrentYield st c tid s).objects,
                machine := (completeCurrentYield st c tid s).machine } := by
  unfold completeCurrentYield
  split
  · dsimp only
    rw [SystemState.completeYieldTo_eq_objects st tid]
  · rw [SystemState.completeYieldTo_eq_objects st tid]

/-- The linked case's machine: its input's, or core `c`'s bank with the two
registers written. -/
theorem completeCurrentYield_machine (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (s : SeLe4n.SchedContextId) :
    (completeCurrentYield st c tid s).machine = st.machine ∨
      ∃ w : UInt64, (completeCurrentYield st c tid s).machine =
        st.machine.modifyRegsOnCore c (·.withConsumed w) := by
  unfold completeCurrentYield
  have hM : (completeYieldTo st tid).machine = st.machine := by
    rw [SystemState.completeYieldTo_eq_objects st tid]
  split
  · exact Or.inr ⟨_, by dsimp only; rw [hM]⟩
  · exact Or.inl hM

/-- The activation writes the objects and the machine alone. -/
theorem activateThreadOnCore_eq_objects_machine (st : SystemState) (c : CoreId) :
    activateThreadOnCore st c =
      { st with objects := (activateThreadOnCore st c).objects,
                machine := (activateThreadOnCore st c).machine } := by
  rcases activateThreadOnCore_cases st c with h | ⟨tid, t, k, _, _, _, h⟩ <;> rw [h]
  exact completeCurrentYield_eq_objects_machine st c tid ⟨k⟩

theorem activateThreadOnCore_scheduler (st : SystemState) (c : CoreId) :
    (activateThreadOnCore st c).scheduler = st.scheduler := by
  rw [activateThreadOnCore_eq_objects_machine]

theorem activateThreadOnCore_tlbShootdown (st : SystemState) (c : CoreId) :
    (activateThreadOnCore st c).tlbShootdown = st.tlbShootdown := by
  rw [activateThreadOnCore_eq_objects_machine]

theorem activateThreadOnCore_referenceTables (st : SystemState) (c : CoreId) :
    (activateThreadOnCore st c).referenceTables = st.referenceTables := by
  rw [activateThreadOnCore_eq_objects_machine]; rfl

/-- The activation's machine: its input's, or core `c`'s bank with the two
registers the completion wrote. -/
theorem activateThreadOnCore_machine (st : SystemState) (c : CoreId) :
    (activateThreadOnCore st c).machine = st.machine ∨
      ∃ w : UInt64, (activateThreadOnCore st c).machine =
        st.machine.modifyRegsOnCore c (·.withConsumed w) := by
  rcases activateThreadOnCore_cases st c with h | ⟨tid, t, k, _, _, _, h⟩ <;> rw [h]
  · exact Or.inl rfl
  · exact completeCurrentYield_machine st c tid ⟨k⟩

/-- The activation's objects: its input's, or `completeYieldTo` of core `c`'s
current thread. -/
theorem activateThreadOnCore_objects (st : SystemState) (c : CoreId) :
    (activateThreadOnCore st c).objects = st.objects ∨
      ∃ tid, st.scheduler.currentOnCore c = some tid ∧
        (activateThreadOnCore st c).objects = (completeYieldTo st tid).objects := by
  rcases activateThreadOnCore_cases st c with h | ⟨tid, t, k, hC, _, _, h⟩ <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr ⟨tid, hC, completeCurrentYield_objects st c tid ⟨k⟩⟩

/-- Every field of the machine but the register banks is its input's. -/
theorem activateThreadOnCore_machine_eq_regs (st : SystemState) (c : CoreId) :
    (activateThreadOnCore st c).machine = { st.machine with
      coreRegs := (activateThreadOnCore st c).machine.coreRegs } := by
  rcases activateThreadOnCore_machine st c with h | ⟨w, h⟩ <;> rw [h] <;> rfl

/-- No core's bank but `c`'s is written. -/
theorem activateThreadOnCore_regsOnCore_ne (st : SystemState) (c d : CoreId) (h : d ≠ c) :
    (activateThreadOnCore st c).machine.regsOnCore d = st.machine.regsOnCore d := by
  rcases activateThreadOnCore_machine st c with e | ⟨w, e⟩ <;> rw [e]
  rw [MachineState.modifyRegsOnCore_eq]
  exact MachineState.regsOnCore_setRegsOnCore_ne _ _ _ _ (Ne.symm h)

/-! ### Invariants and the run-queue stage -/

theorem completeYieldTo_objectsAgreeOffYield (st : SystemState) (y : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : SystemState.objectsAgreeOffYield (completeYieldTo st y) st := by
  unfold completeYieldTo
  split
  · split
    · exact .refl st
    · exact (SystemState.cancelYieldTo_objectsAgreeOffYield _ _
        (SystemState.setConsumed_preserves_objects_invExt _ _ _ hInv)).trans
        (SystemState.setConsumed_objectsAgreeOffYield _ _ _ hInv)
  · exact .refl st

/-- **The activation writes the yield writes alone** in the object store: the
current thread's yield-to code and two return registers, the context's
yield-from code and consumed count. -/
theorem activateThreadOnCore_objectsAgreeOffYield (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) :
    SystemState.objectsAgreeOffYield (activateThreadOnCore st c) st := by
  rcases activateThreadOnCore_objects st c with h | ⟨tid, _, h⟩
  · exact fun x => by rw [h]
  · exact fun x => by rw [h]; exact completeYieldTo_objectsAgreeOffYield st tid hInv x

theorem activateThreadOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) : (activateThreadOnCore st c).objects.invExt := by
  rcases activateThreadOnCore_objects st c with h | ⟨tid, _, h⟩ <;> rw [h]
  · exact hInv
  · exact SystemState.completeYieldTo_preserves_objects_invExt st tid hInv

/-- **The activation keeps every taint word and reference table** (a table
reference frame): a thread's yield-to code and return registers and a context's
yield-from code and consumed count are neither, so the declassification taint
is unchanged and the step propagates none — as seL4's `activateThread`, which
moves no capability and no badge. -/
theorem activateThreadOnCore_tableReferenceFrame (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) :
    SystemState.TableReferenceFrame st (activateThreadOnCore st c) :=
  .of_map (g := KernelObject.withoutYield) (fun o => by cases o <;> rfl)
    (activateThreadOnCore_referenceTables st c) (activateThreadOnCore_objectsAgreeOffYield st c hInv)

/-- **The activation propagates no taint.** -/
theorem activateThreadOnCore_declassificationTaint (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) :
    (activateThreadOnCore st c).declassificationTaint = st.declassificationTaint :=
  (activateThreadOnCore_tableReferenceFrame st c hInv).declassificationTaint

theorem activateThreadAt_declassificationTaint (st : SystemState) (coreId : UInt64)
    (hInv : st.objects.invExt) :
    (activateThreadAt st coreId).declassificationTaint = st.declassificationTaint := by
  unfold activateThreadAt
  split
  · exact activateThreadOnCore_declassificationTaint st _ hInv
  · rfl

/-- The activation writes threads and contexts alone. -/
theorem activateThreadOnCore_writesTcbScOnly (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) : SystemState.writesTcbScOnly (activateThreadOnCore st c) st := by
  rcases activateThreadOnCore_objects st c with h | ⟨tid, _, h⟩
  · exact fun x => Or.inl (by rw [h])
  · intro x
    rw [h]
    exact SystemState.completeYieldTo_writesTcbScOnly st tid hInv x

/-- The linked case is a run-queue stage: the completion
(`completeYieldTo_runQueueStage`), then the bank, which no stage reads. -/
theorem completeCurrentYield_runQueueStage (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (s : SeLe4n.SchedContextId) :
    SystemState.RunQueueStage st (completeCurrentYield st c tid s) := by
  unfold completeCurrentYield
  split
  · exact (SystemState.completeYieldTo_runQueueStage st tid).trans
      (SystemState.RunQueueStage.of_frame rfl rfl rfl)
  · exact SystemState.completeYieldTo_runQueueStage st tid

/-- **The activation is a run-queue stage**: it keeps the run-queue links, the
table references, the release queues, the refill state and — the completion
clearing both ends of the one link it reads — the yield-link agreement. -/
theorem activateThreadOnCore_runQueueStage (st : SystemState) (c : CoreId) :
    SystemState.RunQueueStage st (activateThreadOnCore st c) := by
  rcases activateThreadOnCore_cases st c with h | ⟨tid, t, k, _, _, _, h⟩ <;> rw [h]
  · exact .refl st
  · exact completeCurrentYield_runQueueStage st c tid ⟨k⟩

theorem activateThreadAt_runQueueStage (st : SystemState) (coreId : UInt64) :
    SystemState.RunQueueStage st (activateThreadAt st coreId) := by
  unfold activateThreadAt
  split
  · exact activateThreadOnCore_runQueueStage st _
  · exact .refl st

/-- **The activation keeps the yield links in agreement.** -/
theorem activateThreadOnCore_preserves_yieldLinksAgree (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) (hY : st.yieldLinksAgree) :
    (activateThreadOnCore st c).yieldLinksAgree :=
  (activateThreadOnCore_runQueueStage st c).1.yield hInv hR hY

/-- **The activation is confined to its core**: of the per-core slots it writes
core `c`'s register bank alone, and no scheduler slot. -/
theorem activateThreadOnCore_confinedToCores (st : SystemState) (c : CoreId) :
    observableSlotsConfinedToCores st (activateThreadOnCore st c) [c] := by
  have hS := activateThreadOnCore_scheduler st c
  refine ⟨fun _ _ => by rw [hS], fun _ _ => by rw [hS], fun _ _ => by rw [hS],
    fun _ _ => by rw [hS], fun _ _ => by rw [hS], fun d hd => ?_⟩
  exact activateThreadOnCore_regsOnCore_ne st c d (fun h => hd (h ▸ List.mem_singleton_self _))

/-! ### What the activation does on a linked thread -/

/-- **The activation completes the current thread's yield**: on core `c`'s
current thread `tid`, linked to context `⟨k⟩` with consumed time
`sc.consumedReading`, the thread holds that time in `x2` (with the one-register
message info in `x1`) and no link, the context has the time taken off and no
yielder, and the core's register bank, the thread's live context, holds the same
two registers — seL4-MCS's `schedContext_completeYieldTo(ksCurThread)` at
`activateThread`. -/
theorem activateThreadOnCore_completes (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (t : TCB) (k : Nat) (sc : SchedContext) (hInv : st.objects.invExt)
    (hC : st.scheduler.currentOnCore c = some tid) (hT : st.getTcb? tid = some t)
    (hY : t.yieldToCode = k + 1) (hS : st.getSchedContext? ⟨k⟩ = some sc) :
    (activateThreadOnCore st c).getTcb? tid =
        some (t.withConsumed sc.consumedReading.toUInt64).yieldCleared ∧
      (activateThreadOnCore st c).getSchedContext? ⟨k⟩ =
        some sc.updateConsumed.yieldCleared ∧
      (activateThreadOnCore st c).machine.regsOnCore c =
        (st.machine.regsOnCore c).withConsumed sc.consumedReading.toUInt64 := by
  rw [activateThreadOnCore_of_linked st c tid t k hC hT hY]
  have hM : (completeYieldTo st tid).machine = st.machine := by
    rw [SystemState.completeYieldTo_eq_objects st tid]
  have h1 : completeYieldTo st tid = cancelYieldTo (setConsumed st ⟨k⟩ tid) tid := by
    unfold completeYieldTo; rw [hT]; dsimp only; rw [hY]
  have h2 : setConsumed st ⟨k⟩ tid =
      (st.updateSchedContext ⟨k⟩ SchedContext.updateConsumed).updateTcb tid
        (TCB.withConsumed · sc.consumedReading.toUInt64) := by
    unfold setConsumed; rw [hS]
  have hI1 := SystemState.updateSchedContext_preserves_objects_invExt st ⟨k⟩
    SchedContext.updateConsumed hInv
  have hI0 := SystemState.setConsumed_preserves_objects_invExt st ⟨k⟩ tid hInv
  rw [h2] at hI0
  have hT0 : ((st.updateSchedContext ⟨k⟩ SchedContext.updateConsumed).updateTcb tid
      (TCB.withConsumed · sc.consumedReading.toUInt64)).getTcb? tid =
      some (t.withConsumed sc.consumedReading.toUInt64) := by
    rw [SystemState.updateTcb_getTcb?_self _ _ _ hI1,
      SystemState.updateSchedContext_getTcb? _ _ _ hInv, hT]; rfl
  have hS0 : ((st.updateSchedContext ⟨k⟩ SchedContext.updateConsumed).updateTcb tid
      (TCB.withConsumed · sc.consumedReading.toUInt64)).getSchedContext? ⟨k⟩ =
      some sc.updateConsumed := by
    rw [SystemState.updateTcb_getSchedContext? _ _ _ hI1,
      SystemState.updateSchedContext_getSchedContext?_self _ _ _ hInv, hS]; rfl
  have h3 : cancelYieldTo ((st.updateSchedContext ⟨k⟩ SchedContext.updateConsumed).updateTcb tid
      (TCB.withConsumed · sc.consumedReading.toUInt64)) tid =
      (((st.updateSchedContext ⟨k⟩ SchedContext.updateConsumed).updateTcb tid
        (TCB.withConsumed · sc.consumedReading.toUInt64)).updateSchedContext ⟨k⟩
        SchedContext.yieldCleared).updateTcb tid TCB.yieldCleared := by
    unfold cancelYieldTo; rw [hT0]; dsimp only [TCB.withConsumed]; rw [hY]
  have hI2 := SystemState.updateSchedContext_preserves_objects_invExt _ ⟨k⟩
    SchedContext.yieldCleared hI0
  unfold completeCurrentYield
  rw [hS]
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · show (completeYieldTo st tid).getTcb? tid = _
    rw [h1, h2, h3, SystemState.updateTcb_getTcb?_self _ _ _ hI2,
      SystemState.updateSchedContext_getTcb? _ _ _ hI0, hT0]; rfl
  · show (completeYieldTo st tid).getSchedContext? ⟨k⟩ = _
    rw [h1, h2, h3, SystemState.updateTcb_getSchedContext? _ _ _ hI2,
      SystemState.updateSchedContext_getSchedContext?_self _ _ _ hI0, hS0]; rfl
  · rw [hM, MachineState.modifyRegsOnCore_eq, MachineState.regsOnCore_setRegsOnCore_self]

/-- **The activation keeps the core's bank its current thread's context**
(`contextMatchesCurrentOnCore`): the completion writes the thread's saved `x1`
and `x2`, and the bank takes the same two, which is why the step writes it. -/
theorem activateThreadOnCore_preserves_contextMatchesCurrentOnCore (st : SystemState)
    (c : CoreId) (hInv : st.objects.invExt) (h : contextMatchesCurrentOnCore st c) :
    contextMatchesCurrentOnCore (activateThreadOnCore st c) c := by
  rcases activateThreadOnCore_cases st c with e | ⟨tid, t, k, hC, hT, hY, _⟩
  · rw [e]; exact h
  have hBank : st.machine.regsOnCore c = t.registerContext := by
    unfold contextMatchesCurrentOnCore at h
    rw [hC] at h; dsimp only at h; rw [hT] at h
    exact beq_iff_eq.mp h
  unfold contextMatchesCurrentOnCore
  rw [activateThreadOnCore_scheduler, hC]
  dsimp only
  cases hS : st.getSchedContext? ⟨k⟩ with
  | some sc =>
    obtain ⟨hT', -, hR'⟩ := activateThreadOnCore_completes st c tid t k sc hInv hC hT hY hS
    rw [hT', hR', hBank]
    exact beq_iff_eq.mpr rfl
  | none =>
    rw [activateThreadOnCore_of_linked st c tid t k hC hT hY]
    unfold completeCurrentYield
    rw [hS]
    dsimp only
    have h1 : completeYieldTo st tid =
        (st.updateSchedContext ⟨k⟩ SchedContext.yieldCleared).updateTcb tid TCB.yieldCleared := by
      have hC0 : setConsumed st ⟨k⟩ tid = st := by unfold setConsumed; rw [hS]
      unfold completeYieldTo; rw [hT]; dsimp only; rw [hY]; dsimp only
      rw [hC0]
      unfold cancelYieldTo; rw [hT]; dsimp only; rw [hY]
    have hM : (completeYieldTo st tid).machine = st.machine := by
      rw [SystemState.completeYieldTo_eq_objects st tid]
    rw [hM, h1, SystemState.updateTcb_getTcb?_self _ _ _
      (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv),
      SystemState.updateSchedContext_getTcb? _ _ _ hInv, hT]
    exact beq_iff_eq.mpr hBank

/-! ### No current or resident thread is left with a pending yield

seL4-MCS's `setConsumed` at a context's final delete writes the yielder's saved
registers, which is sound only while those are the yielder's live registers:
the yielder must be neither a core's current thread with its frame in flight
nor a core's resident thread whose frame a vacate left unsaved.  The
activation is what keeps it so on the core an entry ran on: after the
residency settle and the activation, that core's current and resident threads
hold no yield link. -/

/-- **After the activation, core `c`'s current thread has no pending yield.** -/
theorem activateThreadOnCore_current_unlinked (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (tid : SeLe4n.ThreadId) (t : TCB)
    (hC : (activateThreadOnCore st c).scheduler.currentOnCore c = some tid)
    (hT : (activateThreadOnCore st c).getTcb? tid = some t) : t.yieldToCode = 0 := by
  rw [activateThreadOnCore_scheduler] at hC
  cases hT0 : st.getTcb? tid with
  | none =>
    rcases activateThreadOnCore_cases st c with e | ⟨tid', t', k, hC', hT', _, _⟩
    · rw [e, hT0] at hT; cases hT
    · rw [hC] at hC'; cases hC'; rw [hT0] at hT'; cases hT'
  | some t0 =>
    cases hY : t0.yieldToCode with
    | zero =>
      have e : activateThreadOnCore st c = st :=
        activateThreadOnCore_of_unlinked st c (fun tid' t' h1 h2 => by
          rw [hC] at h1; cases h1; rw [hT0] at h2; cases h2; exact hY)
      rw [e, hT0] at hT; cases hT; exact hY
    | succ k =>
      cases hS : st.getSchedContext? ⟨k⟩ with
      | some sc =>
        obtain ⟨hT', -, -⟩ := activateThreadOnCore_completes st c tid t0 k sc hInv hC hT0 hY hS
        rw [hT'] at hT; cases hT; rfl
      | none =>
        rw [activateThreadOnCore_of_linked st c tid t0 k hC hT0 hY] at hT
        unfold completeCurrentYield at hT
        rw [hS] at hT
        have h1 : completeYieldTo st tid =
            (st.updateSchedContext ⟨k⟩ SchedContext.yieldCleared).updateTcb tid TCB.yieldCleared := by
          have hC0 : setConsumed st ⟨k⟩ tid = st := by unfold setConsumed; rw [hS]
          unfold completeYieldTo; rw [hT0]; dsimp only; rw [hY]; dsimp only
          rw [hC0]
          unfold cancelYieldTo; rw [hT0]; dsimp only; rw [hY]
        rw [h1, SystemState.updateTcb_getTcb?_self _ _ _
          (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv),
          SystemState.updateSchedContext_getTcb? _ _ _ hInv, hT0] at hT
        cases hT; rfl

/-- The activation writes no residency record. -/
theorem activateThreadOnCore_residentOnCore (st : SystemState) (c d : CoreId) :
    (activateThreadOnCore st c).machine.residentOnCore d = st.machine.residentOnCore d := by
  rcases activateThreadOnCore_machine st c with h | ⟨w, h⟩ <;> rw [h]; rfl

/-- **An entry's tail leaves its core with no pending yield in reach**: after
the residency settle and the activation on core `c`, neither the core's current
thread nor its resident thread has a yield link — the resident thread is the
current one, or none (`settleResidencyOnCore_resident`). -/
theorem activateThreadOnCore_settle_unlinkedOnCore (st : SystemState) (c : CoreId)
    (hInv : (PriorityInheritance.settleResidencyOnCore st c).objects.invExt)
    (tid : SeLe4n.ThreadId) (t : TCB)
    (hR : (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore st c) c
        ).scheduler.currentOnCore c = some tid ∨
      (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore st c) c
        ).machine.residentOnCore c = some tid)
    (hT : (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore st c) c
        ).getTcb? tid = some t) : t.yieldToCode = 0 := by
  refine activateThreadOnCore_current_unlinked _ c hInv tid t ?_ hT
  rcases hR with h | h
  · exact h
  · rw [activateThreadOnCore_residentOnCore, PriorityInheritance.settleResidencyOnCore_resident] at h
    rw [activateThreadOnCore_scheduler, PriorityInheritance.settleResidencyOnCore_currentOnCore]
    split at h
    · exact h
    · cases h

end SeLe4n.Kernel
