-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.ReleaseLinks

/-! # The release-queue purge and a returned context's settle

The two release-queue writes a context handed between threads takes: its
purge off whichever release queue holds it (`purgeReplenishment`, seL4's
`tcbReleaseRemove`), and the settle of a returned context (`settleReturnedContext`,
the tail of seL4's `schedContext_donate`).  They sit below the donation
primitives, which run the settle on every return, and below
`SchedContext/Operations.lean`, which holds their frames and stages.
-/

namespace SeLe4n.Kernel.SchedContextOps

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel

/-- WS-SM SM8.B / WS-ZA ZA6.3: drop `scId`'s replenishment from the release
queue that holds it, read from the context's own link
(`SystemState.releaseRemoveAnywhere`): exact whichever core that is, so neither
a home core to compute nor a sweep over every core is needed (a context whose
bound thread is gone from the store is purged the same way). -/
def purgeReplenishment (st : SystemState) (scId : SchedContextId) : SystemState :=
  st.releaseRemoveAnywhere scId

/-- WS-ZA ZA6.3: the cores whose replenish queue the purge of `scId` writes —
the one its own link names, or none — read from the context alone, so a
footprint locks the queue the purge edits and no other. -/
def purgeReplenishCores (st : SystemState) (scId : SchedContextId) :
    List SeLe4n.Kernel.Concurrency.CoreId :=
  match st.releaseCoreOf scId with
  | some d => [d]
  | none => []

/-- WS-ZA ZA6.33: whether context `s`'s holder is not suspended
(`SystemState.holderActive`), read in a call of its own so the settle reads the
store once before it writes. -/
@[noinline] def contextHolderActive (st : SystemState) (s : SchedContextId) : Bool :=
  (st.getSchedContext? s).any st.holderActive

/-- WS-ZA ZA6.33: **the tail of seL4's `schedContext_donate` for a context
handed back to its caller**: off every release queue (`tcbReleaseRemove` of the
thread it leaves), then, while the thread it now serves is not suspended, placed
on core `c` by its refills — seL4's `postpone` of a context that is not ready,
which `doReplyTransfer` runs for a runnable receiver.  A context whose new
holder is suspended stays off every queue until `restart` resumes it. -/
def settleReturnedContext (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId)
    (s : SchedContextId) : SystemState :=
  let st1 := purgeReplenishment st s
  if contextHolderActive st1 s then st1.releasePlace c s else st1

theorem purgeReplenishment_releaseOnlyWrite (st : SystemState) (scId : SchedContextId) :
    (purgeReplenishment st scId).releaseOnlyWrite st :=
  SystemState.releaseRemoveAnywhere_releaseOnlyWrite st scId

/-- The settle is the purge, or the purge and the placement. -/
theorem settleReturnedContext_cases (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId)
    (s : SchedContextId) :
    settleReturnedContext st c s = purgeReplenishment st s ∨
      settleReturnedContext st c s = (purgeReplenishment st s).releasePlace c s := by
  unfold settleReturnedContext; dsimp only; split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The settle writes the contexts' release fields and the release queues
alone. -/
theorem settleReturnedContext_releaseOnlyWrite (st : SystemState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (s : SchedContextId) :
    (settleReturnedContext st c s).releaseOnlyWrite st := by
  rcases settleReturnedContext_cases st c s with h | h <;> rw [h]
  · exact purgeReplenishment_releaseOnlyWrite st s
  · exact (SystemState.releasePlace_releaseOnlyWrite _ c s).trans
      (purgeReplenishment_releaseOnlyWrite st s)

/-- WS-UC UC2: the settle moves no bookkeeping ghost. -/
@[simp] theorem settleReturnedContext_lifecycle (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId) (s : SchedContextId) :
    (settleReturnedContext st c s).lifecycle = st.lifecycle := by
  rw [(settleReturnedContext_releaseOnlyWrite st c s).1]
@[simp] theorem settleReturnedContext_objectIndex (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId) (s : SchedContextId) :
    (settleReturnedContext st c s).objectIndex = st.objectIndex :=
  (settleReturnedContext_releaseOnlyWrite st c s).ghostsKept.index
@[simp] theorem settleReturnedContext_objectIndexSet (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId) (s : SchedContextId) :
    (settleReturnedContext st c s).objectIndexSet = st.objectIndexSet :=
  (settleReturnedContext_releaseOnlyWrite st c s).ghostsKept.indexSet

@[simp] theorem settleReturnedContext_machine (st : SystemState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (s : SchedContextId) :
    (settleReturnedContext st c s).machine = st.machine :=
  (settleReturnedContext_releaseOnlyWrite st c s).machine

theorem purgeReplenishment_agree (st : SystemState) (scId : SchedContextId) :
    (purgeReplenishment st scId).objectsAgreeOffReleaseLinks st :=
  SystemState.releaseRemoveAnywhere_agree st scId

theorem purgeReplenishment_objects_invExt (st : SystemState) (scId : SchedContextId)
    (h : st.objects.invExt) : (purgeReplenishment st scId).objects.invExt :=
  SystemState.releaseRemoveAnywhere_objects_invExt st scId h

theorem settleReturnedContext_agree (st : SystemState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (s : SchedContextId) :
    (settleReturnedContext st c s).objectsAgreeOffReleaseLinks st := by
  rcases settleReturnedContext_cases st c s with h | h <;> rw [h]
  · exact purgeReplenishment_agree st s
  · exact (SystemState.releasePlace_agree _ c s).trans (purgeReplenishment_agree st s)

theorem settleReturnedContext_objects_invExt (st : SystemState)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (s : SchedContextId) (h : st.objects.invExt) :
    (settleReturnedContext st c s).objects.invExt := by
  rcases settleReturnedContext_cases st c s with e | e <;> rw [e]
  · exact purgeReplenishment_objects_invExt st s h
  · exact SystemState.releasePlace_objects_invExt _ c s (purgeReplenishment_objects_invExt st s h)

/-- WS-ZA ZA6.33: the purge's core is read off the release links alone, so a
step that keeps them keeps it. -/
theorem purgeReplenishCores_of_linksAgree {st st' : SystemState}
    (h : SystemState.ReleaseLinksAgree st' st) (scId : SchedContextId) :
    purgeReplenishCores st' scId = purgeReplenishCores st scId := by
  unfold purgeReplenishCores; rw [SystemState.releaseCoreOf_of_linksAgree h]

end SeLe4n.Kernel.SchedContextOps
